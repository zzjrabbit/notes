use serde::Deserialize;
use statrs::distribution::{ContinuousCDF, Normal};
use std::{env, error::Error, fs};

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Configuration {
    model: ModelParameters,
    sweep: WeightSweep,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ModelParameters {
    population: f64,
    earliest_arrival: f64,
    log_mean: f64,
    log_stddev: f64,
    arrival_window_start: f64,
    arrival_window_end: f64,
    service_rate: f64,
    distance: f64,
    comfortable_speed: f64,
    minimum_speed: f64,
    maximum_speed: f64,
    quality_decline: f64,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct WeightSweep {
    quality_over_time: Vec<f64>,
    speed_over_time: Vec<f64>,
    output_csv: String,
}

#[derive(Clone, Copy, Debug)]
struct RelativeWeights {
    quality_over_time: f64,
    speed_over_time: f64,
}

#[derive(Clone, Copy, Debug)]
struct QueueWindow {
    start: f64,
    end: f64,
}

#[derive(Clone, Copy, Debug)]
struct Solution {
    weights: RelativeWeights,
    arrival_time: f64,
    departure_time: f64,
    speed: f64,
    walking_time: f64,
    waiting_time: f64,
    quality_loss: f64,
    total_penalty: f64,
}

struct Model<'a> {
    parameters: &'a ModelParameters,
    standard_normal: Normal,
    queue: Option<QueueWindow>,
}

impl Configuration {
    fn validate(&self) -> Result<(), String> {
        self.model.validate()?;
        if self.sweep.quality_over_time.is_empty() || self.sweep.speed_over_time.is_empty() {
            return Err("both weight lists must be nonempty".to_owned());
        }
        for (name, values) in [
            ("quality_over_time", &self.sweep.quality_over_time),
            ("speed_over_time", &self.sweep.speed_over_time),
        ] {
            if values
                .iter()
                .any(|value| !value.is_finite() || *value < 0.0)
            {
                return Err(format!("every {name} value must be finite and nonnegative"));
            }
        }
        if self.sweep.output_csv.trim().is_empty() {
            return Err("output_csv must not be empty".to_owned());
        }
        Ok(())
    }
}

impl ModelParameters {
    fn validate(&self) -> Result<(), String> {
        let positive = [
            ("population", self.population),
            ("log_stddev", self.log_stddev),
            ("service_rate", self.service_rate),
            ("distance", self.distance),
            ("comfortable_speed", self.comfortable_speed),
            ("minimum_speed", self.minimum_speed),
            ("maximum_speed", self.maximum_speed),
        ];
        for (name, value) in positive {
            if !value.is_finite() || value <= 0.0 {
                return Err(format!("{name} must be finite and positive"));
            }
        }
        if self.arrival_window_start < self.earliest_arrival
            || self.arrival_window_start >= self.arrival_window_end
        {
            return Err(
                "arrival window must start after earliest_arrival and end after it".to_owned(),
            );
        }
        if self.minimum_speed > self.maximum_speed {
            return Err("minimum_speed must not exceed maximum_speed".to_owned());
        }
        if !(0.0..=1.0).contains(&self.quality_decline) {
            return Err("quality_decline must lie in [0, 1]".to_owned());
        }
        Ok(())
    }
}

impl<'a> Model<'a> {
    fn new(parameters: &'a ModelParameters) -> Result<Self, String> {
        parameters.validate()?;
        let standard_normal = Normal::new(0.0, 1.0).map_err(|error| error.to_string())?;
        let mut model = Self {
            parameters,
            standard_normal,
            queue: None,
        };
        model.queue = model.queue_window()?;
        Ok(model)
    }

    fn arrival_cdf(&self, time: f64) -> f64 {
        let p = self.parameters;
        if time <= p.earliest_arrival {
            0.0
        } else {
            let z = ((time - p.earliest_arrival).ln() - p.log_mean) / p.log_stddev;
            self.standard_normal.cdf(z)
        }
    }

    fn arrival_pdf(&self, time: f64) -> f64 {
        let p = self.parameters;
        if time <= p.earliest_arrival {
            return 0.0;
        }
        let delay = time - p.earliest_arrival;
        let z = (delay.ln() - p.log_mean) / p.log_stddev;
        (-0.5 * z * z).exp() / (delay * p.log_stddev * std::f64::consts::TAU.sqrt())
    }

    fn maximum_arrival_density(&self) -> f64 {
        let p = self.parameters;
        let mode = p.earliest_arrival + (p.log_mean - p.log_stddev.powi(2)).exp();
        self.arrival_pdf(mode)
    }

    fn queue_window(&self) -> Result<Option<QueueWindow>, String> {
        let p = self.parameters;
        let maximum_rate = p.population * self.maximum_arrival_density();
        if maximum_rate <= p.service_rate {
            return Ok(None);
        }

        let radius = p.log_stddev * (2.0 * (maximum_rate / p.service_rate).ln()).sqrt();
        let centre = p.log_mean - p.log_stddev.powi(2);
        let start = p.earliest_arrival + (centre - radius).exp();
        let falling_crossing = p.earliest_arrival + (centre + radius).exp();
        let start_cdf = self.arrival_cdf(start);
        let net_queue = |time: f64| {
            p.population * (self.arrival_cdf(time) - start_cdf) - p.service_rate * (time - start)
        };

        let mut left = falling_crossing;
        if net_queue(left) <= 0.0 {
            return Ok(Some(QueueWindow { start, end: left }));
        }
        let mut span = (falling_crossing - start).max(1.0);
        let mut right = left + span;
        for _ in 0..100 {
            if net_queue(right) <= 0.0 {
                break;
            }
            span *= 2.0;
            right = left + span;
        }
        if net_queue(right) > 0.0 {
            return Err("failed to bracket the time at which the queue clears".to_owned());
        }

        for _ in 0..100 {
            let middle = 0.5 * (left + right);
            if net_queue(middle) > 0.0 {
                left = middle;
            } else {
                right = middle;
            }
        }
        Ok(Some(QueueWindow {
            start,
            end: 0.5 * (left + right),
        }))
    }

    fn waiting_time(&self, arrival_time: f64) -> f64 {
        let Some(queue) = self.queue else {
            return 0.0;
        };
        if arrival_time <= queue.start || arrival_time >= queue.end {
            return 0.0;
        }
        let p = self.parameters;
        p.population / p.service_rate
            * (self.arrival_cdf(arrival_time) - self.arrival_cdf(queue.start))
            - (arrival_time - queue.start)
    }

    fn arrival_penalty(&self, arrival_time: f64, weights: RelativeWeights) -> f64 {
        self.waiting_time(arrival_time)
            + weights.quality_over_time
                * self.parameters.quality_decline
                * self.arrival_cdf(arrival_time)
    }

    fn speed_penalty(&self, speed: f64, weights: RelativeWeights) -> f64 {
        let p = self.parameters;
        let excess = ((speed - p.comfortable_speed) / p.comfortable_speed).max(0.0);
        p.distance / speed + weights.speed_over_time * excess.powi(2)
    }

    fn optimal_arrival_time(&self, weights: RelativeWeights) -> f64 {
        let p = self.parameters;
        let mut candidates = vec![p.arrival_window_start, p.arrival_window_end];

        if let Some(queue) = self.queue {
            candidates.extend([queue.start, queue.end]);

            let denominator =
                p.population / p.service_rate + weights.quality_over_time * p.quality_decline;
            if denominator > 0.0 {
                let target_density = 1.0 / denominator;
                let maximum_density = self.maximum_arrival_density();
                if target_density <= maximum_density {
                    let radius =
                        p.log_stddev * (2.0 * (maximum_density / target_density).ln()).sqrt();
                    let centre = p.log_mean - p.log_stddev.powi(2);
                    candidates.extend([
                        p.earliest_arrival + (centre - radius).exp(),
                        p.earliest_arrival + (centre + radius).exp(),
                    ]);
                }
            }
        }

        candidates
            .into_iter()
            .filter(|time| *time >= p.arrival_window_start && *time <= p.arrival_window_end)
            .min_by(|left, right| {
                self.arrival_penalty(*left, weights)
                    .total_cmp(&self.arrival_penalty(*right, weights))
                    .then_with(|| left.total_cmp(right))
            })
            .expect("arrival interval contributes at least one candidate")
    }

    fn optimal_speed(&self, weights: RelativeWeights) -> f64 {
        let p = self.parameters;
        let mut candidates = vec![p.minimum_speed, p.maximum_speed];
        if (p.minimum_speed..=p.maximum_speed).contains(&p.comfortable_speed) {
            candidates.push(p.comfortable_speed);
        }

        if weights.speed_over_time > 0.0 {
            let derivative = |speed: f64| {
                -p.distance / speed.powi(2)
                    + 2.0 * weights.speed_over_time * (speed - p.comfortable_speed)
                        / p.comfortable_speed.powi(2)
            };
            let mut left = p.comfortable_speed.max(p.minimum_speed);
            let mut right = p.maximum_speed;
            if left <= right && derivative(left) <= 0.0 && derivative(right) >= 0.0 {
                for _ in 0..100 {
                    let middle = 0.5 * (left + right);
                    if derivative(middle) <= 0.0 {
                        left = middle;
                    } else {
                        right = middle;
                    }
                }
                candidates.push(0.5 * (left + right));
            }
        }

        candidates
            .into_iter()
            .min_by(|left, right| {
                self.speed_penalty(*left, weights)
                    .total_cmp(&self.speed_penalty(*right, weights))
            })
            .expect("speed interval contributes at least one candidate")
    }

    fn solve(&self, weights: RelativeWeights) -> Solution {
        let p = self.parameters;
        let arrival_time = self.optimal_arrival_time(weights);
        let speed = self.optimal_speed(weights);
        let walking_time = p.distance / speed;
        let departure_time = arrival_time - walking_time;
        let waiting_time = self.waiting_time(arrival_time);
        let quality_loss = p.quality_decline * self.arrival_cdf(arrival_time);
        let total_penalty =
            self.arrival_penalty(arrival_time, weights) + self.speed_penalty(speed, weights);
        Solution {
            weights,
            arrival_time,
            departure_time,
            speed,
            walking_time,
            waiting_time,
            quality_loss,
            total_penalty,
        }
    }
}

fn clock(minutes: f64) -> String {
    let total_seconds = (minutes * 60.0).round() as i64;
    let hours = total_seconds.div_euclid(3600);
    let minutes = total_seconds.rem_euclid(3600) / 60;
    let seconds = total_seconds.rem_euclid(60);
    format!("{hours:02}:{minutes:02}:{seconds:02}")
}

fn write_csv(path: &str, solutions: &[Solution]) -> Result<(), Box<dyn Error>> {
    let mut output = String::from(
        "quality_over_time,speed_over_time,arrival_time,arrival_clock,departure_time,departure_clock,speed,speed_display,walking_time,waiting_time,quality_loss,total_penalty\n",
    );
    for solution in solutions {
        output.push_str(&format!(
            "{:.6},{:.6},{:.6},{},{:.6},{},{:.6},{:.1},{:.6},{:.6},{:.6},{:.6}\n",
            solution.weights.quality_over_time,
            solution.weights.speed_over_time,
            solution.arrival_time,
            clock(solution.arrival_time),
            solution.departure_time,
            clock(solution.departure_time),
            solution.speed,
            solution.speed,
            solution.walking_time,
            solution.waiting_time,
            solution.quality_loss,
            solution.total_penalty,
        ));
    }
    fs::write(path, output)?;
    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let path = env::args()
        .nth(1)
        .ok_or("usage: cafeteria <configuration.toml>")?;
    let source = fs::read_to_string(path)?;
    let configuration: Configuration = toml::from_str(&source)?;
    configuration.validate()?;
    let model = Model::new(&configuration.model)?;

    let mut solutions = Vec::new();
    for &quality_over_time in &configuration.sweep.quality_over_time {
        for &speed_over_time in &configuration.sweep.speed_over_time {
            solutions.push(model.solve(RelativeWeights {
                quality_over_time,
                speed_over_time,
            }));
        }
    }
    write_csv(&configuration.sweep.output_csv, &solutions)?;

    if let Some(queue) = model.queue {
        println!("queue_start = {}", clock(queue.start));
        println!("queue_end   = {}", clock(queue.end));
    } else {
        println!("queue       = never forms");
    }
    println!("rows        = {}", solutions.len());
    println!("output      = {}", configuration.sweep.output_csv);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parameters() -> ModelParameters {
        ModelParameters {
            population: 600.0,
            earliest_arrival: 720.0,
            log_mean: 2.30,
            log_stddev: 0.45,
            arrival_window_start: 720.1,
            arrival_window_end: 780.0,
            service_rate: 25.0,
            distance: 650.0,
            comfortable_speed: 80.0,
            minimum_speed: 50.0,
            maximum_speed: 160.0,
            quality_decline: 0.50,
        }
    }

    fn weights() -> RelativeWeights {
        RelativeWeights {
            quality_over_time: 20.0,
            speed_over_time: 4.0,
        }
    }

    #[test]
    fn cdf_starts_at_zero() {
        let parameters = parameters();
        let model = Model::new(&parameters).unwrap();
        assert_eq!(model.arrival_cdf(parameters.earliest_arrival), 0.0);
        assert!(model.arrival_cdf(parameters.earliest_arrival + 10.0) > 0.0);
    }

    #[test]
    fn sufficiently_fast_service_prevents_a_queue() {
        let mut parameters = parameters();
        parameters.service_rate = 1_000.0;
        let model = Model::new(&parameters).unwrap();
        assert!(model.queue.is_none());
        assert_eq!(model.waiting_time(735.0), 0.0);
    }

    #[test]
    fn queue_is_positive_between_its_endpoints() {
        let parameters = parameters();
        let model = Model::new(&parameters).unwrap();
        let queue = model.queue.unwrap();
        assert_eq!(model.waiting_time(queue.start), 0.0);
        assert!(model.waiting_time(0.5 * (queue.start + queue.end)) > 0.0);
        assert_eq!(model.waiting_time(queue.end), 0.0);
    }

    #[test]
    fn solution_is_finite_and_respects_bounds() {
        let parameters = parameters();
        let model = Model::new(&parameters).unwrap();
        let solution = model.solve(weights());
        assert!(solution.total_penalty.is_finite());
        assert!(
            (parameters.arrival_window_start..=parameters.arrival_window_end)
                .contains(&solution.arrival_time)
        );
        assert!((parameters.minimum_speed..=parameters.maximum_speed).contains(&solution.speed));
    }

    #[test]
    fn equal_penalties_prefer_the_earliest_arrival() {
        let mut parameters = parameters();
        parameters.arrival_window_start = 726.0;
        let model = Model::new(&parameters).unwrap();
        let queue = model.queue.unwrap();
        let solution = model.solve(RelativeWeights {
            quality_over_time: 0.0,
            speed_over_time: 0.0,
        });
        assert!((solution.arrival_time - queue.end).abs() < 1e-9);
    }

    #[test]
    fn larger_speed_penalty_never_increases_optimal_speed() {
        let parameters = parameters();
        let model = Model::new(&parameters).unwrap();
        let fast = model.solve(RelativeWeights {
            quality_over_time: 0.0,
            speed_over_time: 1.0,
        });
        let gentle = model.solve(RelativeWeights {
            quality_over_time: 0.0,
            speed_over_time: 8.0,
        });
        assert!(gentle.speed <= fast.speed);
    }
}
