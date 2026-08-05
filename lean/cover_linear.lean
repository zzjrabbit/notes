import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Cover lifting and linearization of homomorphisms

This file formalizes the topological part of cover linearization for maps `f : X → M`. The
parameter `X` is a simply connected, locally path-connected, locally compact topological group;
these are the properties of the intended simply connected locally compact Lie group that the
proof uses. The value space `M` is an arbitrary second-countable Hausdorff topological space.

Mathlib does not yet provide the required classification of homomorphisms between general Lie
groups. The final Lie-theoretic step is therefore stated through `ExponentialClassification`.
For a general source group, its abstract generator need not be a single target Lie algebra element:
in the intended application it can encode an integrable Lie algebra homomorphism.

The argument has three layers:

* `ContinuousGroupHom` packages a continuous homomorphism between multiplicative topological
  groups.
* `lift` constructs the identity-based lift of such a subgroup through a covering homomorphism.
  Uniqueness of covering-space lifts forces this lift to preserve multiplication, even though it is
  initially constructed only as a continuous map.
* `existsUnique_generator` applies the abstract classification upstairs and projects the resulting
  homomorphism back to the base group.

The lifting layer assumes that the parameter group is simply connected and locally path connected.
The linearization layer additionally records local compactness of `X` and the separation and
countability assumptions on `M`. A final wrapper accepts continuous or Borel-measurable `M`-valued
data and isolates measurable-homomorphism automatic continuity in `WeylAutomaticContinuity`.
-/

open Function
open scoped BigOperators

namespace CoverLinearization

/-- A continuous homomorphism from the multiplicative group `X` to the multiplicative group `G`.

The group law is recorded explicitly so the covering-space argument can use the minimal topology
needed at each stage. -/
structure ContinuousGroupHom (X G : Type*)
    [Group X] [TopologicalSpace X] [Group G] [TopologicalSpace G] where
  /-- The group-valued curve underlying the subgroup. -/
  toFun : X → G
  /-- The underlying curve is continuous in its parameter. -/
  continuous_toFun : Continuous toFun
  /-- The parameter identity is sent to the group identity. -/
  map_one' : toFun 1 = 1
  /-- Multiplication of parameters is sent to multiplication in `G`. -/
  map_mul' : ∀ s t, toFun (s * t) = toFun s * toFun t

/-- A continuous homomorphism from the additive real line, presented multiplicatively. -/
abbrev RealContinuousGroupHom (G : Type*) [Group G] [TopologicalSpace G] :=
  ContinuousGroupHom (Multiplicative ℝ) G

/-- The multiplicative presentation of the additive real line has the same topology. -/
private def realParameterHomeomorph : Multiplicative ℝ ≃ₜ ℝ where
  toEquiv := Multiplicative.ofAdd.symm
  continuous_toFun := continuous_toAdd
  continuous_invFun := continuous_ofAdd

private instance : SimplyConnectedSpace (Multiplicative ℝ) :=
  realParameterHomeomorph.toHomotopyEquiv.simplyConnectedSpace

private instance : LocallyPathConnectedSpace (Multiplicative ℝ) :=
  realParameterHomeomorph.isOpenEmbedding.locallyPathConnectedSpace

namespace ContinuousGroupHom

variable {X G : Type*}
  [Group X] [TopologicalSpace X] [Group G] [TopologicalSpace G]

instance : CoeFun (ContinuousGroupHom X G) fun _ ↦ X → G := ⟨toFun⟩

/-- Two parameterized subgroups are equal when they agree at every parameter. -/
@[ext]
theorem ext {φ ψ : ContinuousGroupHom X G} (h : ∀ x, φ x = ψ x) : φ = ψ := by
  cases φ
  cases ψ
  simp only [mk.injEq]
  exact funext h

/-- A parameterized subgroup takes the identity to the group identity. -/
@[simp]
theorem map_one (φ : ContinuousGroupHom X G) : φ 1 = 1 := φ.map_one'

/-- The parameter group law becomes multiplication in the target group. -/
theorem map_mul (φ : ContinuousGroupHom X G) (s t : X) : φ (s * t) = φ s * φ t :=
  φ.map_mul' s t

/-- The function underlying a parameterized subgroup is continuous. -/
theorem continuous (φ : ContinuousGroupHom X G) : Continuous φ := φ.continuous_toFun

/-- The continuous map underlying a parameterized subgroup. -/
def toContinuousMap (φ : ContinuousGroupHom X G) : C(X, G) := ⟨φ, φ.continuous⟩

/-- Passing to the bundled continuous map does not change the underlying function. -/
@[simp]
theorem coe_toContinuousMap (φ : ContinuousGroupHom X G) : ⇑φ.toContinuousMap = φ := rfl

end ContinuousGroupHom

section Lift

variable {X G Gtilde : Type*}
  [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
  [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
  [Group G] [TopologicalSpace G]
  [Group Gtilde] [TopologicalSpace Gtilde] [IsTopologicalGroup Gtilde]
  (p : Gtilde →* G) (hp : IsCoveringMap p)

include p hp

/-- The continuous lift through `p` whose value at `1` is the identity of `Gtilde`.

Existence and uniqueness use simple connectedness and local path connectedness of `X`. At this
stage the result is only a continuous map; preservation of the group law is proved below. -/
noncomputable def liftContinuousMap (p : Gtilde →* G) (hp : IsCoveringMap p)
    (φ : ContinuousGroupHom X G) : C(X, Gtilde) :=
  (hp.existsUnique_continuousMap_lifts φ.toContinuousMap 1 1 (by simp)).choose

omit [IsTopologicalGroup X] [IsTopologicalGroup Gtilde] in
/-- The chosen continuous lift is based at the identity. -/
@[simp]
theorem liftContinuousMap_one (φ : ContinuousGroupHom X G) :
    liftContinuousMap p hp φ 1 = 1 :=
  (hp.existsUnique_continuousMap_lifts φ.toContinuousMap 1 1 (by simp)).choose_spec.1.1

omit [IsTopologicalGroup X] [IsTopologicalGroup Gtilde] in
/-- Composing the chosen lift with the covering homomorphism recovers the original subgroup. -/
theorem liftContinuousMap_lifts (φ : ContinuousGroupHom X G) :
    p ∘ liftContinuousMap p hp φ = φ :=
  (hp.existsUnique_continuousMap_lifts φ.toContinuousMap 1 1 (by simp)).choose_spec.1.2

/-- The identity-based continuous lift respects the parameter group law. -/
theorem liftContinuousMap_map_mul (φ : ContinuousGroupHom X G) (s t : X) :
    liftContinuousMap p hp φ (s * t) =
      liftContinuousMap p hp φ s * liftContinuousMap p hp φ t := by
  let φtilde := liftContinuousMap p hp φ
  -- For fixed `s`, translation `u ↦ φtilde (s * u)` and multiplication
  -- `u ↦ φtilde s * φtilde u` are lifts of the same path and agree at `u = 1`.
  -- Uniqueness of lifts therefore identifies them for every `u`.
  have hEq : (fun u ↦ φtilde (s * u)) = (fun u ↦ φtilde s * φtilde u) := by
    let g₁ : X → Gtilde := fun u ↦ φtilde (s * u)
    let g₂ : X → Gtilde := fun u ↦ φtilde s * φtilde u
    have hg₁ : Continuous g₁ :=
      φtilde.continuous.comp (continuous_const.mul continuous_id)
    have hg₂ : Continuous g₂ := continuous_const.mul φtilde.continuous
    have hcomp : p ∘ g₁ = p ∘ g₂ := by
      funext u
      change p (φtilde (s * u)) = p (φtilde s * φtilde u)
      rw [MonoidHom.map_mul]
      have hl (v : X) : p (φtilde v) = φ v := by
        exact congrFun (liftContinuousMap_lifts p hp φ) v
      rw [hl, hl, hl]
      exact φ.map_mul s u
    have hone : g₁ 1 = g₂ 1 := by
      simp [g₁, g₂, φtilde]
    exact hp.eq_of_comp_eq hg₁ hg₂ hcomp 1 hone
  exact congrFun hEq t

/-- The identity-based lift is itself a continuous homomorphism. -/
noncomputable def lift (φ : ContinuousGroupHom X G) : ContinuousGroupHom X Gtilde where
  toFun := liftContinuousMap p hp φ
  continuous_toFun := (liftContinuousMap p hp φ).continuous
  map_one' := liftContinuousMap_one p hp φ
  map_mul' := liftContinuousMap_map_mul p hp φ

/-- The bundled lifted subgroup is based at the identity. -/
@[simp]
theorem lift_one (φ : ContinuousGroupHom X G) : lift p hp φ 1 = 1 := by
  simp [lift]

/-- The bundled lifted subgroup projects pointwise to the original subgroup. -/
theorem lift_lifts (φ : ContinuousGroupHom X G) (x : X) : p (lift p hp φ x) = φ x := by
  exact congrFun (liftContinuousMap_lifts p hp φ) x

/-- Uniqueness of the lifted continuous homomorphism. -/
theorem lift_unique (φ : ContinuousGroupHom X G) (ψ : ContinuousGroupHom X Gtilde)
    (hψ : ∀ x, p (ψ x) = φ x) : ψ = lift p hp φ := by
  ext x
  -- Both subgroup maps are continuous lifts based at the identity, so ordinary covering-space
  -- uniqueness applies to their underlying functions.
  have hEq : (ψ : X → Gtilde) = liftContinuousMap p hp φ := by
    have hcomp : p ∘ (ψ : X → Gtilde) = p ∘ liftContinuousMap p hp φ := by
      funext t
      exact (hψ t).trans (lift_lifts p hp φ t).symm
    have hone : ψ 1 = liftContinuousMap p hp φ 1 := by simp
    exact hp.eq_of_comp_eq ψ.continuous (liftContinuousMap p hp φ).continuous hcomp 1 hone
  exact congrFun hEq x

omit [IsTopologicalGroup X] [LocallyPathConnectedSpace X] in
/-- Any two continuous lifts of the same continuous homomorphism differ by left multiplication
by a unique element of the kernel of the covering homomorphism.

The lifts need not preserve the group law: their values at one determine the constant factor.
This is the unbased counterpart of `lift_unique`. -/
theorem continuous_lifts_differ_by_constant
    (φ : ContinuousGroupHom X G) (ψ₁ ψ₂ : X → Gtilde)
    (hψ₁cont : Continuous ψ₁) (hψ₂cont : Continuous ψ₂)
    (hψ₁ : ∀ x, p (ψ₁ x) = φ x) (hψ₂ : ∀ x, p (ψ₂ x) = φ x) :
    ∃! c : Gtilde, p c = 1 ∧ ∀ x, ψ₁ x = c * ψ₂ x := by
  -- The value at one determines the only possible translation factor.
  let c := ψ₁ 1 * (ψ₂ 1)⁻¹
  have hc : p c = 1 := by
    simp only [c, map_mul, map_inv, hψ₁, hψ₂, ContinuousGroupHom.map_one,
      inv_one, mul_one]
  have hEq : ψ₁ = fun x ↦ c * ψ₂ x := by
    -- Left multiplication by a kernel element does not change the projection, and the two
    -- resulting lifts agree at one.
    have hcomp : p ∘ ψ₁ = p ∘ fun x ↦ c * ψ₂ x := by
      funext x
      simp only [Function.comp_apply, map_mul, hc, one_mul, hψ₁, hψ₂]
    exact hp.eq_of_comp_eq hψ₁cont (hψ₂cont.const_mul c) hcomp 1 (by simp [c])
  refine ⟨c, ⟨hc, fun x ↦ congrFun hEq x⟩, ?_⟩
  intro c' hc'
  have hone := (hc'.2 1).symm
  apply mul_right_cancel (b := ψ₂ 1)
  exact hone.trans (congrFun hEq 1)

end Lift

/-- Classification data for continuous homomorphisms from a parameter group `X` to `G`.

For a simply connected Lie group `X`, the intended generator type `g` can be a type of integrable
Lie algebra homomorphisms from the Lie algebra of `X` to that of `G`. Unlike the real
one-parameter case, a general source Lie group is not classified by a single element of the target
Lie algebra. The abstract generator type keeps that distinction explicit. -/
structure ExponentialClassification
    (X G g : Type*) [Group X] [TopologicalSpace X] [Group G] [TopologicalSpace G] where
  /-- The homomorphism value at `x` associated with a generator. -/
  exp : X → g → G
  /-- Every classified homomorphism sends the source identity to the target identity. -/
  exp_one : ∀ a, exp 1 a = 1
  /-- For a fixed generator, multiplication in `X` corresponds to multiplication in `G`. -/
  exp_mul : ∀ a x y, exp (x * y) a = exp x a * exp y a
  /-- Every classified homomorphism is continuous in its source variable. -/
  continuous_exp : ∀ a, Continuous fun x ↦ exp x a
  /-- Every continuous homomorphism from `X` has exactly one generator. -/
  existsUnique_generator : ∀ φ : ContinuousGroupHom X G,
    ∃! a, ∀ x, φ x = exp x a

/-- The real-parameter specialization of `ExponentialClassification`. -/
abbrev RealExponentialClassification
    (G g : Type*) [Group G] [TopologicalSpace G] :=
  ExponentialClassification (Multiplicative ℝ) G g

namespace ExponentialClassification

variable {X G g : Type*}
  [Group X] [TopologicalSpace X] [Group G] [TopologicalSpace G]

/-- The continuous homomorphism generated by `a`. -/
def homomorphism (C : ExponentialClassification X G g) (a : g) :
    ContinuousGroupHom X G where
  toFun x := C.exp x a
  continuous_toFun := C.continuous_exp a
  map_one' := C.exp_one a
  map_mul' := C.exp_mul a

/-- Evaluating the homomorphism generated by `a` evaluates its exponential classification. -/
@[simp]
theorem homomorphism_apply (C : ExponentialClassification X G g) (a : g) (x : X) :
    C.homomorphism a x = C.exp x a := rfl

end ExponentialClassification

section Linearization

variable {X G Gtilde g : Type*}
  [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
  [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
  [Group G] [TopologicalSpace G]
  [Group Gtilde] [TopologicalSpace Gtilde] [IsTopologicalGroup Gtilde]
  (p : Gtilde →* G) (hp : IsCoveringMap p)
  (C : ExponentialClassification X Gtilde g)

include hp

/-- A continuous homomorphism from `X` to the base has a unique generator after lifting to a
covering group. -/
theorem existsUnique_generator (φ : ContinuousGroupHom X G) :
    ∃! a : g, ∀ x : X, φ x = p (C.exp x a) := by
  -- Classify the canonical lifted subgroup upstairs, where the exponential interface is
  -- available, then project the resulting curve through `p`.
  obtain ⟨a, ha, ha_unique⟩ := C.existsUnique_generator (lift p hp φ)
  refine ⟨a, ?_, ?_⟩
  · intro x
    rw [← lift_lifts p hp φ x, ha x]
  · intro a' ha'
    -- A competing projected generator defines another identity-based lift of `φ`; uniqueness of
    -- the lift turns equality after projection into equality upstairs.
    have hLift : C.homomorphism a' = lift p hp φ :=
      lift_unique p hp φ (C.homomorphism a') fun x ↦ (ha' x).symm
    apply ha_unique a'
    intro x
    exact congrArg (fun ψ : ContinuousGroupHom X Gtilde ↦ ψ x) hLift.symm

/-- The cover-linearization formula for a function `f : X → M` projected from a homomorphism.

Here `X` records the topological consequences needed from a simply connected, locally compact Lie
group. The codomain `M` is an arbitrary second-countable Hausdorff topological space.

Uniqueness is deliberately stated using both `φ` and `f`: an arbitrary projection `π` need not be
injective, so the displayed formula for `f` alone cannot determine the generator. -/
theorem cover_linearization
    {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [LocallyCompactSpace X]
    (f : X → M) (π : G → M) (φ : ContinuousGroupHom X G)
    (hf : ∀ x, f x = π (φ x)) :
    ∃! a : g,
      (∀ x : X, φ x = p (C.exp x a)) ∧
      (∀ x : X, f x = π (p (C.exp x a))) := by
  obtain ⟨a, ha, ha_unique⟩ := existsUnique_generator p hp C φ
  -- The formula for `f` is obtained by substituting the classified subgroup into `hf`; uniqueness
  -- still comes from the group-valued formula, since `π` is arbitrary.
  refine ⟨a, ⟨ha, fun x ↦ (hf x).trans congr(π $(ha x))⟩, ?_⟩
  intro a' ha'
  exact ha_unique a' ha'.1

/-- Cover linearization together with the classification of all continuous lifts.

For the unique generator `a`, every continuous lift of `φ` is uniquely of the form
`c * C.exp x a`, where the constant `c` lies in the kernel of `p`. Thus dropping the choice of
basepoint introduces exactly one constant parameter and no further solutions. -/
theorem cover_linearization_with_lifts
    {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [LocallyCompactSpace X]
    (f : X → M) (π : G → M) (φ : ContinuousGroupHom X G)
    (hf : ∀ x, f x = π (φ x)) :
    ∃! a : g,
      (∀ x : X, φ x = p (C.exp x a)) ∧
      (∀ x : X, f x = π (p (C.exp x a))) ∧
      ∀ ψ : X → Gtilde, Continuous ψ → (∀ x, p (ψ x) = φ x) →
        ∃! c : Gtilde, p c = 1 ∧ ∀ x, ψ x = c * C.exp x a := by
  obtain ⟨a, ha, ha_unique⟩ := cover_linearization p hp C f π φ hf
  refine ⟨a, ⟨ha.1, ha.2, ?_⟩, ?_⟩
  · intro ψ hψcont hψ
    -- Compare an arbitrary lift with the exponential lift. Their sole freedom is the kernel
    -- element measuring the discrepancy at one.
    obtain ⟨c, hc, hc_unique⟩ :=
      continuous_lifts_differ_by_constant p hp φ ψ (C.homomorphism a)
        hψcont (C.homomorphism a).continuous hψ (fun x ↦ (ha.1 x).symm)
    refine ⟨c, hc, ?_⟩
    intro c' hc'
    exact hc_unique c' hc'
  · intro a' ha'
    exact ha_unique a' ⟨ha'.1, ha'.2.1⟩

/-- Topological regularity hypotheses available for a map between arbitrary Borel spaces. -/
def HasWeylRegularity {X M : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [TopologicalSpace M] [MeasurableSpace M] (f : X → M) : Prop :=
  Continuous f ∨ Measurable f

/-- The missing automatic-continuity API isolated as a reusable interface.

For locally compact second-countable Hausdorff groups `X` and `G`, the standard automatic-
continuity theorem says that a Borel-measurable algebraic homomorphism `X → G` is continuous.

Only the measurable theorem is included.  There is intentionally no field asserting that a
homomorphism with bounded or relatively compact range is continuous: discontinuous homomorphisms
`ℝ → S¹` show that such a statement is false even for compact Lie groups.  Once Mathlib has the
general measurable-homomorphism theorem, this structure can be instantiated from it without
changing the covering-space argument. -/
structure WeylAutomaticContinuity
    (X G : Type*) [Group X] [TopologicalSpace X] [MeasurableSpace X]
    [IsTopologicalGroup X] [BorelSpace X] [T2Space X]
    [SecondCountableTopology X] [LocallyCompactSpace X]
    [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [IsTopologicalGroup G] [BorelSpace G] [T2Space G]
    [SecondCountableTopology G] [LocallyCompactSpace G] where
  /-- A measurable algebraic homomorphism is continuous. -/
  continuous_of_measurable : ∀ φ : X → G, Measurable φ → φ 1 = 1 →
    (∀ x y, φ (x * y) = φ x * φ y) → Continuous φ

/-- Apply cover linearization to an algebraic homomorphism under a standard regularity hypothesis
on its `M`-valued projection.

The data have the following roles:

* `hφcont` handles the continuous branch directly;
* `hφmeas` records how measurability of the `M`-valued solution `f` makes the constructed map `φ`
  measurable.

After continuity of `φ` is established, `hφone` and `hφmul` package it as a continuous
homomorphism. The theorem then delegates all covering, classification, uniqueness, and
classification-of-lifts work to `cover_linearization_with_lifts`. -/
theorem cover_linearization_with_lifts_of_regular_solution
    {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [T2Space X] [SecondCountableTopology X]
    [MeasurableSpace M] [BorelSpace M]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [SecondCountableTopology G] [LocallyCompactSpace G]
    (W : WeylAutomaticContinuity X G)
    (f : X → M) (π : G → M) (φ : X → G)
    (hregular : HasWeylRegularity f)
    (hφcont : Continuous f → Continuous φ)
    (hφmeas : Measurable f → Measurable φ)
    (hφone : φ 1 = 1) (hφmul : ∀ x y, φ (x * y) = φ x * φ y)
    (hf : ∀ x, f x = π (φ x)) :
    ∃! a : g,
      (∀ x : X, φ x = p (C.exp x a)) ∧
      (∀ x : X, f x = π (p (C.exp x a))) ∧
      ∀ ψ : X → Gtilde, Continuous ψ → (∀ x, p (ψ x) = φ x) →
        ∃! c : Gtilde, p c = 1 ∧ ∀ x, ψ x = c * C.exp x a := by
  have hφcontinuous : Continuous φ := by
    rcases hregular with hfcont | hfmeas
    · exact hφcont hfcont
    · exact W.continuous_of_measurable φ (hφmeas hfmeas) hφone hφmul
  let φ' : ContinuousGroupHom X G :=
    { toFun := φ
      continuous_toFun := hφcontinuous
      map_one' := hφone
      map_mul' := hφmul }
  simpa [φ'] using cover_linearization_with_lifts p hp C f π φ' hf

end Linearization

end CoverLinearization

