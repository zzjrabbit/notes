import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.RepresentationTheory.Continuous.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
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
def WeylAutomaticContinuity
    (X G : Type*) [Group X] [TopologicalSpace X] [MeasurableSpace X]
    [IsTopologicalGroup X] [BorelSpace X] [T2Space X]
    [SecondCountableTopology X] [LocallyCompactSpace X]
    [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [IsTopologicalGroup G] [BorelSpace G] [T2Space G]
    [SecondCountableTopology G] [LocallyCompactSpace G] : Prop :=
  ∀ φ : X → G, Measurable φ → φ 1 = 1 →
    (∀ x y, φ (x * y) = φ x * φ y) → Continuous φ

namespace WeylAutomaticContinuity

variable {X G : Type*}
  [Group X] [TopologicalSpace X] [MeasurableSpace X]
  [IsTopologicalGroup X] [BorelSpace X] [T2Space X]
  [SecondCountableTopology X] [LocallyCompactSpace X]
  [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [IsTopologicalGroup G] [BorelSpace G] [T2Space G]
  [SecondCountableTopology G] [LocallyCompactSpace G]

/-- A measurable algebraic homomorphism is continuous. -/
theorem continuous_of_measurable (W : WeylAutomaticContinuity X G)
    (φ : X → G) (hφ : Measurable φ) (hone : φ 1 = 1)
    (hmul : ∀ x y, φ (x * y) = φ x * φ y) : Continuous φ :=
  W φ hφ hone hmul

end WeylAutomaticContinuity

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
    · exact W φ (hφmeas hfmeas) hφone hφmul
  let φ' : ContinuousGroupHom X G :=
    { toFun := φ
      continuous_toFun := hφcontinuous
      map_one' := hφone
      map_mul' := hφmul }
  simpa [φ'] using cover_linearization_with_lifts p hp C f π φ' hf

end Linearization

section MinimalRepresentations

/-!
### Minimal representations

The preceding theorems formalize the covering-space part of the argument.  The proposed
minimal-representation theorem needs additional Lie-group infrastructure which is not currently
available in Mathlib: a notion of Lie-group dimension, universal covers of Lie groups, and the
comparison of the quotients obtained from two dense one-parameter representations.

The definitions below make those missing hypotheses explicit.  In particular, they do not encode
the false assertion that a dense connected subgroup of a connected Lie group is open.  The two
comparison predicates below are only properties: this file does not assert that arbitrary
representations satisfy them.
-/

/-! A dimension label used by the minimality predicate.

This is only a local interface because the present file does not model finite-dimensional
manifolds.  The field records a dimension value; no geometric existence theorem is asserted here.
-/
class LieGroupDimension (G : Type*) [Group G] [TopologicalSpace G] where
  dimension : ℕ

namespace LieGroupDimension

/-- Notation-friendly projection for the dimension interface. -/
abbrev dim (G : Type*) [Group G] [TopologicalSpace G] [LieGroupDimension G] : ℕ :=
  LieGroupDimension.dimension G

end LieGroupDimension

/-- The scalar-valued matrix coefficient of a continuous linear representation. -/
def matrixCoefficient
    {G V : Type*} [Monoid G] [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [Module ℝ V]
    (ρ : ContRepresentation ℝ G V) (ell : V →L[ℝ] ℝ) (v : V) : G → ℝ :=
  fun g ↦ ell (ρ g v)

@[simp]
theorem matrixCoefficient_apply
    {G V : Type*} [Monoid G] [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [Module ℝ V]
    (ρ : ContRepresentation ℝ G V) (ell : V →L[ℝ] ℝ) (v : V) (g : G) :
    matrixCoefficient ρ ell v g = ell (ρ g v) := rfl

/-- The two finite-dimensional minimality conditions for a matrix coefficient.

`cyclic` says that the vector generates the whole representation, while `separating` says that
the orbit of the covector detects every nonzero vector.  The vector formulation of separation is
convenient in Lean and implies the corresponding statement for every subspace. -/
def IsObservable
    {G V : Type*} [Group G] [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [Module ℝ V]
    (ρ : ContRepresentation ℝ G V) (v : V) (ell : V →L[ℝ] ℝ) : Prop :=
  Submodule.span ℝ (Set.range (fun g : G ↦ ρ g v)) = ⊤ ∧
    ∀ w, (∀ g : G, ell (ρ g w) = 0) → w = 0

namespace IsObservable

variable {G V : Type*} [Group G] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module ℝ V]

/-- The orbit of the coefficient vector spans the representation space. -/
theorem cyclic {ρ : ContRepresentation ℝ G V} {v : V} {ell : V →L[ℝ] ℝ}
    (h : IsObservable ρ v ell) :
    Submodule.span ℝ (Set.range (fun g : G ↦ ρ g v)) = ⊤ := h.1

/-- The orbit of the coefficient covector separates vectors. -/
theorem separating {ρ : ContRepresentation ℝ G V} {v : V} {ell : V →L[ℝ] ℝ}
    (h : IsObservable ρ v ell) :
    ∀ w, (∀ g : G, ell (ρ g w) = 0) → w = 0 := h.2

end IsObservable

/-- The target group acts faithfully on the coefficient space.

This condition removes group directions which are invisible to the matrix coefficient.  It is
strictly stronger than observability: observability concerns the vectors and covectors in `V`,
whereas faithfulness concerns the kernel of the action of `G` itself. -/
def IsFaithful
    {G V : Type*} [Group G] [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [Module ℝ V]
    (ρ : ContRepresentation ℝ G V) : Prop :=
  Function.Injective (fun g : G ↦ ρ g)

namespace IsFaithful

variable {G V : Type*} [Group G] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module ℝ V]

/-- Equal operators come from equal elements of the target group. -/
theorem injective {ρ : ContRepresentation ℝ G V} (h : IsFaithful ρ) :
    Function.Injective (fun g : G ↦ ρ g) := h

end IsFaithful

/-- A dense continuous subgroup representation whose observable is a finite-dimensional matrix
coefficient.

The separate continuity field is intentional.  Mathlib's `ContRepresentation` guarantees that
each operator `ρ g` is continuous on `V`, but it does not require the parameter map
`g ↦ ρ g` to be continuous. -/
structure MatrixCoefficientRepresentation
    (X G V : Type*)
    [Group X] [TopologicalSpace X] [Group G] [TopologicalSpace G]
    [ConnectedSpace G] [Nontrivial G]
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [T2Space V] [ContinuousSMul ℝ V]
    [FiniteDimensional ℝ V]
    (f : X → ℝ) where
  /-- The group-valued parameterization. -/
  φ : ContinuousGroupHom X G
  /-- A finite-dimensional continuous linear representation of the target group. -/
  ρ : ContRepresentation ℝ G V
  /-- The vector in the matrix coefficient. -/
  v : V
  /-- The covector in the matrix coefficient. -/
  ell : V →L[ℝ] ℝ
  /-- Continuity of the coefficient as a function on the target group. -/
  continuous_coefficient : Continuous (matrixCoefficient ρ ell v)
  /-- The coefficient realizes the function. -/
  realizes : ∀ x, f x = matrixCoefficient ρ ell v (φ x)
  /-- The parameterized subgroup is dense. -/
  dense_range : DenseRange φ
  /-- The coefficient representation is observable. -/
  observable : IsObservable ρ v ell
  /-- The target group has no nontrivial kernel in the coefficient representation. -/
  faithful : IsFaithful ρ
  /-- The representation action is continuous in the group parameter. -/
  continuous_orbit : ∀ w, Continuous (fun g : G ↦ ρ g w)

/-!
The span of a parameter orbit is not an extra datum.  It is a submodule of the finite-dimensional
Hausdorff topological vector space `V`, hence is closed by the standard finite-dimensional
topological-vector-space theorem.
-/

theorem parameter_span_closed
    {X G V : Type*}
    [Group X] [TopologicalSpace X] [Group G] [TopologicalSpace G]
    [ConnectedSpace G] [Nontrivial G]
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [T2Space V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V]
    {f : X → ℝ} (R : MatrixCoefficientRepresentation X G V f) :
    IsClosed (Submodule.span ℝ (Set.range (fun x : X ↦ R.ρ (R.φ x) R.v)) : Set V) := by
  exact Submodule.closed_of_finiteDimensional _

namespace MatrixCoefficientRepresentation

variable {X G V : Type*}
  [Group X] [TopologicalSpace X] [Group G] [TopologicalSpace G]
  [ConnectedSpace G] [Nontrivial G]
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [T2Space V] [ContinuousSMul ℝ V]
  [FiniteDimensional ℝ V] {f : X → ℝ}

/-- Faithfulness lets the coefficient representation distinguish target-group elements. -/
theorem faithful_eq_of_representation_eq
    (R : MatrixCoefficientRepresentation X G V f) {g h : G}
    (hρ : R.ρ g = R.ρ h) : g = h := by
  exact R.faithful.injective hρ

/-- The only target-group element represented by the identity operator is the identity. -/
theorem faithful_eq_one
    (R : MatrixCoefficientRepresentation X G V f) {g : G}
    (hρ : R.ρ g = 1) : g = 1 := by
  apply R.faithful.injective
  simpa using hρ

/-- The observable function associated with a vector in the coefficient representation. -/
def observableMap (R : MatrixCoefficientRepresentation X G V f) : V →ₗ[ℝ] (X → ℝ) where
  toFun w x := R.ell (R.ρ (R.φ x) w)
  map_add' w₁ w₂ := by
    funext x
    simp
  map_smul' c w := by
    funext x
    simp

@[simp]
theorem observableMap_apply (R : MatrixCoefficientRepresentation X G V f) (w : V) (x : X) :
    R.observableMap w x = R.ell (R.ρ (R.φ x) w) := rfl

/-- If a vector gives the zero observable function, it is zero. -/
theorem observableMap_eq_zero_iff (R : MatrixCoefficientRepresentation X G V f) (w : V) :
    R.observableMap w = 0 ↔ w = 0 := by
  constructor
  · intro hw
    apply R.observable.separating w
    intro g
    have hclosed : IsClosed {g : G | R.ell (R.ρ g w) = 0} :=
      isClosed_eq (R.ell.continuous.comp (R.continuous_orbit w)) continuous_const
    exact R.dense_range.induction_on g hclosed (fun x => by
      have hx := congrFun hw x
      simpa using hx)
  · intro hw
    subst w
    simp

/-- The observable map is injective for an observable coefficient. -/
theorem observableMap_injective (R : MatrixCoefficientRepresentation X G V f) :
    Function.Injective R.observableMap := by
  intro w₁ w₂ h
  apply sub_eq_zero.mp
  apply (R.observableMap_eq_zero_iff (w₁ - w₂)).mp
  rw [map_sub, h, sub_self]

/-- Subspace form of the separation condition. -/
theorem separating_submodule (R : MatrixCoefficientRepresentation X G V f)
    (W : Submodule ℝ V)
    (hW : ∀ w ∈ W, ∀ g : G, R.ell (R.ρ g w) = 0) : W = ⊥ := by
  apply le_antisymm
  · intro w hw
    rw [Submodule.mem_bot]
    exact R.observable.separating w (hW w hw)
  · exact bot_le

/-- The target orbit of the coefficient vector is already generated by the dense parameter orbit. -/
theorem parameter_orbit_span_eq_top (R : MatrixCoefficientRepresentation X G V f) :
    Submodule.span ℝ (Set.range (fun x : X ↦ R.ρ (R.φ x) R.v)) = ⊤ := by
  let S : Submodule ℝ V :=
    Submodule.span ℝ (Set.range (fun x : X ↦ R.ρ (R.φ x) R.v))
  have hclosed : IsClosed {g : G | R.ρ g R.v ∈ S} := by
    change IsClosed ((fun g : G ↦ R.ρ g R.v) ⁻¹' (S : Set V))
    exact parameter_span_closed R |>.preimage (R.continuous_orbit R.v)
  have hmem : ∀ g : G, R.ρ g R.v ∈ S := by
    intro g
    exact R.dense_range.induction_on g hclosed (fun x =>
      Submodule.subset_span ⟨x, rfl⟩)
  change S = ⊤
  apply top_unique
  rw [← R.observable.cyclic]
  exact Submodule.span_le.2 (by
    rintro _ ⟨g, hg⟩
    rw [← hg]
    exact hmem g)

/-- Right translation of a scalar-valued function on a group. -/
def translate {X : Type*} [Group X] (a : X) (h : X → ℝ) : X → ℝ :=
  fun x ↦ h (x * a)

@[simp]
theorem translate_one {X : Type*} [Group X] (h : X → ℝ) : translate 1 h = h := by
  funext x
  simp [translate]

theorem translate_translate {X : Type*} [Group X] (a b : X) (h : X → ℝ) :
    translate a (translate b h) = translate (a * b) h := by
  funext x
  simp [translate, mul_assoc]

theorem translate_add {X : Type*} [Group X] (a : X) (h₁ h₂ : X → ℝ) :
    translate a (h₁ + h₂) = translate a h₁ + translate a h₂ := by
  funext x
  simp [translate]

theorem translate_smul {X : Type*} [Group X] (a : X) (c : ℝ) (h : X → ℝ) :
    translate a (c • h) = c • translate a h := by
  funext x
  simp [translate]

/-- The linear span of all right translates of a function. -/
def translationSpan {X : Type*} [Group X] (f : X → ℝ) : Submodule ℝ (X → ℝ) :=
  Submodule.span ℝ (Set.range (fun a : X ↦ translate a f))

@[simp]
theorem translate_realizes (R : MatrixCoefficientRepresentation X G V f) (a : X) :
    translate a f = R.observableMap (R.ρ (R.φ a) R.v) := by
  funext x
  change f (x * a) = R.ell (R.ρ (R.φ x) (R.ρ (R.φ a) R.v))
  rw [R.realizes (x * a), matrixCoefficient_apply, R.φ.map_mul, map_mul]
  rfl

theorem translationSpan_le_observableMap_range
    (R : MatrixCoefficientRepresentation X G V f) :
    translationSpan f ≤ LinearMap.range R.observableMap := by
  apply Submodule.span_le.2
  rintro _ ⟨a, rfl⟩
  refine ⟨R.ρ (R.φ a) R.v, ?_⟩
  exact (R.translate_realizes a).symm

theorem observableMap_range_le_translationSpan
    (R : MatrixCoefficientRepresentation X G V f) :
    LinearMap.range R.observableMap ≤ translationSpan f := by
  rintro _ ⟨w, rfl⟩
  have hw : w ∈ Submodule.span ℝ (Set.range (fun a : X ↦ R.ρ (R.φ a) R.v)) := by
    rw [R.parameter_orbit_span_eq_top]
    exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem w hw =>
      rcases hw with ⟨a, ha⟩
      rw [← ha, ← R.translate_realizes a]
      exact Submodule.subset_span ⟨a, rfl⟩
  | zero =>
      simpa using (Submodule.zero_mem (translationSpan f))
  | add w₁ w₂ hw₁ hw₂ ih₁ ih₂ =>
      simpa using (Submodule.add_mem (translationSpan f) ih₁ ih₂)
  | smul c w hw ih =>
      simpa using (Submodule.smul_mem (translationSpan f) c ih)

/-- The translation space of a matrix coefficient is exactly the observable range. -/
theorem translationSpan_eq_observableMap_range
    (R : MatrixCoefficientRepresentation X G V f) :
    translationSpan f = LinearMap.range R.observableMap := by
  exact le_antisymm R.translationSpan_le_observableMap_range
    R.observableMap_range_le_translationSpan

theorem translationSpan_finiteDimensional
    (R : MatrixCoefficientRepresentation X G V f) :
    FiniteDimensional ℝ (translationSpan f) := by
  rw [R.translationSpan_eq_observableMap_range]
  infer_instance

/-- The original coefficient vector is sent to `f` by the observable map. -/
theorem observableMap_vector (R : MatrixCoefficientRepresentation X G V f) :
    R.observableMap R.v = f := by
  funext x
  simpa [observableMap, matrixCoefficient] using (R.realizes x).symm

/-- The translation operator on the ambient function space. -/
def translateLinearMap {X : Type*} [Group X] (a : X) :
    (X → ℝ) →ₗ[ℝ] (X → ℝ) where
  toFun h := translate a h
  map_add' h₁ h₂ := translate_add a h₁ h₂
  map_smul' c h := translate_smul a c h

@[simp]
theorem translateLinearMap_apply {X : Type*} [Group X] (a : X) (h : X → ℝ) :
    translateLinearMap a h = translate a h := rfl

/-- The observable map intertwines the parameter action with right translation. -/
theorem translate_observableMap (R : MatrixCoefficientRepresentation X G V f)
    (a : X) (w : V) :
    translate a (R.observableMap w) =
      R.observableMap (R.ρ (R.φ a) w) := by
  funext x
  change R.ell (R.ρ (R.φ (x * a)) w) =
    R.ell (R.ρ (R.φ x) (R.ρ (R.φ a) w))
  rw [R.φ.map_mul, map_mul]
  rfl

/-- The intrinsic translation space is linearly equivalent to every observable coefficient space. -/
noncomputable def intrinsicEquiv
    (R : MatrixCoefficientRepresentation X G V f) :
    V ≃ₗ[ℝ] translationSpan f :=
  (LinearEquiv.ofInjective R.observableMap R.observableMap_injective).trans
    (LinearEquiv.ofEq _ _ (R.translationSpan_eq_observableMap_range).symm)

@[simp]
theorem intrinsicEquiv_coe_apply
    (R : MatrixCoefficientRepresentation X G V f) (w : V) :
    (R.intrinsicEquiv w : X → ℝ) = R.observableMap w := by
  simp [intrinsicEquiv]

theorem intrinsicEquiv_vector (R : MatrixCoefficientRepresentation X G V f) :
    (R.intrinsicEquiv R.v : X → ℝ) = f := by
  rw [R.intrinsicEquiv_coe_apply, R.observableMap_vector]

end MatrixCoefficientRepresentation

/-! Any two observable coefficient spaces have the same intrinsic translation model. -/

namespace MatrixCoefficientRepresentation

variable {X G₁ G₂ V₁ V₂ : Type*}
  [Group X] [TopologicalSpace X]
  [Group G₁] [TopologicalSpace G₁] [ConnectedSpace G₁] [Nontrivial G₁]
  [Group G₂] [TopologicalSpace G₂] [ConnectedSpace G₂] [Nontrivial G₂]
  [AddCommGroup V₁] [Module ℝ V₁] [TopologicalSpace V₁] [IsTopologicalAddGroup V₁]
  [T2Space V₁] [ContinuousSMul ℝ V₁]
  [FiniteDimensional ℝ V₁]
  [AddCommGroup V₂] [Module ℝ V₂] [TopologicalSpace V₂] [IsTopologicalAddGroup V₂]
  [T2Space V₂] [ContinuousSMul ℝ V₂]
  [FiniteDimensional ℝ V₂]
  {f : X → ℝ}

/-- The canonical vector-space comparison induced by the intrinsic translation space. -/
noncomputable def observableEquiv
    (R₁ : MatrixCoefficientRepresentation X G₁ V₁ f)
    (R₂ : MatrixCoefficientRepresentation X G₂ V₂ f) :
    V₁ ≃ₗ[ℝ] V₂ :=
  R₁.intrinsicEquiv.trans R₂.intrinsicEquiv.symm

theorem observableEquiv_vector
    (R₁ : MatrixCoefficientRepresentation X G₁ V₁ f)
    (R₂ : MatrixCoefficientRepresentation X G₂ V₂ f) :
    R₁.observableEquiv R₂ R₁.v = R₂.v := by
  apply R₂.intrinsicEquiv.injective
  simp only [observableEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  exact (R₁.intrinsicEquiv_vector).trans (R₂.intrinsicEquiv_vector).symm

/-- The intrinsic comparison intertwines the two parameterized actions.

This is the precise equivariance statement supplied by the common translation space.  It is an
intertwining statement for the parameter group `X`; by itself it does not produce a map between the
ambient target groups `G₁` and `G₂`. -/
theorem observableEquiv_intertwines
    (R₁ : MatrixCoefficientRepresentation X G₁ V₁ f)
    (R₂ : MatrixCoefficientRepresentation X G₂ V₂ f)
    (x : X) (w : V₁) :
    R₁.observableEquiv R₂ (R₁.ρ (R₁.φ x) w) =
      R₂.ρ (R₂.φ x) (R₁.observableEquiv R₂ w) := by
  apply R₂.intrinsicEquiv.injective
  apply Subtype.ext
  have hE : R₂.intrinsicEquiv (R₁.observableEquiv R₂ w) = R₁.intrinsicEquiv w := by
    simp [observableEquiv]
  have hEfun : R₂.observableMap (R₁.observableEquiv R₂ w) = R₁.observableMap w := by
    rw [← R₂.intrinsicEquiv_coe_apply, ← R₁.intrinsicEquiv_coe_apply]
    exact congrArg (fun z : translationSpan f => (z : X → ℝ)) hE
  have hE' : R₂.intrinsicEquiv
      (R₁.observableEquiv R₂ (R₁.ρ (R₁.φ x) w)) =
      R₁.intrinsicEquiv (R₁.ρ (R₁.φ x) w) := by
    simp [observableEquiv]
  have hE'fun : R₂.observableMap
      (R₁.observableEquiv R₂ (R₁.ρ (R₁.φ x) w)) =
      R₁.observableMap (R₁.ρ (R₁.φ x) w) := by
    rw [← R₂.intrinsicEquiv_coe_apply, ← R₁.intrinsicEquiv_coe_apply]
    exact congrArg (fun z : translationSpan f => (z : X → ℝ)) hE'
  rw [R₂.intrinsicEquiv_coe_apply, R₂.intrinsicEquiv_coe_apply]
  calc
    R₂.observableMap (R₁.observableEquiv R₂ (R₁.ρ (R₁.φ x) w)) =
        R₁.observableMap (R₁.ρ (R₁.φ x) w) := hE'fun
    _ = translate x (R₁.observableMap w) := (R₁.translate_observableMap x w).symm
    _ = translate x (R₂.observableMap (R₁.observableEquiv R₂ w)) := by rw [hEfun]
    _ = R₂.observableMap (R₂.ρ (R₂.φ x) (R₁.observableEquiv R₂ w)) :=
      R₂.translate_observableMap x (R₁.observableEquiv R₂ w)

/-- The two representations identify the same parameter pairs at the operator level. -/
theorem parameter_operator_eq_iff
    (R₁ : MatrixCoefficientRepresentation X G₁ V₁ f)
    (R₂ : MatrixCoefficientRepresentation X G₂ V₂ f)
    (x y : X) :
    R₁.ρ (R₁.φ x) = R₁.ρ (R₁.φ y) ↔
      R₂.ρ (R₂.φ x) = R₂.ρ (R₂.φ y) := by
  constructor
  · intro h
    ext z
    calc
      R₂.ρ (R₂.φ x) z =
          R₁.observableEquiv R₂
            (R₁.ρ (R₁.φ x) ((R₁.observableEquiv R₂).symm z)) := by
              rw [R₁.observableEquiv_intertwines]
              simp
      _ = R₁.observableEquiv R₂
            (R₁.ρ (R₁.φ y) ((R₁.observableEquiv R₂).symm z)) := by
              rw [h]
      _ = R₂.ρ (R₂.φ y) z := by
              rw [R₁.observableEquiv_intertwines]
              simp
  · intro h
    ext z
    calc
      R₁.ρ (R₁.φ x) z =
          (R₁.observableEquiv R₂).symm
            (R₂.ρ (R₂.φ x) ((R₁.observableEquiv R₂) z)) := by
              rw [← R₁.observableEquiv_intertwines]
              simp
      _ = (R₁.observableEquiv R₂).symm
            (R₂.ρ (R₂.φ y) ((R₁.observableEquiv R₂) z)) := by
              rw [h]
      _ = R₁.ρ (R₁.φ y) z := by
              rw [← R₁.observableEquiv_intertwines]
              simp

/-- Faithfulness upgrades the operator-level statement to equality in the parameterized groups. -/
theorem parameter_eq_iff
    (R₁ : MatrixCoefficientRepresentation X G₁ V₁ f)
    (R₂ : MatrixCoefficientRepresentation X G₂ V₂ f)
    (x y : X) :
    R₁.φ x = R₁.φ y ↔ R₂.φ x = R₂.φ y := by
  constructor
  · intro h
    apply R₂.faithful.injective
    apply R₁.parameter_operator_eq_iff R₂ x y |>.mp
    simpa [h]
  · intro h
    apply R₁.faithful.injective
    apply R₁.parameter_operator_eq_iff R₂ x y |>.mpr
    simpa [h]

/-- The parameter action is conjugated by the intrinsic comparison as an endomorphism. -/
theorem observableEquiv_conj_parameter_action
    (R₁ : MatrixCoefficientRepresentation X G₁ V₁ f)
    (R₂ : MatrixCoefficientRepresentation X G₂ V₂ f)
    (x : X) :
    (R₁.observableEquiv R₂).conj (R₁.ρ (R₁.φ x)).toLinearMap =
      (R₂.ρ (R₂.φ x)).toLinearMap := by
  ext z
  change R₁.observableEquiv R₂
      (R₁.ρ (R₁.φ x) ((R₁.observableEquiv R₂).symm z)) =
    R₂.ρ (R₂.φ x) z
  rw [R₁.observableEquiv_intertwines]
  simp

end MatrixCoefficientRepresentation

namespace MatrixCoefficientRepresentation

variable {X G V : Type*}
  [Group X] [TopologicalSpace X] [Group G] [TopologicalSpace G]
  [ConnectedSpace G] [Nontrivial G]
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [T2Space V] [ContinuousSMul ℝ V]
  [FiniteDimensional ℝ V] {f : X → ℝ}

/-- A matrix-coefficient representation automatically represents a continuous function. -/
theorem continuous_function (R : MatrixCoefficientRepresentation X G V f) : Continuous f := by
  rw [show f = matrixCoefficient R.ρ R.ell R.v ∘ R.φ by
    funext x
    exact R.realizes x]
  exact R.continuous_coefficient.comp R.φ.continuous

/-- Minimality with respect to finite-dimensional matrix-coefficient representations.

The comparison ranges over both the target group and the finite-dimensional coefficient space. The
dimension being minimized is still the dimension of the target group. -/
def IsMinimal (_R : MatrixCoefficientRepresentation X G V f) [LieGroupDimension G] : Prop :=
  ∀ {G' V' : Type} [Group G'] [TopologicalSpace G'] [ConnectedSpace G'] [Nontrivial G']
    [LieGroupDimension G']
    [AddCommGroup V'] [Module ℝ V'] [TopologicalSpace V'] [IsTopologicalAddGroup V']
    [T2Space V'] [ContinuousSMul ℝ V'] [FiniteDimensional ℝ V'],
    MatrixCoefficientRepresentation X G' V' f →
      LieGroupDimension.dim G ≤ LieGroupDimension.dim G'

end MatrixCoefficientRepresentation

/-! A universal-cover predicate for the group homomorphisms used below. -/

/-- The part of the universal-cover definition needed by this file.

The existence and Lie-group construction of universal covers are not asserted here; whenever a
cover is available, this proposition packages its covering, surjectivity, and simple-connectedness
properties.
The `surjective` field is included because a covering map in the minimal topological API need not
itself be the full universal-cover statement. -/
def IsUniversalCover
    (Gtilde G : Type*) [Group Gtilde] [TopologicalSpace Gtilde] [Group G] [TopologicalSpace G]
    (p : Gtilde →* G) : Prop :=
  IsCoveringMap p ∧ Function.Surjective p ∧ SimplyConnectedSpace Gtilde

namespace IsUniversalCover

variable {Gtilde G : Type*}
  [Group Gtilde] [TopologicalSpace Gtilde] [Group G] [TopologicalSpace G]
  {p : Gtilde →* G}

theorem is_covering (h : IsUniversalCover Gtilde G p) : IsCoveringMap p := h.1

theorem surjective (h : IsUniversalCover Gtilde G p) : Function.Surjective p := h.2.1

theorem simply_connected (h : IsUniversalCover Gtilde G p) : SimplyConnectedSpace Gtilde := h.2.2

end IsUniversalCover

/-- An admissible representation together with its covering and exponential data. -/
structure CoveredRepresentation
    (X G V Gtilde 𝔤 : Type*)
    [Group X] [TopologicalSpace X] [Group G] [TopologicalSpace G]
    [ConnectedSpace G] [Nontrivial G]
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [T2Space V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V]
    [Group Gtilde] [TopologicalSpace Gtilde]
    (f : X → ℝ) where
  base : MatrixCoefficientRepresentation X G V f
  p : Gtilde →* G
  universal_cover : IsUniversalCover Gtilde G p
  exponential : ExponentialClassification X Gtilde 𝔤

namespace CoveredRepresentation

variable {X G V Gtilde 𝔤 : Type*}
  [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
  [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
  [Group G] [TopologicalSpace G] [ConnectedSpace G] [Nontrivial G]
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [T2Space V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V]
  [Group Gtilde] [TopologicalSpace Gtilde] [IsTopologicalGroup Gtilde] {f : X → ℝ}

/-- The dimension-minimality predicate for a covered representation. -/
def IsMinimal (R : CoveredRepresentation X G V Gtilde 𝔤 f) [LieGroupDimension G] : Prop :=
  MatrixCoefficientRepresentation.IsMinimal (_R := R.base)

/-- The unique generator supplied by the covering-linearization theorem.

This is noncomputable because it is obtained by choosing the witness from an `∃!` theorem. -/
noncomputable def generator (R : CoveredRepresentation X G V Gtilde 𝔤 f) : 𝔤 :=
  Classical.choose
    (CoverLinearization.existsUnique_generator R.p R.universal_cover.is_covering R.exponential
      R.base.φ)

/-- The chosen generator reproduces the represented subgroup. -/
theorem generator_spec (R : CoveredRepresentation X G V Gtilde 𝔤 f) (x : X) :
    R.base.φ x = R.p (R.exponential.exp x R.generator) := by
  exact (Classical.choose_spec
    (CoverLinearization.existsUnique_generator R.p R.universal_cover.is_covering R.exponential
      R.base.φ)).1 x

/-- The chosen generator is unique among all generators for the represented subgroup. -/
theorem generator_unique (R : CoveredRepresentation X G V Gtilde 𝔤 f) {a : 𝔤}
    (ha : ∀ x, R.base.φ x = R.p (R.exponential.exp x a)) :
    a = R.generator := by
  exact (Classical.choose_spec
    (CoverLinearization.existsUnique_generator R.p R.universal_cover.is_covering R.exponential
      R.base.φ)).2 a ha

end CoveredRepresentation

/-- Infinitesimal data for an exponentially compatible coefficient representation.

`IsFaithful` is a statement about the group representation.  It does not, in the present abstract
API, imply that the infinitesimal representation below is injective.  The latter is therefore
recorded explicitly. -/
structure ExponentialRepresentationData
    {X G V Gtilde 𝔤 : Type*}
    [Group X] [TopologicalSpace X] [Group G] [TopologicalSpace G]
    [ConnectedSpace G] [Nontrivial G]
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [T2Space V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V]
    [Group Gtilde] [TopologicalSpace Gtilde]
  [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    {f : X → ℝ}
    (R : CoveredRepresentation X G V Gtilde 𝔤 f) where
  /-- The infinitesimal representation on the coefficient space. -/
  dρ : 𝔤 →ₗ[ℝ] Module.End ℝ V
  /-- The infinitesimal action respects the commutator bracket on endomorphisms. -/
  dρ_map_lie : ∀ ξ η,
    dρ ⁅ξ, η⁆ = dρ ξ * dρ η - dρ η * dρ ξ
  /-- Infinitesimal faithfulness. -/
  dρ_injective : Function.Injective dρ
  /-- The abstract operator exponential supplied by the Lie-group interface. -/
  operatorExp : X → Module.End ℝ V → Module.End ℝ V
  /-- The operator exponential separates infinitesimal operators. -/
  operatorExp_injective :
    ∀ {A B : Module.End ℝ V},
      (∀ x : X, operatorExp x A = operatorExp x B) → A = B
  /-- The group representation and infinitesimal representation have compatible exponentials. -/
  dρ_exp : ∀ (x : X) (ξ : 𝔤),
    (R.base.ρ (R.p (R.exponential.exp x ξ))).toLinearMap = operatorExp x (dρ ξ)

/-! The property needed to compare two exponential representations.

This is deliberately a proposition, not a structure asserting that the comparison exists.  The
existence of such a comparison for arbitrary covered representations is not a standard theorem
available under the hypotheses of this file.  A concrete Lie-group construction may establish this
property, after which the conditional algebraic consequence below applies. -/
def CommonExponentialComparison
    {X G₁ G₂ V₁ V₂ Gtilde₁ Gtilde₂ 𝔤₁ 𝔤₂ : Type*}
    [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    [Group G₁] [TopologicalSpace G₁] [ConnectedSpace G₁] [Nontrivial G₁]
    [Group G₂] [TopologicalSpace G₂] [ConnectedSpace G₂] [Nontrivial G₂]
    [AddCommGroup V₁] [Module ℝ V₁] [TopologicalSpace V₁] [IsTopologicalAddGroup V₁]
    [T2Space V₁] [ContinuousSMul ℝ V₁] [FiniteDimensional ℝ V₁]
    [AddCommGroup V₂] [Module ℝ V₂] [TopologicalSpace V₂] [IsTopologicalAddGroup V₂]
    [T2Space V₂] [ContinuousSMul ℝ V₂] [FiniteDimensional ℝ V₂]
    [Group Gtilde₁] [TopologicalSpace Gtilde₁] [IsTopologicalGroup Gtilde₁]
    [Group Gtilde₂] [TopologicalSpace Gtilde₂] [IsTopologicalGroup Gtilde₂]
    [LieRing 𝔤₁] [LieAlgebra ℝ 𝔤₁]
    [LieRing 𝔤₂] [LieAlgebra ℝ 𝔤₂]
    {f : X → ℝ}
    (R₁ : CoveredRepresentation X G₁ V₁ Gtilde₁ 𝔤₁ f)
    (R₂ : CoveredRepresentation X G₂ V₂ Gtilde₂ 𝔤₂ f)
    (D₁ : ExponentialRepresentationData R₁)
    (D₂ : ExponentialRepresentationData R₂) : Prop :=
  ∃ generatorEquiv : 𝔤₁ ≃ₗ⁅ℝ⁆ 𝔤₂,
    (∀ ξ,
      (R₁.base.observableEquiv R₂.base).conj (D₁.dρ ξ) =
        D₂.dρ (generatorEquiv ξ)) ∧
    (∀ (x : X) (A : Module.End ℝ V₁),
      (R₁.base.observableEquiv R₂.base).conj (D₁.operatorExp x A) =
        D₂.operatorExp x ((R₁.base.observableEquiv R₂.base).conj A))

namespace CommonExponentialComparison

variable {X G₁ G₂ V₁ V₂ Gtilde₁ Gtilde₂ 𝔤₁ 𝔤₂ : Type*}
  [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
  [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
  [Group G₁] [TopologicalSpace G₁] [ConnectedSpace G₁] [Nontrivial G₁]
  [Group G₂] [TopologicalSpace G₂] [ConnectedSpace G₂] [Nontrivial G₂]
  [AddCommGroup V₁] [Module ℝ V₁] [TopologicalSpace V₁] [IsTopologicalAddGroup V₁]
  [T2Space V₁] [ContinuousSMul ℝ V₁] [FiniteDimensional ℝ V₁]
  [AddCommGroup V₂] [Module ℝ V₂] [TopologicalSpace V₂] [IsTopologicalAddGroup V₂]
  [T2Space V₂] [ContinuousSMul ℝ V₂] [FiniteDimensional ℝ V₂]
  [Group Gtilde₁] [TopologicalSpace Gtilde₁] [IsTopologicalGroup Gtilde₁]
  [Group Gtilde₂] [TopologicalSpace Gtilde₂] [IsTopologicalGroup Gtilde₂]
  [LieRing 𝔤₁] [LieAlgebra ℝ 𝔤₁]
  [LieRing 𝔤₂] [LieAlgebra ℝ 𝔤₂]
  {f : X → ℝ}

/-- Exponential compatibility forces the comparison to carry the first generator to the second. -/
theorem generator_equiv_generator
    (R₁ : CoveredRepresentation X G₁ V₁ Gtilde₁ 𝔤₁ f)
    (R₂ : CoveredRepresentation X G₂ V₂ Gtilde₂ 𝔤₂ f)
    (D₁ : ExponentialRepresentationData R₁)
    (D₂ : ExponentialRepresentationData R₂)
    (C : CommonExponentialComparison R₁ R₂ D₁ D₂) :
    ∃ α : 𝔤₁ ≃ₗ⁅ℝ⁆ 𝔤₂, α R₁.generator = R₂.generator := by
  rcases C with ⟨generatorEquiv, hdρ_conjugate, hoperatorExp_conjugate⟩
  refine ⟨generatorEquiv, ?_⟩
  apply D₂.dρ_injective
  apply D₂.operatorExp_injective
  intro x
  calc
    D₂.operatorExp x (D₂.dρ (generatorEquiv R₁.generator)) =
        (R₁.base.observableEquiv R₂.base).conj
          (D₁.operatorExp x (D₁.dρ R₁.generator)) := by
      rw [hoperatorExp_conjugate, hdρ_conjugate]
    _ = (R₁.base.observableEquiv R₂.base).conj
          (R₁.base.ρ (R₁.base.φ x)).toLinearMap := by
      congr 1
      rw [← D₁.dρ_exp x R₁.generator, R₁.generator_spec x]
    _ = (R₂.base.ρ (R₂.base.φ x)).toLinearMap :=
      R₁.base.observableEquiv_conj_parameter_action R₂.base x
    _ = (R₂.base.ρ (R₂.p (R₂.exponential.exp x R₂.generator))).toLinearMap := by
      rw [R₂.generator_spec x]
    _ = D₂.operatorExp x (D₂.dρ R₂.generator) := D₂.dρ_exp x R₂.generator

end CommonExponentialComparison

section CommonReduction

variable {𝔤₀ 𝔤₁ 𝔤₂ : Type*}
  [LieRing 𝔤₀] [LieAlgebra ℝ 𝔤₀]
  [LieRing 𝔤₁] [LieAlgebra ℝ 𝔤₁]
  [LieRing 𝔤₂] [LieAlgebra ℝ 𝔤₂]

/-! A direct comparison of two Lie algebras is already a standard `LieEquiv`.

No separate common-algebra structure is needed here: if a concrete construction produces two
equivalences, they can be composed directly with `LieEquiv.trans`.
-/

/-! The property supplied by a common reduced Lie algebra.

The intended construction takes the connected closure of the product representation, removes the
largest *relevant* connected normal subgroup, and compares the resulting reduced representation
with both minimal representations.  That construction is not asserted here.  The following
predicate only records the property needed by the elementary comparison lemma.
-/
def CommonReducedGenerator {𝔤₀ 𝔤₁ 𝔤₂ : Type*}
    [LieRing 𝔤₀] [LieAlgebra ℝ 𝔤₀]
    [LieRing 𝔤₁] [LieAlgebra ℝ 𝔤₁]
    [LieRing 𝔤₂] [LieAlgebra ℝ 𝔤₂]
    (ξ₁ : 𝔤₁) (ξ₂ : 𝔤₂) : Prop :=
  ∃ ξ₀ : 𝔤₀, ∃ toFirst : 𝔤₀ ≃ₗ⁅ℝ⁆ 𝔤₁, ∃ toSecond : 𝔤₀ ≃ₗ⁅ℝ⁆ 𝔤₂,
    toFirst ξ₀ = ξ₁ ∧ toSecond ξ₀ = ξ₂

/-! A common reduced generator yields the desired Lie-algebra equivalence. -/
theorem commonReducedGenerator_equiv
    {ξ₁ : 𝔤₁} {ξ₂ : 𝔤₂}
    (C : CommonReducedGenerator (𝔤₀ := 𝔤₀) (𝔤₁ := 𝔤₁) (𝔤₂ := 𝔤₂) ξ₁ ξ₂) :
    ∃ α : 𝔤₁ ≃ₗ⁅ℝ⁆ 𝔤₂, α ξ₁ = ξ₂ := by
  rcases C with ⟨ξ₀, toFirst, toSecond, hFirst, hSecond⟩
  refine ⟨toFirst.symm.trans toSecond, ?_⟩
  have hξ : toFirst.symm ξ₁ = ξ₀ := by
    have h := congrArg toFirst.symm hFirst
    calc
      toFirst.symm ξ₁ = toFirst.symm (toFirst ξ₀) := h.symm
      _ = ξ₀ := toFirst.symm_apply_apply _
  change toSecond (toFirst.symm ξ₁) = ξ₂
  exact (congrArg toSecond hξ).trans hSecond

end CommonReduction

variable {X G₁ G₂ V₁ V₂ Gtilde₁ Gtilde₂ 𝔤₁ 𝔤₂ : Type*}
  [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
  [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
  [Group G₁] [TopologicalSpace G₁] [ConnectedSpace G₁] [Nontrivial G₁]
  [Group G₂] [TopologicalSpace G₂] [ConnectedSpace G₂] [Nontrivial G₂]
  [AddCommGroup V₁] [Module ℝ V₁] [TopologicalSpace V₁] [IsTopologicalAddGroup V₁]
  [T2Space V₁] [ContinuousSMul ℝ V₁] [FiniteDimensional ℝ V₁]
  [AddCommGroup V₂] [Module ℝ V₂] [TopologicalSpace V₂] [IsTopologicalAddGroup V₂]
  [T2Space V₂] [ContinuousSMul ℝ V₂] [FiniteDimensional ℝ V₂]
  [Group Gtilde₁] [TopologicalSpace Gtilde₁] [IsTopologicalGroup Gtilde₁]
  [Group Gtilde₂] [TopologicalSpace Gtilde₂] [IsTopologicalGroup Gtilde₂]
  [LieRing 𝔤₁] [LieAlgebra ℝ 𝔤₁]
  [LieRing 𝔤₂] [LieAlgebra ℝ 𝔤₂]
  {f : X → ℝ}

/-! Conditional formalization of the minimal-representation uniqueness theorem.

`C` is a property, not an existence assertion.  Given it, the promised Lie-algebra isomorphism and
the correspondence of generators are proved by composing the two comparison isomorphisms.
-/
theorem generator_equiv_of_common_reduced_generator
    (R₁ : CoveredRepresentation X G₁ V₁ Gtilde₁ 𝔤₁ f)
    (R₂ : CoveredRepresentation X G₂ V₂ Gtilde₂ 𝔤₂ f)
    {𝔤₀ : Type*} [LieRing 𝔤₀] [LieAlgebra ℝ 𝔤₀]
    (C : CommonReducedGenerator (𝔤₀ := 𝔤₀) (𝔤₁ := 𝔤₁) (𝔤₂ := 𝔤₂)
      R₁.generator R₂.generator) :
    ∃ α : 𝔤₁ ≃ₗ⁅ℝ⁆ 𝔤₂, α R₁.generator = R₂.generator := by
  exact commonReducedGenerator_equiv C

end MinimalRepresentations

end CoverLinearization
