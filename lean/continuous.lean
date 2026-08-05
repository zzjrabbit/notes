import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Continuity

For a function defined on `ℝ`, continuity on a set `A` is characterized by the
fact that the preimage of every open set agrees on `A` with the preimage of an
open set of the ambient space.

The source note writes `f : A → ℝ`.  In this file we use Mathlib's equivalent
ambient-space formulation, `ContinuousOn f A`, which makes the equality
`f ⁻¹' U ∩ A = V ∩ A` well-typed.
-/

theorem continuous_iff_open_preimage_inter
    {A : Set ℝ} {f : ℝ → ℝ} :
    ContinuousOn f A ↔
      ∀ U : Set ℝ, IsOpen U →
        ∃ V : Set ℝ, IsOpen V ∧ f ⁻¹' U ∩ A = V ∩ A := by
  exact continuousOn_iff'

