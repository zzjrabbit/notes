import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Matrix.Mul

open scoped BigOperators Matrix

namespace Exterior

/-- A matrix over `R`, viewed as a matrix over an `R`-algebra `A`. -/
def scalarMatrix {R A n : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (S : Matrix n n R) : Matrix n n A :=
  fun i j => algebraMap R A (S i j)

/-- The quadratic form `vᵀ S v` when the entries of `S` are scalars in `R`. -/
def quadraticForm {R A n : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [Fintype n] (S : Matrix n n R) (v : n → A) : A :=
  v ⬝ᵥ (scalarMatrix S *ᵥ v)

/-- Expanding a matrix quadratic form gives the corresponding double sum. -/
theorem quadraticForm_eq_sum {R A n : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [Fintype n] (S : Matrix n n R) (v : n → A) :
    quadraticForm S v = ∑ i, ∑ j, S i j • (v i * v j) := by
  classical
  simp only [quadraticForm, scalarMatrix, dotProduct, Matrix.mulVec]
  simp_rw [Finset.mul_sum]
  simp_rw [← Algebra.smul_def, Algebra.mul_smul_comm]

end Exterior
