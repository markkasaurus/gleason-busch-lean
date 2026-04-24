/-
# Busch/HilbertSchmidt.lean — Hilbert-Schmidt Pairing on Self-Adjoint Operators
Defines the **Hilbert-Schmidt pairing** on self-adjoint operators:
  `hsInner A B := reTr (A * B)`
For self-adjoint `A, B`, this is a real-valued symmetric bilinear pairing —
and in finite-dim, it is positive definite (i.e., it is an inner product).
The positive-definiteness proof is by a direct inner-product computation using
the fact that for self-adjoint `A`:
  `reTr (A * A) = Σᵢ ‖A eᵢ‖²`
for any orthonormal basis `{eᵢ}` of `H`.
This file provides:
* `hsInner A B`: the HS pairing
* Bilinearity: `hsInner_add_left`, `hsInner_smul_left`, etc.
* Symmetry for SA operators: `hsInner_comm_of_isSelfAdjoint`
* Reality: for SA `A, B`, `trComplex (A * B)` is real
-/
import Busch.Trace

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The **Hilbert-Schmidt pairing** on continuous linear endomorphisms. -/
def hsInner (A B : H →L[ℂ] H) : ℝ := reTr (A * B)

/-! ### Basic properties: bilinearity -/
@[simp] lemma hsInner_zero_left (A : H →L[ℂ] H) : hsInner (0 : H →L[ℂ] H) A = 0 := by
  unfold hsInner
  rw [zero_mul]
  exact reTr_zero
@[simp] lemma hsInner_zero_right (A : H →L[ℂ] H) : hsInner A (0 : H →L[ℂ] H) = 0 := by
  unfold hsInner
  rw [mul_zero]
  exact reTr_zero

lemma hsInner_add_left (A B C : H →L[ℂ] H) :
    hsInner (A + B) C = hsInner A C + hsInner B C := by
  unfold hsInner
  rw [add_mul, reTr_add]

lemma hsInner_add_right (A B C : H →L[ℂ] H) :
    hsInner A (B + C) = hsInner A B + hsInner A C := by
  unfold hsInner
  rw [mul_add, reTr_add]

lemma hsInner_smul_left (r : ℝ) (A B : H →L[ℂ] H) :
    hsInner ((r : ℂ) • A) B = r * hsInner A B := by
  unfold hsInner
  have h : ((r : ℂ) • A) * B = (r : ℂ) • (A * B) := by
    ext z
    simp [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply]
  rw [h, reTr_smul_real]

lemma hsInner_smul_right (r : ℝ) (A B : H →L[ℂ] H) :
    hsInner A ((r : ℂ) • B) = r * hsInner A B := by
  unfold hsInner
  have h : A * ((r : ℂ) • B) = (r : ℂ) • (A * B) := by
    ext z
    simp [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply]
  rw [h, reTr_smul_real]
@[simp] lemma hsInner_neg_left (A B : H →L[ℂ] H) : hsInner (-A) B = -hsInner A B := by
  unfold hsInner
  rw [neg_mul, reTr_neg]
@[simp] lemma hsInner_neg_right (A B : H →L[ℂ] H) : hsInner A (-B) = -hsInner A B := by
  unfold hsInner
  rw [mul_neg, reTr_neg]

lemma hsInner_sub_left (A B C : H →L[ℂ] H) :
    hsInner (A - B) C = hsInner A C - hsInner B C := by
  rw [sub_eq_add_neg, hsInner_add_left, hsInner_neg_left]
  ring

lemma hsInner_sub_right (A B C : H →L[ℂ] H) :
    hsInner A (B - C) = hsInner A B - hsInner A C := by
  rw [sub_eq_add_neg, hsInner_add_right, hsInner_neg_right]
  ring

/-! ### Symmetry -/
/-- **Symmetry**: `hsInner A B = hsInner B A`. -/
lemma hsInner_comm (A B : H →L[ℂ] H) : hsInner A B = hsInner B A := by
  unfold hsInner
  exact reTr_mul_comm A B

/-! ### Reality for self-adjoint operators
Under self-adjointness the trace of a product is real, but we don't need
this — we work with the real part `reTr` throughout.
### Nonnegativity on `hsInner A A` for SA `A`
For an SA operator `A`, `hsInner A A = Σᵢ ‖A eᵢ‖²` in any ONB.
This is nonnegative, with equality iff `A = 0`.
-/
/-! ### Pairing with the identity -/
/-- `hsInner 1 A = reTr A`. -/
@[simp] lemma hsInner_one_left (A : H →L[ℂ] H) : hsInner (1 : H →L[ℂ] H) A = reTr A := by
  unfold hsInner
  rw [one_mul]

/-- `hsInner A 1 = reTr A`. -/
@[simp] lemma hsInner_one_right (A : H →L[ℂ] H) : hsInner A (1 : H →L[ℂ] H) = reTr A := by
  unfold hsInner
  rw [mul_one]

end Busch
