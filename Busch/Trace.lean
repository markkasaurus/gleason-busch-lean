/-
# Busch/Trace.lean — Real Part of Operator Trace
In finite-dim complex Hilbert space `H`, the trace of a continuous linear
endomorphism is a complex number; its real part is a real-linear functional
of `A`. This file builds the basic infrastructure needed for the
Hilbert-Schmidt inner product and Riesz representation.
Main definitions:
* `reTr A := (LinearMap.trace ℂ H A.toLinearMap).re`
* Linearity properties: `reTr_add`, `reTr_smul_real`, `reTr_zero`, `reTr_one`
* `reTr_mul_comm`: `reTr (A * B) = reTr (B * A)`
-/
import Busch.SALinearity
import Mathlib.LinearAlgebra.Trace

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [instCompleteSpace : CompleteSpace H] [instFiniteDimensional : FiniteDimensional ℂ H]

/-- The trace of a continuous linear operator, returned as a complex number. -/
def trComplex (A : H →L[ℂ] H) : ℂ := LinearMap.trace ℂ H A.toLinearMap

/-- The **real part of the operator trace**. -/
def reTr (A : H →L[ℂ] H) : ℝ := (trComplex A).re
section
omit instCompleteSpace instFiniteDimensional
@[simp] lemma trComplex_zero : trComplex (0 : H →L[ℂ] H) = 0 := by
  unfold trComplex
  show LinearMap.trace ℂ H (0 : H →L[ℂ] H).toLinearMap = 0
  rw [show ((0 : H →L[ℂ] H) : H →ₗ[ℂ] H) = 0 from rfl]
  exact LinearMap.map_zero _
@[simp] lemma reTr_zero : reTr (0 : H →L[ℂ] H) = 0 := by
  unfold reTr
  rw [trComplex_zero]
  simp

lemma trComplex_add (A B : H →L[ℂ] H) : trComplex (A + B) = trComplex A + trComplex B := by
  unfold trComplex
  have h : (A + B).toLinearMap = A.toLinearMap + B.toLinearMap := by
    ext z; simp
  rw [h]
  exact LinearMap.map_add _ _ _

lemma reTr_add (A B : H →L[ℂ] H) : reTr (A + B) = reTr A + reTr B := by
  unfold reTr
  rw [trComplex_add, Complex.add_re]

lemma trComplex_smul_complex (c : ℂ) (A : H →L[ℂ] H) :
    trComplex (c • A) = c * trComplex A := by
  unfold trComplex
  have h : (c • A).toLinearMap = c • A.toLinearMap := by
    ext z; simp
  rw [h]
  rw [LinearMap.map_smul]
  rfl

lemma reTr_smul_real (r : ℝ) (A : H →L[ℂ] H) :
    reTr ((r : ℂ) • A) = r * reTr A := by
  unfold reTr
  rw [trComplex_smul_complex]
  simp [Complex.mul_re]
@[simp] lemma reTr_neg (A : H →L[ℂ] H) : reTr (-A) = -reTr A := by
  have h : trComplex (-A) = -trComplex A := by
    have := trComplex_smul_complex (-1 : ℂ) A
    rw [show ((-1 : ℂ) • A) = -A by simp] at this
    rw [this]
    ring
  unfold reTr
  rw [h]
  simp

lemma reTr_sub (A B : H →L[ℂ] H) : reTr (A - B) = reTr A - reTr B := by
  rw [sub_eq_add_neg, reTr_add, reTr_neg, sub_eq_add_neg]

/-- **Trace commutes**: `reTr (A * B) = reTr (B * A)`. -/
lemma reTr_mul_comm (A B : H →L[ℂ] H) : reTr (A * B) = reTr (B * A) := by
  unfold reTr trComplex
  have h : (A * B).toLinearMap = A.toLinearMap.comp B.toLinearMap := by
    ext z; rfl
  have h' : (B * A).toLinearMap = B.toLinearMap.comp A.toLinearMap := by
    ext z; rfl
  rw [h, h']
  show (LinearMap.trace ℂ H (A.toLinearMap * B.toLinearMap)).re
    = (LinearMap.trace ℂ H (B.toLinearMap * A.toLinearMap)).re
  rw [LinearMap.trace_mul_comm]
end
section
omit instCompleteSpace

/-- **Trace of the identity operator** equals the complex dimension of `H`. -/
@[simp] lemma trComplex_one : trComplex (1 : H →L[ℂ] H) = (Module.finrank ℂ H : ℂ) := by
  unfold trComplex
  have h : (1 : H →L[ℂ] H).toLinearMap = 1 := by
    ext z; simp
  rw [h]
  exact LinearMap.trace_one ℂ H
@[simp] lemma reTr_one : reTr (1 : H →L[ℂ] H) = (Module.finrank ℂ H : ℝ) := by
  unfold reTr
  rw [trComplex_one]
  simp
end

end Busch
