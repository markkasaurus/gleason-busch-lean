/-
# Busch/TraceONB.lean — Orthonormal-basis expansion of the trace
Bridge lemma connecting `reTr` (defined via `LinearMap.trace`) to the
orthonormal-basis expansion `∑ᵢ ⟨bᵢ, A bᵢ⟩.re`. This is the key algebraic
input for proving positive-definiteness of the Hilbert-Schmidt inner product
on self-adjoint operators.
Main results:
* `reTr_eq_sum_inner_orthonormalBasis`: `reTr A = ∑ i, (⟨b i, A (b i)⟩).re`
* `reTr_selfAdjoint_mul_self_eq_sum_normSq`: for SA `A`,
  `reTr (A * A) = ∑ i, ‖A (b i)‖²`
The second lemma is the concrete form used for positive-definiteness.
-/
import Busch.Trace
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [instCompleteSpace : CompleteSpace H] [instFiniteDimensional : FiniteDimensional ℂ H]

omit instCompleteSpace instFiniteDimensional in
/-- **Trace expansion in an orthonormal basis**: `reTr A = ∑ i, (⟨bᵢ, A bᵢ⟩).re`. -/
lemma reTr_eq_sum_inner_orthonormalBasis {ι : Type*} [Fintype ι]
    (A : H →L[ℂ] H) (b : OrthonormalBasis ι ℂ H) :
    reTr A = ∑ i, (inner (𝕜 := ℂ) (b i) (A (b i))).re := by
  unfold reTr trComplex
  rw [LinearMap.trace_eq_sum_inner A.toLinearMap b]
  rw [Complex.re_sum]
  rfl

omit instFiniteDimensional in
/-- **Key identity for positive-definiteness**: for a self-adjoint operator `A`,
`reTr (A * A) = ∑ i, ‖A (b i)‖²` in any orthonormal basis. -/
lemma reTr_selfAdjoint_mul_self_eq_sum_normSq {ι : Type*} [Fintype ι]
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (b : OrthonormalBasis ι ℂ H) :
    reTr (A * A) = ∑ i, ‖A (b i)‖ ^ 2 := by
  rw [reTr_eq_sum_inner_orthonormalBasis (A * A) b]
  apply Finset.sum_congr rfl
  intro i _
  show (inner (𝕜 := ℂ) (b i) ((A * A) (b i))).re = ‖A (b i)‖ ^ 2
  have h_mul_apply : (A * A) (b i) = A (A (b i)) := rfl
  rw [h_mul_apply]
  have h_sa_inner : inner (𝕜 := ℂ) (b i) (A (A (b i)))
      = inner (𝕜 := ℂ) (A (b i)) (A (b i)) := by
    have h_sym : (A : H →ₗ[ℂ] H).IsSymmetric := hA.isSymmetric
    exact (h_sym (b i) (A (b i))).symm
  rw [h_sa_inner]
  exact_mod_cast (@inner_self_eq_norm_sq ℂ H _ _ _ (A (b i)))

/-- **Nonnegativity of `reTr (A * A)` for self-adjoint `A`**. -/
lemma reTr_selfAdjoint_mul_self_nonneg (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    0 ≤ reTr (A * A) := by
  let b := stdOrthonormalBasis ℂ H
  rw [reTr_selfAdjoint_mul_self_eq_sum_normSq A hA b]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- **Positive-definiteness of `reTr (A * A)` for SA**: if `reTr (A * A) = 0`
for a self-adjoint `A`, then `A = 0`. -/
lemma reTr_selfAdjoint_mul_self_eq_zero_iff (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    reTr (A * A) = 0 ↔ A = 0 := by
  constructor
  · intro h
    let b := stdOrthonormalBasis ℂ H
    rw [reTr_selfAdjoint_mul_self_eq_sum_normSq A hA b] at h
    have h_each : ∀ i ∈ Finset.univ, ‖A (b i)‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp h
    have h_zero_on_basis : ∀ i, A (b i) = 0 := by
      intro i
      have hi : ‖A (b i)‖ ^ 2 = 0 := h_each i (Finset.mem_univ _)
      have : ‖A (b i)‖ = 0 := by
        have := sq_eq_zero_iff.mp hi
        exact this
      exact norm_eq_zero.mp this
    apply ContinuousLinearMap.ext
    intro x
    have hx_repr : x = ∑ i, (inner (𝕜 := ℂ) (b i) x) • b i := (b.sum_repr' x).symm
    conv_lhs => rw [hx_repr]
    rw [map_sum]
    simp only [ContinuousLinearMap.map_smul, h_zero_on_basis, smul_zero, Finset.sum_const_zero]
    rfl
  · intro h
    subst h
    show reTr (0 * 0 : H →L[ℂ] H) = 0
    rw [mul_zero]
    exact reTr_zero

end Busch
