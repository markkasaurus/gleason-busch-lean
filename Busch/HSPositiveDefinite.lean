/-
# Busch/HSPositiveDefinite.lean — Positive-definiteness of `hsInner` on SA
The Hilbert-Schmidt pairing `hsInner A B = reTr (A * B)` is a real inner
product on the real vector space of self-adjoint operators. This file proves
the two nontrivial positivity properties:
* `hsInner_self_nonneg_of_isSelfAdjoint`: `0 ≤ hsInner A A` for SA `A`
* `hsInner_self_eq_zero_iff_isSelfAdjoint`: `hsInner A A = 0 ↔ A = 0` for SA `A`
Both follow directly from the ONB expansion
`reTr (A * A) = ∑ ‖A (b i)‖²` (from `TraceONB.lean`).
-/
import Busch.HilbertSchmidt
import Busch.TraceONB

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

/-- **Positive (semi-)definiteness of `hsInner` on SA**: for any self-adjoint
operator `A`, `hsInner A A = reTr (A * A) ≥ 0`. -/
theorem hsInner_self_nonneg_of_isSelfAdjoint (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    0 ≤ hsInner A A := by
  unfold hsInner
  exact reTr_selfAdjoint_mul_self_nonneg A hA

/-- **Definiteness**: for SA `A`, `hsInner A A = 0` iff `A = 0`. -/
theorem hsInner_self_eq_zero_iff_isSelfAdjoint (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    hsInner A A = 0 ↔ A = 0 := by
  unfold hsInner
  exact reTr_selfAdjoint_mul_self_eq_zero_iff A hA

end Busch
