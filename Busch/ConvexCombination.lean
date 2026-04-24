/-
# Busch/ConvexCombination.lean — General Convex Combinations
Generalizes `ConvexLinearity.lean` from t ∈ [0,1] combinations to any
nonneg combinations αE + βF with α + β ≤ 1 (which keeps αE + βF an effect).
This is needed for the linear extension step, where we express any
self-adjoint operator as a difference of scaled effects.
-/
import Busch.ConvexLinearity

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Effect

/-- For `α, β ≥ 0` with `α + β ≤ 1`, `αE + βF` is an effect (summability condition). -/
lemma smulIcc_pair_summable (α β : UnitIcc) (h : α.1 + β.1 ≤ 1) (E F : Effect H) :
    Summable (smulIcc α E) (smulIcc β F) := by
  intro x
  show (inner (𝕜 := ℂ) x
      (((α.1 : ℂ) • E.op + (β.1 : ℂ) • F.op) x)).re ≤ _
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    inner_add_right, inner_smul_right]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  have h_α : α.1 * (inner (𝕜 := ℂ) x (E.op x)).re ≤ α.1 * (inner (𝕜 := ℂ) x x).re :=
    mul_le_mul_of_nonneg_left (E.le_one x) α.2.1
  have h_β : β.1 * (inner (𝕜 := ℂ) x (F.op x)).re ≤ β.1 * (inner (𝕜 := ℂ) x x).re :=
    mul_le_mul_of_nonneg_left (F.le_one x) β.2.1
  have h_self_nn : 0 ≤ (inner (𝕜 := ℂ) x x).re := @inner_self_nonneg ℂ H _ _ _ x
  have h_ab : α.1 * (inner (𝕜 := ℂ) x x).re + β.1 * (inner (𝕜 := ℂ) x x).re ≤
      (inner (𝕜 := ℂ) x x).re := by
    have : α.1 + β.1 ≤ 1 := h
    nlinarith
  linarith

end Effect

namespace GenFrameFunction

/-- **General linear combination**: `μ(αE + βF) = αμ(E) + βμ(F)` for `α, β ≥ 0`
    with `α + β ≤ 1`. -/
theorem μ_pair_sum (f : GenFrameFunction H) (α β : Effect.UnitIcc)
    (h : α.1 + β.1 ≤ 1) (E F : Effect H) :
    f.μ (Effect.orthoSum (Effect.smulIcc α E) (Effect.smulIcc β F)
        (Effect.smulIcc_pair_summable α β h E F)) =
      α.1 * f.μ E + β.1 * f.μ F := by
  rw [f.additive]
  rw [f.μ_smulIcc, f.μ_smulIcc]

end GenFrameFunction

end Busch
