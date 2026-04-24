/-
# Busch/ConvexLinearity.lean — Convex Linearity of Frame Functions
This file proves affine behavior of generalized frame functions along convex
combinations of effects. The key input is that `tE` and `(1 - t)F` are
summable whenever `t ∈ [0, 1]`, so additivity and real homogeneity combine to
give convex linearity.
-/
import Busch.RealHomogeneity

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Effect

/-- For `t ∈ [0, 1]`, the pair `(tE, (1-t)F)` is summable for any effects `E, F`. -/
lemma smulIcc_convex_summable (t : UnitIcc) (E F : Effect H) :
    Summable (smulIcc t E)
        (smulIcc ⟨1 - t.1, by linarith [t.2.2], by linarith [t.2.1]⟩ F) := by
  intro x
  show (inner (𝕜 := ℂ) x
      (((t.1 : ℂ) • E.op + ((1 - t.1 : ℝ) : ℂ) • F.op) x)).re ≤ _
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    inner_add_right, inner_smul_right]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  have h_t_pos : 0 ≤ t.1 := t.2.1
  have h_1t_pos : 0 ≤ 1 - t.1 := by linarith [t.2.2]
  have h_E_le : t.1 * (inner (𝕜 := ℂ) x (E.op x)).re ≤ t.1 * (inner (𝕜 := ℂ) x x).re :=
    mul_le_mul_of_nonneg_left (E.le_one x) h_t_pos
  have h_F_le : (1 - t.1) * (inner (𝕜 := ℂ) x (F.op x)).re ≤
      (1 - t.1) * (inner (𝕜 := ℂ) x x).re :=
    mul_le_mul_of_nonneg_left (F.le_one x) h_1t_pos
  have h_sum : t.1 * (inner (𝕜 := ℂ) x x).re + (1 - t.1) * (inner (𝕜 := ℂ) x x).re
      = (inner (𝕜 := ℂ) x x).re := by ring
  linarith

/-- **Convex combination as an effect**. -/
def convexComb (t : UnitIcc) (E F : Effect H) : Effect H :=
  orthoSum (smulIcc t E)
      (smulIcc ⟨1 - t.1, by linarith [t.2.2], by linarith [t.2.1]⟩ F)
      (smulIcc_convex_summable t E F)
@[simp] lemma convexComb_op (t : UnitIcc) (E F : Effect H) :
    (convexComb t E F).op = (t.1 : ℂ) • E.op + ((1 - t.1 : ℝ) : ℂ) • F.op := rfl

end Effect

namespace GenFrameFunction

/-- **Convex linearity**: `μ(tE + (1-t)F) = t·μ(E) + (1-t)·μ(F)` for `t ∈ [0,1]`. -/
theorem μ_convexComb (f : GenFrameFunction H) (t : Effect.UnitIcc) (E F : Effect H) :
    f.μ (Effect.convexComb t E F) = t.1 * f.μ E + (1 - t.1) * f.μ F := by
  unfold Effect.convexComb
  rw [f.additive]
  rw [f.μ_smulIcc, f.μ_smulIcc]

/-- **Linearity on scaled pairs**: `μ(tE ⊕ sF) = tμ(E) + sμ(F)` when `tE + sF ≤ 1`. -/
theorem μ_smulIcc_sum (f : GenFrameFunction H) (t s : Effect.UnitIcc) (E F : Effect H)
    (h : Effect.Summable (Effect.smulIcc t E) (Effect.smulIcc s F)) :
    f.μ (Effect.orthoSum (Effect.smulIcc t E) (Effect.smulIcc s F) h) =
      t.1 * f.μ E + s.1 * f.μ F := by
  rw [f.additive]
  rw [f.μ_smulIcc, f.μ_smulIcc]

end GenFrameFunction

end Busch
