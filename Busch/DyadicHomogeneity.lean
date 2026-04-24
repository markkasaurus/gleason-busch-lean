/-
# Busch/DyadicHomogeneity.lean — Dyadic Rational Homogeneity
This file establishes the dyadic scaling identities needed for the passage from
additivity on orthogonal sums to real homogeneity. It develops repeated halving
and compatibility of `smulIcc` with multiplication of dyadic scalars.
-/
import Busch.NatScalar

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Effect

/-- `smulIcc` respects multiplication of scalars:
    `smulIcc s (smulIcc t E) = smulIcc (s * t) E`
given that `s, t, s*t ∈ [0, 1]`. -/
lemma smulIcc_smulIcc (s t : UnitIcc) (E : Effect H)
    (hst : s.1 * t.1 ∈ Set.Icc (0 : ℝ) 1) :
    smulIcc s (smulIcc t E) = smulIcc ⟨s.1 * t.1, hst.1, hst.2⟩ E := by
  apply ext
  intro x
  show (s.1 : ℂ) • (smulIcc t E).op x = ((s.1 * t.1 : ℝ) : ℂ) • E.op x
  simp only [smulIcc_op, ContinuousLinearMap.smul_apply]
  rw [smul_smul]
  push_cast
  ring_nf

/-- Power-of-two element in `[0, 1]`: `1 / 2^n`. -/
def halfPow (n : ℕ) : UnitIcc := by
  refine ⟨(1 : ℝ) / 2^n, ?_, ?_⟩
  · positivity
  · rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ 2^n := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    exact this
@[simp] lemma halfPow_val (n : ℕ) : (halfPow n).1 = (1 : ℝ) / 2^n := rfl

/-- `halfPow 0 = 1`. -/
lemma halfPow_zero : (halfPow 0 : UnitIcc).1 = 1 := by
  simp [halfPow]

/-- `halfPow (n+1) = halfIcc * halfPow n = halfPow n * halfIcc`. -/
lemma halfPow_succ_eq_half_mul_prev (n : ℕ) :
    (halfPow (n + 1)).1 = (1 / 2 : ℝ) * (halfPow n).1 := by
  simp only [halfPow_val]
  rw [pow_succ]
  field_simp

/-- `smulIcc (halfPow (n+1)) E = smulIcc halfIcc (smulIcc (halfPow n) E)`. -/
lemma smulIcc_halfPow_succ (n : ℕ) (E : Effect H) :
    smulIcc (halfPow (n + 1)) E =
      smulIcc halfIcc (smulIcc (halfPow n) E) := by
  apply ext
  intro x
  show ((halfPow (n+1)).1 : ℂ) • E.op x =
    ((1/2 : ℝ) : ℂ) • (((halfPow n).1 : ℂ) • E.op x)
  rw [smul_smul]
  rw [halfPow_succ_eq_half_mul_prev]
  push_cast
  ring_nf

end Effect

namespace GenFrameFunction

/-- **Iterated half-scaling**: `μ((1/2^n) E) = (1/2^n) μ(E)`. -/
theorem μ_halfPow (f : GenFrameFunction H) (n : ℕ) (E : Effect H) :
    f.μ (Effect.smulIcc (Effect.halfPow n) E) = (1 / 2^n : ℝ) * f.μ E := by
  induction n with
  | zero =>
    have h_eq : Effect.smulIcc (Effect.halfPow 0) E = E := by
      apply Effect.ext
      intro x
      show ((Effect.halfPow 0).1 : ℂ) • E.op x = E.op x
      rw [Effect.halfPow_zero]
      simp
    rw [h_eq]
    simp
  | succ n ih =>
    rw [Effect.smulIcc_halfPow_succ]
    rw [μ_half]
    rw [ih]
    have : (1 / 2^(n+1) : ℝ) = (1/2) * (1 / 2^n) := by
      rw [pow_succ]; field_simp
    rw [this]
    ring

end GenFrameFunction

end Busch
