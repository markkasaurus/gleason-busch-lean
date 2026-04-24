/-
# Busch/DyadicRational.lean — Dyadic Rational Homogeneity
This file upgrades the halving identities from `DyadicHomogeneity` to arbitrary
dyadic rationals `k / 2^n`. The argument decomposes dyadically scaled effects
into orthogonal sums of `1 / 2^n` pieces and applies additivity of `μ`.
-/
import Busch.DyadicHomogeneity

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Effect

/-- For `k ≤ 2^n`, the scalar `k / 2^n` is in `[0, 1]`. -/
def dyadicIcc (k n : ℕ) (h : k ≤ 2^n) : UnitIcc := by
  refine ⟨(k : ℝ) / 2^n, ?_, ?_⟩
  · positivity
  · rw [div_le_one (by positivity)]
    exact_mod_cast h
@[simp] lemma dyadicIcc_val (k n : ℕ) (h : k ≤ 2^n) :
    (dyadicIcc k n h).1 = (k : ℝ) / 2^n := rfl

/-- `dyadicIcc 0 n _ = 0` (as a scalar). -/
lemma dyadicIcc_zero (n : ℕ) : (dyadicIcc 0 n (Nat.zero_le _)).1 = 0 := by
  simp [dyadicIcc]

/-- `dyadicIcc k n + dyadicIcc 1 n = dyadicIcc (k+1) n` (when both are valid). -/
lemma dyadicIcc_succ_eq_add (k n : ℕ) (h : k + 1 ≤ 2^n) :
    (dyadicIcc (k + 1) n h).1 = (dyadicIcc k n (by omega)).1 + (halfPow n).1 := by
  simp only [dyadicIcc_val, halfPow_val]
  field_simp
  push_cast
  ring

/-- Dyadic scaling is compatible with adjoining one additional `1 / 2^n` piece:
`(k/2^n) E ⊕ (1/2^n) E = ((k+1)/2^n) E` when `(k+1)/2^n ≤ 1`. -/
lemma dyadicIcc_succ_summable (k n : ℕ) (h : k + 1 ≤ 2^n) (E : Effect H) :
    Summable (smulIcc (dyadicIcc k n (by omega)) E) (smulIcc (halfPow n) E) := by
  intro x
  show (inner (𝕜 := ℂ) x
      ((((dyadicIcc k n (by omega)).1 : ℂ) • E.op + ((halfPow n).1 : ℂ) • E.op) x)).re ≤ _
  have h_sum : ((dyadicIcc k n (by omega)).1 : ℂ) • E.op + ((halfPow n).1 : ℂ) • E.op =
      ((dyadicIcc (k+1) n h).1 : ℂ) • E.op := by
    ext y
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    rw [dyadicIcc_succ_eq_add k n h]
    push_cast
    rw [add_smul]
  rw [h_sum]
  have h_effect := (smulIcc (dyadicIcc (k+1) n h) E).le_one x
  show (inner (𝕜 := ℂ) x (((dyadicIcc (k+1) n h).1 : ℂ) • E.op x)).re ≤ _
  exact h_effect

/-- `smulIcc (dyadicIcc k n) E ⊕ smulIcc (halfPow n) E = smulIcc (dyadicIcc (k+1) n) E`. -/
lemma dyadicIcc_succ_sum (k n : ℕ) (h : k + 1 ≤ 2^n) (E : Effect H) :
    orthoSum (smulIcc (dyadicIcc k n (by omega)) E) (smulIcc (halfPow n) E)
        (dyadicIcc_succ_summable k n h E) =
      smulIcc (dyadicIcc (k+1) n h) E := by
  apply ext
  intro x
  show (smulIcc (dyadicIcc k n (by omega)) E) x + (smulIcc (halfPow n) E) x =
    (smulIcc (dyadicIcc (k+1) n h) E) x
  simp only [smulIcc_apply]
  have hcast : ((dyadicIcc (k+1) n h).1 : ℂ) =
      ((dyadicIcc k n (by omega)).1 : ℂ) + ((halfPow n).1 : ℂ) := by
    rw [dyadicIcc_succ_eq_add k n h]
    push_cast; ring
  rw [hcast, add_smul]

end Effect

namespace GenFrameFunction

/-- **Dyadic rational homogeneity**: `μ((k/2^n) E) = (k/2^n) μ(E)` for `k ≤ 2^n`. -/
theorem μ_dyadicIcc (f : GenFrameFunction H) (k n : ℕ) (h : k ≤ 2^n) (E : Effect H) :
    f.μ (Effect.smulIcc (Effect.dyadicIcc k n h) E) = ((k : ℝ) / 2^n) * f.μ E := by
  induction k with
  | zero =>
    have h_eq : Effect.smulIcc (Effect.dyadicIcc 0 n h) E = (0 : Effect H) := by
      apply Effect.ext
      intro x
      show ((Effect.dyadicIcc 0 n h).1 : ℂ) • E.op x = (0 : Effect H).op x
      rw [Effect.dyadicIcc_zero]
      simp [Effect.zero_op]
    rw [h_eq, f.μ_zero]
    simp
  | succ k ih =>
    have h_prev : k ≤ 2^n := by omega
    have h_ih := ih h_prev
    have h_sum := Effect.dyadicIcc_succ_sum k n h E
    have h_add := f.additive (Effect.smulIcc (Effect.dyadicIcc k n h_prev) E)
      (Effect.smulIcc (Effect.halfPow n) E)
      (Effect.dyadicIcc_succ_summable k n h E)
    rw [h_sum] at h_add
    rw [h_add, h_ih, μ_halfPow]
    have h_cast : ((k + 1 : ℕ) : ℝ) / 2^n = (k : ℝ) / 2^n + 1 / 2^n := by
      push_cast; ring
    rw [h_cast]
    ring

end GenFrameFunction

end Busch
