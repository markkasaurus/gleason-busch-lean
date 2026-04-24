/-
# Busch/RealHomogeneity.lean — Real Homogeneity of Frame Functions
This file proves real homogeneity of generalized frame functions on effects.
The argument uses dyadic rational approximations to a scalar `t ∈ [0, 1]`
together with monotonicity of `μ` in the scalar parameter.
-/
import Busch.DyadicRational

noncomputable section

open Filter Topology

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Effect

/-- **Monotonicity in the scalar**: if `s ≤ t` then `smulIcc s E ≤ smulIcc t E`. -/
lemma smulIcc_mono (s t : UnitIcc) (h : s.1 ≤ t.1) (E : Effect H) :
    smulIcc s E ≤ smulIcc t E := by
  intro x
  simp only [smulIcc_apply]
  rw [inner_smul_right, inner_smul_right]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_right h (E.nonneg x)

end Effect

namespace GenFrameFunction

/-- **Monotonicity in the scalar** (μ version): if `s ≤ t` then `μ(sE) ≤ μ(tE)`. -/
lemma μ_smulIcc_mono (f : GenFrameFunction H) (s t : Effect.UnitIcc)
    (h : s.1 ≤ t.1) (E : Effect H) :
    f.μ (Effect.smulIcc s E) ≤ f.μ (Effect.smulIcc t E) :=
  f.monotone (Effect.smulIcc_mono s t h E)

/-- Exists dyadic approximation from below: for `t ∈ [0, 1]` and `n ∈ ℕ`,
there is `k ≤ 2^n` with `k/2^n ≤ t < k/2^n + 1/2^n`. -/
lemma exists_dyadic_le (t : Effect.UnitIcc) (n : ℕ) :
    ∃ k : ℕ, k ≤ 2^n ∧ (k : ℝ) / 2^n ≤ t.1 ∧ t.1 - (k : ℝ) / 2^n < 1 / 2^n := by
  have hpos : (0 : ℝ) < 2^n := by positivity
  have h_tpow_nn : (0 : ℝ) ≤ t.1 * 2^n := mul_nonneg t.2.1 (by positivity)
  have h_tpow_le : (t.1 : ℝ) * 2^n ≤ 2^n := by
    calc (t.1 : ℝ) * 2^n ≤ 1 * 2^n := mul_le_mul_of_nonneg_right t.2.2 (by positivity)
      _ = 2^n := by ring
  refine ⟨⌊(t.1 : ℝ) * 2^n⌋₊, ?_, ?_, ?_⟩
  ·
    have h1 : (⌊(t.1 : ℝ) * 2^n⌋₊ : ℝ) ≤ (t.1 : ℝ) * 2^n := Nat.floor_le h_tpow_nn
    have h2 : (⌊(t.1 : ℝ) * 2^n⌋₊ : ℝ) ≤ (2^n : ℝ) := le_trans h1 h_tpow_le
    have h3 : (⌊(t.1 : ℝ) * 2^n⌋₊ : ℝ) ≤ ((2^n : ℕ) : ℝ) := by push_cast; exact h2
    exact_mod_cast h3
  ·
    rw [div_le_iff₀ hpos]
    exact Nat.floor_le h_tpow_nn
  ·
    have h_floor_lt : (t.1 : ℝ) * 2^n < (⌊(t.1 : ℝ) * 2^n⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one (t.1 * 2^n)
    rw [show t.1 - (⌊(t.1 : ℝ) * 2^n⌋₊ : ℝ) / 2^n =
          (t.1 * 2^n - ⌊(t.1 : ℝ) * 2^n⌋₊) / 2^n by field_simp]
    rw [div_lt_div_iff₀ hpos hpos]
    nlinarith

/-- Exists dyadic approximation from above: for `t ∈ [0, 1]` and `n ∈ ℕ`,
there is `k ≤ 2^n` with `t ≤ k/2^n` and `k/2^n - t ≤ 1/2^n`. -/
lemma exists_dyadic_ge (t : Effect.UnitIcc) (n : ℕ) :
    ∃ k : ℕ, k ≤ 2^n ∧ t.1 ≤ (k : ℝ) / 2^n ∧ (k : ℝ) / 2^n - t.1 ≤ 1 / 2^n := by
  by_cases ht : t.1 = 1
  · refine ⟨2^n, le_refl _, ?_, ?_⟩
    · rw [ht]
      have : ((2^n : ℕ) : ℝ) = (2^n : ℝ) := by push_cast; rfl
      rw [this, div_self (by positivity : (2^n : ℝ) ≠ 0)]
    · rw [ht]
      have : ((2^n : ℕ) : ℝ) = (2^n : ℝ) := by push_cast; rfl
      rw [this, div_self (by positivity : (2^n : ℝ) ≠ 0)]
      have : (0 : ℝ) ≤ 1 / 2^n := by positivity
      linarith
  · have ht_lt : t.1 < 1 := lt_of_le_of_ne t.2.2 ht
    have hpos : (0 : ℝ) < 2^n := by positivity
    have h_tpow_nn : (0 : ℝ) ≤ t.1 * 2^n := mul_nonneg t.2.1 (by positivity)
    refine ⟨⌈(t.1 : ℝ) * 2^n⌉₊, ?_, ?_, ?_⟩
    ·
      have h_tpow_lt : (t.1 : ℝ) * 2^n < 2^n := by
        calc (t.1 : ℝ) * 2^n < 1 * 2^n :=
              mul_lt_mul_of_pos_right ht_lt (by positivity)
          _ = 2^n := by ring
      have h_ceil_le : ⌈(t.1 : ℝ) * 2^n⌉₊ ≤ 2^n := by
        rw [Nat.ceil_le]
        push_cast
        linarith
      exact h_ceil_le
    · rw [le_div_iff₀ hpos]
      exact Nat.le_ceil (t.1 * 2^n)
    ·
      have h_ceil_lt : (⌈(t.1 : ℝ) * 2^n⌉₊ : ℝ) < t.1 * 2^n + 1 :=
        Nat.ceil_lt_add_one h_tpow_nn
      rw [show (⌈(t.1 : ℝ) * 2^n⌉₊ : ℝ) / 2^n - t.1 =
            ((⌈(t.1 : ℝ) * 2^n⌉₊ : ℝ) - t.1 * 2^n) / 2^n by field_simp]
      rw [div_le_div_iff₀ hpos hpos]
      nlinarith

/-- **Real homogeneity**: `μ(t · E) = t · μ(E)` for all `t ∈ [0, 1]` and effects `E`. -/
theorem μ_smulIcc (f : GenFrameFunction H) (t : Effect.UnitIcc) (E : Effect H) :
    f.μ (Effect.smulIcc t E) = t.1 * f.μ E := by
  have h_muE_nonneg : 0 ≤ f.μ E := f.nonneg E
  apply le_antisymm
  ·
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt ((f.μ E + 1) / ε)
    have h_pow_gt : (n : ℝ) < (2 : ℝ)^n := by exact_mod_cast Nat.lt_two_pow_self
    have h_small : (f.μ E + 1) / 2^n < ε := by
      have h_pow_pos : (0 : ℝ) < 2^n := by positivity
      have : (f.μ E + 1) / ε < (2 : ℝ)^n := lt_trans hn h_pow_gt
      rw [div_lt_iff₀ hε] at this
      rw [div_lt_iff₀ h_pow_pos]
      linarith
    obtain ⟨k, hk_bd, ht_le, h_diff⟩ := exists_dyadic_ge t n
    have h_dy_ge : t.1 ≤ (Effect.dyadicIcc k n hk_bd).1 := by
      simp [Effect.dyadicIcc]
      exact ht_le
    have h_mono : f.μ (Effect.smulIcc t E) ≤
        f.μ (Effect.smulIcc (Effect.dyadicIcc k n hk_bd) E) :=
      f.μ_smulIcc_mono t (Effect.dyadicIcc k n hk_bd) h_dy_ge E
    rw [f.μ_dyadicIcc k n hk_bd E] at h_mono
    have h_diff_mul : ((k : ℝ) / 2^n - t.1) * f.μ E ≤ (1 / 2^n) * f.μ E :=
      mul_le_mul_of_nonneg_right h_diff h_muE_nonneg
    have h_bd : (1 / 2^n) * f.μ E ≤ (f.μ E + 1) / 2^n := by
      calc (1 / 2^n) * f.μ E = f.μ E / 2^n := by ring
        _ ≤ (f.μ E + 1) / 2^n :=
            div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith
  ·
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt ((f.μ E + 1) / ε)
    have h_pow_gt : (n : ℝ) < (2 : ℝ)^n := by exact_mod_cast Nat.lt_two_pow_self
    have h_small : (f.μ E + 1) / 2^n < ε := by
      have h_pow_pos : (0 : ℝ) < 2^n := by positivity
      have : (f.μ E + 1) / ε < (2 : ℝ)^n := lt_trans hn h_pow_gt
      rw [div_lt_iff₀ hε] at this
      rw [div_lt_iff₀ h_pow_pos]
      linarith
    obtain ⟨k, hk_bd, ht_ge, h_diff⟩ := exists_dyadic_le t n
    have h_dy_le : (Effect.dyadicIcc k n hk_bd).1 ≤ t.1 := by
      simp [Effect.dyadicIcc]
      exact ht_ge
    have h_mono : f.μ (Effect.smulIcc (Effect.dyadicIcc k n hk_bd) E) ≤
        f.μ (Effect.smulIcc t E) :=
      f.μ_smulIcc_mono (Effect.dyadicIcc k n hk_bd) t h_dy_le E
    rw [f.μ_dyadicIcc k n hk_bd E] at h_mono
    have h_diff_mul : (t.1 - (k : ℝ) / 2^n) * f.μ E ≤ (1 / 2^n) * f.μ E :=
      mul_le_mul_of_nonneg_right (le_of_lt h_diff) h_muE_nonneg
    have h_bd : (1 / 2^n) * f.μ E ≤ (f.μ E + 1) / 2^n := by
      calc (1 / 2^n) * f.μ E = f.μ E / 2^n := by ring
        _ ≤ (f.μ E + 1) / 2^n :=
            div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith

end GenFrameFunction

end Busch
