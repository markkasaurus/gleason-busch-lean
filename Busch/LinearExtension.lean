/-
# Busch/LinearExtension.lean — Well-definedness of muScaled on the Positive Cone
Setting up the linear extension of `μ` beyond the effect set:
* Positive cone: scaled effects `c · E` for `c ≥ 0`, giving the set of positive
  operators of bounded spectrum.
* **Well-definedness**: if two scaled effects `(c₁, E₁)` and `(c₂, E₂)` have the
  same underlying operator `c₁ · E₁.op = c₂ · E₂.op`, then
  `c₁ · μ(E₁) = c₂ · μ(E₂)`.
The proof uses **real homogeneity**: if `c₁ ≤ c₂` then `E₂ = (c₁/c₂) · E₁`, and
`μ(E₂) = (c₁/c₂) · μ(E₁)` by real homogeneity, so `c₂ · μ(E₂) = c₁ · μ(E₁)`.
This supports the subsequent shift-based extension to self-adjoint operators.
-/
import Busch.RealHomogeneity
import Busch.PositiveExtension

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace SclEffect

/-- Two scaled effects are **equivalent** if their underlying operators agree. -/
def Equiv (S T : SclEffect H) : Prop := S.op = T.op

lemma Equiv.refl' (S : SclEffect H) : Equiv S S := rfl

lemma Equiv.symm' {S T : SclEffect H} (h : Equiv S T) : Equiv T S :=
  Eq.symm h

lemma Equiv.trans' {S T U : SclEffect H}
    (h₁ : Equiv S T) (h₂ : Equiv T U) : Equiv S U :=
  Eq.trans h₁ h₂

end SclEffect

namespace GenFrameFunction

open SclEffect

/-- **Key lemma**: if the scale of a scaled effect is zero, its operator is zero. -/
lemma op_eq_zero_of_scale_zero {S : SclEffect H} (hS : S.scale = 0) :
    S.op = 0 := by
  show (S.scale : ℂ) • S.effect.op = 0
  rw [hS]
  simp

/-- If `S.op = 0` and `S.scale > 0`, then `S.effect` is the zero effect. -/
lemma effect_eq_zero_of_op_zero_of_pos {S : SclEffect H}
    (hOp : S.op = 0) (hS : 0 < S.scale) : S.effect.op = 0 := by
  have h1 : (S.scale : ℂ) • S.effect.op = 0 := hOp
  have h_ne : (S.scale : ℂ) ≠ 0 := by
    intro h
    have : S.scale = 0 := by exact_mod_cast h
    linarith
  exact (smul_eq_zero.mp h1).resolve_left h_ne

/-- **Scaling lemma**: If `c₁ · E₁ = c₂ · E₂` as operators with `0 < c₁ ≤ c₂`,
then `E₂.op = (c₁/c₂) · E₁.op`. This is the technical bridge. -/
lemma effect_ratio_of_scaled_eq {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hle : c₁ ≤ c₂)
    {E₁ E₂ : Effect H} (h : (c₁ : ℂ) • E₁.op = (c₂ : ℂ) • E₂.op) :
    E₂.op = ((c₁ / c₂ : ℝ) : ℂ) • E₁.op := by
  have hc₂_pos : 0 < c₂ := lt_of_lt_of_le hc₁ hle
  have hc₂_ne : (c₂ : ℂ) ≠ 0 := by
    intro heq
    have : c₂ = 0 := by exact_mod_cast heq
    linarith
  have step1 : (c₂⁻¹ : ℂ) • ((c₁ : ℂ) • E₁.op) = (c₂⁻¹ : ℂ) • ((c₂ : ℂ) • E₂.op) := by
    rw [h]
  rw [smul_smul, smul_smul] at step1
  rw [inv_mul_cancel₀ hc₂_ne, one_smul] at step1
  have h_cast : ((c₁ / c₂ : ℝ) : ℂ) = (c₂⁻¹ : ℂ) * (c₁ : ℂ) := by
    push_cast
    ring
  rw [h_cast]
  exact step1.symm

/-- Ratio `c₁/c₂` lies in [0, 1] when `0 < c₁ ≤ c₂`, giving a `UnitIcc` element. -/
def ratioIcc {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hle : c₁ ≤ c₂) (hc₂_pos : 0 < c₂) :
    Effect.UnitIcc :=
  ⟨c₁ / c₂, div_nonneg hc₁ hc₂_pos.le,
    (div_le_one hc₂_pos).mpr hle⟩

/-- **Well-definedness of `muScaled`**: if two scaled effects `S₁, S₂` have the
same underlying operator, their `muScaled` values agree. -/
theorem muScaled_well_defined (f : GenFrameFunction H) (S₁ S₂ : SclEffect H)
    (hEq : S₁.op = S₂.op) : f.muScaled S₁ = f.muScaled S₂ := by
  show S₁.scale * f.μ S₁.effect = S₂.scale * f.μ S₂.effect
  rcases eq_or_lt_of_le S₁.scale_nn with hz₁ | hp₁
  ·
    have : S₁.scale = 0 := hz₁.symm
    rw [this]
    simp only [zero_mul]
    have hS₂_op : S₂.op = 0 := by
      rw [← hEq]
      exact op_eq_zero_of_scale_zero this
    rcases eq_or_lt_of_le S₂.scale_nn with hz₂ | hp₂
    · rw [← hz₂]; ring
    ·
      have h_eff : S₂.effect.op = 0 :=
        effect_eq_zero_of_op_zero_of_pos hS₂_op hp₂
      have h_eff_eq : S₂.effect = (0 : Effect H) := by
        apply Effect.ext_op; rw [h_eff]; rfl
      rw [h_eff_eq, f.μ_zero]
      ring
  ·
    rcases eq_or_lt_of_le S₂.scale_nn with hz₂ | hp₂
    ·
      have hS₂_scale : S₂.scale = 0 := hz₂.symm
      have hS₁_op : S₁.op = 0 := by
        rw [hEq]
        exact op_eq_zero_of_scale_zero hS₂_scale
      have h_eff : S₁.effect.op = 0 :=
        effect_eq_zero_of_op_zero_of_pos hS₁_op hp₁
      have h_eff_eq : S₁.effect = (0 : Effect H) := by
        apply Effect.ext_op; rw [h_eff]; rfl
      rw [h_eff_eq, f.μ_zero, hS₂_scale]
      ring
    ·
      rcases le_or_gt S₁.scale S₂.scale with hle | hlt
      ·
        have h_op_eq : (S₁.scale : ℂ) • S₁.effect.op = (S₂.scale : ℂ) • S₂.effect.op := hEq
        have h_ratio : S₂.effect.op = ((S₁.scale / S₂.scale : ℝ) : ℂ) • S₁.effect.op :=
          effect_ratio_of_scaled_eq hp₁ hle h_op_eq
        set r : Effect.UnitIcc := ratioIcc hp₁.le hle hp₂ with hr_def
        have h_eff_eq : S₂.effect = Effect.smulIcc r S₁.effect := by
          apply Effect.ext_op
          show S₂.effect.op = (r.1 : ℂ) • S₁.effect.op
          rw [h_ratio]
          show ((S₁.scale / S₂.scale : ℝ) : ℂ) • S₁.effect.op = (r.1 : ℂ) • S₁.effect.op
          rfl
        rw [h_eff_eq, f.μ_smulIcc]
        show S₁.scale * f.μ S₁.effect = S₂.scale * (r.1 * f.μ S₁.effect)
        show S₁.scale * f.μ S₁.effect = S₂.scale * ((S₁.scale / S₂.scale) * f.μ S₁.effect)
        have hS₂_ne : S₂.scale ≠ 0 := ne_of_gt hp₂
        field_simp
      ·
        have hle' : S₂.scale ≤ S₁.scale := hlt.le
        have h_op_eq : (S₂.scale : ℂ) • S₂.effect.op = (S₁.scale : ℂ) • S₁.effect.op := hEq.symm
        have h_ratio : S₁.effect.op = ((S₂.scale / S₁.scale : ℝ) : ℂ) • S₂.effect.op :=
          effect_ratio_of_scaled_eq hp₂ hle' h_op_eq
        set r : Effect.UnitIcc := ratioIcc hp₂.le hle' hp₁ with hr_def
        have h_eff_eq : S₁.effect = Effect.smulIcc r S₂.effect := by
          apply Effect.ext_op
          show S₁.effect.op = (r.1 : ℂ) • S₂.effect.op
          rw [h_ratio]
          show ((S₂.scale / S₁.scale : ℝ) : ℂ) • S₂.effect.op = (r.1 : ℂ) • S₂.effect.op
          rfl
        rw [h_eff_eq, f.μ_smulIcc]
        show S₁.scale * (r.1 * f.μ S₂.effect) = S₂.scale * f.μ S₂.effect
        show S₁.scale * ((S₂.scale / S₁.scale) * f.μ S₂.effect) = S₂.scale * f.μ S₂.effect
        have hS₁_ne : S₁.scale ≠ 0 := ne_of_gt hp₁
        field_simp

/-- **Corollary**: `muScaled` descends to a function on operator-equivalence classes. -/
theorem muScaled_eq_of_op_eq (f : GenFrameFunction H) {S₁ S₂ : SclEffect H}
    (h : S₁.op = S₂.op) : f.muScaled S₁ = f.muScaled S₂ :=
  muScaled_well_defined f S₁ S₂ h

/-- **Additivity on scaled effects** for pairs that sum to an effect.
If the sum of two scaled effects equals an effect's operator, and `muScaled` is
already known to be additive in this situation, we recover `μ(E)`. -/
theorem muScaled_add_when_effect (f : GenFrameFunction H) (S₁ S₂ : SclEffect H)
    (E : Effect H) :
    f.muScaled S₁ + f.muScaled S₂
      = f.muScaled (SclEffect.ofEffect E) → f.μ E = f.muScaled S₁ + f.muScaled S₂ := by
  intro h
  rw [h]
  simp

end GenFrameFunction

end Busch
