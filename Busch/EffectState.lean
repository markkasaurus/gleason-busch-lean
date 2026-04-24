/-
# Busch/EffectState.lean — Effect States

This file defines an auxiliary state object on the effect algebra. An
`EffectState H` assigns a nonnegative, normalized, orthogonally additive real
value to each effect.

The final representation theorem constructs an actual operator
`ρ : H →L[ℂ] H`. The type in this file is used only for the backward examples
and compatibility lemmas.
-/
import Busch.PureState

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Effect states -/
/-- A state on the effect algebra of a Hilbert space `H`. -/
structure EffectState (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The induced value on each effect. -/
  frameValue : Effect H → ℝ
  /-- Nonnegativity. -/
  nonneg : ∀ E : Effect H, 0 ≤ frameValue E
  /-- Additivity on orthogonal sums. -/
  additive : ∀ (E F : Effect H) (h : Effect.Summable E F),
      frameValue (Effect.orthoSum E F h) = frameValue E + frameValue F
  /-- Normalization: the value at the identity effect is 1. -/
  normalized : frameValue (1 : Effect H) = 1

namespace EffectState

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every effect state is a generalized frame function. -/
def toFrameFunction (ρ : EffectState H) : GenFrameFunction H where
  μ := ρ.frameValue
  nonneg := ρ.nonneg
  additive := ρ.additive
  normalized := ρ.normalized

@[simp] lemma toFrameFunction_μ (ρ : EffectState H) (E : Effect H) :
    (ρ.toFrameFunction).μ E = ρ.frameValue E := rfl

/-! ### Pure states -/
/-- The pure effect state associated to a unit vector `x`.
Its value is `E ↦ Re⟪x, E x⟫`. -/
def pure (x : H) (hx : ‖x‖ = 1) : EffectState H where
  frameValue E := (inner (𝕜 := ℂ) x (E.op x)).re
  nonneg E := E.nonneg x
  additive E F h := by
    simp only [Effect.orthoSum_op, ContinuousLinearMap.add_apply, inner_add_right,
      Complex.add_re]
  normalized := by
    show (inner (𝕜 := ℂ) x ((1 : Effect H).op x)).re = 1
    simp only [Effect.one_op, ContinuousLinearMap.id_apply]
    have h : (inner (𝕜 := ℂ) x x).re = ‖x‖ ^ 2 := by
      exact_mod_cast @inner_self_eq_norm_sq ℂ H _ _ _ x
    rw [h, hx]
    norm_num

@[simp] lemma pure_frameValue (x : H) (hx : ‖x‖ = 1) (E : Effect H) :
    (pure x hx).frameValue E = (inner (𝕜 := ℂ) x (E.op x)).re := rfl

/-- The frame function of a pure effect state matches the direct pure-state
frame function. -/
lemma pure_toFrameFunction (x : H) (hx : ‖x‖ = 1) :
    (pure x hx).toFrameFunction = GenFrameFunction.pureState x hx := by
  rfl

/-! ### Convex combinations -/
/-- Convex combination of effect states. -/
def mixed (ρ σ : EffectState H) (t : Effect.UnitIcc) : EffectState H where
  frameValue E := t.1 * ρ.frameValue E + (1 - t.1) * σ.frameValue E
  nonneg E := by
    have h_t : 0 ≤ t.1 := t.2.1
    have h_1t : 0 ≤ 1 - t.1 := by linarith [t.2.2]
    have h₁ : 0 ≤ t.1 * ρ.frameValue E := mul_nonneg h_t (ρ.nonneg E)
    have h₂ : 0 ≤ (1 - t.1) * σ.frameValue E := mul_nonneg h_1t (σ.nonneg E)
    linarith
  additive E F h := by
    rw [ρ.additive E F h, σ.additive E F h]
    ring
  normalized := by
    rw [ρ.normalized, σ.normalized]
    ring

@[simp] lemma mixed_frameValue (ρ σ : EffectState H) (t : Effect.UnitIcc) (E : Effect H) :
    (mixed ρ σ t).frameValue E = t.1 * ρ.frameValue E + (1 - t.1) * σ.frameValue E := rfl

/-- Mixing with the trivial parameter `t = 1` recovers the first state. -/
lemma mixed_one (ρ σ : EffectState H) :
    mixed ρ σ ⟨1, zero_le_one, le_refl _⟩ = ρ := by
  cases ρ with | mk μρ nnρ addρ nρ =>
  cases σ with | mk μσ nnσ addσ nσ =>
  simp only [mixed]
  congr
  ext E
  simp

/-- Mixing with the trivial parameter `t = 0` recovers the second state. -/
lemma mixed_zero (ρ σ : EffectState H) :
    mixed ρ σ ⟨0, le_refl _, zero_le_one⟩ = σ := by
  cases ρ with | mk μρ nnρ addρ nρ =>
  cases σ with | mk μσ nnσ addσ nσ =>
  simp only [mixed]
  congr
  ext E
  simp

end EffectState

end Busch
