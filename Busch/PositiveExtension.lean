/-
# Busch/PositiveExtension.lean — Extension to Scaled Effects
This file defines the positive-cone extension of a generalized frame function.
A scaled effect packages a scalar `c ≥ 0` and an effect `E`, with underlying
operator `c • E.op`, and `muScaled` evaluates it as `c * μ(E)`.
The main well-definedness result shows that equal scaled-effect operators have
equal `muScaled` values. This prepares the extension from effects to positive
bounded operators.
-/
import Busch.ConvexCombination

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A scaled effect: a pair `(c, E)` with `c ≥ 0` and `E : Effect H`.
The underlying operator is `c · E.op`. -/
structure SclEffect (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  scale : ℝ
  scale_nn : 0 ≤ scale
  effect : Effect H

namespace SclEffect

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The underlying operator: `c · E.op`. -/
def op (S : SclEffect H) : H →L[ℂ] H := (S.scale : ℂ) • S.effect.op

/-- Scaled effect from an effect (with scale 1). -/
def ofEffect (E : Effect H) : SclEffect H := ⟨1, zero_le_one, E⟩
@[simp] lemma ofEffect_op (E : Effect H) : (ofEffect E).op = E.op := by
  simp [ofEffect, op]

/-- Zero scaled effect. -/
def zero : SclEffect H := ⟨0, le_refl _, (0 : Effect H)⟩

instance : Zero (SclEffect H) := ⟨zero⟩

lemma zero_op : (0 : SclEffect H).op = (0 : H →L[ℂ] H) := by
  show ((0 : ℝ) : ℂ) • (zero : SclEffect H).effect.op = 0
  simp

/-- Scaling a scaled effect by `c ≥ 0`: produces `(c · S.scale, S.effect)`. -/
def smul (c : ℝ) (hc : 0 ≤ c) (S : SclEffect H) : SclEffect H :=
  ⟨c * S.scale, mul_nonneg hc S.scale_nn, S.effect⟩

lemma smul_op (c : ℝ) (hc : 0 ≤ c) (S : SclEffect H) :
    (S.smul c hc).op = (c : ℂ) • S.op := by
  show ((c * S.scale : ℝ) : ℂ) • S.effect.op = (c : ℂ) • ((S.scale : ℂ) • S.effect.op)
  rw [smul_smul]
  push_cast
  ring_nf

end SclEffect

namespace GenFrameFunction

/-- **Positive extension**: For a scaled effect `(c, E)`, define `muScaled(c, E) = c · μ(E)`. -/
def muScaled (f : GenFrameFunction H) (S : SclEffect H) : ℝ := S.scale * f.μ S.effect
@[simp] lemma muScaled_ofEffect (f : GenFrameFunction H) (E : Effect H) :
    f.muScaled (SclEffect.ofEffect E) = f.μ E := by
  simp [muScaled, SclEffect.ofEffect]
@[simp] lemma muScaled_zero (f : GenFrameFunction H) : f.muScaled (0 : SclEffect H) = 0 := by
  show (0 : SclEffect H).scale * f.μ (0 : SclEffect H).effect = 0
  show SclEffect.zero.scale * f.μ SclEffect.zero.effect = 0
  simp [SclEffect.zero]

/-- `muScaled` is nonnegative. -/
lemma muScaled_nonneg (f : GenFrameFunction H) (S : SclEffect H) : 0 ≤ f.muScaled S :=
  mul_nonneg S.scale_nn (f.nonneg S.effect)

/-- Scaling: `muScaled(c · S) = c · muScaled(S)`. -/
lemma muScaled_smul (f : GenFrameFunction H) (c : ℝ) (hc : 0 ≤ c) (S : SclEffect H) :
    f.muScaled (SclEffect.smul c hc S) = c * f.muScaled S := by
  simp [muScaled, SclEffect.smul]
  ring

end GenFrameFunction

end Busch
