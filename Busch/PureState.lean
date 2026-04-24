/-
# Busch/PureState.lean — Pure-State Frame Functions
For any unit vector `x ∈ H`, the map `E ↦ Re ⟨x, E x⟩` is a generalized frame
function on effects. These are the **pure states**: the simplest concrete
examples of `GenFrameFunction H`.
This establishes that the space of Busch frame functions is nonempty (for every
unit vector) and supplies concrete examples used by the state interface.
-/
import Busch.GenFrameFunction
import Busch.EffectScalar

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace GenFrameFunction

/-- The pure-state frame function: `μ_x(E) := Re ⟨x, E x⟩` for a unit vector `x`. -/
def pureState (x : H) (hx : ‖x‖ = 1) : GenFrameFunction H where
  μ E := (inner (𝕜 := ℂ) x (E.op x)).re
  nonneg E := E.nonneg x
  additive E F h := by
    show (inner (𝕜 := ℂ) x ((Effect.orthoSum E F h).op x)).re
        = (inner (𝕜 := ℂ) x (E.op x)).re + (inner (𝕜 := ℂ) x (F.op x)).re
    simp only [Effect.orthoSum_op, ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
  normalized := by
    show (inner (𝕜 := ℂ) x ((1 : Effect H).op x)).re = 1
    simp only [Effect.one_op, ContinuousLinearMap.id_apply]
    have h : (inner (𝕜 := ℂ) x x).re = ‖x‖ ^ 2 := by
      exact_mod_cast @inner_self_eq_norm_sq ℂ H _ _ _ x
    rw [h, hx]
    norm_num
@[simp] lemma pureState_apply (x : H) (hx : ‖x‖ = 1) (E : Effect H) :
    (pureState x hx).μ E = (inner (𝕜 := ℂ) x (E.op x)).re := rfl

/-- The pure state at zero effect is zero. -/
lemma pureState_zero (x : H) (hx : ‖x‖ = 1) : (pureState x hx).μ 0 = 0 := by
  simp [pureState]

/-- Pure states evaluated on the identity effect yield 1. -/
lemma pureState_one (x : H) (hx : ‖x‖ = 1) : (pureState x hx).μ 1 = 1 :=
  (pureState x hx).normalized

/-- **Affine combinations of pure states are frame functions**: for `t ∈ [0,1]`,
the convex combination `t·μ_x + (1-t)·μ_y` is again a frame function. -/
def mixed (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (t : Effect.UnitIcc) :
    GenFrameFunction H where
  μ E := t.1 * (inner (𝕜 := ℂ) x (E.op x)).re + (1 - t.1) * (inner (𝕜 := ℂ) y (E.op y)).re
  nonneg E := by
    have h_t : 0 ≤ t.1 := t.2.1
    have h_1t : 0 ≤ 1 - t.1 := by linarith [t.2.2]
    have h_x : 0 ≤ (inner (𝕜 := ℂ) x (E.op x)).re := E.nonneg x
    have h_y : 0 ≤ (inner (𝕜 := ℂ) y (E.op y)).re := E.nonneg y
    have h1 : 0 ≤ t.1 * (inner (𝕜 := ℂ) x (E.op x)).re := mul_nonneg h_t h_x
    have h2 : 0 ≤ (1 - t.1) * (inner (𝕜 := ℂ) y (E.op y)).re := mul_nonneg h_1t h_y
    linarith
  additive E F h := by
    show t.1 * (inner (𝕜 := ℂ) x ((Effect.orthoSum E F h).op x)).re
          + (1 - t.1) * (inner (𝕜 := ℂ) y ((Effect.orthoSum E F h).op y)).re
        = (t.1 * (inner (𝕜 := ℂ) x (E.op x)).re
            + (1 - t.1) * (inner (𝕜 := ℂ) y (E.op y)).re)
          + (t.1 * (inner (𝕜 := ℂ) x (F.op x)).re
              + (1 - t.1) * (inner (𝕜 := ℂ) y (F.op y)).re)
    simp only [Effect.orthoSum_op, ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
    ring
  normalized := by
    show t.1 * (inner (𝕜 := ℂ) x ((1 : Effect H).op x)).re
          + (1 - t.1) * (inner (𝕜 := ℂ) y ((1 : Effect H).op y)).re = 1
    simp only [Effect.one_op, ContinuousLinearMap.id_apply]
    have hxx : (inner (𝕜 := ℂ) x x).re = ‖x‖ ^ 2 := by
      exact_mod_cast @inner_self_eq_norm_sq ℂ H _ _ _ x
    have hyy : (inner (𝕜 := ℂ) y y).re = ‖y‖ ^ 2 := by
      exact_mod_cast @inner_self_eq_norm_sq ℂ H _ _ _ y
    rw [hxx, hyy, hx, hy]
    ring
@[simp] lemma mixed_apply (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (t : Effect.UnitIcc) (E : Effect H) :
    (mixed x y hx hy t).μ E
      = t.1 * (inner (𝕜 := ℂ) x (E.op x)).re
        + (1 - t.1) * (inner (𝕜 := ℂ) y (E.op y)).re := rfl

end GenFrameFunction

end Busch
