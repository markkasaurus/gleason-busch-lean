/-
# Busch/GleasonBusch.lean — Gleason's Theorem (Busch Route)
This file records the basic representation interfaces for Busch's effects
formulation of Gleason's theorem. It includes the backward map from effect
states to generalized frame functions, the pure-state instance, and
compatibility with convex combinations.
The arbitrary-frame-function direction is assembled in the later files
`GleasonFull` and `GleasonUnconditional`, after extending the effect functional
to self-adjoint operators and applying the finite-dimensional trace-pairing
representation theorem.
-/
import Busch.EffectState
import Busch.LinearExtension
import Busch.SegmentContinuity
import Busch.ClassicalBridge

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Backward direction: effect states yield frame functions -/
/-- Every effect state `ρ` yields a generalized frame function `μ_ρ` with
`μ_ρ(E) = ρ.frameValue E` for every
effect `E`. -/
theorem gleason_busch_backward (ρ : EffectState H) :
    ∃ μ : GenFrameFunction H, ∀ E : Effect H, μ.μ E = ρ.frameValue E :=
  ⟨ρ.toFrameFunction, fun _ => rfl⟩

/-! ### Forward direction — the pure-state case -/
/-- **Gleason forward direction, pure-state case**: Every pure-state frame
function comes from a pure effect state.  -/
theorem gleason_busch_forward_pureState (x : H) (hx : ‖x‖ = 1) :
    ∃ ρ : EffectState H,
      ∀ E : Effect H,
        (GenFrameFunction.pureState x hx).μ E = ρ.frameValue E :=
  ⟨EffectState.pure x hx, fun _ => rfl⟩

/-- **Round-trip identity for pure states**: the frame function of the pure
effect state at `x` equals the direct pure-state construction. -/
@[simp] theorem pure_toFrameFunction_eq_pureState (x : H) (hx : ‖x‖ = 1) :
    (EffectState.pure x hx).toFrameFunction
      = GenFrameFunction.pureState x hx := rfl

/-! ### Convex combinations are compatible -/
/-- **Frame function of a mixed effect state**: mixing effect states
produces the mixed frame function. This is the compatibility of the
`EffectState → GenFrameFunction` map with convex combinations. -/
theorem toFrameFunction_mixed (ρ σ : EffectState H) (t : Effect.UnitIcc) (E : Effect H) :
    (EffectState.mixed ρ σ t).toFrameFunction.μ E
      = t.1 * ρ.toFrameFunction.μ E + (1 - t.1) * σ.toFrameFunction.μ E := rfl

/-- **Mixing pure states** under the forward map recovers the `mixed` frame
function of `GenFrameFunction`. -/
theorem mixed_pure_toFrameFunction (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (t : Effect.UnitIcc) (E : Effect H) :
    (EffectState.mixed (EffectState.pure x hx) (EffectState.pure y hy) t
        ).toFrameFunction.μ E
      = (GenFrameFunction.mixed x y hx hy t).μ E := rfl

/-! ### The classical bridge: Busch ↔ classical frame functions on projections -/
variable [FiniteDimensional ℂ H]

/-- The backward direction, **restricted to projections**, recovers a classical
`FrameFunction H` from every effect state. -/
theorem gleason_busch_backward_classical (ρ : EffectState H) :
    ∃ f : FrameFunction H, ∀ P : Projection H,
      f.μ P = ρ.frameValue (Effect.ofClassicalProjection P) :=
  ⟨ρ.toFrameFunction.toFrameFunction, fun _ => rfl⟩

/-- **Summary theorem**: the Busch route yields a well-defined map
  `EffectState H → GenFrameFunction H → FrameFunction H`
from effect states to classical frame functions (on projections). -/
theorem busch_to_classical_factorization (ρ : EffectState H) (P : Projection H) :
    ρ.toFrameFunction.toFrameFunction.μ P
      = ρ.toFrameFunction.μ (Effect.ofClassicalProjection P) := rfl

end Busch
