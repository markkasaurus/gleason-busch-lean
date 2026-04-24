/-
# Busch/RankOneEffect.lean — Rank-One Effects
For every non-zero `x ∈ H`, the rank-one projection `|x⟩⟨x|` onto `ℂ · x` is
an effect in the Busch sense. We call it `Effect.rankOne x hx`.
This is the bridge between:
- the analytic objects used in classical Gleason (rank-one projections),
- the Busch effect algebra (`Effect H`),
- the pure effect states (`EffectState.pure x`).
The value `μ(Effect.rankOne x hx)` is the rank-one value used to compare the
effect formulation with projection-based notation.
-/
import Busch.ClassicalBridge
import Classical.RankOneProjection

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

namespace Effect

/-- The **rank-one effect** `|x⟩⟨x|` for `x ≠ 0`: lift the rank-one projection
onto `ℂ · x` via the classical bridge. -/
def rankOne (x : H) (hx : x ≠ 0) : Effect H :=
  Effect.ofClassicalProjection (RankOne.rankOneProjection x hx)

omit [FiniteDimensional ℂ H] in
@[simp] lemma rankOne_op (x : H) (hx : x ≠ 0) :
    (rankOne x hx).op = (RankOne.rankOneProjection x hx).1 := rfl

omit [FiniteDimensional ℂ H] in
/-- `rankOne` is a projection-effect (idempotent). -/
lemma rankOne_isProjection (x : H) (hx : x ≠ 0) : IsProjection (rankOne x hx) :=
  Effect.ofClassicalProjection_isProjection _

end Effect

namespace GenFrameFunction

/-- The **quadratic form** `Q(x) := μ(|x⟩⟨x|) · ‖x‖²` for `x ≠ 0`, and `Q(0) := 0`. -/
def frameQuadratic (f : GenFrameFunction H) (x : H) : ℝ := by
  classical
  exact if hx : x = 0 then 0 else f.μ (Effect.rankOne x hx) * ‖x‖ ^ 2

omit [FiniteDimensional ℂ H] in
@[simp] lemma frameQuadratic_zero (f : GenFrameFunction H) : f.frameQuadratic 0 = 0 := by
  unfold frameQuadratic
  simp

omit [FiniteDimensional ℂ H] in
lemma frameQuadratic_of_ne_zero (f : GenFrameFunction H) {x : H} (hx : x ≠ 0) :
    f.frameQuadratic x = f.μ (Effect.rankOne x hx) * ‖x‖ ^ 2 := by
  unfold frameQuadratic
  simp [hx]

omit [FiniteDimensional ℂ H] in
/-- `frameQuadratic μ` is nonnegative. -/
theorem frameQuadratic_nonneg (f : GenFrameFunction H) (x : H) : 0 ≤ f.frameQuadratic x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [f.frameQuadratic_of_ne_zero hx]
    exact mul_nonneg (f.nonneg _) (sq_nonneg _)

omit [FiniteDimensional ℂ H] in
/-- For a unit vector `x`, the quadratic form equals `μ(|x⟩⟨x|)`. -/
theorem frameQuadratic_unit (f : GenFrameFunction H) {x : H} (hx : ‖x‖ = 1) :
    f.frameQuadratic x = f.μ (Effect.rankOne x (by
      intro h
      rw [h, norm_zero] at hx
      exact one_ne_zero hx.symm)) := by
  have hx_ne : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    exact one_ne_zero hx.symm
  rw [f.frameQuadratic_of_ne_zero hx_ne]
  have : ‖x‖ ^ 2 = 1 := by rw [hx]; norm_num
  rw [this]
  ring

end GenFrameFunction

/-! ### Projection-frame connection -/
/-- The Busch `frameQuadratic` of a generalized frame function `f` agrees with
the classical `frame_quadratic` of its restriction `f.toFrameFunction`. -/
theorem frameQuadratic_toFrameFunction (f : GenFrameFunction H) (x : H) :
    f.frameQuadratic x = frame_quadratic (H := H) f.toFrameFunction x := by
  unfold GenFrameFunction.frameQuadratic frame_quadratic
  by_cases hx : x = 0
  · simp [hx]
  · simp only [hx, ↓reduceDIte]
    rfl

end Busch
