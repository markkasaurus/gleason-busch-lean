/-
# Busch/GleasonFull.lean — Full Forward Direction of Gleason (Busch Route)
This file assembles the conditional form of the Busch representation theorem.
The main theorem states that a trace-pairing representation for the linear
extension of a generalized frame function yields the desired representing
operator on effects. The unconditional discharge of the trace-pairing
representation is completed in `GleasonUnconditional`.
-/
import Busch.TraceRepresentation
import Busch.GleasonBusch
import Busch.RankOneEffect

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

/-! ### Pure-state case
For a **pure-state frame function** `f = GenFrameFunction.pureState y hy` with
`‖y‖ = 1`, the representing effect is the rank-one projection onto `y`.
-/
omit [FiniteDimensional ℂ H] in
/-- Helper: a pure state is self-adjoint (via rank-one projection). -/
lemma pure_rankOne_isSelfAdjoint {y : H} (hy : y ≠ 0) :
    ∀ x z : H, inner (𝕜 := ℂ) ((Effect.rankOne y hy).op x) z
      = inner (𝕜 := ℂ) x ((Effect.rankOne y hy).op z) :=
  (Effect.rankOne y hy).isSelfAdjoint

/-! ### Conditional representation theorem -/
/-- **Gleason forward direction (Busch route, conditional form)**:
given the Riesz-type hypothesis on the Hilbert-Schmidt trace pairing, every
Busch generalized frame function in finite-dim `H` (dim ≥ 2) has a self-adjoint
trace-one representing operator satisfying the trace formula.
This is the final theorem in a form directly reducible to the `TracePairingRiesz`
hypothesis. `GleasonUnconditional` discharges that hypothesis.
-/
theorem gleason_busch_full (hdim : 2 ≤ Module.finrank ℂ H) (f : GenFrameFunction H)
    (hRiesz : TracePairingRiesz f) :
    ∃ ρ : H →L[ℂ] H,
      (∀ x y : H, inner (𝕜 := ℂ) (ρ x) y = inner (𝕜 := ℂ) x (ρ y)) ∧
      reTr ρ = 1 ∧
      (∀ E : Effect H, f.μ E = reTr (ρ * E.op)) ∧
      (∀ E : Effect H, 0 ≤ reTr (ρ * E.op)) :=
  gleasonBuschStatement_of_tracePairingRiesz hdim f hRiesz

/-- **Packaged as `GleasonBuschStatement`**: the conditional representation
theorem in the bundled statement form. -/
theorem gleason_busch_full_statement (hdim : 2 ≤ Module.finrank ℂ H)
    (f : GenFrameFunction H) (hRiesz : TracePairingRiesz f) :
    GleasonBuschStatement H f :=
  gleasonBuschStatement_of_tracePairingRiesz hdim f hRiesz

/-! ### Trace-representation target -/
/-- The target representation statement for Busch generalized frame functions.
The existential provides a self-adjoint trace-one operator whose trace pairing
agrees with `f.μ` on every effect and is nonnegative on effects. -/
def GleasonTarget (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H] (f : GenFrameFunction H) : Prop :=
  ∃ ρ : H →L[ℂ] H,
    (∀ x y : H, inner (𝕜 := ℂ) (ρ x) y = inner (𝕜 := ℂ) x (ρ y)) ∧
    reTr ρ = 1 ∧
    (∀ E : Effect H, f.μ E = reTr (ρ * E.op)) ∧
    (∀ E : Effect H, 0 ≤ reTr (ρ * E.op))

/-- **Final reduction theorem**: the forward direction of Gleason's theorem
reduces, for any Busch generalized frame function, to the Hilbert-Schmidt Riesz
representation step on SA(H). -/
theorem gleason_target_from_trace_pairing (hdim : 2 ≤ Module.finrank ℂ H)
    (f : GenFrameFunction H) (hRiesz : TracePairingRiesz f) :
    GleasonTarget H f := by
  obtain ⟨ρ, hSA, _, hTrace, hNonneg⟩ := gleason_busch_full hdim f hRiesz
  refine ⟨ρ, hSA, ?_, hTrace, hNonneg⟩
  have := hTrace (1 : Effect H)
  rw [f.normalized] at this
  have h_op : (1 : Effect H).op = 1 := rfl
  rw [h_op, mul_one] at this
  exact this.symm

end Busch
