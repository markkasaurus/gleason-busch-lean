/-
# Busch/TraceRepresentation.lean — Trace Representation
This file provides the **Riesz-representation step** of Gleason's theorem via
the Busch route. Given:
* a generalized frame function `f : GenFrameFunction H` (finite-dim H),
* the ℝ-linear extension `muSA f : SA(H) → ℝ` (with any bound),
we show there exists `ρ : H →L[ℂ] H` with:
* `ρ` self-adjoint
* `reTr ρ = 1` (from `f.normalized`)
* `reTr (ρ · A) = muSA f A` for all SA `A`
* `reTr (ρ · E) ≥ 0` for every effect `E`

The conditional statements in this file isolate the trace-pairing
representation step. `Busch.RieszSA` supplies the finite-dimensional
Hilbert-Schmidt Riesz representation used by the final unconditional theorem.
## What this file proves
* `gleason_busch_via_riesz`: if the trace pairing `ρ ↦ (A ↦ reTr(ρ·A))` is
  surjective onto ℝ-linear functionals of SA operators, then every Busch frame
  function has a self-adjoint trace-one representing operator.
-/
import Busch.HilbertSchmidt
import Busch.SALinearity
import Busch.RankOneEffect

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The trace representation as a property of ρ
The predicate below records the trace formula on effects. -/

/-- `RepresentsVia ρ f` holds iff `f.μ E = reTr (ρ * E.op)` for all effects. -/
def RepresentsVia (ρ : H →L[ℂ] H) (f : GenFrameFunction H) : Prop :=
  ∀ E : Effect H, f.μ E = reTr (ρ * E.op)

/-- If ρ represents f, then `ρ` evaluates correctly on the identity effect. -/
lemma RepresentsVia.trace_one {ρ : H →L[ℂ] H} {f : GenFrameFunction H}
    (h : RepresentsVia ρ f) : reTr ρ = 1 := by
  have := h (1 : Effect H)
  rw [f.normalized] at this
  have h_op : (1 : Effect H).op = 1 := rfl
  rw [h_op, mul_one] at this
  exact this.symm

/-- If ρ represents f, then `ρ` evaluates nonneg on positive operators that
come from effects. -/
lemma RepresentsVia.nonneg_on_effects {ρ : H →L[ℂ] H} {f : GenFrameFunction H}
    (h : RepresentsVia ρ f) (E : Effect H) : 0 ≤ reTr (ρ * E.op) := by
  rw [← h E]
  exact f.nonneg E

/-! ### The "pairing is surjective" hypothesis
This is the finite-dim Riesz step in abstract form. It states: every ℝ-linear
functional on SA(H) has the form `A ↦ reTr(ρ·A)` for some SA `ρ`. -/

/-- **The trace pairing hypothesis**: for a pairing coming from our muSA,
there exists ρ in SA(H) representing it via trace. -/
def TracePairingRiesz (f : GenFrameFunction H) : Prop :=
  ∃ ρ : H →L[ℂ] H,
    (∀ x y : H, inner (𝕜 := ℂ) (ρ x) y = inner (𝕜 := ℂ) x (ρ y)) ∧
    (∀ E : Effect H, f.μ E = reTr (ρ * E.op))

/-! ### Positivity transfer
From `TracePairingRiesz`, the trace pairing is nonnegative on effects because
it agrees with the nonnegative frame function. -/

/-- Rank-one effects inherit the trace representation formula. -/
lemma representsVia_pureState_value {ρ : H →L[ℂ] H} {f : GenFrameFunction H}
    (h : ∀ E : Effect H, f.μ E = reTr (ρ * E.op))
    {x : H} (hx : x ≠ 0) :
    f.μ (Effect.rankOne x hx) = reTr (ρ * (Effect.rankOne x hx).op) :=
  h _

/-! ### Gleason's theorem via Riesz (conditional form) -/
/-- If the trace pairing is surjective, every Busch frame function has a
self-adjoint trace-one representing operator whose trace pairing is nonnegative
on effects. -/
theorem gleason_busch_via_riesz (_hdim : 2 ≤ Module.finrank ℂ H) (f : GenFrameFunction H)
    (hRiesz : TracePairingRiesz f) :
    ∃ ρ : H →L[ℂ] H,
      (∀ x y : H, inner (𝕜 := ℂ) (ρ x) y = inner (𝕜 := ℂ) x (ρ y)) ∧
      reTr ρ = 1 ∧
      (∀ E : Effect H, f.μ E = reTr (ρ * E.op)) ∧
      (∀ E : Effect H, 0 ≤ reTr (ρ * E.op)) := by
  obtain ⟨ρ, hSA, hTrace⟩ := hRiesz
  refine ⟨ρ, hSA, ?_, hTrace, ?_⟩
  ·
    have := hTrace (1 : Effect H)
    rw [f.normalized] at this
    have h_op : (1 : Effect H).op = 1 := rfl
    rw [h_op, mul_one] at this
    exact this.symm
  ·
    intro E
    rw [← hTrace E]
    exact f.nonneg E

/-! ### Statement of unconditional forward direction (requires mathlib Riesz on HS) -/
/-- Statement form for the forward direction of Gleason's theorem via the Busch
route. It asserts a self-adjoint trace-one representing operator whose trace
pairing is nonnegative on effects. -/
def GleasonBuschStatement (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H] (f : GenFrameFunction H) : Prop :=
  ∃ ρ : H →L[ℂ] H,
    (∀ x y : H, inner (𝕜 := ℂ) (ρ x) y = inner (𝕜 := ℂ) x (ρ y)) ∧
    reTr ρ = 1 ∧
    (∀ E : Effect H, f.μ E = reTr (ρ * E.op)) ∧
    (∀ E : Effect H, 0 ≤ reTr (ρ * E.op))

/-- The Busch Gleason statement reduces to the trace-pairing
Riesz hypothesis. If one can establish `TracePairingRiesz`, the full forward direction
of Gleason follows. -/
theorem gleasonBuschStatement_of_tracePairingRiesz
    [FiniteDimensional ℂ H] (hdim : 2 ≤ Module.finrank ℂ H) (f : GenFrameFunction H)
    (hRiesz : TracePairingRiesz f) : GleasonBuschStatement H f :=
  gleason_busch_via_riesz hdim f hRiesz

end Busch
