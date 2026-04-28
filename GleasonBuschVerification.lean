/-
# Verification Entry Point

This file proves the statement from `GleasonBuschStatement.lean` using the
formalization in `Busch/`.
-/
import GleasonBuschStatement
import Busch.EffectPredicate
import Busch.GleasonUnconditional

noncomputable section

namespace GleasonBusch

namespace StatementBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
lemma isEffect_to_busch {E : H →L[ℂ] H} (hE : IsEffect E) : Busch.IsEffect E := by
  simpa [IsEffect, Busch.IsEffect] using hE

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
lemma isEffect_of_busch {E : H →L[ℂ] H} (hE : Busch.IsEffect E) : IsEffect E := by
  simpa [IsEffect, Busch.IsEffect] using hE

def toBundledFrameFunction (f : GenFrameFunction H) : Busch.GenFrameFunction H where
  μ E := f.μ E.op
  nonneg E := by
    exact f.nonneg E.op (isEffect_of_busch (Busch.Effect.isEffect_op E))
  additive E F h := by
    have hE : IsEffect E.op := isEffect_of_busch (Busch.Effect.isEffect_op E)
    have hF : IsEffect F.op := isEffect_of_busch (Busch.Effect.isEffect_op F)
    have hsum : IsEffect (E.op + F.op) := by
      have h' : Busch.IsEffect (Busch.Effect.orthoSum E F h).op :=
        Busch.Effect.isEffect_op (Busch.Effect.orthoSum E F h)
      simpa [Busch.Effect.orthoSum_op, IsEffect, Busch.IsEffect] using h'
    simpa [Busch.Effect.orthoSum_op] using f.additive E.op F.op hE hF hsum
  normalized := by
    simpa using f.normalized

omit [FiniteDimensional ℂ H] in
lemma selfAdjoint_of_inner
    {ρ : H →L[ℂ] H}
    (hρ : ∀ x y : H, inner (𝕜 := ℂ) (ρ x) y = inner (𝕜 := ℂ) x (ρ y)) :
    IsSelfAdjoint ρ := by
  have hSymm : ρ.IsSymmetric := fun x y => hρ x y
  exact hSymm.isSelfAdjoint

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
lemma reTr_eq_busch_reTr (A : H →L[ℂ] H) :
    reTr A = Busch.reTr A := by
  rfl

end StatementBridge

open StatementBridge

/-- Proof of the statement-only entry point. -/
theorem gleason_busch_verified : GleasonBuschTheorem := by
  intro H _ _ _ _ hdim f
  let fB : Busch.GenFrameFunction H := toBundledFrameFunction f
  obtain ⟨ρ, hρ, htr, htrace, hnonneg⟩ :=
    Busch.gleason_busch_unconditional (H := H) hdim fB
  refine ⟨ρ, selfAdjoint_of_inner hρ, ?_, ?_, ?_⟩
  · simpa [reTr_eq_busch_reTr] using htr
  · intro E hE
    let EB : Busch.Effect H := Busch.Effect.ofIsEffect E (isEffect_to_busch hE)
    have hEB := htrace EB
    simpa [EB, fB, Busch.Effect.ofIsEffect_op, reTr_eq_busch_reTr] using hEB
  · intro E hE
    let EB : Busch.Effect H := Busch.Effect.ofIsEffect E (isEffect_to_busch hE)
    have hEB := hnonneg EB
    simpa [EB, Busch.Effect.ofIsEffect_op, reTr_eq_busch_reTr] using hEB

end GleasonBusch
