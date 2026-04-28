/-
# Statement-Only Entry Point

This file contains the public theorem statement using only Mathlib imports.
It intentionally does not import any file from this repository.
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Trace

noncomputable section

namespace GleasonBusch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An effect, stated as an unbundled predicate on continuous linear operators. -/
def IsEffect (E : H →L[ℂ] H) : Prop :=
  ContinuousLinearMap.IsPositive E ∧
    ∀ x : H, (inner (𝕜 := ℂ) x (E x)).re ≤ (inner (𝕜 := ℂ) x x).re

/-- A generalized frame function on effects, stated without bundling effects. -/
structure GenFrameFunction (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  μ : (H →L[ℂ] H) → ℝ
  nonneg : ∀ E : H →L[ℂ] H, IsEffect E → 0 ≤ μ E
  additive : ∀ E F : H →L[ℂ] H,
    IsEffect E → IsEffect F → IsEffect (E + F) → μ (E + F) = μ E + μ F
  normalized : μ (1 : H →L[ℂ] H) = 1

variable [FiniteDimensional ℂ H]

/-- The real part of the complex trace of a continuous linear operator. -/
def reTr (A : H →L[ℂ] H) : ℝ :=
  (LinearMap.trace ℂ H A.toLinearMap).re

/-- Trace-pairing representation target for an unbundled generalized frame function. -/
def GleasonTarget (f : GenFrameFunction H) : Prop :=
  ∃ ρ : H →L[ℂ] H,
    IsSelfAdjoint ρ ∧
    reTr ρ = 1 ∧
    (∀ E : H →L[ℂ] H, IsEffect E → f.μ E = reTr (ρ * E)) ∧
    (∀ E : H →L[ℂ] H, IsEffect E → 0 ≤ reTr (ρ * E))

/-- Busch's effects formulation of Gleason's theorem, as a standalone statement. -/
def GleasonBuschTheorem : Prop :=
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [FiniteDimensional ℂ H],
    2 ≤ Module.finrank ℂ H →
    ∀ f : GenFrameFunction H, GleasonTarget f

end GleasonBusch
