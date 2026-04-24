import Classical.Projection
import Classical.RankOneProjection
import Mathlib

noncomputable section

open RankOne

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

/-- Frame functions on projections. -/
structure FrameFunction (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H] where
  μ : Projection H → ℝ
  nonneg : ∀ P : Projection H, 0 ≤ μ P
  additive :
    ∀ P Q (h : Projection.orthogonal P Q),
      μ (Projection.add P Q h) = μ P + μ Q
  normalized : μ Projection.one = 1

/-- Quadratic form induced by a frame function using rank-one projections. -/
def frame_quadratic (μ : FrameFunction H) (x : H) : ℝ := by
  classical
  exact if h : x = 0 then 0 else μ.μ (rankOneProjection (H := H) x h) * ‖x‖ ^ 2

namespace FrameFunction

/-- 2D quadratic-form property on orthonormal pairs `u,v`. -/
def HasQuad2D (μ : FrameFunction H) : Prop :=
  ∀ u v : H,
    ‖u‖ = (1 : ℝ) →
    ‖v‖ = (1 : ℝ) →
    inner (𝕜 := ℂ) u v = 0 →
    ∃ α β γ : ℝ,
      ∀ a b : ℝ,
        frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v) +
          frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v)
          = α * a ^ 2 + β * a * b + γ * b ^ 2

end FrameFunction
