/-
# Busch/SegmentContinuity.lean — Lipschitz Continuity Along Convex Segments
From convex linearity:
  `μ(tE + (1-t)F) = t·μ(E) + (1-t)·μ(F)`
it follows that the map `t ↦ μ(tE + (1-t)F)` is affine in `t`, hence
Lipschitz with constant `|μ(E) - μ(F)|`. Since `μ : Effect H → ℝ` with
values in `[0,1]`, we also get the uniform Lipschitz bound `1`.
-/
import Busch.ConvexLinearity

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace GenFrameFunction

/-- **Affine along segments**: `t ↦ μ(tE + (1-t)F)` is an affine function of `t`. -/
theorem μ_convexComb_affine (f : GenFrameFunction H) (E F : Effect H)
    (s t : Effect.UnitIcc) :
    f.μ (Effect.convexComb s E F) - f.μ (Effect.convexComb t E F)
      = (s.1 - t.1) * (f.μ E - f.μ F) := by
  rw [f.μ_convexComb s, f.μ_convexComb t]
  ring

/-- **Lipschitz bound along segments** (raw form). -/
theorem μ_convexComb_lipschitz_raw (f : GenFrameFunction H) (E F : Effect H)
    (s t : Effect.UnitIcc) :
    |f.μ (Effect.convexComb s E F) - f.μ (Effect.convexComb t E F)|
      = |s.1 - t.1| * |f.μ E - f.μ F| := by
  rw [f.μ_convexComb_affine E F s t]
  rw [abs_mul]

/-- **Uniform Lipschitz bound**: along any convex segment of effects, `μ` is
    Lipschitz with constant `1`. This uses the fact that `μ` takes values in `[0,1]`. -/
theorem μ_convexComb_lipschitz_one (f : GenFrameFunction H) (E F : Effect H)
    (s t : Effect.UnitIcc) :
    |f.μ (Effect.convexComb s E F) - f.μ (Effect.convexComb t E F)| ≤ |s.1 - t.1| := by
  rw [f.μ_convexComb_lipschitz_raw E F s t]
  have h_E : f.μ E ∈ Set.Icc (0 : ℝ) 1 := f.μ_mem_unitInterval E
  have h_F : f.μ F ∈ Set.Icc (0 : ℝ) 1 := f.μ_mem_unitInterval F
  have h_bound : |f.μ E - f.μ F| ≤ 1 := by
    rcases h_E with ⟨hE0, hE1⟩
    rcases h_F with ⟨hF0, hF1⟩
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have h_nonneg : (0 : ℝ) ≤ |s.1 - t.1| := abs_nonneg _
  calc |s.1 - t.1| * |f.μ E - f.μ F|
      ≤ |s.1 - t.1| * 1 := mul_le_mul_of_nonneg_left h_bound h_nonneg
    _ = |s.1 - t.1| := by ring

/-- **Monotonicity on segments**: if `μ(E) ≤ μ(F)` then `s ↦ μ(sE + (1-s)F)` is
    nonincreasing in `s` on `[0,1]`. -/
theorem μ_convexComb_monotone (f : GenFrameFunction H) {E F : Effect H}
    (h : f.μ E ≤ f.μ F) {s t : Effect.UnitIcc} (hst : s.1 ≤ t.1) :
    f.μ (Effect.convexComb t E F) ≤ f.μ (Effect.convexComb s E F) := by
  rw [f.μ_convexComb s, f.μ_convexComb t]
  have h_diff : 0 ≤ t.1 - s.1 := by linarith
  nlinarith

/-- **Endpoint values**: at `t = 1`, the convex combination is `E`. -/
@[simp] lemma convexComb_one (E F : Effect H) :
    Effect.convexComb ⟨1, zero_le_one, le_refl _⟩ E F = E := by
  apply Effect.ext
  intro x
  show ((1 : ℝ) : ℂ) • E.op x + (((1 - 1) : ℝ) : ℂ) • F.op x = E.op x
  simp

/-- **Endpoint values**: at `t = 0`, the convex combination is `F`. -/
@[simp] lemma convexComb_zero (E F : Effect H) :
    Effect.convexComb ⟨0, le_refl _, zero_le_one⟩ E F = F := by
  apply Effect.ext
  intro x
  show ((0 : ℝ) : ℂ) • E.op x + (((1 - 0) : ℝ) : ℂ) • F.op x = F.op x
  simp

/-- **μ is Lipschitz as the segment parameter varies from 1 (= `E`) to 0 (= `F`)**.
    The Lipschitz constant is `|μ(E) - μ(F)| ≤ 1`. -/
theorem μ_endpoint_difference (f : GenFrameFunction H) (E F : Effect H) :
    f.μ E - f.μ F
      = f.μ (Effect.convexComb ⟨1, zero_le_one, le_refl _⟩ E F)
        - f.μ (Effect.convexComb ⟨0, le_refl _, zero_le_one⟩ E F) := by
  rw [convexComb_one, convexComb_zero]

end GenFrameFunction

end Busch
