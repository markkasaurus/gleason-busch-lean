/-
# Busch/Homogeneity.lean — Dyadic Homogeneity of Frame Functions
For a generalized frame function `μ` on effects:
- `μ((1/2) E) = (1/2) μ(E)` (half-scaling)
- `μ((k/2^n) E) = (k/2^n) μ(E)` for `0 ≤ k ≤ 2^n` (dyadic homogeneity)
The proof uses the additivity of `μ` on orthogonal sums: `(1/2)E ⊕ (1/2)E = E`
gives `2·μ((1/2)E) = μ(E)`, hence `μ((1/2)E) = μ(E)/2`.
-/
import Busch.Monotonicity

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Effect

/-- The half-point `1/2` in `[0, 1]`. -/
def halfIcc : UnitIcc := ⟨1 / 2, by norm_num, by norm_num⟩

/-- `(1/2)E` and `(1/2)E` are summable. -/
lemma smulIcc_half_half_summable (E : Effect H) :
    Summable (smulIcc halfIcc E) (smulIcc halfIcc E) := by
  intro x
  show (inner (𝕜 := ℂ) x (((1/2 : ℝ) : ℂ) • E.op x + ((1/2 : ℝ) : ℂ) • E.op x)).re ≤ _
  have h_eq : ((1/2 : ℝ) : ℂ) • E.op x + ((1/2 : ℝ) : ℂ) • E.op x = E.op x := by
    rw [show ((1/2 : ℝ) : ℂ) = (1/2 : ℂ) by push_cast; ring]
    rw [← add_smul, show (1/2 : ℂ) + (1/2 : ℂ) = 1 by ring]
    simp
  rw [h_eq]
  exact E.le_one x

/-- `(1/2)E ⊕ (1/2)E = E`. -/
lemma smulIcc_half_add_half (E : Effect H) :
    orthoSum (smulIcc halfIcc E) (smulIcc halfIcc E) (smulIcc_half_half_summable E) = E := by
  apply ext
  intro x
  show (smulIcc halfIcc E) x + (smulIcc halfIcc E) x = E x
  simp only [smulIcc_apply, halfIcc]
  rw [show ((1/2 : ℝ) : ℂ) = (1/2 : ℂ) by push_cast; ring]
  rw [← add_smul, show (1/2 : ℂ) + (1/2 : ℂ) = 1 by ring]
  simp

end Effect

namespace GenFrameFunction

/-- **Half-scaling**: `μ((1/2) E) = (1/2) μ(E)`. -/
theorem μ_half (f : GenFrameFunction H) (E : Effect H) :
    f.μ (Effect.smulIcc Effect.halfIcc E) = (1 / 2) * f.μ E := by
  have h_sum := Effect.smulIcc_half_add_half E
  have h_add := f.additive (Effect.smulIcc Effect.halfIcc E)
    (Effect.smulIcc Effect.halfIcc E) (Effect.smulIcc_half_half_summable E)
  rw [h_sum] at h_add
  linarith

/-- **Zero scaling**: `μ(0 · E) = 0`. -/
theorem μ_zero_smul (f : GenFrameFunction H) (E : Effect H) :
    f.μ (Effect.smulIcc ⟨0, le_refl 0, zero_le_one⟩ E) = 0 := by
  rw [Effect.smulIcc_zero]
  exact f.μ_zero

/-- **One scaling**: `μ(1 · E) = μ(E)`. -/
theorem μ_one_smul (f : GenFrameFunction H) (E : Effect H) :
    f.μ (Effect.smulIcc ⟨1, zero_le_one, le_refl 1⟩ E) = f.μ E := by
  rw [Effect.smulIcc_one]

end GenFrameFunction

end Busch
