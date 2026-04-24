/-
# Busch/PositiveOp.lean — Extension to Bounded Positive Operators
Given a **positive self-adjoint operator** `A` with an explicit upper bound
`c > 0` (i.e., `⟨x, A x⟩.re ≤ c · ⟨x, x⟩.re` for all `x`), we can form the effect
`(1/c) · A.op` and extend `μ` via:
  `muPosBounded f A c hSA hNN hLe := c · f.μ (effectOfBounded A c hSA hNN hLe)`
This is well-defined in the sense that **different valid bounds give the same
result** (by `muScaled_well_defined` from `LinearExtension.lean`).
This file provides the rigorous extension of `μ` to the subcone of positive
operators with a known bound, preparing the subsequent shift-based extension to
self-adjoint operators.
-/
import Busch.LinearExtension

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Effects from positive-bounded operators -/
namespace Effect

/-- An operator `A` with positive + self-adjoint + bounded-above-by-`c·I`
yields a scaled effect `(c, (1/c) • A)`. -/
def ofPosBounded (A : H →L[ℂ] H) (c : ℝ) (hc : 0 < c)
    (hSA : ∀ x y : H, inner (𝕜 := ℂ) (A x) y = inner (𝕜 := ℂ) x (A y))
    (hNN : ∀ x, 0 ≤ (inner (𝕜 := ℂ) x (A x)).re)
    (hLe : ∀ x, (inner (𝕜 := ℂ) x (A x)).re ≤ c * (inner (𝕜 := ℂ) x x).re) :
    Effect H where
  op := ((c⁻¹ : ℝ) : ℂ) • A
  isSelfAdjoint := fun x y => by
    simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right]
    rw [hSA x y]
    simp [Complex.conj_ofReal]
  nonneg x := by
    simp only [ContinuousLinearMap.smul_apply, inner_smul_right, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (inv_nonneg.mpr hc.le) (hNN x)
  le_one x := by
    simp only [ContinuousLinearMap.smul_apply, inner_smul_right, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hbound := hLe x
    have hinv_pos : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc
    have : c⁻¹ * (inner (𝕜 := ℂ) x (A x)).re ≤ c⁻¹ * (c * (inner (𝕜 := ℂ) x x).re) :=
      mul_le_mul_of_nonneg_left hbound hinv_pos.le
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul] at this
    exact this
@[simp] lemma ofPosBounded_op (A : H →L[ℂ] H) (c : ℝ) (hc : 0 < c)
    (hSA : ∀ x y : H, inner (𝕜 := ℂ) (A x) y = inner (𝕜 := ℂ) x (A y))
    (hNN : ∀ x, 0 ≤ (inner (𝕜 := ℂ) x (A x)).re)
    (hLe : ∀ x, (inner (𝕜 := ℂ) x (A x)).re ≤ c * (inner (𝕜 := ℂ) x x).re) :
    (ofPosBounded A c hc hSA hNN hLe).op = ((c⁻¹ : ℝ) : ℂ) • A := rfl

end Effect

/-! ### Scaled-effect lift from positive-bounded operator -/
namespace SclEffect

/-- The scaled effect `(c, ofPosBounded A c …)` whose underlying operator is `A`. -/
def ofPosBounded (A : H →L[ℂ] H) (c : ℝ) (hc : 0 < c)
    (hSA : ∀ x y : H, inner (𝕜 := ℂ) (A x) y = inner (𝕜 := ℂ) x (A y))
    (hNN : ∀ x, 0 ≤ (inner (𝕜 := ℂ) x (A x)).re)
    (hLe : ∀ x, (inner (𝕜 := ℂ) x (A x)).re ≤ c * (inner (𝕜 := ℂ) x x).re) :
    SclEffect H where
  scale := c
  scale_nn := hc.le
  effect := Effect.ofPosBounded A c hc hSA hNN hLe
@[simp] lemma ofPosBounded_op (A : H →L[ℂ] H) (c : ℝ) (hc : 0 < c)
    (hSA : ∀ x y : H, inner (𝕜 := ℂ) (A x) y = inner (𝕜 := ℂ) x (A y))
    (hNN : ∀ x, 0 ≤ (inner (𝕜 := ℂ) x (A x)).re)
    (hLe : ∀ x, (inner (𝕜 := ℂ) x (A x)).re ≤ c * (inner (𝕜 := ℂ) x x).re) :
    (ofPosBounded A c hc hSA hNN hLe).op = A := by
  show ((c : ℂ) • ((c⁻¹ : ℝ) : ℂ) • A) = A
  rw [smul_smul]
  have h_cast : (c : ℂ) * ((c⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    rw [mul_inv_cancel₀]
    exact_mod_cast ne_of_gt hc
  rw [h_cast, one_smul]

end SclEffect

/-! ### The extended function on positive-bounded operators -/
namespace GenFrameFunction

/-- **`muPosBounded`**: the value of the frame function extended to a positive
operator `A` with explicit bound `c`. Equals `c · μ(A/c)` where `A/c` is an
effect. -/
def muPosBounded (f : GenFrameFunction H) (A : H →L[ℂ] H) (c : ℝ) (hc : 0 < c)
    (hSA : ∀ x y : H, inner (𝕜 := ℂ) (A x) y = inner (𝕜 := ℂ) x (A y))
    (hNN : ∀ x, 0 ≤ (inner (𝕜 := ℂ) x (A x)).re)
    (hLe : ∀ x, (inner (𝕜 := ℂ) x (A x)).re ≤ c * (inner (𝕜 := ℂ) x x).re) : ℝ :=
  f.muScaled (SclEffect.ofPosBounded A c hc hSA hNN hLe)

lemma muPosBounded_eq_muScaled (f : GenFrameFunction H) (A : H →L[ℂ] H) (c : ℝ) (hc : 0 < c)
    (hSA : ∀ x y : H, inner (𝕜 := ℂ) (A x) y = inner (𝕜 := ℂ) x (A y))
    (hNN : ∀ x, 0 ≤ (inner (𝕜 := ℂ) x (A x)).re)
    (hLe : ∀ x, (inner (𝕜 := ℂ) x (A x)).re ≤ c * (inner (𝕜 := ℂ) x x).re) :
    f.muPosBounded A c hc hSA hNN hLe
      = f.muScaled (SclEffect.ofPosBounded A c hc hSA hNN hLe) := rfl

/-- **Independence of bound**: different valid bounds for the same positive
operator give the same `muPosBounded` value. -/
theorem muPosBounded_bound_independent (f : GenFrameFunction H) (A : H →L[ℂ] H)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hSA : ∀ x y : H, inner (𝕜 := ℂ) (A x) y = inner (𝕜 := ℂ) x (A y))
    (hNN : ∀ x, 0 ≤ (inner (𝕜 := ℂ) x (A x)).re)
    (hLe₁ : ∀ x, (inner (𝕜 := ℂ) x (A x)).re ≤ c₁ * (inner (𝕜 := ℂ) x x).re)
    (hLe₂ : ∀ x, (inner (𝕜 := ℂ) x (A x)).re ≤ c₂ * (inner (𝕜 := ℂ) x x).re) :
    f.muPosBounded A c₁ hc₁ hSA hNN hLe₁ = f.muPosBounded A c₂ hc₂ hSA hNN hLe₂ := by
  unfold muPosBounded
  exact muScaled_well_defined f _ _ (by
    show (SclEffect.ofPosBounded A c₁ hc₁ hSA hNN hLe₁).op
        = (SclEffect.ofPosBounded A c₂ hc₂ hSA hNN hLe₂).op
    rw [SclEffect.ofPosBounded_op, SclEffect.ofPosBounded_op])

/-- **Nonnegativity of `muPosBounded`**. -/
theorem muPosBounded_nonneg (f : GenFrameFunction H) (A : H →L[ℂ] H) (c : ℝ) (hc : 0 < c)
    (hSA : ∀ x y : H, inner (𝕜 := ℂ) (A x) y = inner (𝕜 := ℂ) x (A y))
    (hNN : ∀ x, 0 ≤ (inner (𝕜 := ℂ) x (A x)).re)
    (hLe : ∀ x, (inner (𝕜 := ℂ) x (A x)).re ≤ c * (inner (𝕜 := ℂ) x x).re) :
    0 ≤ f.muPosBounded A c hc hSA hNN hLe :=
  f.muScaled_nonneg _

/-- **Scale compatibility**: for `r ≥ 0`, `muPosBounded (r·A) = r · muPosBounded A`. -/
theorem muPosBounded_scale (f : GenFrameFunction H) (A : H →L[ℂ] H) (c : ℝ) (hc : 0 < c)
    (hSA : ∀ x y : H, inner (𝕜 := ℂ) (A x) y = inner (𝕜 := ℂ) x (A y))
    (hNN : ∀ x, 0 ≤ (inner (𝕜 := ℂ) x (A x)).re)
    (hLe : ∀ x, (inner (𝕜 := ℂ) x (A x)).re ≤ c * (inner (𝕜 := ℂ) x x).re)
    {r : ℝ} (hr : 0 < r)
    (hSA' : ∀ x y : H, inner (𝕜 := ℂ) ((r : ℂ) • A $ x) y
                      = inner (𝕜 := ℂ) x ((r : ℂ) • A $ y))
    (hNN' : ∀ x, 0 ≤ (inner (𝕜 := ℂ) x (((r : ℂ) • A) x)).re)
    (hLe' : ∀ x, (inner (𝕜 := ℂ) x (((r : ℂ) • A) x)).re ≤ (r * c) * (inner (𝕜 := ℂ) x x).re) :
    f.muPosBounded ((r : ℂ) • A) (r * c) (mul_pos hr hc) hSA' hNN' hLe'
      = r * f.muPosBounded A c hc hSA hNN hLe := by
  unfold muPosBounded muScaled
  show (r * c) * f.μ (Effect.ofPosBounded ((r : ℂ) • A) (r * c) (mul_pos hr hc) hSA' hNN' hLe')
      = r * (c * f.μ (Effect.ofPosBounded A c hc hSA hNN hLe))
  have h_eff_eq :
      Effect.ofPosBounded ((r : ℂ) • A) (r * c) (mul_pos hr hc) hSA' hNN' hLe'
        = Effect.ofPosBounded A c hc hSA hNN hLe := by
    apply Effect.ext_op
    show (((r * c)⁻¹ : ℝ) : ℂ) • ((r : ℂ) • A) = ((c⁻¹ : ℝ) : ℂ) • A
    rw [smul_smul]
    have : ((((r * c)⁻¹ : ℝ)) : ℂ) * (r : ℂ) = ((c⁻¹ : ℝ) : ℂ) := by
      have hr_ne : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
      have hc_ne : (c : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hc)
      push_cast
      field_simp
    rw [this]
  rw [h_eff_eq]
  ring

end GenFrameFunction

end Busch
