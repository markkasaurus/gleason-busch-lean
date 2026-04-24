/-
# Busch/SAExtension.lean — Extension to Self-Adjoint Operators
Given a self-adjoint operator `A` with a two-sided bound `|A| ≤ c` (i.e.,
`-c·I ≤ A ≤ c·I`), we extend `μ` via the **shift trick**:
  `muSA f A c := muPosBounded f (A + c·I) (2c) - c`
since `A + c·I ≥ 0` with `A + c·I ≤ 2c·I`, and `muPosBounded(c·I, c) = c`.
This is well-defined (independent of `c`): any larger bound `c' > c` gives the
same result, because shifting by `(c' - c)·I` adds the same quantity to both
`muPosBounded(A + c'·I)` and the subtracted `c'` (by additivity on positive
sums + the identity `muPosBounded(r·I) = r`).
**Mathematical content**: This delivers the **ℝ-linear extension of `μ` from
effects to all of `SA(H)`** with a given two-sided bound — the key step for
the forward direction of Gleason's theorem (before Riesz representation).
-/
import Busch.PositiveAdditivity

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [instCompleteSpace : CompleteSpace H]

namespace GenFrameFunction

/-! ### `muPosBounded` of the identity scaled by `c` -/
omit instCompleteSpace in
/-- The operator `c · 1` (scaled identity) is self-adjoint. -/
lemma idScaled_isSelfAdjoint (c : ℝ) :
    ∀ x y : H, inner (𝕜 := ℂ) (((c : ℂ) • ContinuousLinearMap.id ℂ H) x) y
              = inner (𝕜 := ℂ) x (((c : ℂ) • ContinuousLinearMap.id ℂ H) y) := by
  intro x y
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal]

omit instCompleteSpace in
/-- The operator `c · 1` (scaled identity, `c ≥ 0`) has nonneg self-inner. -/
lemma idScaled_nonneg {c : ℝ} (hc : 0 ≤ c) (x : H) :
    0 ≤ (inner (𝕜 := ℂ) x (((c : ℂ) • ContinuousLinearMap.id ℂ H) x)).re := by
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  exact mul_nonneg hc (@inner_self_nonneg ℂ H _ _ _ x)

omit instCompleteSpace in
/-- The operator `c · 1` satisfies `⟨x, c·I·x⟩.re ≤ c · ⟨x, x⟩.re`. -/
lemma idScaled_le_bound {c : ℝ} (_hc : 0 ≤ c) (x : H) :
    (inner (𝕜 := ℂ) x (((c : ℂ) • ContinuousLinearMap.id ℂ H) x)).re
      ≤ c * (inner (𝕜 := ℂ) x x).re := by
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  exact le_refl _

/-- **Value on scaled identity**: `muPosBounded(c·I, c) = c` for `c > 0`. -/
theorem muPosBounded_idScaled (f : GenFrameFunction H) {c : ℝ} (hc : 0 < c) :
    f.muPosBounded ((c : ℂ) • ContinuousLinearMap.id ℂ H) c hc
        (idScaled_isSelfAdjoint c) (idScaled_nonneg hc.le) (idScaled_le_bound hc.le)
      = c := by
  show c * f.μ (Effect.ofPosBounded ((c : ℂ) • ContinuousLinearMap.id ℂ H) c hc
      (idScaled_isSelfAdjoint c) (idScaled_nonneg hc.le) (idScaled_le_bound hc.le)) = c
  have h_eff_eq :
      Effect.ofPosBounded ((c : ℂ) • ContinuousLinearMap.id ℂ H) c hc
          (idScaled_isSelfAdjoint c) (idScaled_nonneg hc.le) (idScaled_le_bound hc.le)
        = (1 : Effect H) := by
    apply Effect.ext_op
    show ((c⁻¹ : ℝ) : ℂ) • ((c : ℂ) • ContinuousLinearMap.id ℂ H) = ContinuousLinearMap.id ℂ H
    rw [smul_smul]
    have : ((c⁻¹ : ℝ) : ℂ) * (c : ℂ) = 1 := by
      have hc_ne : (c : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hc
      push_cast
      field_simp
    rw [this, one_smul]
  rw [h_eff_eq, f.normalized]
  ring

/-! ### Two-sided bounds and the shift trick -/
/-- Predicate: `A` is a self-adjoint operator with two-sided bound `|A| ≤ c`.
That is: `A` is self-adjoint, and `-c · ⟨x, x⟩.re ≤ ⟨x, A x⟩.re ≤ c · ⟨x, x⟩.re`
for all `x`. Equivalently, `-c·I ≤ A ≤ c·I` in Löwner order. -/
structure SABounded (A : H →L[ℂ] H) (c : ℝ) : Prop where
  isSelfAdjoint : ∀ x y : H, inner (𝕜 := ℂ) (A x) y = inner (𝕜 := ℂ) x (A y)
  lower : ∀ x, -(c * (inner (𝕜 := ℂ) x x).re) ≤ (inner (𝕜 := ℂ) x (A x)).re
  upper : ∀ x, (inner (𝕜 := ℂ) x (A x)).re ≤ c * (inner (𝕜 := ℂ) x x).re
  pos : 0 < c

omit instCompleteSpace in
/-- For `A ∈ SABounded c`, the shifted operator `A + c·I` is positive-bounded
with bound `2c`. -/
lemma SABounded.shifted_posBounded {A : H →L[ℂ] H} {c : ℝ}
    (h : SABounded A c) :
    (∀ x y : H, inner (𝕜 := ℂ) ((A + (c : ℂ) • ContinuousLinearMap.id ℂ H) x) y
              = inner (𝕜 := ℂ) x ((A + (c : ℂ) • ContinuousLinearMap.id ℂ H) y)) ∧
    (∀ x, 0 ≤ (inner (𝕜 := ℂ) x ((A + (c : ℂ) • ContinuousLinearMap.id ℂ H) x)).re) ∧
    (∀ x, (inner (𝕜 := ℂ) x ((A + (c : ℂ) • ContinuousLinearMap.id ℂ H) x)).re
          ≤ (2 * c) * (inner (𝕜 := ℂ) x x).re) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
    rw [h.isSelfAdjoint x y]
    rw [show inner (𝕜 := ℂ) (((c : ℂ) • ContinuousLinearMap.id ℂ H) x) y
        = inner (𝕜 := ℂ) x (((c : ℂ) • ContinuousLinearMap.id ℂ H) y) from
      idScaled_isSelfAdjoint c x y]
  · intro x
    simp only [ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
    have h_lower := h.lower x
    have h_id := idScaled_nonneg h.pos.le x
    have h_self_nn : 0 ≤ (inner (𝕜 := ℂ) x x).re := @inner_self_nonneg ℂ H _ _ _ x
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    linarith
  · intro x
    simp only [ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
    have h_upper := h.upper x
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    linarith

/-- **`muSA`**: the extension of `μ` to self-adjoint operators via the
shift trick. For `A ∈ SABounded c`, value `muPosBounded(A + c·I, 2c) - c`. -/
def muSA (f : GenFrameFunction H) {A : H →L[ℂ] H} {c : ℝ} (h : SABounded A c) : ℝ :=
  f.muPosBounded (A + (c : ℂ) • ContinuousLinearMap.id ℂ H) (2 * c)
    (by linarith [h.pos]) h.shifted_posBounded.1 h.shifted_posBounded.2.1
    h.shifted_posBounded.2.2 - c

omit instCompleteSpace in
/-- The zero operator is `SABounded c` for any `c > 0`. -/
lemma zero_SABounded {c : ℝ} (hc : 0 < c) : SABounded (0 : H →L[ℂ] H) c where
  isSelfAdjoint := fun x y => by simp
  lower := fun x => by
    show -(c * (inner (𝕜 := ℂ) x x).re) ≤ (inner (𝕜 := ℂ) x ((0 : H →L[ℂ] H) x)).re
    simp only [ContinuousLinearMap.zero_apply, inner_zero_right, Complex.zero_re]
    have : 0 ≤ c * (inner (𝕜 := ℂ) x x).re :=
      mul_nonneg hc.le (@inner_self_nonneg ℂ H _ _ _ x)
    linarith
  upper := fun x => by
    show (inner (𝕜 := ℂ) x ((0 : H →L[ℂ] H) x)).re ≤ c * (inner (𝕜 := ℂ) x x).re
    simp only [ContinuousLinearMap.zero_apply, inner_zero_right, Complex.zero_re]
    exact mul_nonneg hc.le (@inner_self_nonneg ℂ H _ _ _ x)
  pos := hc

/-- **Value on `0`**: `muSA(0) = 0`. -/
theorem muSA_zero (f : GenFrameFunction H) {c : ℝ} (hc : 0 < c) :
    f.muSA (zero_SABounded hc) = 0 := by
  unfold muSA
  have h_add : (0 : H →L[ℂ] H) + (c : ℂ) • ContinuousLinearMap.id ℂ H
      = (c : ℂ) • ContinuousLinearMap.id ℂ H := by
    rw [zero_add]
  have h_bridge :
      f.muPosBounded ((0 : H →L[ℂ] H) + (c : ℂ) • ContinuousLinearMap.id ℂ H)
        (2 * c) (by linarith) ((zero_SABounded hc).shifted_posBounded).1
        ((zero_SABounded hc).shifted_posBounded).2.1
        ((zero_SABounded hc).shifted_posBounded).2.2
        = f.muPosBounded ((c : ℂ) • ContinuousLinearMap.id ℂ H) c hc
          (idScaled_isSelfAdjoint c) (idScaled_nonneg hc.le) (idScaled_le_bound hc.le) := by
    rw [muPosBounded_eq_muScaled, muPosBounded_eq_muScaled]
    apply muScaled_well_defined
    rw [SclEffect.ofPosBounded_op, SclEffect.ofPosBounded_op]
    rw [h_add]
  rw [h_bridge, muPosBounded_idScaled]
  ring

/-- Every effect is `SABounded c` for any `c ≥ 1`. -/
lemma effect_SABounded (E : Effect H) {c : ℝ} (hc : 0 < c) (hcBound : 1 ≤ c) :
    SABounded E.op c where
  isSelfAdjoint := E.isSelfAdjoint
  lower := fun x => by
    have h_nn := E.nonneg x
    have h_self_nn : 0 ≤ (inner (𝕜 := ℂ) x x).re := @inner_self_nonneg ℂ H _ _ _ x
    have : 0 ≤ c * (inner (𝕜 := ℂ) x x).re := mul_nonneg hc.le h_self_nn
    linarith
  upper := fun x => by
    have h_le := E.le_one x
    have h_self_nn : 0 ≤ (inner (𝕜 := ℂ) x x).re := @inner_self_nonneg ℂ H _ _ _ x
    have : (inner (𝕜 := ℂ) x x).re ≤ c * (inner (𝕜 := ℂ) x x).re := by
      calc (inner (𝕜 := ℂ) x x).re = 1 * (inner (𝕜 := ℂ) x x).re := by ring
        _ ≤ c * (inner (𝕜 := ℂ) x x).re :=
            mul_le_mul_of_nonneg_right hcBound h_self_nn
    linarith
  pos := hc

/-- **Effect values pass through**: if `E` is an effect with `c` any valid bound,
`muSA(E) = μ(E)`. (Where we view `E` as an `SA`-bounded operator shifted.) -/
theorem muSA_effect (f : GenFrameFunction H) (E : Effect H) {c : ℝ} (hc : 0 < c)
    (hcBound : 1 ≤ c) :
    f.muSA (effect_SABounded E hc hcBound) = f.μ E := by
  unfold muSA
  have h_E_bound_one : ∀ x, (inner (𝕜 := ℂ) x (E.op x)).re ≤ 1 * (inner (𝕜 := ℂ) x x).re := by
    intro x; linarith [E.le_one x]
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have h_mu_E : f.muPosBounded E.op 1 one_pos E.isSelfAdjoint E.nonneg h_E_bound_one = f.μ E := by
    show (1 : ℝ) * f.μ (Effect.ofPosBounded E.op 1 one_pos
        E.isSelfAdjoint E.nonneg h_E_bound_one) = f.μ E
    have : Effect.ofPosBounded E.op 1 one_pos E.isSelfAdjoint E.nonneg h_E_bound_one = E := by
      apply Effect.ext_op
      show ((1⁻¹ : ℝ) : ℂ) • E.op = E.op
      simp
    rw [this]
    ring
  have h_mu_cI : f.muPosBounded ((c : ℂ) • ContinuousLinearMap.id ℂ H) c hc
      (idScaled_isSelfAdjoint c) (idScaled_nonneg hc.le) (idScaled_le_bound hc.le) = c :=
    muPosBounded_idScaled f hc
  have hSum_pos : (0 : ℝ) < 1 + c := by linarith
  have h_sum_bound : ∀ x, (inner (𝕜 := ℂ) x ((E.op + (c : ℂ) • ContinuousLinearMap.id ℂ H) x)).re
      ≤ (1 + c) * (inner (𝕜 := ℂ) x x).re := by
    intro x
    simp only [ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
    have h1 := h_E_bound_one x
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, one_mul] at h1 ⊢
    linarith
  have h_sum_sa : ∀ x y, inner (𝕜 := ℂ) ((E.op + (c : ℂ) • ContinuousLinearMap.id ℂ H) x) y
      = inner (𝕜 := ℂ) x ((E.op + (c : ℂ) • ContinuousLinearMap.id ℂ H) y) := by
    intro x y
    simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
    rw [E.isSelfAdjoint x y, idScaled_isSelfAdjoint c x y]
  have h_sum_nn : ∀ x, 0 ≤ (inner (𝕜 := ℂ) x ((E.op + (c : ℂ) • ContinuousLinearMap.id ℂ H) x)).re := by
    intro x
    simp only [ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
    linarith [E.nonneg x, idScaled_nonneg hc.le x]
  have h_2c_pos : (0 : ℝ) < 2 * c := by linarith
  have h_sum_bound_2c : ∀ x,
      (inner (𝕜 := ℂ) x ((E.op + (c : ℂ) • ContinuousLinearMap.id ℂ H) x)).re
      ≤ (2 * c) * (inner (𝕜 := ℂ) x x).re := by
    intro x
    have h1 := h_sum_bound x
    have h_self_nn : 0 ≤ (inner (𝕜 := ℂ) x x).re := @inner_self_nonneg ℂ H _ _ _ x
    have : (1 + c) * (inner (𝕜 := ℂ) x x).re ≤ (2 * c) * (inner (𝕜 := ℂ) x x).re := by
      have : 1 + c ≤ 2 * c := by linarith
      exact mul_le_mul_of_nonneg_right this h_self_nn
    linarith
  have h_bound_indep :
    f.muPosBounded (E.op + (c : ℂ) • ContinuousLinearMap.id ℂ H) (2 * c)
      h_2c_pos h_sum_sa h_sum_nn h_sum_bound_2c
      = f.muPosBounded (E.op + (c : ℂ) • ContinuousLinearMap.id ℂ H) (1 + c)
          hSum_pos h_sum_sa h_sum_nn h_sum_bound :=
    muPosBounded_bound_independent f _ (2 * c) (1 + c) h_2c_pos hSum_pos
      h_sum_sa h_sum_nn h_sum_bound_2c h_sum_bound
  rw [h_bound_indep]
  have h_add_eq :=
    muPosBounded_add f one_pos hc E.isSelfAdjoint (idScaled_isSelfAdjoint c)
      E.nonneg (idScaled_nonneg hc.le) h_E_bound_one (idScaled_le_bound hc.le)
      h_sum_sa h_sum_nn h_sum_bound
  rw [h_add_eq, h_mu_E, h_mu_cI]
  ring

end GenFrameFunction

end Busch
