/-
# Busch/SALinearity.lean — ℝ-Linearity of `muSA`
Building on `Busch/SAExtension.lean`, we prove that `muSA` is **ℝ-linear** on
self-adjoint operators. Specifically:
* `muSA(A + B) = muSA(A) + muSA(B)` (additivity)
* `muSA(r · A) = r · muSA(A)` (scalar compatibility, for `r ∈ ℝ`)
Combined with the pass-through for effects (`muSA_effect`) from `SAExtension.lean`,
this is **the ℝ-linear extension of `μ`** from the effect set to the real vector
space of self-adjoint operators.
This supplies the linear functional used by the **Riesz representation theorem**:
a ℝ-linear functional on the finite-dim real Hilbert space `(SA(H), ⟨·,·⟩_HS)`
is represented by a unique operator `ρ ∈ SA(H)`.
-/
import Busch.SAExtension

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [instCompleteSpace : CompleteSpace H]

namespace GenFrameFunction

/-! ### Additivity on same-bound SA operators -/
omit instCompleteSpace in
/-- Sum of two `SABounded c` operators is `SABounded (2c)`. -/
lemma SABounded.add {A B : H →L[ℂ] H} {c : ℝ}
    (hA : SABounded A c) (hB : SABounded B c) : SABounded (A + B) (2 * c) where
  isSelfAdjoint := fun x y => by
    simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
    rw [hA.isSelfAdjoint x y, hB.isSelfAdjoint x y]
  lower := fun x => by
    simp only [ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
    have ha := hA.lower x
    have hb := hB.lower x
    linarith
  upper := fun x => by
    simp only [ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
    have ha := hA.upper x
    have hb := hB.upper x
    linarith
  pos := by linarith [hA.pos]

/-- **Additivity of `muSA`** on same-bound SA operators. -/
theorem muSA_add (f : GenFrameFunction H) {A B : H →L[ℂ] H} {c : ℝ}
    (hA : SABounded A c) (hB : SABounded B c) :
    f.muSA (hA.add hB) = f.muSA hA + f.muSA hB := by
  unfold muSA
  have hA_shift := hA.shifted_posBounded
  have hB_shift := hB.shifted_posBounded
  have hAB_shift := (hA.add hB).shifted_posBounded
  have h_2c_pos : (0 : ℝ) < 2 * c := by linarith [hA.pos]
  have h_op_eq : (A + B) + ((2 * c : ℝ) : ℂ) • ContinuousLinearMap.id ℂ H
      = (A + (c : ℂ) • ContinuousLinearMap.id ℂ H)
        + (B + (c : ℂ) • ContinuousLinearMap.id ℂ H) := by
    ext z
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply]
    push_cast
    module
  obtain ⟨h_sum_sa, h_sum_nn, h_sum_bound⟩ :=
    posBounded_add h_2c_pos h_2c_pos hA_shift.1 hB_shift.1
      hA_shift.2.1 hB_shift.2.1 hA_shift.2.2 hB_shift.2.2
  have h_add_eq :=
    muPosBounded_add f h_2c_pos h_2c_pos
      hA_shift.1 hB_shift.1 hA_shift.2.1 hB_shift.2.1 hA_shift.2.2 hB_shift.2.2
      h_sum_sa h_sum_nn h_sum_bound
  have h4c_pos : (0 : ℝ) < 2 * (2 * c) := by linarith [hA.pos]
  have h_bridge : f.muPosBounded ((A + B) +
      (((2 * c : ℝ)) : ℂ) • ContinuousLinearMap.id ℂ H) (2 * (2 * c))
      h4c_pos hAB_shift.1 hAB_shift.2.1 hAB_shift.2.2
      = f.muPosBounded ((A + (c : ℂ) • ContinuousLinearMap.id ℂ H)
        + (B + (c : ℂ) • ContinuousLinearMap.id ℂ H)) (2 * c + 2 * c)
        (by linarith [hA.pos]) h_sum_sa h_sum_nn h_sum_bound := by
    rw [muPosBounded_eq_muScaled, muPosBounded_eq_muScaled]
    apply muScaled_well_defined
    rw [SclEffect.ofPosBounded_op, SclEffect.ofPosBounded_op]
    exact h_op_eq
  rw [h_bridge, h_add_eq]
  ring

/-! ### Negation -/
omit instCompleteSpace in
/-- `-A` is `SABounded c` when `A` is. -/
lemma SABounded.neg {A : H →L[ℂ] H} {c : ℝ} (h : SABounded A c) :
    SABounded (-A) c where
  isSelfAdjoint := fun x y => by
    simp only [ContinuousLinearMap.neg_apply, inner_neg_left, inner_neg_right]
    rw [h.isSelfAdjoint x y]
  lower := fun x => by
    simp only [ContinuousLinearMap.neg_apply, inner_neg_right, Complex.neg_re]
    linarith [h.upper x]
  upper := fun x => by
    simp only [ContinuousLinearMap.neg_apply, inner_neg_right, Complex.neg_re]
    linarith [h.lower x]
  pos := h.pos

/-- **Negation of `muSA`**: `muSA(-A) = -muSA(A)`. -/
theorem muSA_neg (f : GenFrameFunction H) {A : H →L[ℂ] H} {c : ℝ} (h : SABounded A c) :
    f.muSA h.neg = -f.muSA h := by
  have h_pos := h.pos
  have h_2c_pos : (0 : ℝ) < 2 * c := by linarith
  have h_neg_shift := h.neg.shifted_posBounded
  have h_shift := h.shifted_posBounded
  have h_op_eq : (-A + (c : ℂ) • ContinuousLinearMap.id ℂ H)
        + (A + (c : ℂ) • ContinuousLinearMap.id ℂ H)
      = ((2 * c : ℝ) : ℂ) • ContinuousLinearMap.id ℂ H := by
    ext z
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    push_cast
    module
  obtain ⟨h_sum_sa, h_sum_nn, h_sum_bound⟩ :=
    posBounded_add h_2c_pos h_2c_pos h_neg_shift.1 h_shift.1
      h_neg_shift.2.1 h_shift.2.1 h_neg_shift.2.2 h_shift.2.2
  have h_add_eq :=
    muPosBounded_add f h_2c_pos h_2c_pos
      h_neg_shift.1 h_shift.1 h_neg_shift.2.1 h_shift.2.1
      h_neg_shift.2.2 h_shift.2.2 h_sum_sa h_sum_nn h_sum_bound
  have h_sum_as_scaled_id :
    f.muPosBounded ((-A + (c : ℂ) • ContinuousLinearMap.id ℂ H)
      + (A + (c : ℂ) • ContinuousLinearMap.id ℂ H)) (2 * c + 2 * c)
      (by linarith) h_sum_sa h_sum_nn h_sum_bound
    = 2 * c := by
    have h_bridge :
      f.muPosBounded ((-A + (c : ℂ) • ContinuousLinearMap.id ℂ H)
        + (A + (c : ℂ) • ContinuousLinearMap.id ℂ H)) (2 * c + 2 * c)
        (by linarith) h_sum_sa h_sum_nn h_sum_bound
      = f.muPosBounded ((((2 * c : ℝ)) : ℂ) • ContinuousLinearMap.id ℂ H) (2 * c + 2 * c)
        (by linarith) (idScaled_isSelfAdjoint (2 * c))
        (idScaled_nonneg (show (0:ℝ) ≤ 2*c by linarith))
        (fun x => by
          have h1 : (inner (𝕜 := ℂ) x ((((2 * c : ℝ)) : ℂ) • ContinuousLinearMap.id ℂ H $ x)).re
                  ≤ (2 * c) * (inner (𝕜 := ℂ) x x).re :=
            idScaled_le_bound (show (0:ℝ) ≤ 2*c by linarith) x
          have h2 : (2 * c) * (inner (𝕜 := ℂ) x x).re ≤ (2 * c + 2 * c) * (inner (𝕜 := ℂ) x x).re := by
            have : 2 * c ≤ 2 * c + 2 * c := by linarith
            exact mul_le_mul_of_nonneg_right this (@inner_self_nonneg ℂ H _ _ _ x)
          linarith)
      := by
      rw [muPosBounded_eq_muScaled, muPosBounded_eq_muScaled]
      apply muScaled_well_defined
      rw [SclEffect.ofPosBounded_op, SclEffect.ofPosBounded_op]
      exact h_op_eq
    rw [h_bridge]
    have h_2c_nn : (0 : ℝ) ≤ 2 * c := h_2c_pos.le
    have h_bound_2c_le : ∀ x,
        (inner (𝕜 := ℂ) x ((((2 * c : ℝ)) : ℂ) • ContinuousLinearMap.id ℂ H $ x)).re
        ≤ (2 * c + 2 * c) * (inner (𝕜 := ℂ) x x).re := fun x => by
      have h1 := idScaled_le_bound h_2c_nn x
      have h2 : (2 * c) * (inner (𝕜 := ℂ) x x).re ≤ (2 * c + 2 * c) * (inner (𝕜 := ℂ) x x).re := by
        have : 2 * c ≤ 2 * c + 2 * c := by linarith
        exact mul_le_mul_of_nonneg_right this (@inner_self_nonneg ℂ H _ _ _ x)
      linarith
    have h_bound_indep :
      f.muPosBounded ((((2 * c : ℝ)) : ℂ) • ContinuousLinearMap.id ℂ H) (2 * c + 2 * c)
        (by linarith) (idScaled_isSelfAdjoint (2 * c))
        (idScaled_nonneg h_2c_nn) h_bound_2c_le
      = f.muPosBounded ((((2 * c : ℝ)) : ℂ) • ContinuousLinearMap.id ℂ H) (2 * c)
        h_2c_pos (idScaled_isSelfAdjoint (2 * c))
        (idScaled_nonneg h_2c_nn) (idScaled_le_bound h_2c_nn) :=
      muPosBounded_bound_independent f _ _ _ _ _ _ _ _ _
    rw [h_bound_indep]
    exact muPosBounded_idScaled f h_2c_pos
  unfold muSA
  rw [h_add_eq] at h_sum_as_scaled_id
  linarith

/-! ### Zero operator and nonneg-scalar compatibility -/
omit instCompleteSpace in
/-- **Scalar multiplication by a non-neg real**. For `r ≥ 0`, `r·A` is
`SABounded (r*c)` and `muSA(r·A) = r · muSA(A)` (plus normalization by
muScaled_well_defined). -/
lemma SABounded.smul_nn {A : H →L[ℂ] H} {c : ℝ}
    (h : SABounded A c) {r : ℝ} (hr : 0 < r) :
    SABounded ((r : ℂ) • A) (r * c) where
  isSelfAdjoint := fun x y => by
    simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal]
    rw [h.isSelfAdjoint x y]
  lower := fun x => by
    simp only [ContinuousLinearMap.smul_apply, inner_smul_right, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have h_lower := h.lower x
    nlinarith
  upper := fun x => by
    simp only [ContinuousLinearMap.smul_apply, inner_smul_right, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have h_upper := h.upper x
    nlinarith
  pos := mul_pos hr h.pos

omit instCompleteSpace in
/-- `SABounded` is compatible with any-sign scalar multiplication: if `r = 0`, `r·A = 0`. -/
lemma SABounded.smul_zero {A : H →L[ℂ] H} {c : ℝ} (h : SABounded A c) :
    SABounded ((0 : ℂ) • A) c where
  isSelfAdjoint := fun x y => by simp
  lower := fun x => by
    simp only [zero_smul, ContinuousLinearMap.zero_apply, inner_zero_right, Complex.zero_re]
    have : 0 ≤ c * (inner (𝕜 := ℂ) x x).re :=
      mul_nonneg h.pos.le (@inner_self_nonneg ℂ H _ _ _ x)
    linarith
  upper := fun x => by
    simp only [zero_smul, ContinuousLinearMap.zero_apply, inner_zero_right, Complex.zero_re]
    exact mul_nonneg h.pos.le (@inner_self_nonneg ℂ H _ _ _ x)
  pos := h.pos

/-- **Positive scalar compatibility**: `muSA(r·A) = r · muSA(A)` for `r > 0`. -/
theorem muSA_smul_nn (f : GenFrameFunction H) {A : H →L[ℂ] H} {c : ℝ}
    (h : SABounded A c) {r : ℝ} (hr : 0 < r) :
    f.muSA (h.smul_nn hr) = r * f.muSA h := by
  unfold muSA
  have h_shift := h.shifted_posBounded
  have h_smul_shift := (h.smul_nn hr).shifted_posBounded
  have h_c_pos := h.pos
  have h_2c_pos : (0 : ℝ) < 2 * c := by linarith
  have h_op_eq : ((r : ℂ) • A) + ((r * c : ℝ) : ℂ) • ContinuousLinearMap.id ℂ H
      = (r : ℂ) • (A + (c : ℂ) • ContinuousLinearMap.id ℂ H) := by
    ext z
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply]
    push_cast
    module
  have h_bound_eq : 2 * (r * c) = r * (2 * c) := by ring
  have h_lhs_eq :
    f.muPosBounded (((r : ℂ) • A) + ((r * c : ℝ) : ℂ) • ContinuousLinearMap.id ℂ H)
      (2 * (r * c)) (by linarith [mul_pos hr h_c_pos])
      h_smul_shift.1 h_smul_shift.2.1 h_smul_shift.2.2
    = f.muPosBounded ((r : ℂ) • (A + (c : ℂ) • ContinuousLinearMap.id ℂ H))
      (2 * (r * c)) (by linarith [mul_pos hr h_c_pos])
      (by
        intro x y
        rw [show (r : ℂ) • (A + (c : ℂ) • ContinuousLinearMap.id ℂ H)
            = ((r : ℂ) • A) + ((r * c : ℝ) : ℂ) • ContinuousLinearMap.id ℂ H from h_op_eq.symm]
        exact h_smul_shift.1 x y)
      (by
        intro x
        rw [show (r : ℂ) • (A + (c : ℂ) • ContinuousLinearMap.id ℂ H)
            = ((r : ℂ) • A) + ((r * c : ℝ) : ℂ) • ContinuousLinearMap.id ℂ H from h_op_eq.symm]
        exact h_smul_shift.2.1 x)
      (by
        intro x
        rw [show (r : ℂ) • (A + (c : ℂ) • ContinuousLinearMap.id ℂ H)
            = ((r : ℂ) • A) + ((r * c : ℝ) : ℂ) • ContinuousLinearMap.id ℂ H from h_op_eq.symm]
        exact h_smul_shift.2.2 x) := by
    rw [muPosBounded_eq_muScaled, muPosBounded_eq_muScaled]
    apply muScaled_well_defined
    rw [SclEffect.ofPosBounded_op, SclEffect.ofPosBounded_op]
    exact h_op_eq
  rw [h_lhs_eq]
  have h_smul_shift' : (∀ x y : H,
      inner (𝕜 := ℂ) (((r : ℂ) • (A + (c : ℂ) • ContinuousLinearMap.id ℂ H)) x) y
      = inner (𝕜 := ℂ) x (((r : ℂ) • (A + (c : ℂ) • ContinuousLinearMap.id ℂ H)) y)) ∧
    (∀ x, 0 ≤ (inner (𝕜 := ℂ) x
      (((r : ℂ) • (A + (c : ℂ) • ContinuousLinearMap.id ℂ H)) x)).re) ∧
    (∀ x, (inner (𝕜 := ℂ) x
      (((r : ℂ) • (A + (c : ℂ) • ContinuousLinearMap.id ℂ H)) x)).re
      ≤ (r * (2 * c)) * (inner (𝕜 := ℂ) x x).re) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y
      rw [show (r : ℂ) • (A + (c : ℂ) • ContinuousLinearMap.id ℂ H)
          = ((r : ℂ) • A) + ((r * c : ℝ) : ℂ) • ContinuousLinearMap.id ℂ H from h_op_eq.symm]
      exact h_smul_shift.1 x y
    · intro x
      rw [show (r : ℂ) • (A + (c : ℂ) • ContinuousLinearMap.id ℂ H)
          = ((r : ℂ) • A) + ((r * c : ℝ) : ℂ) • ContinuousLinearMap.id ℂ H from h_op_eq.symm]
      exact h_smul_shift.2.1 x
    · intro x
      rw [show (r : ℂ) • (A + (c : ℂ) • ContinuousLinearMap.id ℂ H)
          = ((r : ℂ) • A) + ((r * c : ℝ) : ℂ) • ContinuousLinearMap.id ℂ H from h_op_eq.symm]
      have := h_smul_shift.2.2 x
      rw [show r * (2 * c) = 2 * (r * c) by ring]
      exact this
  have h_bound_indep :
    f.muPosBounded ((r : ℂ) • (A + (c : ℂ) • ContinuousLinearMap.id ℂ H))
      (2 * (r * c))
      (by linarith [mul_pos hr h_c_pos])
      (fun x y => by
        rw [show (r : ℂ) • (A + (c : ℂ) • ContinuousLinearMap.id ℂ H)
            = ((r : ℂ) • A) + ((r * c : ℝ) : ℂ) • ContinuousLinearMap.id ℂ H from h_op_eq.symm]
        exact h_smul_shift.1 x y)
      (fun x => by
        rw [show (r : ℂ) • (A + (c : ℂ) • ContinuousLinearMap.id ℂ H)
            = ((r : ℂ) • A) + ((r * c : ℝ) : ℂ) • ContinuousLinearMap.id ℂ H from h_op_eq.symm]
        exact h_smul_shift.2.1 x)
      (fun x => by
        rw [show (r : ℂ) • (A + (c : ℂ) • ContinuousLinearMap.id ℂ H)
            = ((r : ℂ) • A) + ((r * c : ℝ) : ℂ) • ContinuousLinearMap.id ℂ H from h_op_eq.symm]
        exact h_smul_shift.2.2 x)
    = f.muPosBounded ((r : ℂ) • (A + (c : ℂ) • ContinuousLinearMap.id ℂ H))
      (r * (2 * c))
      (by positivity)
      h_smul_shift'.1 h_smul_shift'.2.1 h_smul_shift'.2.2 :=
    muPosBounded_bound_independent f _ _ _ _ _ _ _ _ _
  rw [h_bound_indep]
  have h_scale_eq :=
    muPosBounded_scale f (A + (c : ℂ) • ContinuousLinearMap.id ℂ H) (2 * c) h_2c_pos
      h_shift.1 h_shift.2.1 h_shift.2.2 hr
      h_smul_shift'.1 h_smul_shift'.2.1 h_smul_shift'.2.2
  rw [h_scale_eq]
  ring

/-- **Bound independence**: `muSA A` is the same regardless of which valid bound is used. -/
private theorem muSA_bound_independent_aux (f : GenFrameFunction H) {A : H →L[ℂ] H} {c₁ c₂ : ℝ}
    (h₁ : SABounded A c₁) (h₂ : SABounded A c₂) (hle : c₁ ≤ c₂) :
    f.muSA h₁ = f.muSA h₂ := by
  unfold muSA
  rcases eq_or_lt_of_le hle with heq | hlt
  · subst heq
    rfl
  · have h_delta_pos : (0 : ℝ) < c₂ - c₁ := by linarith
    have h_shift₁ := h₁.shifted_posBounded
    have h_shift₂ := h₂.shifted_posBounded
    have h_c1_pos : (0 : ℝ) < c₁ := h₁.pos
    have h_c2_pos : (0 : ℝ) < c₂ := h₂.pos
    have h_op_eq : A + (c₂ : ℂ) • ContinuousLinearMap.id ℂ H
        = (A + (c₁ : ℂ) • ContinuousLinearMap.id ℂ H)
          + (((c₂ - c₁ : ℝ)) : ℂ) • ContinuousLinearMap.id ℂ H := by
      ext z
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply]
      push_cast
      module
    have h_2c1_pos : (0 : ℝ) < 2 * c₁ := by linarith
    have h_2c2_pos : (0 : ℝ) < 2 * c₂ := by linarith
    obtain ⟨h_sum_sa, h_sum_nn, h_sum_bound⟩ :=
      posBounded_add h_2c1_pos h_delta_pos
        h_shift₁.1 (idScaled_isSelfAdjoint (c₂ - c₁))
        h_shift₁.2.1 (idScaled_nonneg h_delta_pos.le)
        h_shift₁.2.2 (idScaled_le_bound h_delta_pos.le)
    have h_add_eq :=
      muPosBounded_add f h_2c1_pos h_delta_pos
        h_shift₁.1 (idScaled_isSelfAdjoint (c₂ - c₁))
        h_shift₁.2.1 (idScaled_nonneg h_delta_pos.le)
        h_shift₁.2.2 (idScaled_le_bound h_delta_pos.le)
        h_sum_sa h_sum_nn h_sum_bound
    have h_bridge :
      f.muPosBounded (A + (c₂ : ℂ) • ContinuousLinearMap.id ℂ H) (2 * c₂)
        h_2c2_pos h_shift₂.1 h_shift₂.2.1 h_shift₂.2.2
      = f.muPosBounded ((A + (c₁ : ℂ) • ContinuousLinearMap.id ℂ H)
          + (((c₂ - c₁ : ℝ)) : ℂ) • ContinuousLinearMap.id ℂ H)
        (2 * c₁ + (c₂ - c₁)) (by linarith)
        h_sum_sa h_sum_nn h_sum_bound := by
      rw [muPosBounded_eq_muScaled, muPosBounded_eq_muScaled]
      apply muScaled_well_defined
      rw [SclEffect.ofPosBounded_op, SclEffect.ofPosBounded_op]
      exact h_op_eq
    rw [h_bridge, h_add_eq]
    rw [muPosBounded_idScaled f h_delta_pos]
    ring

theorem muSA_bound_independent (f : GenFrameFunction H) {A : H →L[ℂ] H} {c₁ c₂ : ℝ}
    (h₁ : SABounded A c₁) (h₂ : SABounded A c₂) :
    f.muSA h₁ = f.muSA h₂ := by
  rcases le_total c₁ c₂ with hle | hle
  ·
    unfold muSA
    rcases eq_or_lt_of_le hle with heq | hlt
    ·
      subst heq
      rfl
    ·
      have h_delta_pos : (0 : ℝ) < c₂ - c₁ := by linarith
      have h_shift₁ := h₁.shifted_posBounded
      have h_shift₂ := h₂.shifted_posBounded
      have h_op_eq : A + (c₂ : ℂ) • ContinuousLinearMap.id ℂ H
          = (A + (c₁ : ℂ) • ContinuousLinearMap.id ℂ H)
            + (((c₂ - c₁ : ℝ)) : ℂ) • ContinuousLinearMap.id ℂ H := by
        ext z
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.id_apply]
        push_cast
        module
      have h_c1_pos : (0 : ℝ) < c₁ := h₁.pos
      have h_c2_pos : (0 : ℝ) < c₂ := h₂.pos
      have h_2c1_pos : (0 : ℝ) < 2 * c₁ := by linarith
      have h_2c2_pos : (0 : ℝ) < 2 * c₂ := by linarith
      obtain ⟨h_sum_sa, h_sum_nn, h_sum_bound⟩ :=
        posBounded_add h_2c1_pos h_delta_pos
          h_shift₁.1 (idScaled_isSelfAdjoint (c₂ - c₁))
          h_shift₁.2.1 (idScaled_nonneg h_delta_pos.le)
          h_shift₁.2.2 (idScaled_le_bound h_delta_pos.le)
      have h_add_eq :=
        muPosBounded_add f h_2c1_pos h_delta_pos
          h_shift₁.1 (idScaled_isSelfAdjoint (c₂ - c₁))
          h_shift₁.2.1 (idScaled_nonneg h_delta_pos.le)
          h_shift₁.2.2 (idScaled_le_bound h_delta_pos.le)
          h_sum_sa h_sum_nn h_sum_bound
      have h_bridge :
        f.muPosBounded (A + (c₂ : ℂ) • ContinuousLinearMap.id ℂ H) (2 * c₂)
          h_2c2_pos h_shift₂.1 h_shift₂.2.1 h_shift₂.2.2
        = f.muPosBounded ((A + (c₁ : ℂ) • ContinuousLinearMap.id ℂ H)
            + (((c₂ - c₁ : ℝ)) : ℂ) • ContinuousLinearMap.id ℂ H)
          (2 * c₁ + (c₂ - c₁)) (by linarith)
          h_sum_sa h_sum_nn h_sum_bound := by
        rw [muPosBounded_eq_muScaled, muPosBounded_eq_muScaled]
        apply muScaled_well_defined
        rw [SclEffect.ofPosBounded_op, SclEffect.ofPosBounded_op]
        exact h_op_eq
      rw [h_bridge, h_add_eq]
      rw [muPosBounded_idScaled f h_delta_pos]
      ring
  ·
    exact (muSA_bound_independent_aux f h₂ h₁ hle).symm

/-! ### All-scalar compatibility -/
omit instCompleteSpace in
/-- `SABounded` for `r < 0`: `r·A = -((-r)·A)` and use negation + positive scaling. -/
lemma SABounded.smul_neg {A : H →L[ℂ] H} {c : ℝ} (h : SABounded A c) {r : ℝ} (hr : r < 0) :
    SABounded ((r : ℂ) • A) ((-r) * c) := by
  have h_neg_r_pos : 0 < -r := by linarith
  have h_eq : ((r : ℂ) • A) = -(((-r : ℝ) : ℂ) • A) := by
    push_cast
    module
  rw [h_eq]
  exact (h.smul_nn h_neg_r_pos).neg

/-- **Subtraction**: `muSA(A + (-B)) = muSA(A) - muSA(B)`.
(For `A - B` written in the `A + (-B)` form.) -/
theorem muSA_sub_as_add_neg (f : GenFrameFunction H) {A B : H →L[ℂ] H} {c : ℝ}
    (hA : SABounded A c) (hB : SABounded B c) :
    f.muSA (hA.add hB.neg) = f.muSA hA - f.muSA hB := by
  rw [muSA_add f hA hB.neg, muSA_neg f hB]
  abel

end GenFrameFunction

end Busch
