/-
# Busch/PositiveAdditivity.lean — Additivity on Positive Operator Sums
This file proves additivity of `muPosBounded` on sums of positive operators:
  `muPosBounded (A + B) = muPosBounded A + muPosBounded B`
for self-adjoint positive `A`, `B` with explicit bounds `c_A, c_B`.
The proof uses:
1. `A + B` has bound `c_A + c_B` (positive + subadditive in the Löwner sense)
2. `A/(c_A+c_B) ⊕ B/(c_A+c_B)` is a summable pair (since their sum is `(A+B)/(c_A+c_B)`
   which is an effect)
3. The additivity of `μ` on summable pairs + well-definedness of `muScaled`
Together with real homogeneity and positive-scaling compatibility, this is the
additive component of the positive-cone extension.
-/
import Busch.PositiveOp

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [instCompleteSpace : CompleteSpace H]

namespace GenFrameFunction

/-- The **sum of two scaled effects** `(c_A, E_A), (c_B, E_B)` with operators
`A = c_A · E_A.op` and `B = c_B · E_B.op` satisfying `A + B = (c_A + c_B) · E`
for an effect `E`. The key input: the pair is summable. -/
lemma muScaled_add_pair (f : GenFrameFunction H) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (E₁ E₂ : Effect H)
    (h_sum : Effect.Summable
        (Effect.smulIcc ⟨c₁ / (c₁ + c₂),
          div_nonneg hc₁.le (by linarith),
          (div_le_one (by linarith)).mpr (by linarith)⟩ E₁)
        (Effect.smulIcc ⟨c₂ / (c₁ + c₂),
          div_nonneg hc₂.le (by linarith),
          (div_le_one (by linarith)).mpr (by linarith)⟩ E₂)) :
    (c₁ + c₂) * f.μ (Effect.orthoSum
        (Effect.smulIcc ⟨c₁ / (c₁ + c₂),
          div_nonneg hc₁.le (by linarith),
          (div_le_one (by linarith)).mpr (by linarith)⟩ E₁)
        (Effect.smulIcc ⟨c₂ / (c₁ + c₂),
          div_nonneg hc₂.le (by linarith),
          (div_le_one (by linarith)).mpr (by linarith)⟩ E₂) h_sum)
      = c₁ * f.μ E₁ + c₂ * f.μ E₂ := by
  have h_pos : 0 < c₁ + c₂ := by linarith
  have h_ne : c₁ + c₂ ≠ 0 := ne_of_gt h_pos
  rw [f.additive, f.μ_smulIcc, f.μ_smulIcc]
  show (c₁ + c₂) * ((c₁ / (c₁ + c₂)) * f.μ E₁ + (c₂ / (c₁ + c₂)) * f.μ E₂)
      = c₁ * f.μ E₁ + c₂ * f.μ E₂
  field_simp
section
omit instCompleteSpace

/-- **Sum of positive-bounded operators is positive-bounded**. -/
lemma posBounded_add {A B : H →L[ℂ] H} {cA cB : ℝ} (_hcA : 0 < cA) (_hcB : 0 < cB)
    (hSA_A : ∀ x y : H, inner (𝕜 := ℂ) (A x) y = inner (𝕜 := ℂ) x (A y))
    (hSA_B : ∀ x y : H, inner (𝕜 := ℂ) (B x) y = inner (𝕜 := ℂ) x (B y))
    (hNN_A : ∀ x, 0 ≤ (inner (𝕜 := ℂ) x (A x)).re)
    (hNN_B : ∀ x, 0 ≤ (inner (𝕜 := ℂ) x (B x)).re)
    (hLe_A : ∀ x, (inner (𝕜 := ℂ) x (A x)).re ≤ cA * (inner (𝕜 := ℂ) x x).re)
    (hLe_B : ∀ x, (inner (𝕜 := ℂ) x (B x)).re ≤ cB * (inner (𝕜 := ℂ) x x).re) :
    (∀ x y : H, inner (𝕜 := ℂ) ((A + B) x) y = inner (𝕜 := ℂ) x ((A + B) y)) ∧
    (∀ x, 0 ≤ (inner (𝕜 := ℂ) x ((A + B) x)).re) ∧
    (∀ x, (inner (𝕜 := ℂ) x ((A + B) x)).re ≤ (cA + cB) * (inner (𝕜 := ℂ) x x).re) := by
  refine ⟨?_, ?_, ?_⟩
  ·
    intro x y
    simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
    rw [hSA_A, hSA_B]
  ·
    intro x
    simp only [ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
    linarith [hNN_A x, hNN_B x]
  ·
    intro x
    simp only [ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
    have := hLe_A x
    have := hLe_B x
    linarith
end

/-- **Summability of scaled-down effect pair**: for positive operators A, B with
bounds cA, cB, the effects `A/(cA+cB)` and `B/(cA+cB)` are summable. -/
lemma summable_scaled_pair {A B : H →L[ℂ] H} {cA cB : ℝ} (hcA : 0 < cA) (hcB : 0 < cB)
    (hSA_A : ∀ x y : H, inner (𝕜 := ℂ) (A x) y = inner (𝕜 := ℂ) x (A y))
    (hSA_B : ∀ x y : H, inner (𝕜 := ℂ) (B x) y = inner (𝕜 := ℂ) x (B y))
    (hNN_A : ∀ x, 0 ≤ (inner (𝕜 := ℂ) x (A x)).re)
    (hNN_B : ∀ x, 0 ≤ (inner (𝕜 := ℂ) x (B x)).re)
    (hLe_A : ∀ x, (inner (𝕜 := ℂ) x (A x)).re ≤ cA * (inner (𝕜 := ℂ) x x).re)
    (hLe_B : ∀ x, (inner (𝕜 := ℂ) x (B x)).re ≤ cB * (inner (𝕜 := ℂ) x x).re) :
    Effect.Summable
        (Effect.smulIcc ⟨cA / (cA + cB),
          div_nonneg hcA.le (by linarith),
          (div_le_one (by linarith)).mpr (by linarith)⟩
          (Effect.ofPosBounded A cA hcA hSA_A hNN_A hLe_A))
        (Effect.smulIcc ⟨cB / (cA + cB),
          div_nonneg hcB.le (by linarith),
          (div_le_one (by linarith)).mpr (by linarith)⟩
          (Effect.ofPosBounded B cB hcB hSA_B hNN_B hLe_B)) := by
  intro x
  show (inner (𝕜 := ℂ) x
    (((Effect.smulIcc _ (Effect.ofPosBounded A cA hcA hSA_A hNN_A hLe_A)).op
      + (Effect.smulIcc _ (Effect.ofPosBounded B cB hcB hSA_B hNN_B hLe_B)).op) x)).re
      ≤ (inner (𝕜 := ℂ) x x).re
  simp only [Effect.smulIcc_op, Effect.ofPosBounded_op]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    inner_add_right, inner_smul_right, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hSum_pos : 0 < cA + cB := by linarith
  have hSum_ne : cA + cB ≠ 0 := ne_of_gt hSum_pos
  have hcA_ne : cA ≠ 0 := ne_of_gt hcA
  have hcB_ne : cB ≠ 0 := ne_of_gt hcB
  have hbound_A := hLe_A x
  have hbound_B := hLe_B x
  have h_self_nn : 0 ≤ (inner (𝕜 := ℂ) x x).re := @inner_self_nonneg ℂ H _ _ _ x
  have h1 : (cA / (cA + cB)) * ((cA)⁻¹ * (inner (𝕜 := ℂ) x (A x)).re)
      ≤ (cA / (cA + cB)) * ((cA)⁻¹ * (cA * (inner (𝕜 := ℂ) x x).re)) := by
    have hfrac_nn : 0 ≤ cA / (cA + cB) := div_nonneg hcA.le hSum_pos.le
    have hcA_inv_nn : (0 : ℝ) ≤ cA⁻¹ := inv_nonneg.mpr hcA.le
    have hprod_nn : 0 ≤ (cA / (cA + cB)) * cA⁻¹ := mul_nonneg hfrac_nn hcA_inv_nn
    nlinarith
  have h2 : (cB / (cA + cB)) * ((cB)⁻¹ * (inner (𝕜 := ℂ) x (B x)).re)
      ≤ (cB / (cA + cB)) * ((cB)⁻¹ * (cB * (inner (𝕜 := ℂ) x x).re)) := by
    have hfrac_nn : 0 ≤ cB / (cA + cB) := div_nonneg hcB.le hSum_pos.le
    have hcB_inv_nn : (0 : ℝ) ≤ cB⁻¹ := inv_nonneg.mpr hcB.le
    have hprod_nn : 0 ≤ (cB / (cA + cB)) * cB⁻¹ := mul_nonneg hfrac_nn hcB_inv_nn
    nlinarith
  have hrhs : (cA / (cA + cB)) * ((cA)⁻¹ * (cA * (inner (𝕜 := ℂ) x x).re))
        + (cB / (cA + cB)) * ((cB)⁻¹ * (cB * (inner (𝕜 := ℂ) x x).re))
      = (inner (𝕜 := ℂ) x x).re := by
    field_simp
  linarith

/-- **Additivity of muPosBounded on positive-bounded sums**:
for positive self-adjoint operators `A, B` with explicit bounds `cA, cB`,
  `muPosBounded (A + B) = muPosBounded A + muPosBounded B`. -/
theorem muPosBounded_add (f : GenFrameFunction H) {A B : H →L[ℂ] H} {cA cB : ℝ}
    (hcA : 0 < cA) (hcB : 0 < cB)
    (hSA_A : ∀ x y : H, inner (𝕜 := ℂ) (A x) y = inner (𝕜 := ℂ) x (A y))
    (hSA_B : ∀ x y : H, inner (𝕜 := ℂ) (B x) y = inner (𝕜 := ℂ) x (B y))
    (hNN_A : ∀ x, 0 ≤ (inner (𝕜 := ℂ) x (A x)).re)
    (hNN_B : ∀ x, 0 ≤ (inner (𝕜 := ℂ) x (B x)).re)
    (hLe_A : ∀ x, (inner (𝕜 := ℂ) x (A x)).re ≤ cA * (inner (𝕜 := ℂ) x x).re)
    (hLe_B : ∀ x, (inner (𝕜 := ℂ) x (B x)).re ≤ cB * (inner (𝕜 := ℂ) x x).re)
    (hSA_AB : ∀ x y : H, inner (𝕜 := ℂ) ((A + B) x) y = inner (𝕜 := ℂ) x ((A + B) y))
    (hNN_AB : ∀ x, 0 ≤ (inner (𝕜 := ℂ) x ((A + B) x)).re)
    (hLe_AB : ∀ x, (inner (𝕜 := ℂ) x ((A + B) x)).re ≤ (cA + cB) * (inner (𝕜 := ℂ) x x).re) :
    f.muPosBounded (A + B) (cA + cB) (by linarith) hSA_AB hNN_AB hLe_AB
      = f.muPosBounded A cA hcA hSA_A hNN_A hLe_A
        + f.muPosBounded B cB hcB hSA_B hNN_B hLe_B := by
  have h_pos : 0 < cA + cB := by linarith
  have hrA : (0 : ℝ) ≤ cA / (cA + cB) := div_nonneg hcA.le h_pos.le
  have hrA_le : cA / (cA + cB) ≤ 1 := (div_le_one h_pos).mpr (by linarith)
  have hrB : (0 : ℝ) ≤ cB / (cA + cB) := div_nonneg hcB.le h_pos.le
  have hrB_le : cB / (cA + cB) ≤ 1 := (div_le_one h_pos).mpr (by linarith)
  set rA : Effect.UnitIcc := ⟨cA / (cA + cB), hrA, hrA_le⟩
  set rB : Effect.UnitIcc := ⟨cB / (cA + cB), hrB, hrB_le⟩
  set EA : Effect H := Effect.ofPosBounded A cA hcA hSA_A hNN_A hLe_A
  set EB : Effect H := Effect.ofPosBounded B cB hcB hSA_B hNN_B hLe_B
  have h_sum : Effect.Summable (Effect.smulIcc rA EA) (Effect.smulIcc rB EB) :=
    summable_scaled_pair hcA hcB hSA_A hSA_B hNN_A hNN_B hLe_A hLe_B
  have h_op_eq :
    (SclEffect.ofPosBounded (A + B) (cA + cB) h_pos hSA_AB hNN_AB hLe_AB).op
      = ((cA + cB : ℝ) : ℂ) • (Effect.orthoSum (Effect.smulIcc rA EA) (Effect.smulIcc rB EB) h_sum).op := by
    rw [SclEffect.ofPosBounded_op]
    show A + B = ((cA + cB : ℝ) : ℂ) •
        ((rA.1 : ℂ) • EA.op + (rB.1 : ℂ) • EB.op)
    show A + B = ((cA + cB : ℝ) : ℂ) •
        ((rA.1 : ℂ) • (((cA)⁻¹ : ℝ) : ℂ) • A + (rB.1 : ℂ) • (((cB)⁻¹ : ℝ) : ℂ) • B)
    rw [smul_smul, smul_smul, smul_add, smul_smul, smul_smul]
    have hA_coef : ((cA + cB : ℝ) : ℂ) * (((cA / (cA + cB)) : ℝ) : ℂ) * (((cA)⁻¹ : ℝ) : ℂ)
        = (1 : ℂ) := by
      have hA_coef_real : (cA + cB) * (cA / (cA + cB)) * cA⁻¹ = (1 : ℝ) := by
        have hsum_ne : cA + cB ≠ 0 := ne_of_gt h_pos
        have hcA_ne : cA ≠ 0 := ne_of_gt hcA
        field_simp [hsum_ne, hcA_ne]
      exact_mod_cast hA_coef_real
    have hB_coef : ((cA + cB : ℝ) : ℂ) * (((cB / (cA + cB)) : ℝ) : ℂ) * (((cB)⁻¹ : ℝ) : ℂ)
        = (1 : ℂ) := by
      have hB_coef_real : (cA + cB) * (cB / (cA + cB)) * cB⁻¹ = (1 : ℝ) := by
        have hsum_ne : cA + cB ≠ 0 := ne_of_gt h_pos
        have hcB_ne : cB ≠ 0 := ne_of_gt hcB
        field_simp [hsum_ne, hcB_ne]
      exact_mod_cast hB_coef_real
    show A + B = (((cA + cB : ℝ) : ℂ) * ((rA.1 : ℂ) * (((cA)⁻¹ : ℝ) : ℂ))) • A
        + (((cA + cB : ℝ) : ℂ) * ((rB.1 : ℂ) * (((cB)⁻¹ : ℝ) : ℂ))) • B
    rw [← mul_assoc, ← mul_assoc, hA_coef, hB_coef, one_smul, one_smul]
  unfold muPosBounded
  have h_bridge :
    f.muScaled (SclEffect.ofPosBounded (A + B) (cA + cB) h_pos hSA_AB hNN_AB hLe_AB)
      = (cA + cB) * f.μ (Effect.orthoSum (Effect.smulIcc rA EA) (Effect.smulIcc rB EB) h_sum) := by
    have h_well :=
      muScaled_well_defined f
        (SclEffect.ofPosBounded (A + B) (cA + cB) h_pos hSA_AB hNN_AB hLe_AB)
        ⟨cA + cB, h_pos.le,
          Effect.orthoSum (Effect.smulIcc rA EA) (Effect.smulIcc rB EB) h_sum⟩
        h_op_eq
    rw [h_well]
    rfl
  rw [h_bridge]
  rw [muScaled_add_pair f cA cB hcA hcB EA EB h_sum]
  show (cA : ℝ) * f.μ EA + cB * f.μ EB
      = f.muScaled (SclEffect.ofPosBounded A cA hcA hSA_A hNN_A hLe_A)
        + f.muScaled (SclEffect.ofPosBounded B cB hcB hSA_B hNN_B hLe_B)
  rfl

end GenFrameFunction

end Busch
