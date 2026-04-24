/-
# Busch/EffectScalar.lean — Scalar Multiplication of Effects
For `t ∈ [0, 1]` and effect `E`, the operator `t · E.op` is again an effect.
This gives a scalar multiplication `smul : ℝ≥0 × Effect H → Effect H` restricted
to `t ∈ [0, 1]`.
This is needed for:
- Defining convex combinations `t E + (1-t) F`
- Proving homogeneity of the frame function: `μ(t E) = t · μ(E)` for `t ∈ [0, 1]`
- Extending `μ` linearly to self-adjoint operators
## Design note
We define scalar multiplication `smulIcc : unitIcc → Effect H → Effect H` only for
`t ∈ [0, 1]`. For negative scalars, the operation does not preserve positivity.
For `t > 1`, the operation does not preserve the `≤ 1` bound without further hypotheses.
-/
import Busch.EffectOrthogonal

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Effect

/-- The unit interval `[0, 1]` as a type (using the standard `Set.Icc`). -/
abbrev UnitIcc : Type := Set.Icc (0 : ℝ) 1

/-- Scalar multiplication of an effect by `t ∈ [0, 1]`.
The underlying operator is `(t : ℂ) • E.op`. The coercion `(t : ℂ)` is through ℝ. -/
def smulIcc (t : UnitIcc) (E : Effect H) : Effect H where
  op := (t.1 : ℂ) • E.op
  isSelfAdjoint := fun x y => by
    simp only [ContinuousLinearMap.smul_apply]
    rw [inner_smul_left, inner_smul_right]
    rw [E.isSelfAdjoint x y]
    rw [Complex.conj_ofReal]
  nonneg := fun x => by
    simp only [ContinuousLinearMap.smul_apply]
    rw [inner_smul_right]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg t.2.1 (E.nonneg x)
  le_one := fun x => by
    simp only [ContinuousLinearMap.smul_apply]
    rw [inner_smul_right]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have h1 : t.1 * (inner (𝕜 := ℂ) x (E.op x)).re ≤ t.1 * (inner (𝕜 := ℂ) x x).re :=
      mul_le_mul_of_nonneg_left (E.le_one x) t.2.1
    have h2 : t.1 * (inner (𝕜 := ℂ) x x).re ≤ 1 * (inner (𝕜 := ℂ) x x).re :=
      mul_le_mul_of_nonneg_right t.2.2 (@inner_self_nonneg ℂ H _ _ _ x)
    linarith
@[simp] lemma smulIcc_op (t : UnitIcc) (E : Effect H) :
    (smulIcc t E).op = (t.1 : ℂ) • E.op := rfl
@[simp] lemma smulIcc_apply (t : UnitIcc) (E : Effect H) (x : H) :
    (smulIcc t E) x = (t.1 : ℂ) • E x := by
  show ((t.1 : ℂ) • E.op) x = (t.1 : ℂ) • E.op x
  rfl

/-- Scalar multiplication by `0` gives the zero effect. -/
lemma smulIcc_zero (E : Effect H) :
    smulIcc ⟨0, le_refl 0, zero_le_one⟩ E = (0 : Effect H) := by
  apply ext
  intro x
  simp [smulIcc, zero_op]

/-- Scalar multiplication by `1` gives the effect itself. -/
lemma smulIcc_one (E : Effect H) :
    smulIcc ⟨1, zero_le_one, le_refl 1⟩ E = E := by
  apply ext
  intro x
  simp [smulIcc]

/-- Scalar multiplication distributes into the zero effect. -/
lemma smulIcc_zero_op (t : UnitIcc) :
    smulIcc t (0 : Effect H) = (0 : Effect H) := by
  apply ext
  intro x
  simp [smulIcc, zero_op]

/-- For `t ∈ [0, 1]`, `tE` is summable with `(1-t)E` (their sum is `E ≤ 1`). -/
lemma smulIcc_summable_complement (t : UnitIcc) (E : Effect H) :
    Summable (smulIcc t E) (smulIcc ⟨1 - t.1, by linarith [t.2.2], by linarith [t.2.1]⟩ E) := by
  intro x
  show (inner (𝕜 := ℂ) x
      (((t.1 : ℂ) • E.op + ((1 - t.1 : ℝ) : ℂ) • E.op) x)).re ≤ _
  have h_eq : ((t.1 : ℂ) • E.op + ((1 - t.1 : ℝ) : ℂ) • E.op) = E.op := by
    ext y
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      Complex.ofReal_sub, Complex.ofReal_one]
    have : (t.1 : ℂ) • E.op y + (1 - (t.1 : ℂ)) • E.op y = E.op y := by
      rw [sub_smul, one_smul]
      abel
    exact this
  rw [h_eq]
  exact E.le_one x

/-- Sum decomposition: `tE + (1-t)E = E`. -/
lemma smulIcc_add_complement (t : UnitIcc) (E : Effect H) :
    orthoSum (smulIcc t E)
        (smulIcc ⟨1 - t.1, by linarith [t.2.2], by linarith [t.2.1]⟩ E)
        (smulIcc_summable_complement t E) = E := by
  apply ext
  intro x
  have h_tvalid_left : (0 : ℝ) ≤ 1 - t.1 := by linarith [t.2.2]
  have h_tvalid_right : 1 - t.1 ≤ 1 := by linarith [t.2.1]
  show (smulIcc t E) x +
      (smulIcc ⟨1 - t.1, h_tvalid_left, h_tvalid_right⟩ E) x = E x
  simp only [smulIcc_apply]
  have hcast : ((1 - t.1 : ℝ) : ℂ) = (1 : ℂ) - (t.1 : ℂ) := by push_cast; ring
  rw [hcast, sub_smul, one_smul]
  abel

end Effect

end Busch
