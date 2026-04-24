/-
# Busch/NatScalar.lean — Scaling by Natural Numbers
For an effect `E` and natural number `n` such that `nE ≤ 1`, the operator
`n · E.op` defines an effect `n • E`. And `μ(n • E) = n · μ(E)` for any
generalized frame function `μ`.
This is the integer homogeneity step leading to rational and eventual real
homogeneity of `μ`.
-/
import Busch.Homogeneity

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Effect

/-- Scalar multiplication of an effect by `n : ℕ` given a proof that `n • E.op`
still satisfies the sub-identity bound. -/
def smulNat (n : ℕ) (E : Effect H)
    (h : ∀ x : H, (inner (𝕜 := ℂ) x ((n : ℂ) • E.op x)).re ≤ (inner (𝕜 := ℂ) x x).re) :
    Effect H where
  op := (n : ℂ) • E.op
  isSelfAdjoint := fun x y => by
    simp only [ContinuousLinearMap.smul_apply]
    rw [inner_smul_left, inner_smul_right]
    rw [E.isSelfAdjoint x y]
    rw [show (starRingEnd ℂ) (n : ℂ) = (n : ℂ) by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.conj_ofReal]]
  nonneg := fun x => by
    simp only [ContinuousLinearMap.smul_apply]
    rw [inner_smul_right]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (E.nonneg x)
  le_one := h

/-- `0 • E = 0`. -/
lemma smulNat_zero (E : Effect H) (h : _) :
    smulNat 0 E h = (0 : Effect H) := by
  apply ext
  intro x
  simp [smulNat, zero_op]

/-- Induction step: `(n+1) • E = n • E ⊕ E` when both are valid. -/
lemma smulNat_succ_summable
    (n : ℕ) (E : Effect H)
    (h_nE : ∀ x : H, (inner (𝕜 := ℂ) x ((n : ℂ) • E.op x)).re ≤
      (inner (𝕜 := ℂ) x x).re)
    (h_succ : ∀ x : H, (inner (𝕜 := ℂ) x (((n + 1 : ℕ) : ℂ) • E.op x)).re ≤
      (inner (𝕜 := ℂ) x x).re) :
    Summable (smulNat n E h_nE) E := by
  intro x
  show (inner (𝕜 := ℂ) x (((n : ℂ) • E.op + E.op) x)).re ≤ _
  have h_eq : (n : ℂ) • E.op + E.op = ((n + 1 : ℕ) : ℂ) • E.op := by
    ext y
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    rw [Nat.cast_succ]
    rw [show ((n : ℂ) + 1) • E.op y = (n : ℂ) • E.op y + E.op y by
      rw [add_smul, one_smul]]
  rw [h_eq]
  exact h_succ x

/-- `smulNat n E + E = smulNat (n+1) E` (as effects). -/
lemma smulNat_add_one
    (n : ℕ) (E : Effect H)
    (h_nE : ∀ x : H, (inner (𝕜 := ℂ) x ((n : ℂ) • E.op x)).re ≤
      (inner (𝕜 := ℂ) x x).re)
    (h_succ : ∀ x : H, (inner (𝕜 := ℂ) x (((n + 1 : ℕ) : ℂ) • E.op x)).re ≤
      (inner (𝕜 := ℂ) x x).re) :
    orthoSum (smulNat n E h_nE) E (smulNat_succ_summable n E h_nE h_succ) =
      smulNat (n + 1) E h_succ := by
  apply ext
  intro x
  show ((n : ℂ) • E.op) x + E.op x = ((n + 1 : ℕ) : ℂ) • E.op x
  rw [Nat.cast_succ]
  rw [show ((n : ℂ) + 1) • E.op x = (n : ℂ) • E.op x + E.op x from by
    rw [add_smul, one_smul]]
  rfl

end Effect

namespace GenFrameFunction

/-- **Natural homogeneity**: `μ(n • E) = n · μ(E)` when `n • E` is a valid effect. -/
theorem μ_smulNat (f : GenFrameFunction H) (n : ℕ) (E : Effect H)
    (h : ∀ x : H, (inner (𝕜 := ℂ) x ((n : ℂ) • E.op x)).re ≤
      (inner (𝕜 := ℂ) x x).re) :
    f.μ (Effect.smulNat n E h) = n * f.μ E := by
  induction n with
  | zero =>
    have : Effect.smulNat 0 E h = (0 : Effect H) :=
      Effect.smulNat_zero E h
    rw [this, f.μ_zero]
    simp
  | succ n ih =>
    have h_nE : ∀ x : H, (inner (𝕜 := ℂ) x ((n : ℂ) • E.op x)).re ≤
        (inner (𝕜 := ℂ) x x).re := by
      intro x
      have h_pos : 0 ≤ (inner (𝕜 := ℂ) x (E.op x)).re := E.nonneg x
      have h_leq : (inner (𝕜 := ℂ) x ((n : ℂ) • E.op x)).re ≤
          (inner (𝕜 := ℂ) x (((n + 1 : ℕ) : ℂ) • E.op x)).re := by
        rw [inner_smul_right, inner_smul_right]
        simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
          zero_mul, sub_zero]
        have : (n : ℝ) * (inner (𝕜 := ℂ) x (E.op x)).re ≤
            ((n : ℝ) + 1) * (inner (𝕜 := ℂ) x (E.op x)).re := by
          have : 0 ≤ (1 : ℝ) * (inner (𝕜 := ℂ) x (E.op x)).re := by
            rw [one_mul]; exact h_pos
          linarith
        have h_cast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        rw [h_cast]
        exact this
      linarith [h x]
    have h_ih := ih h_nE
    have h_sum := Effect.smulNat_add_one n E h_nE h
    have h_add := f.additive (Effect.smulNat n E h_nE) E
      (Effect.smulNat_succ_summable n E h_nE h)
    rw [h_sum] at h_add
    rw [h_add, h_ih]
    push_cast
    ring

end GenFrameFunction

end Busch
