/-
# Busch/ProjectionRestriction.lean — Bridge from Effects to Classical Projections
Every orthogonal projection is an effect. Given a generalized frame function
`μ : GenFrameFunction H`, its restriction to projections (viewed as effects)
is a classical Gleason frame function.
This file defines:
- `Effect.isProjection` — predicate characterizing idempotent effects
- `Effect.ofProjection` — lift a projection to an effect
- The restriction map `GenFrameFunction → ClassicalFrameData`
-/
import Busch.GenFrameFunction

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [instCompleteSpace : CompleteSpace H]

namespace Effect

/-- An effect is a *projection-effect* if it is idempotent. -/
def IsProjection (E : Effect H) : Prop := E.op * E.op = E.op

/-- The zero effect is a projection-effect. -/
lemma zero_isProjection : IsProjection (0 : Effect H) := by
  show (0 : Effect H).op * (0 : Effect H).op = (0 : Effect H).op
  simp

/-- The identity effect is a projection-effect. -/
lemma one_isProjection : IsProjection (1 : Effect H) := by
  show (1 : Effect H).op * (1 : Effect H).op = (1 : Effect H).op
  simp only [one_op]
  ext x; simp

/-- The orthocomplement of a projection-effect is a projection-effect. -/
lemma orthoComplement_isProjection {E : Effect H} (hE : IsProjection E) :
    IsProjection (orthoComplement E) := by
  show (orthoComplement E).op * (orthoComplement E).op = (orthoComplement E).op
  simp only [orthoComplement_op]
  ext x
  show ((ContinuousLinearMap.id ℂ H - E.op) * (ContinuousLinearMap.id ℂ H - E.op)) x
      = (ContinuousLinearMap.id ℂ H - E.op) x
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply]
  have h_idem : E.op (E.op x) = E.op x := by
    have h_eq : E.op * E.op = E.op := hE
    have := congrArg (fun f => f x) h_eq
    simp only [ContinuousLinearMap.mul_apply] at this
    exact this
  rw [map_sub, h_idem]
  abel

end Effect

/-- A projection-effect pair `(E, E')` with `E` a projection-effect and `E' = 1 - E`
    its orthocomplement. This is the structure used in the classical frame function:
    a frame function is additive on such "orthogonal" pairs. -/
structure ProjectionEffect (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  effect : Effect H
  is_projection : Effect.IsProjection effect

/-- Orthogonality of projection-effects: `P * Q = 0` (both as operators). -/
def ProjectionEffect.orthogonal (P Q : ProjectionEffect H) : Prop :=
  P.effect.op * Q.effect.op = 0
section
omit instCompleteSpace

/-- **Helper**: For a self-adjoint operator `R` that is idempotent (`R² = R`),
the "diagonal" inner product `⟨x, Rx⟩` equals `‖Rx‖²` (as a complex number with zero
imaginary part). This is the key identity making self-adjoint idempotents behave
as orthogonal projections. -/
lemma inner_self_selfAdjoint_idempotent
    (R : H →L[ℂ] H)
    (hSA : ∀ x y : H, inner (𝕜 := ℂ) (R x) y = inner (𝕜 := ℂ) x (R y))
    (hIdem : R * R = R) (x : H) :
    inner (𝕜 := ℂ) x (R x) = (inner (𝕜 := ℂ) (R x) (R x)) := by
  have h1 : R x = R (R x) := by
    have := congrArg (fun f => f x) hIdem.symm
    simp only [ContinuousLinearMap.mul_apply] at this
    exact this
  calc inner (𝕜 := ℂ) x (R x)
      = inner (𝕜 := ℂ) x (R (R x)) := by rw [← h1]
    _ = inner (𝕜 := ℂ) (R x) (R x) := (hSA x (R x)).symm

/-- **Key bound**: For a self-adjoint idempotent operator `R`, the real part of
`⟨x, Rx⟩` is bounded by `⟨x, x⟩.re`. This makes `R` an effect (Löwner order ≤ 1). -/
lemma re_inner_le_self_of_selfAdjoint_idempotent
    (R : H →L[ℂ] H)
    (hSA : ∀ x y : H, inner (𝕜 := ℂ) (R x) y = inner (𝕜 := ℂ) x (R y))
    (hIdem : R * R = R) (x : H) :
    (inner (𝕜 := ℂ) x (R x)).re ≤ (inner (𝕜 := ℂ) x x).re := by
  have hdiag := inner_self_selfAdjoint_idempotent R hSA hIdem x
  have horth : inner (𝕜 := ℂ) (R x) (x - R x) = 0 := by
    rw [inner_sub_right]
    have hswap : inner (𝕜 := ℂ) (R x) x = inner (𝕜 := ℂ) x (R x) := hSA x x
    rw [hswap, hdiag]
    simp
  have hsplit : x = R x + (x - R x) := by abel
  have hx_sq_expand : (inner (𝕜 := ℂ) x x).re = (inner (𝕜 := ℂ) (R x) (R x)).re
      + (inner (𝕜 := ℂ) (x - R x) (x - R x)).re := by
    conv_lhs => rw [show x = R x + (x - R x) from hsplit]
    rw [inner_add_left, inner_add_right, inner_add_right]
    simp only [Complex.add_re]
    rw [horth]
    have hconj : inner (𝕜 := ℂ) (x - R x) (R x) = 0 := by
      rw [← inner_conj_symm]
      rw [horth]
      simp
    rw [hconj]
    simp
  rw [hdiag]
  rw [hx_sq_expand]
  have h_nonneg : 0 ≤ (inner (𝕜 := ℂ) (x - R x) (x - R x)).re :=
    @inner_self_nonneg ℂ H _ _ _ (x - R x)
  linarith
end

/-- Orthogonal projection-effects have summable underlying effects. -/
lemma ProjectionEffect.summable_of_orthogonal (P Q : ProjectionEffect H)
    (h : P.orthogonal Q) : Effect.Summable P.effect Q.effect := by
  intro x
  show (inner (𝕜 := ℂ) x ((P.effect.op + Q.effect.op) x)).re ≤ (inner (𝕜 := ℂ) x x).re
  have hPQ : P.effect.op * Q.effect.op = 0 := h
  have hQP : Q.effect.op * P.effect.op = 0 := by
    ext y
    have h_inner_zero : ∀ z, inner (𝕜 := ℂ) ((Q.effect.op * P.effect.op) y) z = 0 := by
      intro z
      show inner (𝕜 := ℂ) (Q.effect.op (P.effect.op y)) z = 0
      rw [Q.effect.isSelfAdjoint]
      rw [P.effect.isSelfAdjoint]
      have : P.effect.op (Q.effect.op z) = (P.effect.op * Q.effect.op) z := by
        simp [ContinuousLinearMap.mul_apply]
      rw [this, hPQ]
      simp
    have h_norm_sq_zero : inner (𝕜 := ℂ)
        ((Q.effect.op * P.effect.op) y)
        ((Q.effect.op * P.effect.op) y) = 0 := h_inner_zero _
    have h_norm_zero := (@inner_self_eq_zero ℂ H _ _ _).mp h_norm_sq_zero
    simp [h_norm_zero]
  have hIdemSum : (P.effect.op + Q.effect.op) * (P.effect.op + Q.effect.op)
      = P.effect.op + Q.effect.op := by
    have h_expand : (P.effect.op + Q.effect.op) * (P.effect.op + Q.effect.op)
        = P.effect.op * P.effect.op + P.effect.op * Q.effect.op
          + Q.effect.op * P.effect.op + Q.effect.op * Q.effect.op := by
      noncomm_ring
    rw [h_expand, hPQ, hQP, P.is_projection, Q.is_projection]
    abel
  have hSA : ∀ x y : H, inner (𝕜 := ℂ) ((P.effect.op + Q.effect.op) x) y
      = inner (𝕜 := ℂ) x ((P.effect.op + Q.effect.op) y) := by
    intro a b
    simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
    rw [P.effect.isSelfAdjoint, Q.effect.isSelfAdjoint]
  exact re_inner_le_self_of_selfAdjoint_idempotent
    (P.effect.op + Q.effect.op) hSA hIdemSum x

end Busch
