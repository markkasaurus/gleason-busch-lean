/-
# Unbundled Effect Predicate

This file connects the bundled `Effect` type used in the formalization with
mathlib's positive-operator predicate on continuous linear maps.
-/
import Busch.Effect
import Mathlib.Analysis.InnerProductSpace.Positive

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An unbundled effect predicate on continuous linear operators.

The positivity component uses mathlib's `ContinuousLinearMap.IsPositive`; the
upper bound is kept in the pointwise form used throughout this development. -/
def IsEffect (T : H →L[ℂ] H) : Prop :=
  ContinuousLinearMap.IsPositive T ∧
    ∀ x : H, (inner (𝕜 := ℂ) x (T x)).re ≤ (inner (𝕜 := ℂ) x x).re

namespace Effect

/-- Every bundled effect determines an operator satisfying the unbundled
`IsEffect` predicate. -/
lemma isEffect_op (E : Effect H) : IsEffect E.op := by
  refine ⟨?_, E.le_one⟩
  rw [ContinuousLinearMap.isPositive_def]
  refine ⟨?_, ?_⟩
  · intro x y
    exact E.isSelfAdjoint x y
  · intro x
    have hdiag := E.isSelfAdjoint x x
    rw [ContinuousLinearMap.reApplyInnerSelf]
    rw [hdiag]
    exact E.nonneg x

/-- Bundle an operator satisfying `IsEffect` as an `Effect`. -/
def ofIsEffect (T : H →L[ℂ] H) (hT : IsEffect T) : Effect H where
  op := T
  isSelfAdjoint := fun x y => hT.1.inner_left_eq_inner_right x y
  nonneg := fun x => by
    have hpos := hT.1.re_inner_nonneg_left x
    have hdiag := hT.1.inner_left_eq_inner_right x x
    rw [hdiag] at hpos
    exact hpos
  le_one := hT.2

@[simp] lemma ofIsEffect_op (T : H →L[ℂ] H) (hT : IsEffect T) :
    (ofIsEffect T hT).op = T :=
  rfl

end Effect

end Busch
