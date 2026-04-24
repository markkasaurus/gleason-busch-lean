/-
# Busch/EffectOrthogonal.lean — Orthogonal Sums of Effects
Two effects `E, F` are said to be *orthogonal* (or *summable*) when `E + F ≤ 1`.
In that case their orthogonal sum `E ⊕ F := E + F` is again an effect.
This file establishes:
- Addition of operators when the sum remains an effect
- The orthocomplement `E' := 1 - E`
- Basic identities: `E ⊕ (1 - E) = 1`, `E ⊕ 0 = E`, etc.
These are the structural primitives used for finite orthogonal sums of effects.
-/
import Busch.Effect

noncomputable section

open scoped ComplexConjugate

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Effect

/-- Predicate: two effects `E`, `F` are summable (orthogonal in Busch's sense)
    when their sum is still ≤ 1. -/
def Summable (E F : Effect H) : Prop :=
  ∀ x : H, (inner (𝕜 := ℂ) x ((E.op + F.op) x)).re ≤ (inner (𝕜 := ℂ) x x).re

/-- If `E, F` are summable, form the orthogonal sum `E ⊕ F`. -/
def orthoSum (E F : Effect H) (h : Summable E F) : Effect H where
  op := E.op + F.op
  isSelfAdjoint := fun x y => by
    simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
    rw [E.isSelfAdjoint x y, F.isSelfAdjoint x y]
  nonneg := fun x => by
    simp only [ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
    linarith [E.nonneg x, F.nonneg x]
  le_one := h
@[simp] lemma orthoSum_op (E F : Effect H) (h : Summable E F) :
    (orthoSum E F h).op = E.op + F.op := rfl
@[simp] lemma orthoSum_apply (E F : Effect H) (h : Summable E F) (x : H) :
    (orthoSum E F h) x = E.op x + F.op x := by
  show (E.op + F.op) x = E.op x + F.op x
  rfl

/-- The orthocomplement `1 - E`. -/
def orthoComplement (E : Effect H) : Effect H where
  op := ContinuousLinearMap.id ℂ H - E.op
  isSelfAdjoint := fun x y => by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      inner_sub_left, inner_sub_right]
    rw [E.isSelfAdjoint x y]
  nonneg := fun x => by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      inner_sub_right, Complex.sub_re]
    linarith [E.le_one x]
  le_one := fun x => by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      inner_sub_right, Complex.sub_re]
    linarith [E.nonneg x]
@[simp] lemma orthoComplement_op (E : Effect H) :
    (orthoComplement E).op = ContinuousLinearMap.id ℂ H - E.op := rfl

/-- An effect and its orthocomplement are summable (their sum is 1). -/
lemma summable_orthoComplement (E : Effect H) : Summable E (orthoComplement E) := by
  intro x
  show (inner (𝕜 := ℂ) x ((E.op + (ContinuousLinearMap.id ℂ H - E.op)) x)).re ≤ _
  have h_add_cancel : E.op + (ContinuousLinearMap.id ℂ H - E.op) = ContinuousLinearMap.id ℂ H := by
    ext z; simp
  rw [h_add_cancel]
  simp only [ContinuousLinearMap.id_apply]
  exact le_refl _

/-- `E ⊕ E' = 1` where `E'` is the orthocomplement. -/
lemma orthoSum_orthoComplement (E : Effect H) :
    orthoSum E (orthoComplement E) (summable_orthoComplement E) = (1 : Effect H) := by
  apply ext
  intro x
  show E.op x + (ContinuousLinearMap.id ℂ H - E.op) x = x
  simp

/-- Zero is summable with any effect. -/
lemma summable_zero_left (E : Effect H) : Summable (0 : Effect H) E := by
  intro x
  show (inner (𝕜 := ℂ) x (((0 : Effect H).op + E.op) x)).re ≤ _
  simp only [zero_op, zero_add]
  exact E.le_one x

lemma summable_zero_right (E : Effect H) : Summable E (0 : Effect H) := by
  intro x
  show (inner (𝕜 := ℂ) x ((E.op + (0 : Effect H).op) x)).re ≤ _
  simp only [zero_op, add_zero]
  exact E.le_one x

/-- `0 ⊕ E = E`. -/
lemma orthoSum_zero_left (E : Effect H) :
    orthoSum (0 : Effect H) E (summable_zero_left E) = E := by
  apply ext
  intro x
  show (0 : Effect H).op x + E.op x = E.op x
  simp

/-- `E ⊕ 0 = E`. -/
lemma orthoSum_zero_right (E : Effect H) :
    orthoSum E (0 : Effect H) (summable_zero_right E) = E := by
  apply ext
  intro x
  show E.op x + (0 : Effect H).op x = E.op x
  simp

/-- Orthogonal sum is commutative (modulo the summability hypothesis). -/
lemma orthoSum_comm (E F : Effect H) (h : Summable E F) :
    ∃ h' : Summable F E, orthoSum F E h' = orthoSum E F h := by
  refine ⟨?_, ?_⟩
  · intro x
    show (inner (𝕜 := ℂ) x ((F.op + E.op) x)).re ≤ _
    have : F.op + E.op = E.op + F.op := add_comm _ _
    rw [this]; exact h x
  · apply ext
    intro x
    show F.op x + E.op x = E.op x + F.op x
    exact add_comm _ _

end Effect

end Busch
