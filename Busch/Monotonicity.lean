/-
# Busch/Monotonicity.lean — Monotonicity of Frame Functions
If `E ≤ F` (Löwner order on effects) then `μ(E) ≤ μ(F)` for any generalized
frame function `μ`.
The proof uses effect subtraction: when `E ≤ F`, the operator `F.op - E.op`
defines an effect `F ⊟ E`, and we have `E ⊕ (F ⊟ E) = F`. Additivity then gives
`μ(F) = μ(E) + μ(F ⊟ E) ≥ μ(E)` since `μ(F ⊟ E) ≥ 0`.
-/
import Busch.EffectScalar
import Busch.GenFrameFunction

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Effect

/-- Effect subtraction: given `E ≤ F`, construct `F ⊟ E := F - E` as an effect.
The operator is `F.op - E.op`. Its positivity follows from `E ≤ F`, and its
sub-identity follows from `F ≤ 1`. -/
def sub (F E : Effect H) (h : E ≤ F) : Effect H where
  op := F.op - E.op
  isSelfAdjoint := fun x y => by
    simp only [ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
    rw [E.isSelfAdjoint x y, F.isSelfAdjoint x y]
  nonneg := fun x => by
    simp only [ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re]
    linarith [h x]
  le_one := fun x => by
    simp only [ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re]
    linarith [F.le_one x, E.nonneg x]
@[simp] lemma sub_op (F E : Effect H) (h : E ≤ F) :
    (sub F E h).op = F.op - E.op := rfl

/-- `E` is summable with `F ⊟ E` when `E ≤ F` (their sum is `F ≤ 1`). -/
lemma summable_sub (F E : Effect H) (h : E ≤ F) : Summable E (sub F E h) := by
  intro x
  show (inner (𝕜 := ℂ) x ((E.op + (F.op - E.op)) x)).re ≤ _
  have h_add_cancel : E.op + (F.op - E.op) = F.op := by
    ext z; simp
  rw [h_add_cancel]
  exact F.le_one x

/-- The orthogonal sum `E ⊕ (F ⊟ E)` equals `F`. -/
lemma orthoSum_sub (F E : Effect H) (h : E ≤ F) :
    orthoSum E (sub F E h) (summable_sub F E h) = F := by
  apply ext
  intro x
  show E.op x + (F.op - E.op) x = F.op x
  simp

end Effect

/-- **Monotonicity**: If `E ≤ F` then `μ(E) ≤ μ(F)`. -/
theorem GenFrameFunction_monotone (f : GenFrameFunction H) (E F : Effect H)
    (h : E ≤ F) : f.μ E ≤ f.μ F := by
  have h_sum := Effect.orthoSum_sub F E h
  have h_add := f.additive E (Effect.sub F E h) (Effect.summable_sub F E h)
  rw [h_sum] at h_add
  have h_nonneg : 0 ≤ f.μ (Effect.sub F E h) := f.nonneg _
  linarith

/-- **Explicit difference formula**: `μ(F ⊟ E) = μ(F) - μ(E)` when `E ≤ F`. -/
theorem GenFrameFunction_μ_sub_eq (f : GenFrameFunction H) (E F : Effect H)
    (h : E ≤ F) : f.μ (Effect.sub F E h) = f.μ F - f.μ E := by
  have h_sum := Effect.orthoSum_sub F E h
  have h_add := f.additive E (Effect.sub F E h) (Effect.summable_sub F E h)
  rw [h_sum] at h_add
  linarith

namespace GenFrameFunction

/-- `μ` as a monotone function. -/
theorem monotone (f : GenFrameFunction H) {E F : Effect H} (h : E ≤ F) :
    f.μ E ≤ f.μ F :=
  GenFrameFunction_monotone f E F h

/-- Explicit difference: `μ(F ⊟ E) = μ(F) - μ(E)` when `E ≤ F`. -/
theorem μ_sub_eq (f : GenFrameFunction H) {E F : Effect H} (h : E ≤ F) :
    f.μ (Effect.sub F E h) = f.μ F - f.μ E :=
  GenFrameFunction_μ_sub_eq f E F h

end GenFrameFunction

end Busch
