/-
# Busch/Effect.lean — The Effect Poset
An "effect" on a Hilbert space `H` is a self-adjoint operator `E : H →L[ℂ] H`
satisfying `0 ≤ E ≤ I` in the Löwner order. The set of effects forms a poset
with:
- Zero effect `0`
- Identity effect `1`
- Orthocomplement `E ↦ 1 - E`
- Partial orthogonal sum (when `E + F ≤ I`)
This file sets up the basic type `Effect H` as a bundled subtype with the required
properties, together with minimal structure.
`Busch/EffectPredicate.lean` provides an unbundled compatibility predicate using
mathlib's `ContinuousLinearMap.IsPositive`.
Effects are not the same as projections; projections are precisely the
idempotent effects. Classical frame functions on projections are recovered by
restricting generalized frame functions to that idempotent subfamily.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Basic

noncomputable section

open scoped ComplexConjugate

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An effect on `H` is a self-adjoint operator `E : H →L[ℂ] H` with
`0 ≤ ⟨x, E x⟩` and `⟨x, E x⟩ ≤ ⟨x, x⟩` for all `x`.
The definition uses the pointwise inner-product characterization of the
Löwner inequalities. -/
structure Effect (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The underlying continuous linear operator. -/
  op : H →L[ℂ] H
  /-- `E` is self-adjoint: `⟨E x, y⟩ = ⟨x, E y⟩`. -/
  isSelfAdjoint : ∀ x y : H, inner (𝕜 := ℂ) (op x) y = inner (𝕜 := ℂ) x (op y)
  /-- `E` is positive: `⟨x, E x⟩` has nonneg real part for all `x`. -/
  nonneg : ∀ x : H, 0 ≤ (inner (𝕜 := ℂ) x (op x)).re
  /-- `E` is sub-identity: `⟨x, E x⟩ ≤ ⟨x, x⟩` (real parts). -/
  le_one : ∀ x : H, (inner (𝕜 := ℂ) x (op x)).re ≤ (inner (𝕜 := ℂ) x x).re

namespace Effect

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Evaluation of the underlying operator on a vector. -/
instance : CoeFun (Effect H) (fun _ => H → H) where
  coe E := fun x => E.op x
@[simp] lemma coe_mk (op : H →L[ℂ] H) (h1 h2 h3) (x : H) :
    (Effect.mk op h1 h2 h3 : H → H) x = op x := rfl
@[simp] lemma coe_op (E : Effect H) (x : H) : E x = E.op x := rfl

/-- The zero effect: `0 : Effect H`. This is the operator `0 : H →L[ℂ] H`. -/
def zero : Effect H where
  op := 0
  isSelfAdjoint := fun x y => by simp
  nonneg := fun x => by simp
  le_one := fun x => by
    show (inner (𝕜 := ℂ) x ((0 : H →L[ℂ] H) x)).re ≤ (inner (𝕜 := ℂ) x x).re
    simp only [ContinuousLinearMap.zero_apply, inner_zero_right, Complex.zero_re]
    exact @inner_self_nonneg ℂ H _ _ _ x

instance : Zero (Effect H) := ⟨zero⟩
@[simp] lemma zero_op : (0 : Effect H).op = 0 := rfl
@[simp] lemma zero_apply (x : H) : (0 : Effect H) x = 0 := by
  show (0 : Effect H).op x = 0; rfl

/-- The identity effect: `1 : Effect H`. This is the identity operator. -/
def one : Effect H where
  op := ContinuousLinearMap.id ℂ H
  isSelfAdjoint := fun x y => by simp
  nonneg := fun x => by
    simp only [ContinuousLinearMap.id_apply]
    exact @inner_self_nonneg ℂ H _ _ _ x
  le_one := fun x => by simp

instance : One (Effect H) := ⟨one⟩
@[simp] lemma one_op : (1 : Effect H).op = ContinuousLinearMap.id ℂ H := rfl
@[simp] lemma one_apply (x : H) : (1 : Effect H) x = x := by
  show (1 : Effect H).op x = x; rfl

/-- The Löwner order on effects: `E ≤ F` iff `⟨x, E x⟩.re ≤ ⟨x, F x⟩.re` for all `x`. -/
instance : LE (Effect H) where
  le E F := ∀ x : H, (inner (𝕜 := ℂ) x (E x)).re ≤ (inner (𝕜 := ℂ) x (F x)).re
@[simp] lemma le_def (E F : Effect H) :
    E ≤ F ↔ ∀ x : H, (inner (𝕜 := ℂ) x (E x)).re ≤ (inner (𝕜 := ℂ) x (F x)).re :=
  Iff.rfl

/-- The zero effect is less than or equal to any effect. -/
lemma zero_le (E : Effect H) : (0 : Effect H) ≤ E := by
  intro x
  simp
  exact E.nonneg x

/-- Any effect is less than or equal to the identity effect. -/
lemma le_one' (E : Effect H) : E ≤ (1 : Effect H) := by
  intro x
  show (inner (𝕜 := ℂ) x (E x)).re ≤ (inner (𝕜 := ℂ) x ((1 : Effect H) x)).re
  simp only [one_apply]
  exact E.le_one x

/-- Reflexivity of the Löwner order. -/
lemma le_refl' (E : Effect H) : E ≤ E := fun _ => le_refl _

/-- Transitivity of the Löwner order. -/
lemma le_trans' {E F G : Effect H} (hEF : E ≤ F) (hFG : F ≤ G) : E ≤ G :=
  fun x => (hEF x).trans (hFG x)

/-- Two effects are equal as subtypes iff their underlying operators are equal. -/
lemma ext_op {E F : Effect H} (h : E.op = F.op) : E = F := by
  cases E; cases F; simp at h; subst h; rfl

/-- Extensionality: two effects are equal if they agree pointwise as operators. -/
@[ext] lemma ext {E F : Effect H} (h : ∀ x, E x = F x) : E = F := by
  apply ext_op
  exact ContinuousLinearMap.ext h

end Effect

end Busch
