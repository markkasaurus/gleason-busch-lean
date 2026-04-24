/-
# Busch/SASubspace.lean — Self-Adjoint Operators as a Real Inner Product Space
Defines `SAOp H` — a structure wrapping `{A : H →L[ℂ] H // IsSelfAdjoint A}`
— and equips it with:
* `AddCommGroup`, `Module ℝ` (via `Function.Injective` pattern)
* `InnerProductSpace ℝ` (via `InnerProductSpace.ofCore` and the
  positive-definite HS pairing from `HSPositiveDefinite.lean`)
* `FiniteDimensional ℝ` (via the `FiniteDimensional ℂ (H →L[ℂ] H)` instance
  combined with `FiniteDimensional.trans ℝ ℂ`)
The norm on `SAOp H` is the **Hilbert-Schmidt norm** — `‖A‖ = √(reTr (A * A))`.
This is distinct from the operator norm on the ambient `H →L[ℂ] H`; we use the
structure-wrapper pattern specifically to avoid inheriting the operator norm.
After this file, `SAOp H` is a real Hilbert space (finite-dim ⇒ complete) with
HS inner product, ready for Riesz representation.
-/
import Busch.HSPositiveDefinite
import Mathlib.Algebra.Star.SelfAdjoint

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

/-- **Self-adjoint operator** on `H`, bundled with its self-adjoint proof. -/
structure SAOp (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H] where
  op : H →L[ℂ] H
  sa : IsSelfAdjoint op

namespace SAOp
@[ext] lemma ext {a b : SAOp H} (h : a.op = b.op) : a = b := by
  cases a; cases b; simp at h; subst h; rfl

/-! ### Algebraic instances -/
instance : Zero (SAOp H) := ⟨0, IsSelfAdjoint.zero _⟩

instance : Add (SAOp H) := ⟨fun a b => ⟨a.op + b.op, a.sa.add b.sa⟩⟩

instance : Neg (SAOp H) := ⟨fun a => ⟨-a.op, a.sa.neg⟩⟩

instance : Sub (SAOp H) := ⟨fun a b => ⟨a.op - b.op, by
  rw [sub_eq_add_neg]; exact a.sa.add b.sa.neg⟩⟩

instance : SMul ℕ (SAOp H) := ⟨fun n a => ⟨n • a.op, by
  induction n with
  | zero => show IsSelfAdjoint (0 • a.op); rw [zero_smul]; exact IsSelfAdjoint.zero _
  | succ k ih => rw [succ_nsmul]; exact ih.add a.sa⟩⟩

instance : SMul ℤ (SAOp H) := ⟨fun n a => ⟨n • a.op, by
  rcases n with n | n
  · rw [Int.ofNat_eq_natCast, natCast_zsmul]
    exact ((inferInstance : SMul ℕ (SAOp H)).smul n a).sa
  · rw [negSucc_zsmul]
    exact IsSelfAdjoint.neg ((inferInstance : SMul ℕ (SAOp H)).smul (n + 1) a).sa⟩⟩

instance : SMul ℝ (SAOp H) := ⟨fun r a => ⟨(r : ℂ) • a.op, by
  have hr : IsSelfAdjoint ((r : ℂ)) := Complex.conj_ofReal r
  exact hr.smul a.sa⟩⟩
@[simp] lemma op_zero : (0 : SAOp H).op = 0 := rfl
@[simp] lemma op_add (a b : SAOp H) : (a + b).op = a.op + b.op := rfl
@[simp] lemma op_neg (a : SAOp H) : (-a).op = -a.op := rfl
@[simp] lemma op_sub (a b : SAOp H) : (a - b).op = a.op - b.op := rfl
@[simp] lemma op_nsmul (n : ℕ) (a : SAOp H) : (n • a).op = n • a.op := rfl
@[simp] lemma op_zsmul (n : ℤ) (a : SAOp H) : (n • a).op = n • a.op := rfl
@[simp] lemma op_smul_real (r : ℝ) (a : SAOp H) : (r • a).op = (r : ℂ) • a.op := rfl

/-- **AddCommGroup** via `Function.Injective` pattern. -/
instance : AddCommGroup (SAOp H) :=
  Function.Injective.addCommGroup SAOp.op
    (fun _ _ h => ext h)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- **Module ℝ** via `Function.Injective.module`. -/
instance : Module ℝ (SAOp H) :=
  Function.Injective.module ℝ
    { toFun := SAOp.op, map_zero' := rfl, map_add' := fun _ _ => rfl }
    (fun _ _ h => ext h)
    (fun _ _ => rfl)

/-! ### Inner product structure -/
/-- **NormedAddCommGroup on `SAOp H`** via the HS inner product. -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (SAOp H) :=
  letI : InnerProductSpace.Core ℝ (SAOp H) :=
    { inner := fun a b => hsInner a.op b.op
      conj_inner_symm := fun a b => by
        show (starRingEnd ℝ) (hsInner b.op a.op) = hsInner a.op b.op
        rw [hsInner_comm b.op a.op]; rfl
      re_inner_nonneg := fun a => by
        show (0 : ℝ) ≤ RCLike.re (hsInner a.op a.op)
        exact hsInner_self_nonneg_of_isSelfAdjoint a.op a.sa
      add_left := fun a b c => by
        show hsInner (a + b).op c.op = hsInner a.op c.op + hsInner b.op c.op
        show hsInner (a.op + b.op) c.op = _
        exact hsInner_add_left _ _ _
      smul_left := fun a b r => by
        show hsInner ((r • a).op) b.op = (starRingEnd ℝ) r * hsInner a.op b.op
        show hsInner ((r : ℂ) • a.op) b.op = (r : ℝ) * hsInner a.op b.op
        rw [hsInner_smul_left]
      definite := fun a h => by
        have h_op : a.op = 0 :=
          (hsInner_self_eq_zero_iff_isSelfAdjoint a.op a.sa).mp h
        exact ext h_op }
  this.toNormedAddCommGroup

/-- **InnerProductSpace ℝ** on `SAOp H`. -/
noncomputable instance instInnerProductSpace : InnerProductSpace ℝ (SAOp H) :=
  InnerProductSpace.ofCore _

/-- The inner product on `SAOp H` is the HS pairing on the underlying operators. -/
@[simp] lemma inner_eq_hsInner (a b : SAOp H) :
    inner (𝕜 := ℝ) a b = hsInner a.op b.op := rfl

/-! ### Finite-dimensionality -/
/-- Embedding `SAOp H ↪ H →L[ℂ] H` as an ℝ-linear map. -/
def toAmbient : SAOp H →ₗ[ℝ] H →L[ℂ] H where
  toFun := SAOp.op
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma toAmbient_injective : Function.Injective (toAmbient : SAOp H → _) := by
  intro a b h
  exact ext h

/-- **`FiniteDimensional ℝ (SAOp H)`** via `FiniteDimensional.trans ℝ ℂ` and
`FiniteDimensional.of_injective`. -/
noncomputable instance instFiniteDimensional : FiniteDimensional ℝ (SAOp H) := by
  haveI : FiniteDimensional ℝ (H →L[ℂ] H) := FiniteDimensional.trans ℝ ℂ (H →L[ℂ] H)
  exact FiniteDimensional.of_injective (toAmbient : SAOp H →ₗ[ℝ] H →L[ℂ] H) toAmbient_injective

end SAOp

end Busch
