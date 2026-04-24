import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

noncomputable section

def Projection (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  { P : H →L[ℂ] H //
      P * P = P ∧ ∀ x y : H, inner (𝕜 := ℂ) (P x) (y - P y) = (0 : ℂ) }

namespace Projection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
@[simp] lemma idempotent (P : Projection H) : P.1 * P.1 = P.1 := P.2.1

lemma inner_err (P : Projection H) (x y : H) :
    inner (𝕜 := ℂ) (P.1 x) (y - P.1 y) = (0 : ℂ) := P.2.2 x y

def orthogonal (P Q : Projection H) : Prop := P.1 * Q.1 = 0

def SelfAdjointOp (T : H →L[ℂ] H) : Prop :=
  ∀ x y : H, inner (𝕜 := ℂ) (T x) y = inner (𝕜 := ℂ) x (T y)

/-- From the defining orthogonality axiom, `P` is self-adjoint in the inner-product sense. -/
lemma selfAdjointOp (P : Projection H) : SelfAdjointOp P.1 := by
  intro x y
  have hxy :
      inner (𝕜 := ℂ) (P.1 x) y - inner (𝕜 := ℂ) (P.1 x) (P.1 y) = 0 := by
    simpa [inner_sub_right] using (P.inner_err x y)
  have h1 :
      inner (𝕜 := ℂ) (P.1 x) y = inner (𝕜 := ℂ) (P.1 x) (P.1 y) :=
    sub_eq_zero.mp hxy
  have hyx0 : inner (𝕜 := ℂ) (P.1 y) (x - P.1 x) = (0 : ℂ) := P.inner_err y x
  have h0 : inner (𝕜 := ℂ) (x - P.1 x) (P.1 y) = (0 : ℂ) := by
    exact (inner_eq_zero_symm.mp hyx0)
  have hx :
      inner (𝕜 := ℂ) x (P.1 y) - inner (𝕜 := ℂ) (P.1 x) (P.1 y) = 0 := by
    simpa [inner_sub_left] using h0
  have h2 :
      inner (𝕜 := ℂ) x (P.1 y) = inner (𝕜 := ℂ) (P.1 x) (P.1 y) :=
    sub_eq_zero.mp hx
  calc
    inner (𝕜 := ℂ) (P.1 x) y
        = inner (𝕜 := ℂ) (P.1 x) (P.1 y) := h1
    _   = inner (𝕜 := ℂ) x (P.1 y) := h2.symm

def one : Projection H :=
  ⟨(1 : H →L[ℂ] H), by
    refine ⟨by simp, ?_⟩
    intro x y
    simp⟩

def zero : Projection H :=
  ⟨(0 : H →L[ℂ] H), by
    refine ⟨by simp, ?_⟩
    intro x y
    simp⟩

/-- If `P ⟂ Q` then `inner (P x) (Q y) = 0`. -/
lemma inner_orthogonal (P Q : Projection H) (h : orthogonal P Q) (x y : H) :
    inner (𝕜 := ℂ) (P.1 x) (Q.1 y) = (0 : ℂ) := by
  have hPQy : P.1 (Q.1 y) = 0 := by
    have := congrArg (fun T : H →L[ℂ] H => T y) h
    simpa using this
  have hSA := selfAdjointOp (H := H) P x (Q.1 y)
  simpa [SelfAdjointOp, hPQy] using hSA

/-- Orthogonality is symmetric for projections. -/
lemma orthogonal_comm (P Q : Projection H) (h : orthogonal P Q) : orthogonal Q P := by
  ext x
  set z : H := Q.1 (P.1 x)
  have hzQmul : (Q.1 * Q.1) (P.1 x) = Q.1 (P.1 x) :=
    congrArg (fun T : H →L[ℂ] H => T (P.1 x)) (Q.idempotent)
  have hzQ : Q.1 z = z := by
    dsimp [z]
    have hzQmul' := hzQmul
    rw [ContinuousLinearMap.mul_apply] at hzQmul'
    exact hzQmul'
  have hPz' : (P.1 * Q.1) (P.1 x) = (0 : H) := by
    exact congrArg (fun T : H →L[ℂ] H => T (P.1 x)) h
  have hPz : P.1 z = 0 := by
    simpa [z, ContinuousLinearMap.mul_apply] using hPz'
  have hz_inner : inner (𝕜 := ℂ) z z = (0 : ℂ) := by
    have hQsa := selfAdjointOp (H := H) Q (P.1 x) z
    have hPsa := selfAdjointOp (H := H) P x z
    calc
      inner (𝕜 := ℂ) z z
          = inner (𝕜 := ℂ) (P.1 x) (Q.1 z) := by
              simpa [SelfAdjointOp, z] using hQsa
      _   = inner (𝕜 := ℂ) (P.1 x) z := by simp [hzQ]
      _   = inner (𝕜 := ℂ) x (P.1 z) := by
              simpa [SelfAdjointOp] using hPsa
      _   = 0 := by simp [hPz]
  have z0 : z = 0 := (inner_self_eq_zero.mp hz_inner)
  simpa [z] using z0

/-- Idempotence of the sum of orthogonal projections. -/
lemma add_idempotent (P Q : Projection H) (h : orthogonal P Q) :
    (P.1 + Q.1) * (P.1 + Q.1) = (P.1 + Q.1) := by
  have hPQ : P.1 * Q.1 = 0 := h
  have hQP : Q.1 * P.1 = 0 := orthogonal_comm (H := H) P Q h
  simp [mul_add, add_mul, P.idempotent, Q.idempotent, hPQ, hQP]

/-- Inner-product axiom for the sum of orthogonal projections. -/
lemma add_inner (P Q : Projection H) (h : orthogonal P Q) :
    ∀ x y : H,
      inner (𝕜 := ℂ) ((P.1 + Q.1) x) (y - (P.1 + Q.1) y) = (0 : ℂ) := by
  intro x y
  have hPQ : P.1 * Q.1 = 0 := h
  have hQP : Q.1 * P.1 = 0 := orthogonal_comm (H := H) P Q h
  have hPQinner :
      inner (𝕜 := ℂ) (P.1 x) (Q.1 y) = 0 := inner_orthogonal (H := H) P Q hPQ x y
  have hQPinner :
      inner (𝕜 := ℂ) (Q.1 x) (P.1 y) = 0 := inner_orthogonal (H := H) Q P hQP x y
  have hPy :
      inner (𝕜 := ℂ) (P.1 x) y = inner (𝕜 := ℂ) (P.1 x) (P.1 y) := by
    have : inner (𝕜 := ℂ) (P.1 x) y - inner (𝕜 := ℂ) (P.1 x) (P.1 y) = 0 := by
      simpa [inner_sub_right] using (P.inner_err x y)
    exact sub_eq_zero.mp this
  have hQy :
      inner (𝕜 := ℂ) (Q.1 x) y = inner (𝕜 := ℂ) (Q.1 x) (Q.1 y) := by
    have : inner (𝕜 := ℂ) (Q.1 x) y - inner (𝕜 := ℂ) (Q.1 x) (Q.1 y) = 0 := by
      simpa [inner_sub_right] using (Q.inner_err x y)
    exact sub_eq_zero.mp this
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
  calc
    inner (𝕜 := ℂ) (P.1 x + Q.1 x) (y - (P.1 y + Q.1 y))
        = inner (𝕜 := ℂ) (P.1 x) y - inner (𝕜 := ℂ) (P.1 x) (P.1 y)
          - inner (𝕜 := ℂ) (P.1 x) (Q.1 y)
          + (inner (𝕜 := ℂ) (Q.1 x) y - inner (𝕜 := ℂ) (Q.1 x) (P.1 y)
          - inner (𝕜 := ℂ) (Q.1 x) (Q.1 y)) := by
            simp only [inner_add_left, inner_sub_right, inner_add_right]
            ring_nf
    _ = 0 := by
      rw [hPy, hQy, hPQinner, hQPinner]
      ring_nf

def add (P Q : Projection H) (h : orthogonal P Q) : Projection H :=
  ⟨P.1 + Q.1, by
    refine ⟨add_idempotent (H := H) P Q h, add_inner (H := H) P Q h⟩⟩

/-- Self-adjointness of the sum of orthogonal projections. -/
lemma add_selfAdjointOp (P Q : Projection H) (h : orthogonal P Q) :
    SelfAdjointOp (add (H := H) P Q h).1 := by
  intro x y
  have hP := selfAdjointOp (H := H) P x y
  have hQ := selfAdjointOp (H := H) Q x y
  simp only [add, ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
  rw [hP, hQ]

end Projection
