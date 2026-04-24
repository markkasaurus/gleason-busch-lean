/-
# Busch/RieszSA.lean — Riesz Representation on Self-Adjoint Operators
Applies mathlib's Fréchet-Riesz representation theorem to the finite-dim real
Hilbert space `(SAOp H, hsInner)` constructed in `SASubspace.lean`.
Main results:
* `riesz_representation_SA`: every ℝ-linear functional `L : SAOp H →ₗ[ℝ] ℝ`
  has a unique representing element `ρ : SAOp H` with `L A = ⟨ρ, A⟩_HS`.
* `riesz_representation_trace`: repackaged as `L A = reTr (ρ.op * A.op)`,
  i.e. the trace-pairing form used for Gleason.
In finite-dim every linear map is continuous, so we can pass from
`LinearMap` to `ContinuousLinearMap` automatically via
`LinearMap.toContinuousLinearMap`.
-/
import Busch.SASubspace
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

/-! ### Riesz representation as an existential -/
/-- **Fréchet-Riesz on `SAOp H`**: every ℝ-linear functional on SA operators has a
unique representing element via the HS inner product. -/
theorem riesz_representation_SA (L : SAOp H →ₗ[ℝ] ℝ) :
    ∃! ρ : SAOp H, ∀ A : SAOp H, L A = inner (𝕜 := ℝ) ρ A := by
  let L_cont : SAOp H →L[ℝ] ℝ := L.toContinuousLinearMap
  have h_dual := (InnerProductSpace.toDual ℝ (SAOp H)).surjective L_cont
  obtain ⟨ρ, hρ⟩ := h_dual
  refine ⟨ρ, ?_, ?_⟩
  · intro A
    have := congr_fun (congr_arg DFunLike.coe hρ) A
    show L A = inner (𝕜 := ℝ) ρ A
    show L_cont A = inner (𝕜 := ℝ) ρ A
    simpa [InnerProductSpace.toDual_apply_apply, L_cont] using this.symm
  · intro ρ' hρ'
    have h_eq : ∀ A, inner (𝕜 := ℝ) ρ A = inner (𝕜 := ℝ) ρ' A := by
      intro A
      rw [← hρ' A]
      show inner (𝕜 := ℝ) ρ A = L A
      have := congr_fun (congr_arg DFunLike.coe hρ) A
      show inner (𝕜 := ℝ) ρ A = L_cont A
      simpa [InnerProductSpace.toDual_apply_apply] using this
    exact (ext_inner_right ℝ h_eq).symm

/-! ### Trace-pairing form -/
/-- **Riesz as trace pairing**: every ℝ-linear functional on `SAOp H` can be
represented as `L A = reTr (ρ.op * A.op)` for a self-adjoint `ρ`. -/
theorem riesz_representation_trace (L : SAOp H →ₗ[ℝ] ℝ) :
    ∃ ρ : H →L[ℂ] H, IsSelfAdjoint ρ ∧
      ∀ A : SAOp H, L A = reTr (ρ * A.op) := by
  obtain ⟨ρSA, hρSA, _⟩ := riesz_representation_SA L
  refine ⟨ρSA.op, ρSA.sa, ?_⟩
  intro A
  rw [hρSA A]
  show inner (𝕜 := ℝ) ρSA A = reTr (ρSA.op * A.op)
  rw [SAOp.inner_eq_hsInner]
  rfl

end Busch
