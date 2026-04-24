/-
# Busch/GenFrameFunction.lean — Generalized Frame Functions on Effects
A *generalized frame function* on `H` assigns a real number to every effect,
is nonneg, normalized (μ(1) = 1), and additive on orthogonal (summable) sums:
`μ(E ⊕ F) = μ(E) + μ(F)` when `E, F` summable.
This definition is structurally analogous to the classical projection-valued
frame-function notion, but operates on `Effect H`. Since every projection is an
idempotent effect, any generalized frame function restricts to a classical
frame function.
**Reference**: Busch, P. (2003). "Quantum States and Generalized Observables:
A Simple Proof of Gleason's Theorem." Phys. Rev. Lett. 91, 120403.
-/
import Busch.EffectOrthogonal

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A generalized frame function on effects. -/
structure GenFrameFunction (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The underlying function. -/
  μ : Effect H → ℝ
  /-- Nonnegativity. -/
  nonneg : ∀ E : Effect H, 0 ≤ μ E
  /-- Additivity on orthogonal sums. -/
  additive : ∀ (E F : Effect H) (h : Effect.Summable E F),
      μ (Effect.orthoSum E F h) = μ E + μ F
  /-- Normalization: `μ(1) = 1`. -/
  normalized : μ 1 = 1

namespace GenFrameFunction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance : CoeFun (GenFrameFunction H) (fun _ => Effect H → ℝ) := ⟨GenFrameFunction.μ⟩
@[simp] lemma coe_mk (μ : Effect H → ℝ) (h1 h2 h3) :
    (⟨μ, h1, h2, h3⟩ : GenFrameFunction H).μ = μ := rfl

/-- The frame value at zero is zero. -/
lemma μ_zero (f : GenFrameFunction H) : f.μ 0 = 0 := by
  have h_sum : Effect.orthoSum (0 : Effect H) (0 : Effect H)
      (Effect.summable_zero_left _) = (0 : Effect H) :=
    Effect.orthoSum_zero_left _
  have h_add := f.additive (0 : Effect H) (0 : Effect H) (Effect.summable_zero_left _)
  rw [h_sum] at h_add
  linarith

/-- The frame value at the orthocomplement: μ(E') = 1 - μ(E). -/
lemma μ_orthoComplement (f : GenFrameFunction H) (E : Effect H) :
    f.μ (Effect.orthoComplement E) = 1 - f.μ E := by
  have h_sum := Effect.orthoSum_orthoComplement E
  have h_add := f.additive E (Effect.orthoComplement E) (Effect.summable_orthoComplement E)
  rw [h_sum] at h_add
  rw [f.normalized] at h_add
  linarith

/-- Frame value at `1`. -/
@[simp] lemma μ_one (f : GenFrameFunction H) : f.μ 1 = 1 := f.normalized

/-- Every generalized frame function value is in [0, 1]. -/
lemma μ_le_one (f : GenFrameFunction H) (E : Effect H) : f.μ E ≤ 1 := by
  have h_add := f.additive E (Effect.orthoComplement E) (Effect.summable_orthoComplement E)
  have h_sum := Effect.orthoSum_orthoComplement E
  rw [h_sum] at h_add
  rw [f.normalized] at h_add
  have h_nonneg_comp : 0 ≤ f.μ (Effect.orthoComplement E) := f.nonneg _
  linarith

/-- The frame value lies in [0, 1]. -/
lemma μ_mem_unitInterval (f : GenFrameFunction H) (E : Effect H) :
    f.μ E ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨f.nonneg E, f.μ_le_one E⟩

end GenFrameFunction

end Busch
