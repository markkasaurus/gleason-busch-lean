/-
# Busch/ClassicalBridge.lean — Bridge from Effects to Classical Frame Functions
Every classical projection `P : Projection H` yields an effect
`Effect.ofClassicalProjection P : Effect H`. This file establishes the
translation:
* classical `Projection.zero ↦ (0 : Effect H)`
* classical `Projection.one ↦ (1 : Effect H)`
* classical orthogonality `P ⟂ Q ↦ Busch summability`
* classical sum `Projection.add P Q h ↦ Busch `orthoSum``
Consequence: every Busch `GenFrameFunction H` restricts to a classical
`FrameFunction H`.
This is a compatibility bridge between the effects formulation and the
projection language.
-/
import Busch.ProjectionRestriction
import Classical.Projection
import Classical.FrameFunction

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

/-! ### Lifting classical projections to effects -/
namespace Effect

/-- Every classical `Projection H` is an effect. -/
def ofClassicalProjection (P : Projection H) : Effect H where
  op := P.1
  isSelfAdjoint := Projection.selfAdjointOp P
  nonneg x := by
    have hIdem : P.1 * P.1 = P.1 := P.2.1
    have hSA : ∀ a b : H, inner (𝕜 := ℂ) (P.1 a) b = inner (𝕜 := ℂ) a (P.1 b) :=
      Projection.selfAdjointOp P
    have hdiag := inner_self_selfAdjoint_idempotent P.1 hSA hIdem x
    rw [hdiag]
    exact @inner_self_nonneg ℂ H _ _ _ (P.1 x)
  le_one x := by
    have hIdem : P.1 * P.1 = P.1 := P.2.1
    have hSA : ∀ a b : H, inner (𝕜 := ℂ) (P.1 a) b = inner (𝕜 := ℂ) a (P.1 b) :=
      Projection.selfAdjointOp P
    exact re_inner_le_self_of_selfAdjoint_idempotent P.1 hSA hIdem x
omit [FiniteDimensional ℂ H] in
@[simp] lemma ofClassicalProjection_op (P : Projection H) :
    (ofClassicalProjection P).op = P.1 := rfl

omit [FiniteDimensional ℂ H] in
/-- The lifted projection is a projection-effect (idempotent). -/
lemma ofClassicalProjection_isProjection (P : Projection H) :
    IsProjection (ofClassicalProjection P) := by
  show (ofClassicalProjection P).op * (ofClassicalProjection P).op = (ofClassicalProjection P).op
  simp only [ofClassicalProjection_op]
  exact P.2.1

end Effect

/-! ### Wrapping as `ProjectionEffect` -/
namespace ProjectionEffect

/-- Every classical `Projection H` is a Busch projection-effect. -/
def ofClassicalProjection (P : Projection H) : ProjectionEffect H where
  effect := Effect.ofClassicalProjection P
  is_projection := Effect.ofClassicalProjection_isProjection P

omit [FiniteDimensional ℂ H] in
@[simp] lemma ofClassicalProjection_effect (P : Projection H) :
    (ofClassicalProjection P).effect = Effect.ofClassicalProjection P := rfl

omit [FiniteDimensional ℂ H] in
@[simp] lemma ofClassicalProjection_op (P : Projection H) :
    (ofClassicalProjection P).effect.op = P.1 := rfl

omit [FiniteDimensional ℂ H] in
/-- Classical orthogonality of projections translates to Busch projection-effect
orthogonality. -/
lemma orthogonal_of_classical {P Q : Projection H} (h : Projection.orthogonal P Q) :
    (ofClassicalProjection P).orthogonal (ofClassicalProjection Q) := by
  show (Effect.ofClassicalProjection P).op * (Effect.ofClassicalProjection Q).op = 0
  simp only [Effect.ofClassicalProjection_op]
  exact h

end ProjectionEffect

/-! ### Summability and orthogonal sums from classical data -/
namespace Effect

omit [FiniteDimensional ℂ H] in
/-- Classical orthogonality of projections implies Busch summability of the
lifted effects. -/
lemma summable_ofClassical {P Q : Projection H} (h : Projection.orthogonal P Q) :
    Summable (ofClassicalProjection P) (ofClassicalProjection Q) :=
  ProjectionEffect.summable_of_orthogonal
    (ProjectionEffect.ofClassicalProjection P)
    (ProjectionEffect.ofClassicalProjection Q)
    (ProjectionEffect.orthogonal_of_classical h)

end Effect

/-! ### Lifting the classical zero/one/add -/
namespace Effect

omit [FiniteDimensional ℂ H] in
/-- The classical zero projection lifts to the zero effect. -/
@[simp] lemma ofClassicalProjection_zero :
    ofClassicalProjection (Projection.zero : Projection H) = (0 : Effect H) := by
  apply Effect.ext
  intro x
  show (Projection.zero : Projection H).1 x = (0 : Effect H).op x
  show (0 : H →L[ℂ] H) x = (0 : Effect H).op x
  simp

omit [FiniteDimensional ℂ H] in
/-- The classical identity projection lifts to the identity effect. -/
@[simp] lemma ofClassicalProjection_one :
    ofClassicalProjection (Projection.one : Projection H) = (1 : Effect H) := by
  apply Effect.ext
  intro x
  show (Projection.one : Projection H).1 x = (1 : Effect H).op x
  show (1 : H →L[ℂ] H) x = (1 : Effect H).op x
  simp

omit [FiniteDimensional ℂ H] in
/-- The classical sum of orthogonal projections lifts to the Busch orthogonal sum. -/
lemma ofClassicalProjection_add {P Q : Projection H} (h : Projection.orthogonal P Q) :
    ofClassicalProjection (Projection.add P Q h) =
      orthoSum (ofClassicalProjection P) (ofClassicalProjection Q)
        (summable_ofClassical h) := by
  apply Effect.ext
  intro x
  show (Projection.add P Q h).1 x
      = (ofClassicalProjection P).op x + (ofClassicalProjection Q).op x
  show (P.1 + Q.1) x = P.1 x + Q.1 x
  rfl

end Effect

/-! ### Classical frame function from a Busch generalized frame function -/
namespace GenFrameFunction

/-- **Restriction theorem**: every Busch generalized frame function restricts to
a classical frame function on projections. -/
def toFrameFunction (f : GenFrameFunction H) : FrameFunction H where
  μ P := f.μ (Effect.ofClassicalProjection P)
  nonneg P := f.nonneg _
  additive P Q h := by
    rw [Effect.ofClassicalProjection_add h]
    exact f.additive _ _ (Effect.summable_ofClassical h)
  normalized := by
    show f.μ (Effect.ofClassicalProjection Projection.one) = 1
    rw [Effect.ofClassicalProjection_one]
    exact f.normalized
@[simp] lemma toFrameFunction_apply (f : GenFrameFunction H) (P : Projection H) :
    (f.toFrameFunction).μ P = f.μ (Effect.ofClassicalProjection P) := rfl

end GenFrameFunction

end Busch
