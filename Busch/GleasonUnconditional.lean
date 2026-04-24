/-
# Busch/GleasonUnconditional.lean — Unconditional Forward Direction of Gleason
Final assembly. Discharges `TracePairingRiesz` unconditionally by:
1. Wrapping `muSA f` as an ℝ-linear map `muSA_as_functional f : SAOp H →ₗ[ℝ] ℝ`.
2. Showing it agrees with `f.μ` on effect operators.
3. Applying `riesz_representation_trace` to get ρ.
-/
import Busch.RieszSA
import Busch.SALinearity
import Busch.GleasonFull
import Busch.TraceRepresentation

noncomputable section

namespace Busch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [instFiniteDimensional : FiniteDimensional ℂ H]

open GenFrameFunction

/-! ### Every `SAOp` admits a `SABounded` witness -/
/-- Canonical bound: `‖A.op‖ + 1`. -/
def SAOp.bound (A : SAOp H) : ℝ := ‖A.op‖ + 1

lemma SAOp.bound_pos (A : SAOp H) : 0 < A.bound := by
  unfold SAOp.bound; linarith [norm_nonneg A.op]

lemma SAOp.bound_ge_one (A : SAOp H) : 1 ≤ A.bound := by
  unfold SAOp.bound; linarith [norm_nonneg A.op]

/-- Bridge from mathlib `IsSelfAdjoint` to pointwise symmetry. -/
lemma SAOp.isSymmetric (A : SAOp H) :
    ∀ x y : H, inner (𝕜 := ℂ) (A.op x) y = inner (𝕜 := ℂ) x (A.op y) :=
  fun x y => A.sa.isSymmetric x y

/-- Self-adjoint operators are bounded by `‖A‖_op + 1` in each direction. -/
lemma SAOp.SABounded_of_SAOp (A : SAOp H) : SABounded A.op A.bound where
  isSelfAdjoint := A.isSymmetric
  lower := fun x => by
    have h_cs : |(inner (𝕜 := ℂ) x (A.op x)).re| ≤ ‖A.op x‖ * ‖x‖ :=
      calc |(inner (𝕜 := ℂ) x (A.op x)).re|
          ≤ ‖inner (𝕜 := ℂ) x (A.op x)‖ := Complex.abs_re_le_norm _
        _ ≤ ‖x‖ * ‖A.op x‖ := norm_inner_le_norm _ _
        _ = ‖A.op x‖ * ‖x‖ := by ring
    have h_opnorm : ‖A.op x‖ ≤ ‖A.op‖ * ‖x‖ := A.op.le_opNorm x
    have h_norm_sq : (inner (𝕜 := ℂ) x x).re = ‖x‖ * ‖x‖ := by
      exact_mod_cast @inner_self_eq_norm_mul_norm ℂ H _ _ _ x
    have h_bound : ‖A.op x‖ * ‖x‖ ≤ ‖A.op‖ * ‖x‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_right h_opnorm (norm_nonneg _)
    have h_norm_bound : ‖A.op‖ * ‖x‖ * ‖x‖ ≤ A.bound * (inner (𝕜 := ℂ) x x).re := by
      rw [h_norm_sq]
      unfold SAOp.bound
      have : ‖A.op‖ * ‖x‖ * ‖x‖ = ‖A.op‖ * (‖x‖ * ‖x‖) := by ring
      rw [this]
      nlinarith [norm_nonneg A.op, norm_nonneg x, mul_nonneg (norm_nonneg x) (norm_nonneg x)]
    have h_abs_neg : -(inner (𝕜 := ℂ) x (A.op x)).re ≤ |(inner (𝕜 := ℂ) x (A.op x)).re| := by
      have := abs_nonneg ((inner (𝕜 := ℂ) x (A.op x)).re)
      have h_abs := abs_le.mp (le_refl |(inner (𝕜 := ℂ) x (A.op x)).re|)
      linarith [neg_le_abs ((inner (𝕜 := ℂ) x (A.op x)).re)]
    linarith
  upper := fun x => by
    have h_cs : (inner (𝕜 := ℂ) x (A.op x)).re ≤ ‖A.op x‖ * ‖x‖ :=
      calc (inner (𝕜 := ℂ) x (A.op x)).re
          ≤ |(inner (𝕜 := ℂ) x (A.op x)).re| := le_abs_self _
        _ ≤ ‖inner (𝕜 := ℂ) x (A.op x)‖ := Complex.abs_re_le_norm _
        _ ≤ ‖x‖ * ‖A.op x‖ := norm_inner_le_norm _ _
        _ = ‖A.op x‖ * ‖x‖ := by ring
    have h_opnorm : ‖A.op x‖ ≤ ‖A.op‖ * ‖x‖ := A.op.le_opNorm x
    have h_norm_sq : (inner (𝕜 := ℂ) x x).re = ‖x‖ * ‖x‖ := by
      exact_mod_cast @inner_self_eq_norm_mul_norm ℂ H _ _ _ x
    have h_bound : ‖A.op x‖ * ‖x‖ ≤ ‖A.op‖ * ‖x‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_right h_opnorm (norm_nonneg _)
    have h_norm_bound : ‖A.op‖ * ‖x‖ * ‖x‖ ≤ A.bound * (inner (𝕜 := ℂ) x x).re := by
      rw [h_norm_sq]
      unfold SAOp.bound
      have : ‖A.op‖ * ‖x‖ * ‖x‖ = ‖A.op‖ * (‖x‖ * ‖x‖) := by ring
      rw [this]
      nlinarith [norm_nonneg A.op, norm_nonneg x, mul_nonneg (norm_nonneg x) (norm_nonneg x)]
    linarith
  pos := A.bound_pos

/-! ### `muSAVal`: evaluating `muSA f` on `SAOp H` via canonical bound -/
/-- `muSA` evaluated on `A : SAOp H` via the canonical bound. -/
def SAOp.muSAVal (f : GenFrameFunction H) (A : SAOp H) : ℝ :=
  f.muSA A.SABounded_of_SAOp

/-- `muSAVal` equals `muSA` evaluated at any other valid bound. -/
lemma SAOp.muSAVal_eq_muSA_any (f : GenFrameFunction H) (A : SAOp H) {c : ℝ}
    (h : SABounded A.op c) : A.muSAVal f = f.muSA h :=
  muSA_bound_independent f A.SABounded_of_SAOp h

/-! ### Zero: muSAVal of zero operator is zero -/
lemma SAOp.muSAVal_zero (f : GenFrameFunction H) : (0 : SAOp H).muSAVal f = 0 := by
  unfold SAOp.muSAVal
  show f.muSA (0 : SAOp H).SABounded_of_SAOp = 0
  have h_op : (0 : SAOp H).op = 0 := rfl
  have h_zero_SABounded : SABounded (0 : H →L[ℂ] H) (1 : ℝ) := zero_SABounded one_pos
  have h_bridge : f.muSA (0 : SAOp H).SABounded_of_SAOp = f.muSA h_zero_SABounded := by
    apply muSA_bound_independent
  rw [h_bridge, muSA_zero f one_pos]

/-! ### Additivity -/
/-- Additivity of `muSAVal`. -/
lemma SAOp.muSAVal_add (f : GenFrameFunction H) (A B : SAOp H) :
    (A + B).muSAVal f = A.muSAVal f + B.muSAVal f := by
  let c : ℝ := A.bound + B.bound
  have hc_pos : 0 < c := by
    show 0 < A.bound + B.bound; linarith [A.bound_pos, B.bound_pos]
  have hA_c : SABounded A.op c := by
    refine ⟨A.isSymmetric, ?_, ?_, hc_pos⟩
    · intro x
      have hA := A.SABounded_of_SAOp.lower x
      have h_self_nn : 0 ≤ (inner (𝕜 := ℂ) x x).re := @inner_self_nonneg ℂ H _ _ _ x
      have h_le : A.bound * (inner (𝕜 := ℂ) x x).re ≤ c * (inner (𝕜 := ℂ) x x).re :=
        mul_le_mul_of_nonneg_right (by show A.bound ≤ _; linarith [B.bound_pos]) h_self_nn
      linarith
    · intro x
      have hA := A.SABounded_of_SAOp.upper x
      have h_self_nn : 0 ≤ (inner (𝕜 := ℂ) x x).re := @inner_self_nonneg ℂ H _ _ _ x
      have h_le : A.bound * (inner (𝕜 := ℂ) x x).re ≤ c * (inner (𝕜 := ℂ) x x).re :=
        mul_le_mul_of_nonneg_right (by show A.bound ≤ _; linarith [B.bound_pos]) h_self_nn
      linarith
  have hB_c : SABounded B.op c := by
    refine ⟨B.isSymmetric, ?_, ?_, hc_pos⟩
    · intro x
      have hB := B.SABounded_of_SAOp.lower x
      have h_self_nn : 0 ≤ (inner (𝕜 := ℂ) x x).re := @inner_self_nonneg ℂ H _ _ _ x
      have h_le : B.bound * (inner (𝕜 := ℂ) x x).re ≤ c * (inner (𝕜 := ℂ) x x).re :=
        mul_le_mul_of_nonneg_right (by show B.bound ≤ _; linarith [A.bound_pos]) h_self_nn
      linarith
    · intro x
      have hB := B.SABounded_of_SAOp.upper x
      have h_self_nn : 0 ≤ (inner (𝕜 := ℂ) x x).re := @inner_self_nonneg ℂ H _ _ _ x
      have h_le : B.bound * (inner (𝕜 := ℂ) x x).re ≤ c * (inner (𝕜 := ℂ) x x).re :=
        mul_le_mul_of_nonneg_right (by show B.bound ≤ _; linarith [A.bound_pos]) h_self_nn
      linarith
  have h_add : f.muSA (hA_c.add hB_c) = f.muSA hA_c + f.muSA hB_c :=
    muSA_add f hA_c hB_c
  rw [A.muSAVal_eq_muSA_any f hA_c, B.muSAVal_eq_muSA_any f hB_c]
  rw [← h_add]
  exact (A + B).muSAVal_eq_muSA_any f (hA_c.add hB_c)

/-! ### Negation -/
/-- `muSAVal` of negation is the negation of `muSAVal`. -/
lemma SAOp.muSAVal_neg (f : GenFrameFunction H) (A : SAOp H) :
    (-A).muSAVal f = -(A.muSAVal f) := by
  unfold SAOp.muSAVal
  have h_neg : f.muSA A.SABounded_of_SAOp.neg = -f.muSA A.SABounded_of_SAOp :=
    muSA_neg f A.SABounded_of_SAOp
  rw [← h_neg]
  exact muSA_bound_independent f _ _

/-! ### Positive scalar -/
/-- `muSAVal (r • A) = r * muSAVal A` for `r > 0`. -/
lemma SAOp.muSAVal_smul_pos (f : GenFrameFunction H) (A : SAOp H) {r : ℝ} (hr : 0 < r) :
    (r • A).muSAVal f = r * A.muSAVal f := by
  unfold SAOp.muSAVal
  have h_smul := muSA_smul_nn f A.SABounded_of_SAOp hr
  rw [← h_smul]
  exact muSA_bound_independent f _ _

/-! ### Full scalar compatibility via trichotomy -/
/-- `muSAVal (r • A) = r * muSAVal A` for all `r : ℝ`. -/
lemma SAOp.muSAVal_smul (f : GenFrameFunction H) (r : ℝ) (A : SAOp H) :
    (r • A).muSAVal f = r * A.muSAVal f := by
  rcases lt_trichotomy r 0 with hr_neg | hr_zero | hr_pos
  ·
    have h_neg_r_pos : (0 : ℝ) < -r := by linarith
    have h_module : r • A = -((-r) • A) := by
      apply SAOp.ext
      simp only [SAOp.op_smul_real, SAOp.op_neg]
      push_cast
      module
    rw [h_module]
    rw [SAOp.muSAVal_neg, SAOp.muSAVal_smul_pos f A h_neg_r_pos]
    ring
  ·
    subst hr_zero
    have h_zero : (0 : ℝ) • A = 0 := by
      apply SAOp.ext
      show ((0 : ℝ) : ℂ) • A.op = (0 : SAOp H).op
      show ((0 : ℝ) : ℂ) • A.op = 0
      simp
    rw [h_zero, SAOp.muSAVal_zero]
    ring
  ·
    exact SAOp.muSAVal_smul_pos f A hr_pos

/-! ### The functional -/
/-- `muSA f` packaged as an ℝ-linear map on `SAOp H`. -/
noncomputable def muSA_as_functional (f : GenFrameFunction H) : SAOp H →ₗ[ℝ] ℝ where
  toFun A := A.muSAVal f
  map_add' := SAOp.muSAVal_add f
  map_smul' := SAOp.muSAVal_smul f
@[simp] lemma muSA_as_functional_apply (f : GenFrameFunction H) (A : SAOp H) :
    muSA_as_functional f A = A.muSAVal f := rfl

/-! ### Pass-through on effects -/
omit instFiniteDimensional in
/-- Every effect is self-adjoint in mathlib's sense. -/
lemma Effect.toIsSelfAdjoint (E : Effect H) : IsSelfAdjoint E.op :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr E.isSelfAdjoint

/-- Lift effect to `SAOp H`. -/
def Effect.toSAOp (E : Effect H) : SAOp H := ⟨E.op, E.toIsSelfAdjoint⟩
@[simp] lemma Effect.toSAOp_op (E : Effect H) : E.toSAOp.op = E.op := rfl

/-- Pass-through: `muSA_as_functional f E.toSAOp = f.μ E`. -/
theorem muSA_as_functional_effect (f : GenFrameFunction H) (E : Effect H) :
    muSA_as_functional f E.toSAOp = f.μ E := by
  show E.toSAOp.muSAVal f = f.μ E
  unfold SAOp.muSAVal
  have h_bound_pos : 0 < E.toSAOp.bound := E.toSAOp.bound_pos
  have h_bound_ge_one : 1 ≤ E.toSAOp.bound := E.toSAOp.bound_ge_one
  have h_effect := f.muSA_effect E h_bound_pos h_bound_ge_one
  rw [← h_effect]

/-! ### Unconditional forward direction -/
/-- The trace-pairing Riesz hypothesis for `f`, discharged from the
finite-dimensional Hilbert-Schmidt representation theorem. -/
theorem tracePairingRiesz_unconditional (f : GenFrameFunction H) :
    TracePairingRiesz f := by
  obtain ⟨ρ, hρ_sa, hρ_trace⟩ := riesz_representation_trace (muSA_as_functional f)
  refine ⟨ρ, hρ_sa.isSymmetric, ?_⟩
  intro E
  have h_riesz := hρ_trace E.toSAOp
  rw [muSA_as_functional_effect f E] at h_riesz
  simpa [Effect.toSAOp_op] using h_riesz

/-- Gleason's theorem in Busch's effects formulation. -/
theorem gleason_busch_unconditional (hdim : 2 ≤ Module.finrank ℂ H)
    (f : GenFrameFunction H) : GleasonTarget H f :=
  gleason_target_from_trace_pairing hdim f (tracePairingRiesz_unconditional f)

end Busch
