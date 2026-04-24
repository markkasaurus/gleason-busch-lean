import Classical.Projection

noncomputable section

namespace RankOne

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

/-- Rank-one projection onto `ℂ ∙ x` as an element of `Projection H`. -/
def rankOneProjection (x : H) (_hx : x ≠ 0) : Projection H := by
  classical
  haveI : CompleteSpace (↥(ℂ ∙ x : Submodule ℂ H)) := by infer_instance
  haveI : (ℂ ∙ x : Submodule ℂ H).HasOrthogonalProjection := by infer_instance
  let K : Submodule ℂ H := (ℂ ∙ x)
  refine ⟨K.starProjection, ?_, ?_⟩
  ·
    exact (Submodule.isIdempotentElem_starProjection (K := K))
  ·
    intro u v
    have hv : v - K.starProjection v ∈ Kᗮ := by
      exact Submodule.sub_starProjection_mem_orthogonal (K := K) v
    have hu : K.starProjection u ∈ K := by
      exact Submodule.starProjection_apply_mem (U := K) u
    exact (Submodule.mem_orthogonal (K := K) (v := v - K.starProjection v)).1 hv
      (K.starProjection u) hu

end RankOne
