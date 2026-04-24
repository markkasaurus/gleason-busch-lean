import Lake
open Lake DSL

package gleasonBuschStandalone where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.26.0"

@[default_target]
lean_lib GleasonBuschStandalone where
  roots := #[
    `Classical.Projection,
    `Classical.RankOneProjection,
    `Classical.FrameFunction,
    `Busch.Effect,
    `Busch.EffectOrthogonal,
    `Busch.GenFrameFunction,
    `Busch.ProjectionRestriction,
    `Busch.EffectScalar,
    `Busch.Monotonicity,
    `Busch.Homogeneity,
    `Busch.NatScalar,
    `Busch.DyadicHomogeneity,
    `Busch.DyadicRational,
    `Busch.RealHomogeneity,
    `Busch.ConvexLinearity,
    `Busch.ConvexCombination,
    `Busch.PositiveExtension,
    `Busch.ClassicalBridge,
    `Busch.SegmentContinuity,
    `Busch.PureState,
    `Busch.LinearExtension,
    `Busch.EffectState,
    `Busch.GleasonBusch,
    `Busch.PositiveOp,
    `Busch.PositiveAdditivity,
    `Busch.SAExtension,
    `Busch.SALinearity,
    `Busch.RankOneEffect,
    `Busch.Trace,
    `Busch.HilbertSchmidt,
    `Busch.TraceRepresentation,
    `Busch.GleasonFull,
    `Busch.TraceONB,
    `Busch.HSPositiveDefinite,
    `Busch.SASubspace,
    `Busch.RieszSA,
    `Busch.GleasonUnconditional,
    `GleasonBuschStandalone
  ]
