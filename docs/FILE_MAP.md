# Dependency Inventory

The proof surface consists of:

- `Busch/`: theorem files for the effect algebra, extension theory, trace
  pairing, Hilbert-Schmidt geometry, and final representation theorem
- `Classical/`: projection, rank-one, and frame-function support
- `GleasonBuschStatement.lean`: statement-only entry point using only Mathlib
- `GleasonBuschVerification.lean`: proof of the statement-only entry point
- `GleasonBuschStandalone.lean`: package entry point
- `Verification/comparator.example.json`: comparator configuration template

The Busch files shipped with the library are:

- `Busch/ClassicalBridge.lean`
- `Busch/ConvexCombination.lean`
- `Busch/ConvexLinearity.lean`
- `Busch/TraceRepresentation.lean`
- `Busch/EffectState.lean`
- `Busch/DyadicHomogeneity.lean`
- `Busch/DyadicRational.lean`
- `Busch/Effect.lean`
- `Busch/EffectPredicate.lean`
- `Busch/EffectOrthogonal.lean`
- `Busch/EffectScalar.lean`
- `Busch/GenFrameFunction.lean`
- `Busch/GleasonBusch.lean`
- `Busch/GleasonFull.lean`
- `Busch/GleasonUnconditional.lean`
- `Busch/HSPositiveDefinite.lean`
- `Busch/HilbertSchmidt.lean`
- `Busch/Homogeneity.lean`
- `Busch/LinearExtension.lean`
- `Busch/Monotonicity.lean`
- `Busch/NatScalar.lean`
- `Busch/PositiveAdditivity.lean`
- `Busch/PositiveExtension.lean`
- `Busch/PositiveOp.lean`
- `Busch/ProjectionRestriction.lean`
- `Busch/PureState.lean`
- `Busch/RankOneEffect.lean`
- `Busch/RealHomogeneity.lean`
- `Busch/RieszSA.lean`
- `Busch/SAExtension.lean`
- `Busch/SALinearity.lean`
- `Busch/SASubspace.lean`
- `Busch/SegmentContinuity.lean`
- `Busch/Trace.lean`
- `Busch/TraceONB.lean`

`Busch/EffectPredicate.lean` is a compatibility bridge to mathlib's
`ContinuousLinearMap.IsPositive` predicate. It is not needed to state the final
theorem, but it provides an unbundled effect predicate for downstream users and
future refactoring.
