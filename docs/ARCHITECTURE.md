# Proof Architecture

The proof is organized in six layers.

## 1. Classical support layer

- `Classical/Projection.lean`
- `Classical/RankOneProjection.lean`
- `Classical/FrameFunction.lean`

This layer provides the minimal projection-theoretic vocabulary needed for the
rank-one and restriction interfaces.

## 2. Effect algebra and generalized frame functions

- `Busch/Effect.lean`
- `Busch/EffectOrthogonal.lean`
- `Busch/ProjectionRestriction.lean`
- `Busch/EffectScalar.lean`
- `Busch/GenFrameFunction.lean`
- `Busch/Monotonicity.lean`
- `Busch/Homogeneity.lean`
- `Busch/NatScalar.lean`
- `Busch/DyadicHomogeneity.lean`
- `Busch/DyadicRational.lean`

These files define the effect algebra and the generalized frame-function
axioms, then derive the basic dyadic algebra used later for real homogeneity.

## 3. Convexity and positive-operator extension

- `Busch/RealHomogeneity.lean`
- `Busch/ConvexLinearity.lean`
- `Busch/ConvexCombination.lean`
- `Busch/PositiveExtension.lean`
- `Busch/LinearExtension.lean`
- `Busch/PositiveOp.lean`
- `Busch/PositiveAdditivity.lean`
- `Busch/SAExtension.lean`
- `Busch/SALinearity.lean`

This layer extends the effect functional to a real-linear functional on the
space of self-adjoint operators.

## 4. Rank-one and state interface

- `Busch/ClassicalBridge.lean`
- `Busch/PureState.lean`
- `Busch/EffectState.lean`
- `Busch/RankOneEffect.lean`
- `Busch/SegmentContinuity.lean`
- `Busch/GleasonBusch.lean`

These files connect generalized frame functions to the rank-one and state
language used in the representation theorem.

## 5. Trace pairing and Hilbert-Schmidt geometry

- `Busch/Trace.lean`
- `Busch/TraceONB.lean`
- `Busch/HilbertSchmidt.lean`
- `Busch/HSPositiveDefinite.lean`
- `Busch/SASubspace.lean`
- `Busch/RieszSA.lean`

This layer develops the Hilbert-Schmidt pairing on self-adjoint operators and
supplies the finite-dimensional Riesz representation step.

## 6. Final representation theorem

- `Busch/TraceRepresentation.lean`
- `Busch/GleasonFull.lean`
- `Busch/GleasonUnconditional.lean`

These files assemble the linear functional into the representing operator and
prove the final theorem.
