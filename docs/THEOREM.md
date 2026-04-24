# Main Theorem

The central result is:

```lean
theorem Busch.gleason_busch_unconditional
    (hdim : 2 ≤ Module.finrank ℂ H)
    (f : GenFrameFunction H) :
    GleasonTarget H f
```

in `Busch/GleasonUnconditional.lean`.

Here:

- `GenFrameFunction H` is a generalized frame function on the effect algebra of
  `H`
- `GleasonTarget H f` asserts the existence of a self-adjoint trace-one
  operator `ρ` satisfying the trace formula
  `f.μ E = reTr (ρ * E.op)` for every effect `E`, with nonnegative trace
  pairing on effects

## Informal statement

Let `H` be a finite-dimensional complex Hilbert space of dimension at least
`2`. Every generalized frame function on the effects of `H` is represented by a
self-adjoint trace-one operator through the trace pairing, and the representing
trace pairing is nonnegative on effects.

The formalization uses `reTr`, the real part of the complex trace, as the
natural real-valued trace functional on self-adjoint operators.

## Scope

The result formalized here is the Busch effects formulation of Gleason's
theorem.

The name `gleason_busch_unconditional` means that the intermediate
`TracePairingRiesz` hypothesis has been discharged in Lean. The theorem still
has the displayed finite-dimensional complex Hilbert-space assumptions and the
dimension hypothesis.

The formal target states nonnegativity of the representing trace pairing on
effects. It does not introduce a separate density-operator wrapper.
