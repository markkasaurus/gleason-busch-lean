# Gleason's Theorem via Busch: A Lean 4 Formalization

This repository contains a Lean 4 formalization of Busch's effects
formulation of Gleason's theorem.

## Main Result

For every generalized frame function `μ` on the effects of a finite-dimensional
complex Hilbert space `H` with `2 ≤ Module.finrank ℂ H`, the formalization
proves the existence of a self-adjoint trace-one operator `ρ` such that
`μ(E) = reTr (ρ * E.op)` for every effect `E`; the same trace pairing is
nonnegative on effects.

## Scope

This repository formalizes the Busch effects formulation on effects. It does
not claim to formalize the projection-only theorem via Gleason's original
continuity argument.

## Verification

```sh
lake build
./scripts/verify.sh
```

The verification script checks:
- a clean Lean build
- explicit axiom inspection of the main theorem and key internal bridge theorems
- absence of `sorry` and `admit` on the active build path
- absence of custom declaration escape hatches on the active build path

## Citation

Citation metadata is provided in `CITATION.cff`.

Version DOI: [10.5281/zenodo.19739805](https://doi.org/10.5281/zenodo.19739805)

Concept DOI: [10.5281/zenodo.19739804](https://doi.org/10.5281/zenodo.19739804)

## License

The repository is released under the Apache License 2.0. See `LICENSE`.

## Repository Layout

- `Busch/` — theorem files for effects, linear extension, Hilbert-Schmidt
  geometry, and the final representation theorem
- `Classical/` — minimal projection and rank-one support
- `Verification/` — axiom-check scripts and Lean verification targets
- `scripts/verify.sh` — repository-wide verification script used locally and in CI

For more detail, see `docs/THEOREM.md`, `docs/ARCHITECTURE.md`,
`docs/VERIFICATION.md`, and `docs/AI_DISCLOSURE.md`.
