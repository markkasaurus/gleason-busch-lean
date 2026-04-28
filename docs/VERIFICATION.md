# Verification

## Build

```sh
./scripts/verify.sh
```

This script runs the full repository verification routine:

- clean `lake build` with no warnings or errors
- axiom checks for the main theorem and key internal bridge theorems
- scan for `sorry` and `admit`
- scan for custom declaration escape hatches on the active build path

The package is intended to verify under the toolchain recorded in
`lean-toolchain`.

## Manual checks

If you prefer to run the checks individually, use the commands below.

### Build

```sh
lake build
```

## Axiom check

```sh
lake env lean Verification/Axioms.lean
```

This prints the axiom dependencies of:

- `Busch.gleason_busch_unconditional`
- `GleasonBusch.gleason_busch_verified`
- `Busch.tracePairingRiesz_unconditional`

The expected output is that both depend only on:

- `propext`
- `Classical.choice`
- `Quot.sound`

For additional independent audit notes, see `docs/AUDIT.md`.

## Placeholder and custom-declaration scan

```sh
grep -RInE "\\b(sorry|admit)\\b" --include="*.lean" --exclude-dir=".lake" --exclude-dir="build" --exclude-dir=".git" .
grep -RInE "^[[:space:]]*(axiom|postulate|unsafe|opaque)\\b" --include="*.lean" --exclude-dir=".lake" --exclude-dir="build" --exclude-dir=".git" .
```

The expected result is no matches corresponding to live declarations on the
active build path.
