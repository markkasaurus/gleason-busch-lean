# Independent Audit

The repository verification script checks the active Lean build, reported axiom
dependencies, placeholder tokens, and project-level declaration escape hatches:

```sh
./scripts/verify.sh
```

For an external kernel-level comparison workflow, `leanprover/comparator` can be
used in a separate trusted checkout. That tool requires additional binaries
such as `landrun` and `lean4export`, and its challenge module should be prepared
outside any potentially adversarial solution checkout.

The permitted axiom set for the main theorem is:

```text
propext
Classical.choice
Quot.sound
```

The theorem to audit is:

```text
GleasonBusch.gleason_busch_verified
```

The statement-only file is:

```text
GleasonBuschStatement.lean
```

It imports only Mathlib and defines:

```text
GleasonBusch.GleasonBuschTheorem
```

The proof file is:

```text
GleasonBuschVerification.lean
```

For comparator use, the trusted challenge should be prepared outside this
repository from the statement in `GleasonBuschStatement.lean`; this avoids
placing a `sorry`-based challenge file inside the proof repository itself.

An example comparator configuration is provided at:

```text
Verification/comparator.example.json
```
