# Contributing

Contributions should preserve the repository's verification standard.

## Required checks

Run the repository verification script before opening a pull request:

```sh
./scripts/verify.sh
```

The repository is expected to remain:

- free of build warnings and build errors
- free of `sorry` and `admit`
- free of custom axioms and other escape hatches on the active build path

## Proof and documentation standard

- Keep theorem statements, README text, and verification docs synchronized.
- Prefer small, reviewable patches over broad refactors.
- If a proof changes the logical scope of the main result, update
  `docs/THEOREM.md` and `docs/ARCHITECTURE.md` in the same change.

## AI assistance disclosure

Generative AI tools must not be listed as authors. If a contribution relied
materially on generative AI to draft proof code, source text, or release
materials, disclose that use in the pull request description with the tool name,
model name, and the scope of the assistance. Human contributors remain fully
responsible for the correctness and presentation of the final artifact.
