# GLang in Lean 4

A Lean 4 / Mathlib formalization of GLang, a coordinate-independent linear
algebra language: source and value syntax, typing, denotation, operational
semantics, and their metatheory.

Start with the [public interface](GLang/Artifact.lean).

```lean
import GLang.Artifact
```

## Checking the artifact

Install Git, Python 3, and Lean's `elan` toolchain manager. Then run:

```sh
lake exe cache get
python3 scripts/check-artifact.py
```

Lean and Mathlib versions are pinned. The core check builds the public interface,
audits theorem axioms, checks examples, and rejects proof holes.

For the complete regression suites:

```sh
python3 scripts/check-artifact.py --suite maintenance --full-build
```

`lake build` builds the public interface and all checked examples.

## Reading the code

Read the definitions first, then follow the public results into their proofs:

| Folder | What to read there |
| --- | --- |
| [Surface](GLang/Surface/) | Surface syntax, typing, and context formation. |
| [Annotated](GLang/Annotated/) | Annotated syntax, typing, and denotation. |
| [Elaboration](GLang/Elaboration/) | Erasure, reconstruction, and uniqueness. |
| [Value](GLang/Value/) | Value syntax, typing, inference, and denotation. |
| [Operational](GLang/Operational/) | Evaluation rules, contexts, and agreement. |
| [Public](GLang/Public/) | Public theorem statements. |
| [Proofs](GLang/Proofs/) | Supporting proofs, grouped by theorem and topic. |
| [Semantics](GLang/Semantics/) and [Numerics](GLang/Numerics/) | Vector-space helpers and spectral, SVD, RREF, and pseudoinverse constructions. |
| [Examples](GLang/Examples/) | Checked examples. |

The three top-level Lean files are entry points: `Artifact.lean` for reviewers,
`Paper.lean` for public results, and `Metatheory.lean` for the established
metatheory API.

## Scope

The formalization includes source and value languages, their metatheory, and
checked examples over real Hilbert spaces.

Licensed under [Apache-2.0](LICENSE).
