# Dependency layout

The development lives in five files under `theories/`, organized by dependency depth.
The organizing criterion is *what you must depend on to state and prove new
theorems*, not where the even cut points fall: reusable mathematical substrate —
field/degree theory, cyclotomics, linear algebra, number theory, complex polynomials
— that "isn't really about origami" sits in the lower layers; origami results sit on
top. The point is that a model can load the foundational layers plus a thin interface
and extend the frontier without re-reading the whole corpus.

Placement is by dependency, not physical location. Number-theoretic machinery
(`primitive_root`, the Frobenius/Dedekind reduction-mod-p apparatus, the
Gaussian-period backbone) is pure substrate and lives in `foundations`, even though
it reads like it belongs next to the n-gon theorem it ultimately serves. Each unit
lands at `max(its own floor, the max over its
dependencies)`, a fixpoint over the dependency graph — sound by construction, since a
unit always lands at or above every unit it uses, so a lower file can never reference
a higher one. The build re-verifies 0 upward references each run.

| File | Role | Depends on |
|------|------|-----------|
| `foundations.v` | Algebra / analysis / number-theory / polynomial / linear-algebra engine; complex numbers (`Cardano_C`); the `OrigamiNum`/`OrigamiNum2`/`OrigamiNum3` algebraic core | — |
| `cyclotomic.v` | Roots of unity, `Φ_n` over ℤ/ℂ, full Dedekind irreducibility, Dickson/Chebyshev, `[ℚ(2cos 2π/n):ℚ]=φ(n)/2`, degree-based impossibility | foundations |
| `geometry.v` | Huzita O1–O7, folds, constructibility + enumeration soundness, `OrigamiNum ↔ Constructible`, Gaussian-period tower + CRT, `ngon_origami_iff_complete` | foundations, cyclotomic |
| `frontier.v` | Scratchpad — beyond-known-origami math. Empty scaffold. | foundations, cyclotomic, geometry |
| `extraction.v` | Demonstrations, density/classifier catalogs, `FloatGeom` + OCaml extraction (`origami_lib.ml`) | foundations, cyclotomic, geometry |

`frontier.v` and `extraction.v` are siblings: both build on the settled core, neither
depends on the other. This is deliberate. `extraction.v` imports `Floats`, which
rebinds `sqrt` to the primitive machine-float root; if the frontier sat downstream of
extraction, loading it would corrupt real-number `sqrt`. The frontier must never
`Require extraction`.

## Axiom guarantee

The math core (`foundations` + `cyclotomic` + `geometry`, via
`coqchk -R . "" -o geometry`) rests on exactly the standard classical-analysis base:
`classic`, `constructive_definite_description`, `constructive_indefinite_description`,
`proof_irrelevance`, `functional_extensionality_dep`, `sig_not_dec`, `sig_forall_dec`.
No type-in-type, no unsafe (co)fixpoints, no assumed positivity, no `admit`/`Axiom`.
The primitive machine-float / `Uint63` axioms (`PrimFloat.sqrt`, `FloatAxioms.*`,
`Uint63Axioms.*`) appear only in `extraction.v` — isolated to extraction, never
reaching the substrate an agent builds on.

## Workflow

1. Prove new results in **`frontier.v`** under its header
   (`Require Import foundations cyclotomic geometry.`) — no need to read `extraction.v`
   or the monolith.
2. Promote matured results *down* into the core at the file their dependencies
   dictate, so they become substrate for the next round.
3. `extraction.v` only showcases/extracts the published core; it is never a dependency.

## Build

```
rocq makefile -f _CoqProject -o Makefile   # regenerate the Makefile from _CoqProject
make                                       # builds the core, then frontier + extraction, in coqdep order
```

`coqdep` derives the build order from the `Require Import` lines, so adding a file to
`_CoqProject` is enough. Edit the files directly; the dependency invariant (no file
references a higher one) is re-checked every build by the compiler itself.
