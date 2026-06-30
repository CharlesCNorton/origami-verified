# Origami Constructibility

*A Formal Verification of Origami Geometry and Constructible Numbers*

Machine-checked proofs determining which regular polygons can be constructed by paper folding.

**Author:** Charles C. Norton | November 2025

## Background

Single-fold origami follows the Huzita-Hatori axioms (O1-O7), which define what points and lines can be constructed from existing ones through paper folding. The resulting field of constructible numbers includes everything obtainable from rationals via arithmetic, square roots, and real roots of cubic polynomials with constructible coefficients.

This field strictly extends classical compass-and-straightedge constructibility. Compass constructions solve linear and quadratic equations; origami additionally solves cubics. The regular heptagon, impossible with compass alone, becomes constructible. Cube doubling, an ancient impossibility, becomes trivial.

## The Main Result

An n-gon is single-fold constructible if and only if φ(n) is 2-3-smooth, meaning a product of powers of 2 and 3 only.

| n-gon | φ(n) | Single-fold? |
| :---- | :--- | :----------- |
| 7 | 6 = 2 × 3 | Yes |
| 9 | 6 = 2 × 3 | Yes |
| 11 | 10 = 2 × 5 | **No** |
| 13 | 12 = 2² × 3 | Yes |

The **hendecagon (11-gon) is the first regular polygon requiring two-fold origami.** This is the boundary between single-fold and multi-fold constructibility.

## What's Proven

The formalization establishes the Huzita-Hatori axioms O1-O7 with existence proofs for each fold operation, and the Alperin-Lang characterization placing every origami number in a field tower of degree 2ᵃ × 3ᵇ over the rationals.

For the constructible direction, heptagon constructibility is derived via Chebyshev polynomial identities, showing that cos(2π/7) satisfies 8c³ + 4c² − 4c − 1 = 0; cube doubling follows from ∛2 being origami-constructible; and Cardano's formula is verified for depressed cubics, supplying a real root for the O6 Beloch fold of any cubic.

For the impossibility direction, the regular hendecagon is shown **not** single-fold constructible. The number 2cos(2π/11) has algebraic degree exactly 5: its minimal polynomial y⁵ + y⁴ − 4y³ − 3y² + 3y + 1 is proved irreducible over ℚ through the monic form of Gauss's lemma together with rational-root and integer-quadratic-factor checks, and 5 is not 2-3-smooth. The exact algebraic degrees of 2cos(2π/7) (3) and 2cos(2π/11) (5) are established, alongside the classical compass-and-straightedge impossibilities — cube doubling, trisection of π/3, and the regular heptagon — via descent through a quadratic tower.

## Extraction

Coq's extraction mechanism produces `origami_lib.ml`, an OCaml module whose functions are guaranteed to match the verified specifications. This is not generated code in the ordinary sense. Every function in `origami_lib.ml` has a corresponding proof in the development ensuring correctness.

The extracted library provides `euler_phi` for computing totients, `ngon_constructible` for checking 2-3-smoothness, `ngon_tool_required` for classifying construction difficulty, and the certified cubic parameters for the O6 Beloch fold that constructs the heptagon.

## Files

The proofs are organized into a dependency-ordered library under `theories/`
(see `ARCHITECTURE.md` for the layering and the axiom guarantee):

```
theories/foundations.v   Algebra / analysis / number theory / polynomials / linear algebra + the OrigamiNum core
theories/cyclotomic.v    Roots of unity, cyclotomic polynomials, the cos-degree theory
theories/geometry.v      Huzita O1-O7, constructibility, the Gaussian-period tower, the n-gon iff
theories/frontier.v      Scratchpad for new results, built on the core
theories/extraction.v    Demonstrations, FloatGeom, and the extraction directives
origami_main.ml          OCaml entry point / demo driver
ARCHITECTURE.md          How the files are layered by dependency
todo.md                  Remaining open items
```

Compiling `theories/extraction.v` (via `make`) extracts the certified library
`origami_lib.ml` and its interface `origami_lib.mli`; these are build outputs and
are not checked in.

## Usage

Build first to extract the library, then run the demo driver:

```bash
make                           # builds theories/; extraction.v emits origami_lib.ml and origami_lib.mli
cat origami_lib.ml origami_main.ml | ocaml
```

As a library:

```ocaml
#use "origami_lib.ml";;

ngon_constructible 43;;              (* false *)
ngon_tool_required 43;;              (* Origami2, needs two-fold *)
euler_phi 43;;                       (* 42 = 2 × 3 × 7, factor 7 obstructs *)

(* Certified O6 Beloch parameters for heptagon *)
(* Cubic: t³ + (p_num/p_den)t + (q_num/q_den) = 0 *)
heptagon_cubic_p_num, heptagon_cubic_p_den;;   (* -7, 12 *)
heptagon_cubic_q_num, heptagon_cubic_q_den;;   (* -7, 216 *)
```

## Building

Requires Rocq/Coq 9.0+ (the development uses the `Stdlib` namespace).

```bash
rocq makefile -f _CoqProject -o Makefile
make
```

This compiles the library in dependency order and extracts fresh `origami_lib.ml`
and `origami_lib.mli`.
