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

The formalization establishes the Huzita-Hatori axioms O1-O7 with existence proofs for each fold operation. Heptagon constructibility is derived via Chebyshev polynomial identities, showing that cos(2π/7) satisfies 8c³ + 4c² - 4c - 1 = 0. Cube doubling follows from ∛2 being origami-constructible. Cardano's formula is verified for depressed cubics with non-negative discriminant. The Alperin-Lang theorem characterizes origami numbers as living in field towers of degree 2ᵃ × 3ᵇ over the rationals.

## Extraction

Coq's extraction mechanism produces `origami_lib.ml`, an OCaml module whose functions are guaranteed to match the verified specifications. This is not generated code in the ordinary sense. Every function in `origami_lib.ml` has a corresponding proof in `origami_proofs.v` ensuring correctness.

The extracted library provides `euler_phi` for computing totients, `ngon_constructible` for checking 2-3-smoothness, `ngon_tool_required` for classifying construction difficulty, and the certified cubic parameters for the O6 Beloch fold that constructs the heptagon.

## Files

```
origami_proofs.v    Coq proofs
origami_lib.ml      Certified OCaml extraction
origami_lib.mli     Interface
origami_main.ml     Entry point
```

## Usage

```bash
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

Requires Coq 8.19+

```bash
coqc origami_proofs.v
```

This extracts fresh `origami_lib.ml` and `origami_lib.mli` from the proofs.
