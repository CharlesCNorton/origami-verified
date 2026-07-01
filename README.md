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

The formalization establishes the Huzita-Hatori axioms O1-O7 with existence proofs for each fold operation, and the Alperin-Lang characterization placing every origami number in a field tower of degree 2ᵃ × 3ᵇ over the rationals. From these the main equivalence is proved in full — both directions, for every n — not merely for sample polygons.

**Constructible direction.** For every n whose φ(n) is 2-3-smooth, cos(2π/n) is shown origami-constructible. The general construction is the real Gaussian-period tower over the cyclic unit group (ℤ/pℤ)\*: a chain of subfields whose successive degrees are the prime factors of φ — each 2 or 3, so each step is solved by one square or cube root — with a CRT reduction assembling the prime-power factors of composite n. The heptagon is the worked example: cos(2π/7) satisfies 8c³ + 4c² − 4c − 1 = 0, cube doubling follows from ∛2 being origami-constructible, and Cardano's formula is verified for depressed cubics, supplying the real root for the O6 Beloch fold of any cubic.

**Impossibility direction.** The exact degree [ℚ(2cos(2π/n)) : ℚ] = φ(n)/2 is established for every n, resting on irreducibility of the cyclotomic polynomial Φₙ for all n — composite included — proved by reduction modulo a prime together with the Dedekind/Frobenius argument. When φ(n) is not 2-3-smooth this degree is not of the form 2ᵃ × 3ᵇ, so cos(2π/n) lies in no origami tower. The hendecagon is the worked example: 2cos(2π/11) has degree exactly 5 (minimal polynomial y⁵ + y⁴ − 4y³ − 3y² + 3y + 1, proved irreducible over ℚ through the monic form of Gauss's lemma with rational-root and integer-quadratic-factor checks), and 5 is not 2-3-smooth. The classical compass-and-straightedge impossibilities — cube doubling, trisection of π/3, the regular heptagon — are derived in passing, via descent through a quadratic tower.

**Casus irreducibilis.** The real-radical counterpart to origami solving every cubic is also established (`casus_irreducibilis_tower`): a monic cubic with rational coefficients, three real roots, and no rational root has no root in any real square+cube-root tower over ℚ. Cardano's formula produces the roots over ℂ through complex cube roots; this is the impossibility of reaching them with real radicals alone. The proof descends through the tower — square steps by Vieta conjugation, cube steps by `casus_cube_heart`, which reduces a candidate root modulo β³ = a and forces the complex conjugate root's imaginary part √3/2·(c₁β − c₂β²) to vanish. The two underlying obstructions are `casus_cube_heart` (the complex-conjugate argument, why a real cube-root tower cannot help) and `casus_sqrt_obstruction` (three elements 1, ρ, ρ² cannot be independent in a two-dimensional square-root extension), and `casus_irreducibilis_split` discharges the three-real-roots hypothesis for any cubic presented by its real roots.

The mathematical core is axiom-clean: it assumes only the standard axioms of classical real analysis, with no admitted proofs (the primitive machine-float axioms used for the extracted numerics are confined to the extraction file). The Organization section below records the exact axiom base.

## Extraction

Coq's extraction mechanism produces `origami_lib.ml`, an OCaml module whose functions are guaranteed to match the verified specifications. This is not generated code in the ordinary sense. Every function in `origami_lib.ml` has a corresponding proof in the development ensuring correctness.

The extracted library provides `euler_phi` for computing totients, `ngon_constructible` for checking 2-3-smoothness, `ngon_tool_required` for classifying construction difficulty, and the certified cubic parameters for the O6 Beloch fold that constructs the heptagon.

## Organization

The development lives in five files under `theories/`, ordered by dependency depth.
The organizing criterion is what a result must *depend on*, not where it reads most
naturally: reusable substrate — field/degree theory, cyclotomics, linear algebra,
number theory, complex polynomials — that isn't really about origami sits in the
lower files; origami-specific results sit on top. So a reader (or an agent extending
the work) can load the foundational files plus this interface and push the frontier
without ingesting the whole corpus.

| File | Contents | Depends on |
| :--- | :--- | :--- |
| `theories/foundations.v` | Algebra / analysis / number theory / polynomials / linear algebra; complex numbers; the `OrigamiNum` algebraic core | — |
| `theories/cyclotomic.v` | Roots of unity, Φₙ over ℤ and ℂ, full Dedekind irreducibility, Chebyshev/Dickson, the cos-degree theory | foundations |
| `theories/geometry.v` | Huzita O1-O7, folds, constructibility and enumeration, the Gaussian-period tower, the n-gon iff, casus irreducibilis for real square+cube-root towers | foundations, cyclotomic |
| `theories/frontier.v` | Reserved for results beyond established origami/constructibility mathematics; currently empty | foundations, cyclotomic, geometry |
| `theories/extraction.v` | Demonstrations, density/classifier catalogs, `FloatGeom`, and the OCaml extraction | foundations, cyclotomic, geometry |

Placement is by dependency, not physical location — number-theoretic machinery
(`primitive_root`, the reduction-mod-p apparatus, the Gaussian-period backbone) lives
in `foundations` even though it ultimately serves the n-gon theorem. `frontier.v` and
`extraction.v` are siblings: both build on the settled core, neither depends on the
other. This matters — `extraction.v` imports `Floats`, which rebinds `sqrt` to the
primitive machine-float root, so the frontier must never `Require` it. `frontier.v`
is reserved for genuinely new mathematics — open problems and theorems not yet proved
on paper; anything classical belongs directly in the settled core at the file its
dependencies dictate, and matured frontier results migrate down the same way, leaving
`frontier.v` empty between campaigns. `extraction.v` only showcases and extracts the
published core.

The mathematical core is axiom-clean. `coqchk -R theories "" geometry` reports only
the standard classical-analysis axioms — excluded middle, the description and choice
operators, proof irrelevance, functional extensionality, and the two classical
Dedekind-reals decidability axioms — with no type-in-type, no unsafe fixpoints, and
no admitted proofs. The primitive machine-float and `Uint63` axioms used by the
extracted numerics appear only in `extraction.v`.

Beyond `theories/`, `origami_main.ml` is the OCaml demo driver and `todo.md` lists
the open theorems. Compiling `theories/extraction.v` (via `make`) extracts the
certified library `origami_lib.ml` and its interface `origami_lib.mli`; build outputs
(`.vo`, `.glob`, `Makefile`, `origami_lib.*`) are not checked in.

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
ngon_tool_required 43;;              (* Higher, needs more than two folds *)
ngon_tool_required 11;;              (* Origami2, two-fold (quintic) *)
euler_phi 43;;                       (* 42; degree φ(43)/2 = 21 = 3 × 7, the 7 obstructs even two-fold *)

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
