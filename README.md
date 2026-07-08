# Origami Constructibility

*A Formal Verification of Origami Geometry and Constructible Numbers*

Machine-checked proofs determining which regular polygons can be constructed by paper folding.

**Author:** Charles C. Norton | November 2025 – July 2026

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

The single-fold theorem is the k = 1 instance of the general hierarchy, proved for every fold budget at once (`ngon_k_fold_iff`): **an n-gon is k-fold constructible if and only if every prime factor of φ(n) is at most 2k + 1.** Each additional simultaneous fold buys exactly the primes up to 2k + 1, nothing more.

| n-gon | φ(n) | Smallest fold budget |
| :---- | :--- | :------------------- |
| 7 | 6 = 2 × 3 | single-fold — the first beyond compass |
| 11 | 10 = 2 × 5 | two-fold — the first beyond single-fold |
| 23 | 22 = 2 × 11 | five-fold — the first beyond two-fold |
| 29 | 28 = 2² × 7 | three-fold — the first requiring exactly three |

## What's Proven

The formalization establishes the Huzita-Hatori axioms O1-O7 with existence proofs for each fold operation, and the Alperin-Lang characterization placing every origami number in a field tower of degree 2ᵃ × 3ᵇ over the rationals. From these the main equivalence is proved in full — both directions, for every n — not merely for sample polygons.

**Constructible direction.** For every n whose φ(n) is 2-3-smooth, cos(2π/n) is shown origami-constructible. The general construction is the real Gaussian-period tower over the cyclic unit group (ℤ/pℤ)\*: a chain of subfields whose successive degrees are the prime factors of φ — each 2 or 3, so each step is solved by one square or cube root — with a CRT reduction assembling the prime-power factors of composite n. The heptagon is the worked example: cos(2π/7) satisfies 8c³ + 4c² − 4c − 1 = 0, cube doubling follows from ∛2 being origami-constructible, and Cardano's formula is verified for depressed cubics, supplying the real root for the O6 Beloch fold of any cubic.

**Impossibility direction.** The exact degree [ℚ(2cos(2π/n)) : ℚ] = φ(n)/2 is established for every n, resting on irreducibility of the cyclotomic polynomial Φₙ for all n — composite included — proved by reduction modulo a prime together with the Dedekind/Frobenius argument. When φ(n) is not 2-3-smooth this degree is not of the form 2ᵃ × 3ᵇ, so cos(2π/n) lies in no origami tower. The hendecagon is the worked example: 2cos(2π/11) has degree exactly 5 (minimal polynomial y⁵ + y⁴ − 4y³ − 3y² + 3y + 1, proved irreducible over ℚ through the monic form of Gauss's lemma with rational-root and integer-quadratic-factor checks), and 5 is not 2-3-smooth. The classical compass-and-straightedge impossibilities — cube doubling, trisection of π/3, the regular heptagon — are derived in passing, via descent through a quadratic tower.

**Casus irreducibilis.** The real-radical counterpart to origami solving every cubic is also established (`casus_irreducibilis_tower`): a monic cubic with rational coefficients, three real roots, and no rational root has no root in any real square+cube-root tower over ℚ. Cardano's formula produces the roots over ℂ through complex cube roots; this is the impossibility of reaching them with real radicals alone. The proof descends through the tower — square steps by Vieta conjugation, cube steps by `casus_cube_heart`, which reduces a candidate root modulo β³ = a and forces the complex conjugate root's imaginary part √3/2·(c₁β − c₂β²) to vanish. The two underlying obstructions are `casus_cube_heart` (the complex-conjugate argument, why a real cube-root tower cannot help) and `casus_sqrt_obstruction` (three elements 1, ρ, ρ² cannot be independent in a two-dimensional square-root extension), and `casus_irreducibilis_split` discharges the three-real-roots hypothesis for any cubic presented by its real roots.

**Two-fold origami.** Simultaneous two-fold origami extends single-fold constructibility from cubics to quintics, and the extended field `OrigamiNum2` is grounded in genuine geometry. Where the single-fold Beloch crease `{t, −1, −t²}` (tangent to a parabola) reflects `(q,p)` onto `{1,0,q}` exactly when `t³ + p t + q = 0`, the two-fold crease `{t, −1, −t⁴}` (tangent to a quartic envelope, a genuine two-fold construction) does so exactly when `t⁵ + p t + q = 0` — the Bring–Jerrard quintic, the degree-5 analog of the Beloch fold (`twofold_reflects_quintic`). More generally the fold solves the entire no-`t³` quintic family via a constructible point and line (`twofold_general_incidence`, `twofold_solves_no_t3`), and the crease and constructed root always lie in `OrigamiNum2`. From this the exact characterization is proved (`OrigamiNum2_eq_TwoFold`): `OrigamiNum2` is precisely the set of two-fold-constructible numbers — the rationals closed under the single-fold field operations, the cubic O6 fold, and the two-fold quintic fold — closing the loop between the algebraic definition and the geometric operations.

**Three-fold origami.** The same geometry lifts one degree further: the septic crease `{t, −1, −t⁶}` reflects `(q,p)` onto `{1,0,q}` exactly when `t⁷ + p t + q = 0`, and the simultaneous three-fold Lill system — three creases coupled by two shared-perpendicular bounce segments — solves the Bring–Jerrard septic (`three_fold_lill_septic`), realizably, with the crease coordinates in `OrigamiNum3`. The three-fold n-gon theorem (`ngon_three_fold_iff`) characterizes: cos(2π/n) is three-fold constructible iff φ(n) is {2,3,5,7}-smooth. The regular 29-gon is the first polygon requiring exactly three folds, and the 23-gon the first beyond two-fold (`ngon_29_first_exactly_three_fold`).

**The k-fold hierarchy.** All of the above are instances of one theorem. `OrigamiNumK k` closes the rationals under field operations, square roots, and roots of monic prime-degree polynomials of degree at most 2k + 1; k = 1, 2, 3 provably coincide with the single-, two-, and three-fold classes (`OrigamiNumK_1_iff` through `OrigamiNumK_3_iff`). The general Lill system grounds the algebra geometrically: k creases coupled by k − 1 shared-perpendicular bounce segments solve an arbitrary monic polynomial of degree 2k + 1 (`general_lill_solves`), realizably (`k_fold_lill_realizable`). The k-fold n-gon theorem (`ngon_k_fold_iff`) then gives, for every k and n at once: cos(2π/n) ∈ `OrigamiNumK k` iff every prime factor of φ(n) is at most 2k + 1. The constructive direction runs the real Gaussian-period tower over an unconditional primitive root (no smoothness hypothesis — assembled by strong induction over the unitary divisors of p − 1), Chebyshev recurrences for prime-power denominators, and CRT for composites; necessity is the smooth degree bound — every `OrigamiNumK k` number has algebraic degree over ℚ with all prime factors at most 2k + 1 — against the exact cosine degree φ(n)/2.

**Coupled two-fold systems escape the quintic closure.** The two creases of a simultaneous two-fold system can also be coupled to each other in general position, and the catalog of mutual couplings is classified by elimination degree: 3, 3, 1, 4, 6, and 10 across the six cells. The cells of degree at most 4 stay inside `OrigamiNum2` — machine-checked closure through Cardano and Ferrari — but the degree-6 cell does not: a rational witness of the pencil–tangent coupling has an elimination sextic with Galois group exactly S₆, and its roots lie outside `OrigamiNum2` (`witness_sextic_outside_ON2`). The conjecture that coupled two-fold constructions remain two-fold constructible is therefore false. The proof is a self-contained Galois development on the frontier: splitting fields and embedding counting over an arbitrary base subfield, the permutation group of an embedding list, factor-exclusion certificates modulo small primes with Bézout cofactors, dyadic root brackets, complex conjugation as an explicit transposition, two-transitivity, and a descent through the pair {A₆, S₆} driven by the simplicity of A₆ from its verified class equation. The degree-10 tangent–tangent cell is the campaign in progress (`todo.md`): a rational witness with its offline certificates is archived in `_galois_decic_candidate.json` (elimination decic irreducible modulo 17, eight real roots and one conjugate pair, the degree-45 squared-difference resolvent excluded by factor patterns modulo 23 and 31), and the ten-letter permutation substrate — parity with multiplicativity via the bubble-sort decomposition, ambient-free groups with pigeonhole inverses — is built without enumeration, since S₁₀ at 3,628,800 elements admits no vm sweep of the A₆ kind. The target is exclusion from `OrigamiNum2`, and it is sharply bounded above: the prime-degree step of `OrigamiNumK` carries no irreducibility requirement, so padding a minimal polynomial to a monic degree-11 multiple places every degree-10 real inside `OrigamiNumK 5`; the intermediate exclusions are gated on complex root existence for monic polynomials of degrees six and seven, which the descent's extension-existence hypothesis requires of degree-seven tower steps.

The mathematical core is axiom-clean: it assumes only the standard axioms of classical real analysis, with no admitted proofs (the primitive machine-float axioms used for the extracted numerics are confined to the extraction and float-soundness files). The Organization section below records the exact axiom base.

The extracted `FloatGeom` primitive-float layer is itself verified against its real-number model in `theories/floatsound.v` via Flocq: each float operation (distance, midpoint, line-through, reflection, perpendicular bisector, the Beloch crease, the depressed cubic and its discriminants, the fold constructors O1/O2, the n-gon angle) is proved to compute the IEEE-754 round-to-nearest value of its exact real model at every primitive step — hence within half an ulp per step, with explicit per-operation error bounds — and the line-intersection routine is proved to decide the real "two lines meet in a point" predicate whenever the determinant does not round to zero.

## Relation to the Literature

The single-fold theory formalizes settled mathematics: the axiom system and its constructions are due to Huzita, Justin, and Hatori, the trisection and heptagon results to Gleason (1988), and the field-theoretic characterization to Alperin (2000); casus irreducibilis for real radical towers follows the line of Isaacs (1985). Multifold axioms and the Lill-method quintic construction were introduced by Alperin and Lang (2009), and the Beloch–Lill connection is surveyed by Hull (2011). We are not aware of a prior proof-assistant formalization of origami constructibility at any level; existing computational treatments verify individual constructions by computer algebra rather than proving the field theory.

Three results appear to have no counterpart in the literature.

1. **The uniform k-fold characterization.** `ngon_k_fold_iff` proves, for every fold budget k at once, that cos(2π/n) is k-fold constructible iff every prime factor of φ(n) is at most 2k + 1 — both directions, resting on an unconditional primitive root, Chebyshev prime-power rungs, and the smooth degree bound. The published k = 1 theorem and the expected k = 2, 3 statements are its first three instances; the placements of the 23- and 29-gons in the fold hierarchy are new concrete consequences.

2. **The coupled two-fold catalog.** Whether mutually coupled two-fold alignments stay inside the quintic closure had not been posed precisely; the septic constructions of König and Nedrenco indicated that two-fold alignment spaces outrun the separated-axiom degree count. Here the six coupling cells are classified by elimination degree (3, 3, 1, 4, 6, 10), the cells of degree at most 4 are proved closed in `OrigamiNum2`, and the degree-6 cell provably escapes: its witness sextic has Galois group exactly S₆ (`witness_sextic_outside_ON2`). The certificate method carrying that proof — factor patterns modulo small primes, conjugation as an explicit transposition, a descent through the pair {A₆, S₆} — appears itself to be new to this domain.

3. **The `OrigamiNumK` hierarchy.** The graded class interpolating the known fold levels is new, and its boundary is delicate: the prime-degree step carries no irreducibility requirement, so a padding argument places any algebraic real inside `OrigamiNumK k` once some prime at most 2k + 1 reaches its degree. The degree-10 exclusion beneath that boundary is the open campaign recorded in `todo.md`.

Corrections on priority are welcome.

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
| `theories/geometry.v` | Huzita O1-O7, folds, constructibility and enumeration, the Gaussian-period towers, the n-gon characterizations through the k-fold theorem (`OrigamiNumK`, `ngon_k_fold_iff`), the two-fold quintic fold and `OrigamiNum2` = the two-fold-constructible numbers, casus irreducibilis for real square+cube-root towers | foundations, cyclotomic |
| `theories/frontier.v` | Staging ground for open conjectures and theorems not yet proved on paper; empty between campaigns | foundations, cyclotomic, geometry |
| `theories/extraction.v` | Demonstrations, density/classifier catalogs, `FloatGeom`, and the OCaml extraction | foundations, cyclotomic, geometry |
| `theories/floatsound.v` | Soundness of the `FloatGeom` primitive-float layer against its real model via Flocq | extraction (+ Flocq) |

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
published core; `floatsound.v` sits above it, proving the extracted `FloatGeom`
primitive-float operations sound against their real-number model via Flocq.

The mathematical core is axiom-clean. `Print Assumptions` reports exactly four
standard classical-analysis axioms — excluded middle (`classic`), functional
extensionality (`functional_extensionality_dep`), and the two classical
Dedekind-reals decidability axioms (`sig_forall_dec`, `sig_not_dec`) that underlie
`Coq.Reals` — with no type-in-type, no unsafe fixpoints, and no admitted proofs. The
whole discrete layer (integers, `nat`, polynomials, the cyclotomic arithmetic) is
outright axiom-free; the four axioms enter only through the real-analysis layer. The
cube-root witness used by the Beloch-crease enumeration is the constructive IVT
witness `depressed_cubic_root_sig`, so no choice operator is needed. The active
frontier campaign additionally draws `constructive_definite_description` (Stdlib's
classical description) in its embedding-counting layer; no settled-core theorem
depends on it. The primitive
machine-float and `Uint63` axioms used by the
extracted numerics appear only in `extraction.v` and `floatsound.v` — the latter
verifies those very primitive-float operations against Flocq's real model, so it
necessarily rests on their defining spec axioms (`add_spec`, `mul_spec`, `div_spec`).

Beyond `theories/`, `origami_main.ml` is the OCaml demo driver, `todo.md` lists
the open theorems, and the `_galois_*.py` scripts with their `.json` outputs
record the offline witness searches and certificate provenance for the frontier
campaigns. Compiling `theories/extraction.v` (via `make`) extracts the
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
euler_phi 43;;                       (* 42; degree φ(43)/2 = 21 = 3 × 7, the 7 obstructs even two-fold;
                                        three folds suffice by the k-fold theorem *)

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
