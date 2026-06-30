# Remaining Work

Open theorems, ordered by logical completion: enabling results precede the
theorems that depend on them. Everything not listed here is already proven
admit-free across the development in `theories/` — including the full
composite-n cyclotomic degree theory (`cyclotomic_irreducible_composite`,
`PhiZ_exists`, `cos_2pi_n_degree_exactly`: [Q(2cos(2π/n)):Q] = φ(n)/2), the
complete single-fold n-gon characterization in both directions for every n
(`cos_2pi_n_origami_smooth_complete`, `ngon_origami_iff_complete`: cos(2π/n) is
single-fold origami iff φ(n) is 2-3-smooth — the constructive direction via the
real Gaussian-period tower over the cyclic unit group (Z/pZ)*, `primitive_root`
and `period_tower`, with the CRT reduction to prime powers), the regular polygon
as a geometric object (`regular_ngon_constructible_iff`: all n vertices are
constructible points iff φ(n) is 2-3-smooth), the degree-indexed n-gon tool
classifier (`ngon_tool_required` with `ngon_tool_single_fold_correct`), and the
general O6 fold as a constructible operation (`O6_general_constructible`: a
constructible crease meets the O6 constraint for any constructible foci and
directrices in general position, via the origami-coordinate crease
`O6_general_good`).

1. **Casus irreducibilis impossibility.** When the depressed cubic has positive
   discriminant (three distinct real roots, irreducible polynomial), its roots lie
   in no real radical tower over Q, the exact counterpart to "origami solves every
   cubic." The complex Cardano formula is available (`Cardano_C.cardano_complex`):
   over C the three roots always exist as nested radicals; the real-radical
   impossibility is the orthogonal direction.

2. **Geometric two-fold operations.** Formalize simultaneous two-fold origami as
   genuine fold pairs with incidence constraints, derive their quintic-solving
   power from the geometry, and prove OrigamiNum2 equals exactly the numbers those
   operations construct.

3. **FloatGeom soundness via Flocq.** Each float operation lies within a proven
   error bound of its real-number model, and the float predicates decide their
   real counterparts on adequately separated inputs.
