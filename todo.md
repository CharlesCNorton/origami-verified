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
`O6_general_good`), and casus irreducibilis for real square+cube-root towers
(`casus_irreducibilis_tower`: a monic cubic with rational coefficients, three
real roots, and no rational root has no root in any real square+cube-root tower
over Q; with `casus_irreducibilis_split` discharging the three-real-roots
hypothesis from a real factorization, and `casus_cube_heart` /
`casus_sqrt_obstruction` the underlying complex-conjugate and dimension
obstructions -- the real-radical counterpart to origami solving every cubic).

1. **Geometric two-fold operations.** Formalize simultaneous two-fold origami as
   genuine fold pairs with incidence constraints, derive their quintic-solving
   power from the geometry, and prove OrigamiNum2 equals exactly the numbers those
   operations construct.

2. **FloatGeom soundness via Flocq.** Each float operation lies within a proven
   error bound of its real-number model, and the float predicates decide their
   real counterparts on adequately separated inputs.
