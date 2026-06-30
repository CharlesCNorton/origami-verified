# Remaining Work

Open theorems, ordered by logical completion: enabling results precede the
theorems that depend on them. Everything not listed here is already proven
admit-free across the development in `theories/` — including the full
composite-n cyclotomic degree theory (`cyclotomic_irreducible_composite`,
`PhiZ_exists`, `cos_2pi_n_degree_exactly`: [Q(2cos(2π/n)):Q] = φ(n)/2) and the
complete single-fold n-gon characterization in both directions for every n
(`cos_2pi_n_origami_smooth_complete`, `ngon_origami_iff_complete`: cos(2π/n) is
single-fold origami iff φ(n) is 2-3-smooth — the constructive direction via the
real Gaussian-period tower over the cyclic unit group (Z/pZ)*, `primitive_root`
and `period_tower`, with the CRT reduction to prime powers).

1. **General O6 constructor.** Promote the general-position O6 solver
   `O6_fully_general` into the `ConstructibleFold` relation, giving `CF_O6` a
   crease that satisfies the O6 incidence constraint for arbitrary constructible
   foci and directrices in general position, so single-fold constructibility rests
   on a fully general O6 fold in place of the common-perpendicular `fold_O6_approx`,
   which meets the O6 constraint only when both points already lie on their target
   lines.

2. **Regular polygon as a geometric object.** Define the regular n-gon as its n
   vertices on the unit circle and prove every vertex and edge crease constructible
   exactly when φ(n) is 2-3-smooth, lifting the angle-level equivalence
   `ngon_origami_iff_complete` (cos(2π/n) ∈ OrigamiNum) to the polygon itself and
   generalizing the worked heptagon vertex construction (`heptagon_vertices`).

3. **Casus irreducibilis impossibility.** When the depressed cubic has positive
   discriminant (three distinct real roots, irreducible polynomial), its roots lie
   in no real radical tower over Q, the exact counterpart to "origami solves every
   cubic." The complex Cardano formula is available (`Cardano_C.cardano_complex`):
   over C the three roots always exist as nested radicals; the real-radical
   impossibility is the orthogonal direction.

4. **Geometric two-fold operations.** Formalize simultaneous two-fold origami as
   genuine fold pairs with incidence constraints, derive their quintic-solving
   power from the geometry, and prove OrigamiNum2 equals exactly the numbers those
   operations construct.

5. **Degree-indexed multifold classifier.** Recast `ngon_tool_required` to key on
   the governing degree φ(n)/2 = [Q(2cos(2π/n)):Q], emitting `Compass` for a power
   of two, `Origami1` for 2-3-smooth, `Origami2` for 5-smooth (the two-fold /
   quintic reach of `OrigamiNum2`), and `Higher` otherwise, with a correctness
   theorem tying each level to the construction hierarchy so the extracted
   catalogue and its README examples (the 43-gon among them) report the true tool
   level.

6. **FloatGeom soundness via Flocq.** Each float operation lies within a proven
   error bound of its real-number model, and the float predicates decide their
   real counterparts on adequately separated inputs.
