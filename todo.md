# Remaining Work

No open theorems remain: every item once listed here is now proven admit-free
across the development in `theories/`. The results below are all complete —
including the full
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
obstructions -- the real-radical counterpart to origami solving every cubic), and
FloatGeom soundness against the real-number model via Flocq (`theories/floatsound.v`:
every extracted primitive-float operation computes the IEEE-754 round-to-nearest
value of its exact real model at each step -- within half an ulp per step, with
explicit per-operation error bounds `add/sub/mul/div_err` -- and
`float_line_intersection` decides the real two-lines-meet predicate when the
determinant does not round to zero), and two-fold origami grounding OrigamiNum2
(`theories/frontier.v`: `twofold_reflects_quintic`, the crease {t,-1,-t^4}
tangent to a quartic envelope reflects (q,p) onto {1,0,q} exactly when
t^5 + p t + q = 0 -- the geometric Bring-Jerrard quintic fold, degree-5 analog of
the Beloch cubic; `twofold_general_incidence` / `twofold_solves_no_t3`, the fold
solves the whole no-t^3 quintic family; and `OrigamiNum2_eq_TwoFold`,
OrigamiNum2 is exactly the two-fold-constructible numbers -- the rationals closed
under the single-fold field operations, the cubic O6 fold, and the two-fold
quintic fold).
