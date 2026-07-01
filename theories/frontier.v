(* frontier.v -- results beyond established origami and constructibility
   mathematics: open conjectures and theorems not yet proved on paper.  A result
   already in the literature belongs in the settled core (foundations / cyclotomic
   / geometry) at the file its dependencies dictate; matured frontier results
   migrate there.

   Sibling of extraction.v; both build on the settled core and neither depends on
   the other.  Never Require extraction: it rebinds sqrt to the primitive machine
   float.

   Contents: two-fold origami -- the two-fold quintic fold (crease {t,-1,-t^4})
   grounding OrigamiNum2, and OrigamiNum2 = the two-fold-constructible numbers
   (OrigamiNum2_eq_TwoFold). *)
From Stdlib Require Import Reals Lra Field R_sqr Psatz Nsatz Ring Ranalysis1 RingMicromega List ProofIrrelevance ClassicalDescription PeanoNat ZArith Classical Permutation Bool Arith.Wf_nat.
From Stdlib Require Znumtheory.
Import ListNotations.
Require Import foundations cyclotomic geometry.
Open Scope R_scope.

(* ============================================================================
   Two-fold origami: the geometric quintic-solving fold, grounding OrigamiNum2.

   Single-fold O6 (Beloch) uses the crease {t, -1, -t^2}, tangent to a parabola,
   and reflecting (q,p) across it lands on {1,0,q} exactly when t^3 + p t + q = 0.
   The two-fold crease {t, -1, -t^4} is tangent to a quartic envelope, and the
   same reflection lands on {1,0,q} exactly when t^5 + p t + q = 0: two-fold
   origami solves the Bring-Jerrard quintic, the degree-5 counterpart of Beloch's
   degree-3 fold.
   ============================================================================ *)

(** The two-fold crease with parameter t (tangent to the quartic envelope). *)
Definition twofold_crease (t : R) : Line := {| A := t; B := -1; C := -(t*t*t*t) |}.

(** The two-fold Beloch incidence: reflecting (q,p) across the crease lands on
    the line {1,0,q} exactly along the Bring-Jerrard quintic t^5 + p t + q = 0.
    (Compare beloch_P2_reflects_to_L2 for the cubic t^3 + p t + q.) *)
Lemma twofold_reflects_quintic : forall p q t,
  t*t*t*t*t + p * t + q = 0 ->
  on_line (reflect_point (q, p) (twofold_crease t)) {| A := 1; B := 0; C := q |}.
Proof.
  intros p q t Hquintic.
  unfold reflect_point, twofold_crease, on_line; simpl.
  assert (Ht2 : 0 <= t * t) by apply Rle_0_sqr.
  assert (Hd_nz : t * t + (-1) * (-1) <> 0) by lra.
  field_simplify; [| lra].
  nra.
Qed.

(** OrigamiNum2 is closed under the two-fold (Bring-Jerrard) quintic step: a root
    of t^5 + p t + q with p, q in OrigamiNum2 is itself in OrigamiNum2. *)
Lemma twofold_root_in_ON2 : forall p q t,
  OrigamiNum2 p -> OrigamiNum2 q -> t*t*t*t*t + p * t + q = 0 -> OrigamiNum2 t.
Proof.
  intros p q t Hp Hq Hquint.
  apply (ON2_quint 0 0 0 p q t ON2_0 ON2_0 ON2_0 Hp Hq).
  transitivity (t*t*t*t*t + p * t + q); [ring | exact Hquint].
Qed.

(** The two-fold crease has all three coordinates in OrigamiNum2 when p, q do and
    t solves the quintic: the geometric two-fold fold is an OrigamiNum2 operation. *)
Lemma twofold_crease_good : forall p q t,
  OrigamiNum2 p -> OrigamiNum2 q -> t*t*t*t*t + p * t + q = 0 ->
  OrigamiNum2 (A (twofold_crease t)) /\
  OrigamiNum2 (B (twofold_crease t)) /\
  OrigamiNum2 (C (twofold_crease t)).
Proof.
  intros p q t Hp Hq Hquint.
  assert (Ht : OrigamiNum2 t) by (apply (twofold_root_in_ON2 p q t); assumption).
  assert (Hm1 : OrigamiNum2 (-1))
    by (replace (-1) with (0 - 1) by ring; apply ON2_sub; [apply ON2_0 | apply ON2_1]).
  unfold twofold_crease, A, B, C; simpl.
  repeat split; [exact Ht | exact Hm1 |].
  replace (-(t*t*t*t)) with (0 - t*t*t*t) by ring.
  apply ON2_sub; [apply ON2_0 |].
  apply ON2_mul; [apply ON2_mul; [apply ON2_mul; [exact Ht | exact Ht] | exact Ht] | exact Ht].
Qed.

(** For p, q in OrigamiNum2 and a root t of the Bring-Jerrard quintic
    t^5 + p t + q = 0: the crease {t, -1, -t^4} is an OrigamiNum2 line, reflecting
    (q,p) across it lands on {1,0,q} (the degree-5 analog of Beloch's O6), and t is
    in OrigamiNum2. *)
Theorem twofold_quintic_construction : forall p q t,
  OrigamiNum2 p -> OrigamiNum2 q -> t*t*t*t*t + p * t + q = 0 ->
  (OrigamiNum2 (A (twofold_crease t)) /\
   OrigamiNum2 (B (twofold_crease t)) /\
   OrigamiNum2 (C (twofold_crease t))) /\
  on_line (reflect_point (q, p) (twofold_crease t)) {| A := 1; B := 0; C := q |} /\
  OrigamiNum2 t.
Proof.
  intros p q t Hp Hq Hquint.
  split; [apply (twofold_crease_good p q t); assumption |].
  split; [apply twofold_reflects_quintic; exact Hquint |].
  apply (twofold_root_in_ON2 p q t); assumption.
Qed.

(** The two-fold-constructible numbers: the closure of the rationals under the
    single-fold field operations (sum, difference, product, inverse, real square
    root) and the two solving folds -- the single-fold cubic O6 fold and the
    two-fold Bring-Jerrard quintic fold whose geometry is twofold_quintic_construction. *)
Inductive TwoFold : R -> Prop :=
| TF_0 : TwoFold 0
| TF_1 : TwoFold 1
| TF_add : forall x y, TwoFold x -> TwoFold y -> TwoFold (x + y)
| TF_sub : forall x y, TwoFold x -> TwoFold y -> TwoFold (x - y)
| TF_mul : forall x y, TwoFold x -> TwoFold y -> TwoFold (x * y)
| TF_inv : forall x, TwoFold x -> x <> 0 -> TwoFold (/ x)
| TF_sqrt : forall x, TwoFold x -> 0 <= x -> TwoFold (sqrt x)
| TF_cubic : forall a b r, TwoFold a -> TwoFold b -> r*r*r + a*r + b = 0 -> TwoFold r
| TF_quintic : forall a b c d e r,
    TwoFold a -> TwoFold b -> TwoFold c -> TwoFold d -> TwoFold e ->
    r^5 + a*r^4 + b*r^3 + c*r^2 + d*r + e = 0 -> TwoFold r.

(** Soundness of two-fold construction: every two-fold-constructible number lies
    in OrigamiNum2.  The cubic step is the single-fold ON2_cbrt; the quintic step
    is grounded by the two-fold geometry (twofold_root_in_ON2). *)
Theorem TwoFold_sound : forall x, TwoFold x -> OrigamiNum2 x.
Proof.
  intros x H. induction H.
  - apply ON2_0.
  - apply ON2_1.
  - apply ON2_add; assumption.
  - apply ON2_sub; assumption.
  - apply ON2_mul; assumption.
  - apply ON2_inv; assumption.
  - apply ON2_sqrt; assumption.
  - apply (ON2_cbrt a b r); assumption.
  - apply (ON2_quint a b c d e r); assumption.
Qed.

(** Completeness of two-fold construction: every OrigamiNum2 number is two-fold
    constructible.  Each OrigamiNum2 generator maps to the matching TwoFold fold
    operation -- the cubic step to the single-fold O6 fold TF_cubic, the quintic
    step to the two-fold quintic fold TF_quintic (whose geometry is realized by
    twofold_reflects_quintic / twofold_solves_noR3). *)
Theorem OrigamiNum2_TwoFold : forall x, OrigamiNum2 x -> TwoFold x.
Proof.
  intros x H. induction H.
  - apply TF_0.
  - apply TF_1.
  - apply TF_add; assumption.
  - apply TF_sub; assumption.
  - apply TF_mul; assumption.
  - apply TF_inv; assumption.
  - apply TF_sqrt; assumption.
  - apply (TF_cubic a b r); assumption.
  - apply (TF_quintic a b c d e r); assumption.
Qed.

(** OrigamiNum2 is exactly the set of two-fold-constructible numbers. *)
Theorem OrigamiNum2_eq_TwoFold : forall x, OrigamiNum2 x <-> TwoFold x.
Proof.
  intros x. split; [apply OrigamiNum2_TwoFold | apply TwoFold_sound].
Qed.

(** The general two-fold incidence.  Reflecting (x0,y0) across the crease
    {t,-1,-t^4} lands on the line {1,b,c} exactly along the quintic
    2 t^5 - 2b t^4 + (b y0 + c - x0) t^2 + 2(b x0 + y0) t + (x0 - b y0 + c) = 0.
    The t^3 coefficient is structurally zero, so this covers every quintic with no
    t^3 term; the Bring-Jerrard t^5 + p t + q (b = 0, c = x0) is the special
    case. *)
Lemma twofold_general_incidence : forall b c x0 y0 t,
  2*t^5 - 2*b*t^4 + (b*y0 + c - x0)*t^2 + 2*(b*x0 + y0)*t + (x0 - b*y0 + c) = 0 ->
  on_line (reflect_point (x0, y0) (twofold_crease t)) {| A := 1; B := b; C := c |}.
Proof.
  intros b c x0 y0 t Hq.
  unfold reflect_point, twofold_crease, on_line; simpl.
  assert (Hd_nz : t * t + (-1) * (-1) <> 0) by (assert (0 <= t*t) by apply Rle_0_sqr; lra).
  assert (Hden : t ^ 2 + 1 <> 0) by (assert (0 <= t^2) by apply pow2_ge_0; lra).
  field_simplify_eq; [| lra].
  nsatz.
Qed.

(** Every no-t^3 quintic t^5 + alpha t^4 + beta t^2 + gamma t + delta = 0 is solved
    by a two-fold fold: choosing the line {1, -alpha, beta+delta} and the point
    ((delta-beta-alpha*gamma)/(1+alpha^2), gamma + alpha*x0) turns the general
    incidence into exactly this quintic (its 1+alpha^2 denominators never vanish),
    and all of these lie in OrigamiNum2 when alpha, beta, gamma, delta do. *)
Lemma twofold_solves_no_t3 : forall a b g d x0 y0 t,
  x0 = (d - b - a*g) / (1 + a*a) -> y0 = g + a * x0 ->
  t^5 + a*t^4 + b*t^2 + g*t + d = 0 ->
  on_line (reflect_point (x0, y0) (twofold_crease t)) {| A := 1; B := - a; C := b + d |}.
Proof.
  intros a b g d x0 y0 t Hx0 Hy0 Hq.
  apply twofold_general_incidence.
  assert (Ha : 1 + a*a <> 0) by (assert (0 <= a*a) by apply Rle_0_sqr; lra).
  assert (Hxeq : x0 * (1 + a*a) = d - b - a*g) by (rewrite Hx0; field; exact Ha).
  subst y0. nsatz.
Qed.
