(* extraction.v -- demonstrations, density/classifier catalogs, the FloatGeom
   primitive-float layer, and the OCaml extraction of the certified library.
   Depends on foundations, cyclotomic, geometry. *)
From Stdlib Require Import Reals Lra Field R_sqr Psatz Nsatz Ring Ranalysis1 RingMicromega List ProofIrrelevance ClassicalDescription PeanoNat ZArith Classical ClassicalEpsilon Permutation Bool Arith.Wf_nat.
From Stdlib Require Znumtheory.
Import ListNotations.
Require Import foundations cyclotomic geometry.
Open Scope R_scope.
Theorem showcase_heptagon :
  heptagon_poly cos_2pi_7 = 0 /\ OrigamiNum cos_2pi_7 /\ OrigamiNum sin_2pi_7.
Proof.
  split. exact cos_2pi_7_satisfies_heptagon_poly.
  split. exact cos_2pi_7_is_origami_constructible.
  exact sin_2pi_7_is_origami_constructible.
Qed.

Theorem showcase_heptagon_expanded :
  let c := cos (2 * PI / 7) in
  8*c^3 + 4*c^2 - 4*c - 1 = 0 /\
  chebyshev_T 7 c = 1 /\
  chebyshev_T 7 c - 1 = (c - 1) * (8*c^3 + 4*c^2 - 4*c - 1)^2.
Proof.
  split. exact cos_2pi_7_satisfies_heptagon_poly.
  split. exact chebyshev_7_cos_2pi_7.
  rewrite chebyshev_7_factorization. unfold heptagon_poly. ring.
Qed.

(** II. CUBE DUPLICATION *)
Theorem showcase_delian : cbrt2 * cbrt2 * cbrt2 = 2 /\ OrigamiNum cbrt2.
Proof. split. exact cbrt2_cubes_to_2. exact cbrt2_is_origami. Qed.

Theorem showcase_delian_expanded :
  cbrt2 > 0 /\
  cbrt2 * cbrt2 * cbrt2 = 2 /\
  (forall p q : Z, (q > 0)%Z -> cbrt2 <> IZR p / IZR q) /\
  OrigamiNum cbrt2.
Proof.
  split. exact cbrt2_pos.
  split. exact cbrt2_cubes_to_2.
  split. exact cbrt2_irrational.
  exact cbrt2_is_origami.
Qed.

(** III. STRICT HIERARCHY *)
Theorem showcase_hierarchy : OrigamiDegree 3 /\ ~ EuclideanDegree 3.
Proof. exact origami_strictly_extends_euclidean_degree. Qed.

Theorem showcase_hierarchy_expanded :
  (forall n, EuclideanDegree n -> exists k, n = Nat.pow 2 k) /\
  (exists n, OrigamiDegree n /\ ~ exists k, n = Nat.pow 2 k).
Proof.
  split.
  - induction 1.
    + exists 0%nat. reflexivity.
    + destruct IHEuclideanDegree as [k Hk]. exists (S k). rewrite Hk. simpl. lia.
  - exists 3%nat. split.
    + exact (proj1 origami_strictly_extends_euclidean_degree).
    + intros [k Hk]. destruct k as [|[|k']]; simpl in Hk; lia.
Qed.

(** IV. CARDANO'S FORMULA *)
Theorem showcase_cardano : forall p q,
  cardano_discriminant p q >= 0 -> depressed_cubic p q (cardano_root p q) = 0.
Proof. exact cardano_formula_is_root. Qed.

Theorem showcase_cardano_expanded : forall p q,
  q*q/4 + p*p*p/27 >= 0 ->
  let u := cbrt(-q/2 + sqrt (q*q/4 + p*p*p/27)) in
  let v := cbrt(-q/2 - sqrt (q*q/4 + p*p*p/27)) in
  (u + v)^3 + p*(u + v) + q = 0.
Proof.
  intros p q HD u v.
  pose proof (cardano_formula_is_root p q) as H.
  assert (Hdisc : cardano_discriminant p q >= 0).
  { unfold cardano_discriminant. exact HD. }
  specialize (H Hdisc).
  unfold depressed_cubic, cardano_root, cardano_u, cardano_v, cardano_discriminant in H.
  unfold u, v. lra.
Qed.

(** V. THE HENDECAGON BOUNDARY *)
Theorem showcase_hendecagon :
  OrigamiNum2 cos_2pi_11 /\ ~ is_2_3_smooth (euler_phi 11) /\ is_5_smooth (euler_phi 11).
Proof.
  split. exact cos_2pi_11_in_OrigamiNum2.
  split. rewrite phi_11. exact ten_not_smooth.
  rewrite phi_11. exists 1%nat, 0%nat, 1%nat. reflexivity.
Qed.

Theorem showcase_hendecagon_expanded :
  (2 * cos (2 * PI / 11))^5 + (2 * cos (2 * PI / 11))^4 -
    4*(2 * cos (2 * PI / 11))^3 - 3*(2 * cos (2 * PI / 11))^2 +
    3*(2 * cos (2 * PI / 11)) + 1 = 0 /\
  euler_phi 11 = 10%nat /\
  (forall a b : nat, (Nat.pow 2 a * Nat.pow 3 b)%nat <> 10%nat) /\
  OrigamiNum2 (cos (2 * PI / 11)).
Proof.
  split.
  - pose proof double_cos_2pi_11_minimal_poly as H.
    unfold minpoly_2cos, cos_2pi_11 in H. lra.
  - split. exact phi_11.
    split.
    + intros a b Heq. apply ten_not_smooth. exists a, b. symmetry. exact Heq.
    + exact cos_2pi_11_in_OrigamiNum2.
Qed.

(** VI. DISCRIMINANT DETERMINES ROOTS *)
Theorem showcase_discriminant :
  forall p q, cubic_discriminant p q > 0 ->
    exists r1 r2 r3, r1^3 + p*r1 + q = 0 /\ r2^3 + p*r2 + q = 0 /\ r3^3 + p*r3 + q = 0 /\
                     r1 < r2 < r3.
Proof.
  intros p q Hpos.
  destruct (pos_disc_three_distinct_roots p q Hpos) as [r1 [r2 [r3 [H1 [H2 [H3 [Hlt12 Hlt23]]]]]]].
  exists r1, r2, r3.
  unfold is_cubic_root, depressed_cubic in *.
  repeat split; lra.
Qed.

(** VII. EULER TOTIENT *)
Theorem showcase_euler_phi :
  euler_phi 7 = 6%nat /\ euler_phi 11 = 10%nat /\ euler_phi 13 = 12%nat /\
  euler_phi (2 * 3) = (euler_phi 2 * euler_phi 3)%nat /\
  euler_phi (3 * 5) = (euler_phi 3 * euler_phi 5)%nat.
Proof.
  repeat split; reflexivity.
Qed.

(** Concrete φ computations *)


(** ═══════════════════════════════════════════════════════════════════════════
    DENSITY OF ORIGAMI-CONSTRUCTIBLE n-GONS
    Analysis of how frequently n-gons are single-fold constructible.
    ═══════════════════════════════════════════════════════════════════════════ *)

Fixpoint count_smooth_aux (fuel lo : nat) : nat :=
  match fuel with
  | O => O
  | S f => (if is_2_3_smooth_b (euler_phi lo) then 1 else 0) + count_smooth_aux f (S lo)
  end.

Definition count_smooth_in_range (lo hi : nat) : nat := count_smooth_aux (hi - lo) lo.

Definition density_numerator (lo hi : nat) : nat := count_smooth_in_range lo hi.
Definition density_denominator (lo hi : nat) : nat := hi - lo.


Fixpoint list_smooth_aux (fuel lo : nat) : list nat :=
  match fuel with
  | O => nil
  | S f => (if is_2_3_smooth_b (euler_phi lo) then lo :: nil else nil) ++
           list_smooth_aux f (S lo)
  end.

Definition list_smooth_in_range (lo hi : nat) : list nat := list_smooth_aux (hi - lo) lo.

Fixpoint list_non_smooth_aux (fuel lo : nat) : list nat :=
  match fuel with
  | O => nil
  | S f => (if is_2_3_smooth_b (euler_phi lo) then nil else lo :: nil) ++
           list_non_smooth_aux f (S lo)
  end.

Definition list_non_smooth_in_range (lo hi : nat) : list nat := list_non_smooth_aux (hi - lo) lo.


(** First 20 non-constructible n values *)

(** Key boundary results - verified by computation *)
Lemma smooth_3_to_10 :
  is_2_3_smooth_b (euler_phi 3) = true /\
  is_2_3_smooth_b (euler_phi 4) = true /\
  is_2_3_smooth_b (euler_phi 5) = true /\
  is_2_3_smooth_b (euler_phi 6) = true /\
  is_2_3_smooth_b (euler_phi 7) = true /\
  is_2_3_smooth_b (euler_phi 8) = true /\
  is_2_3_smooth_b (euler_phi 9) = true /\
  is_2_3_smooth_b (euler_phi 10) = true /\
  is_2_3_smooth_b (euler_phi 11) = false.
Proof. repeat split; reflexivity. Qed.

(** Specific counts *)
Definition constructible_3_to_50 : nat := count_smooth_in_range 3 51.
Definition constructible_3_to_100 : nat := count_smooth_in_range 3 101.


(** Verified boundary: 11-gon is first requiring 2-fold *)
Theorem boundary_11 :
  is_2_3_smooth_b (euler_phi 10) = true /\
  is_2_3_smooth_b (euler_phi 11) = false /\
  euler_phi 11 = 10%nat.
Proof.
  repeat split; reflexivity.
Qed.

(** Classification of first 20 non-constructible *)
Definition first_non_constructible : list nat :=
  list_non_smooth_in_range 3 80.


(** φ values for non-constructible n *)


(** ═══════════════════════════════════════════════════════════════════════════
    ALGEBRAIC NUMBER CLASSIFIER
    Given a polynomial degree, determine constructibility level.
    ═══════════════════════════════════════════════════════════════════════════ *)

Inductive ConstructLevel : Type :=
| Rational : ConstructLevel
| Compass : ConstructLevel
| Origami1 : ConstructLevel
| Origami2 : ConstructLevel
| Higher : ConstructLevel.

Definition is_power_of_2_b (n : nat) : bool :=
  Nat.eqb (remove_twos n) 1.

Definition classify_by_degree (d : nat) : ConstructLevel :=
  match d with
  | O => Rational
  | S O => Rational
  | _ =>
    if is_power_of_2_b d then Compass
    else if is_2_3_smooth_b d then Origami1
    else Higher
  end.


(** Degree classification examples *)
Lemma degree_1_rational : classify_by_degree 1 = Rational.
Proof. reflexivity. Qed.

Lemma degree_2_compass : classify_by_degree 2 = Compass.
Proof. reflexivity. Qed.

Lemma degree_3_origami : classify_by_degree 3 = Origami1.
Proof. reflexivity. Qed.

Lemma degree_4_compass : classify_by_degree 4 = Compass.
Proof. reflexivity. Qed.

Lemma degree_5_higher : classify_by_degree 5 = Higher.
Proof. reflexivity. Qed.

Lemma degree_6_origami : classify_by_degree 6 = Origami1.
Proof. reflexivity. Qed.

(** Key algebraic numbers and their degrees *)
Definition sqrt2_degree : nat := 2.
Definition cbrt2_degree : nat := 3.
Definition cos_2pi_7_degree : nat := 3.
Definition cos_2pi_11_degree : nat := 5.
Definition cos_2pi_17_degree : nat := 8.

Lemma sqrt2_is_compass : classify_by_degree sqrt2_degree = Compass.
Proof. reflexivity. Qed.

Lemma cbrt2_degree_origami : classify_by_degree cbrt2_degree = Origami1.
Proof. reflexivity. Qed.

Lemma cos_2pi_7_degree_origami : classify_by_degree cos_2pi_7_degree = Origami1.
Proof. reflexivity. Qed.

Lemma cos_2pi_11_requires_2fold : classify_by_degree cos_2pi_11_degree = Higher.
Proof. reflexivity. Qed.

Lemma cos_2pi_17_is_compass : classify_by_degree cos_2pi_17_degree = Compass.
Proof. reflexivity. Qed.

(** Summary of classification *)
Definition classification_summary : list (nat * ConstructLevel) :=
  map (fun d => (d, classify_by_degree d)) (seq 1 15).


(** The classification theorem: degree d constructibility *)
Theorem degree_classification :
  (classify_by_degree 2 = Compass) /\
  (classify_by_degree 4 = Compass) /\
  (classify_by_degree 8 = Compass) /\
  (classify_by_degree 16 = Compass) /\
  (classify_by_degree 3 = Origami1) /\
  (classify_by_degree 6 = Origami1) /\
  (classify_by_degree 9 = Origami1) /\
  (classify_by_degree 12 = Origami1) /\
  (classify_by_degree 5 = Higher) /\
  (classify_by_degree 7 = Higher) /\
  (classify_by_degree 10 = Higher).
Proof. repeat split; reflexivity. Qed.


(** ═══════════════════════════════════════════════════════════════════════════
    ALGEBRAIC DEGREE OVER Q
    Polynomials over Z evaluated into R, the algebraic-degree predicate, and a
    worked exact-degree result: a real cube root of 2 has degree exactly 3.
    ═══════════════════════════════════════════════════════════════════════════ *)


(** A polynomial over Z is a coefficient list (low degree first), evaluated into R. *)
Open Scope R_scope.
Open Scope R_scope.
Open Scope R_scope.
Definition ngon_constructible (n : nat) : bool :=
  is_2_3_smooth_b (euler_phi n).

(** Repeatedly divide by 5; composed with remove_twos/remove_threes it tests
    5-smoothness, the degree reach of two-fold (quintic-solving) origami. *)
Fixpoint remove_fives_aux (n fuel : nat) : nat :=
  match fuel with
  | O => n
  | S fuel' =>
    if Nat.eqb (Nat.modulo n 5) 0 then remove_fives_aux (Nat.div n 5) fuel' else n
  end.
Definition remove_fives (n : nat) : nat := remove_fives_aux n n.
Definition is_2_3_5_smooth_b (n : nat) : bool :=
  match n with
  | O => false
  | _ => Nat.eqb (remove_fives (remove_threes (remove_twos n))) 1
  end.

(** Tool level for the regular n-gon, keyed on the totient phi(n) (whose 2/3/5
    smoothness matches that of the governing degree phi(n)/2): a power of two is
    compass, 2-3-smooth is single-fold origami, 5-smooth is two-fold origami, and
    anything else needs more than two folds. *)
Definition ngon_tool_required (n : nat) : ConstructLevel :=
  let phi := euler_phi n in
  if is_power_of_2_b phi then Compass
  else if is_2_3_smooth_b phi then Origami1
  else if is_2_3_5_smooth_b phi then Origami2
  else Higher.

Lemma pow2b_implies_2_3_smoothb : forall n,
  is_power_of_2_b n = true -> is_2_3_smooth_b n = true.
Proof.
  intros n H.
  assert (Hrt : remove_twos n = 1%nat) by (apply Nat.eqb_eq; exact H).
  destruct n as [|m].
  - vm_compute in Hrt. discriminate.
  - unfold is_2_3_smooth_b. rewrite Hrt. reflexivity.
Qed.

(** The 43-gon needs more than two folds: phi(43)/2 = 21 = 3.7 is not 5-smooth. *)
Lemma ngon_tool_43_higher : ngon_tool_required 43 = Higher.
Proof. reflexivity. Qed.

(** The hendecagon is the first two-fold n-gon: phi(11)/2 = 5. *)
Lemma ngon_tool_11_origami2 : ngon_tool_required 11 = Origami2.
Proof. reflexivity. Qed.

Lemma ngon_tool_7_origami1 : ngon_tool_required 7 = Origami1.
Proof. reflexivity. Qed.

Lemma ngon_tool_5_compass : ngon_tool_required 5 = Compass.
Proof. reflexivity. Qed.

(** The single-fold boundary is exact: the n-gon is classified compass or
    single-fold origami iff cos(2pi/n) is an origami number, by
    ngon_origami_iff_complete. *)
Theorem ngon_tool_single_fold_correct : forall n, (3 <= n)%nat ->
  ((ngon_tool_required n = Compass \/ ngon_tool_required n = Origami1)
   <-> OrigamiNum (cos (2 * PI / INR n))).
Proof.
  intros n Hn.
  transitivity (is_2_3_smooth_b (euler_phi n) = true).
  - unfold ngon_tool_required.
    destruct (is_power_of_2_b (euler_phi n)) eqn:Hp.
    + split; intro; [ apply pow2b_implies_2_3_smoothb; exact Hp | left; reflexivity ].
    + destruct (is_2_3_smooth_b (euler_phi n)) eqn:Hs.
      * split; intro; [ reflexivity | right; reflexivity ].
      * destruct (is_2_3_5_smooth_b (euler_phi n));
          split; (intros [H|H] || intro H); discriminate.
  - split.
    + intro Hb. apply (proj2 (ngon_origami_iff_complete n Hn)).
      apply (proj1 (is_2_3_smooth_b_correct (euler_phi n))). exact Hb.
    + intro Ho. apply (proj2 (is_2_3_smooth_b_correct (euler_phi n))).
      exact (proj1 (ngon_origami_iff_complete n Hn) Ho).
Qed.

Definition list_constructible_in_range (lo hi : nat) : list nat :=
  list_smooth_aux (hi - lo) lo.

Definition list_non_constructible_in_range (lo hi : nat) : list nat :=
  list_non_smooth_aux (hi - lo) lo.

Definition count_constructible_in_range (lo hi : nat) : nat :=
  count_smooth_aux (hi - lo) lo.

Definition heptagon_cubic_p_num : Z := (-7)%Z.
Definition heptagon_cubic_p_den : Z := 12%Z.
Definition heptagon_cubic_q_num : Z := (-7)%Z.
Definition heptagon_cubic_q_den : Z := 216%Z.

Definition delian_cubic_p : Z := 0%Z.
Definition delian_cubic_q : Z := (-2)%Z.

Fixpoint map_with_phi (ns : list nat) : list (nat * nat) :=
  match ns with
  | nil => nil
  | n :: rest => (n, euler_phi n) :: map_with_phi rest
  end.

Fixpoint classify_range_aux (fuel lo : nat) : list (nat * nat * ConstructLevel) :=
  match fuel with
  | O => nil
  | S f => (lo, euler_phi lo, ngon_tool_required lo) :: classify_range_aux f (S lo)
  end.

Definition classify_range (lo hi : nat) : list (nat * nat * ConstructLevel) :=
  classify_range_aux (hi - lo) lo.

Definition ngon_report (n : nat) : nat * nat * ConstructLevel * bool :=
  (n, euler_phi n, ngon_tool_required n, ngon_constructible n).

Fixpoint batch_report_aux (fuel lo : nat) : list (nat * nat * ConstructLevel * bool) :=
  match fuel with
  | O => nil
  | S f => ngon_report lo :: batch_report_aux f (S lo)
  end.

Definition batch_report (lo hi : nat) : list (nat * nat * ConstructLevel * bool) :=
  batch_report_aux (hi - lo) lo.


From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOcamlZInt.

Extraction Language OCaml.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "( * )" [ "(,)" ].
Extract Inductive nat => "int" [ "0" "succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Constant plus => "(+)".
Extract Constant mult => "( * )".
Extract Constant minus => "(fun n m -> max 0 (n-m))".
Extract Constant Nat.div => "(/)".
Extract Constant Nat.modulo => "(mod)".
Extract Constant Nat.eqb => "(=)".
Extract Constant Nat.leb => "(<=)".
Extract Constant Nat.ltb => "(<)".
Extract Constant negb => "not".
Extract Constant andb => "(&&)".
Extract Constant orb => "(||)".


(* ═══════════════════════════════════════════════════════════════════════════
   COMPUTABLE FLOAT GEOMETRY
   Uses primitive floats for actual numeric computation.
   ═══════════════════════════════════════════════════════════════════════════ *)

From Stdlib Require Import Floats.
From Stdlib Require Import Uint63.
Close Scope R_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope R_scope.
Module FloatGeom.
Open Scope float_scope.

Definition float_pi : float := 0x1.921fb54442d18p+1.

Definition float_point : Type := float * float.
Definition float_line : Type := float * float * float.

Definition fpx (p : float_point) : float := fst p.
Definition fpy (p : float_point) : float := snd p.

Definition fla (l : float_line) : float := fst (fst l).
Definition flb (l : float_line) : float := snd (fst l).
Definition flc (l : float_line) : float := snd l.

Definition float_dist2 (p1 p2 : float_point) : float :=
  let dx := (fpx p1 - fpx p2)%float in
  let dy := (fpy p1 - fpy p2)%float in
  (dx * dx + dy * dy)%float.

Definition float_midpoint (p1 p2 : float_point) : float_point :=
  (((fpx p1 + fpx p2) / 2)%float, ((fpy p1 + fpy p2) / 2)%float).

Definition float_line_through (p1 p2 : float_point) : float_line :=
  let x1 := fpx p1 in let y1 := fpy p1 in
  let x2 := fpx p2 in let y2 := fpy p2 in
  let a := (y2 - y1)%float in
  let b := (x1 - x2)%float in
  let c := (- (a * x1 + b * y1))%float in
  ((a, b), c).

Definition float_reflect (p : float_point) (l : float_line) : float_point :=
  let x := fpx p in let y := fpy p in
  let a := fla l in let b := flb l in let c := flc l in
  let norm2 := (a * a + b * b)%float in
  let k := (2 * (a * x + b * y + c) / norm2)%float in
  ((x - k * a)%float, (y - k * b)%float).

Definition float_perp_bisector (p1 p2 : float_point) : float_line :=
  let mx := fst (float_midpoint p1 p2) in
  let my := snd (float_midpoint p1 p2) in
  let dx := (fpx p2 - fpx p1)%float in
  let dy := (fpy p2 - fpy p1)%float in
  ((dx, dy), (- (dx * mx + dy * my))%float).

Definition float_line_intersection (l1 l2 : float_line) : option float_point :=
  let a1 := fla l1 in let b1 := flb l1 in let c1 := flc l1 in
  let a2 := fla l2 in let b2 := flb l2 in let c2 := flc l2 in
  let det := (a1 * b2 - a2 * b1)%float in
  if PrimFloat.eqb det 0%float then None
  else Some (((b1 * c2 - b2 * c1) / det)%float, ((a2 * c1 - a1 * c2) / det)%float).

Definition float_fold_O1 (p1 p2 : float_point) : float_line :=
  float_line_through p1 p2.

Definition float_fold_O2 (p1 p2 : float_point) : float_line :=
  float_perp_bisector p1 p2.

Definition float_beloch_crease (t : float) : float_line :=
  ((t, (-1)%float), (- (t * t))%float).

Definition float_depressed_cubic (p q t : float) : float :=
  (t * t * t + p * t + q)%float.

Definition float_cubic_discriminant (p q : float) : float :=
  (- 4 * p * p * p - 27 * q * q)%float.

Definition float_cardano_discriminant (p q : float) : float :=
  (q * q / 4 + p * p * p / 27)%float.

Definition float_heptagon_p : float := (-7 / 12)%float.
Definition float_heptagon_q : float := (-7 / 216)%float.
Definition float_delian_p : float := 0%float.
Definition float_delian_q : float := (-2)%float.

Definition float_ngon_angle (n : nat) : float :=
  (2 * float_pi / PrimFloat.of_uint63 (Uint63.of_Z (Z.of_nat n)))%float.

End FloatGeom.
Close Scope R_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope R_scope.
(* ═══════════════════════════════════════════════════════════════════════════
   COMPREHENSIVE EXTRACTION
   ═══════════════════════════════════════════════════════════════════════════ *)

From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOcamlZInt.
From Stdlib Require Import ExtrOCamlFloats.

(* Uint63 extraction - map to OCaml int operations *)
Extract Constant Uint63.lsl => "(lsl)".
Extract Constant Uint63.lor => "(lor)".
Extract Constant Uint63.sub => "(-)".

(* Float64 extraction - map to OCaml float operations *)
Extract Constant PrimFloat.of_uint63 => "Float.of_int".
Extract Constant PrimFloat.add => "(+.)".
Extract Constant PrimFloat.sub => "(-.)".
Extract Constant PrimFloat.mul => "( *.)".
Extract Constant PrimFloat.div => "(/.)".
Extract Constant PrimFloat.opp => "(~-.)".
Extract Constant PrimFloat.eqb => "(=)".

Extraction Language OCaml.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "( * )" [ "(,)" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive nat => "int" [ "0" "succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Constant plus => "(+)".
Extract Constant mult => "( * )".
Extract Constant minus => "(fun n m -> max 0 (n-m))".
Extract Constant Nat.div => "(/)".
Extract Constant Nat.modulo => "(mod)".
Extract Constant Nat.eqb => "(=)".
Extract Constant Nat.leb => "(<=)".
Extract Constant Nat.ltb => "(<)".
Extract Constant negb => "not".
Extract Constant andb => "(&&)".
Extract Constant orb => "(||)".

Extraction "origami_lib"
  euler_phi
  is_2_3_smooth_b
  is_power_of_2_b
  remove_twos
  remove_threes
  ngon_constructible
  ngon_tool_required
  classify_by_degree
  ConstructLevel
  count_constructible_in_range
  list_constructible_in_range
  list_non_constructible_in_range
  classify_range
  batch_report
  ngon_report
  map_with_phi
  heptagon_cubic_p_num
  heptagon_cubic_p_den
  heptagon_cubic_q_num
  heptagon_cubic_q_den
  delian_cubic_p
  delian_cubic_q
  coprime
  count_coprime
  crt_pair
  count_smooth_in_range
  density_numerator
  density_denominator
  list_smooth_in_range
  list_non_smooth_in_range
  constructible_3_to_50
  constructible_3_to_100
  first_non_constructible
  sqrt2_degree
  cbrt2_degree
  cos_2pi_7_degree
  cos_2pi_11_degree
  cos_2pi_17_degree
  minpoly_2cos_degree
  algebraic_degree_cos_2pi_11
  classification_summary
  FloatGeom.float_pi
  FloatGeom.float_point
  FloatGeom.float_line
  FloatGeom.fpx
  FloatGeom.fpy
  FloatGeom.fla
  FloatGeom.flb
  FloatGeom.flc
  FloatGeom.float_dist2
  FloatGeom.float_midpoint
  FloatGeom.float_line_through
  FloatGeom.float_reflect
  FloatGeom.float_perp_bisector
  FloatGeom.float_line_intersection
  FloatGeom.float_fold_O1
  FloatGeom.float_fold_O2
  FloatGeom.float_beloch_crease
  FloatGeom.float_depressed_cubic
  FloatGeom.float_cubic_discriminant
  FloatGeom.float_cardano_discriminant
  FloatGeom.float_heptagon_p
  FloatGeom.float_heptagon_q
  FloatGeom.float_delian_p
  FloatGeom.float_delian_q
  FloatGeom.float_ngon_angle.


(* ============================================================================
   Finite-dimensional linear algebra over a subfield F of R.
   Vectors are reals (elements of an extension field viewed as an F-space).
   ============================================================================ *)

(* F-linear combination of vs with coefficient list cs *)
Close Scope R_scope.
Close Scope R_scope.
Close Scope R_scope.
Close Scope R_scope.
