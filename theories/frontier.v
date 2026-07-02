(* frontier.v -- staging ground for results beyond established origami and
   constructibility mathematics: open conjectures and theorems not yet proved on
   paper.  A result already in the literature belongs in the settled core
   (foundations / cyclotomic / geometry) at the file its dependencies dictate;
   matured frontier results migrate there.

   Sibling of extraction.v; both build on the settled core and neither depends on
   the other.  Never Require extraction: it rebinds sqrt to the primitive machine
   float.

   Current campaign: the k-fold program.  The three-fold geometric layer
   (septic crease, three-fold Lill system, 29-gon/23-gon separations); the
   parametric class OrigamiNumK with k = 1, 2, 3 exactly the settled classes;
   the parametric prime rung step_prime_K via Newton and Vieta; the
   unconditional primitive root; the general Chebyshev prime-power rung; the
   arbitrary-prime-degree extension PolyF with the oktower smooth degree bound;
   ngon_k_fold_iff, the k-fold n-gon theorem at every fold budget; k_fold_lill
   and the general-coefficient Horner chain general_lill_solves.  All
   not-yet-on-paper; migrates down once established.  Open: the two-fold
   alignment-catalog upper bound (todo.md), which needs multivariate
   elimination machinery the development does not yet have. *)
From Stdlib Require Import Reals Lra Field R_sqr Psatz Nsatz Ring Ranalysis1 RingMicromega List ProofIrrelevance ClassicalDescription PeanoNat ZArith Classical Permutation Bool Arith.Wf_nat.
From Stdlib Require Znumtheory.
Import ListNotations.
Require Import foundations cyclotomic geometry.
Open Scope R_scope.

(* ============================================================================
   The three-fold geometric layer.  The septic crease {t, -1, -t^6} is the
   degree-7 analogue of the Beloch crease {t, -1, -t^2} and the two-fold
   quintic crease {t, -1, -t^4}: reflecting (q, p) across it lands on the line
   x = -q exactly along the Bring-Jerrard septic t^7 + p t + q = 0.  The
   simultaneous three-fold Lill system three_fold_lill extends two_fold_lill by
   one more mirror: three creases coupled by two middle bounce segments, each
   perpendicular to two creases at once.
   ============================================================================ *)

(** The three-fold crease with parameter t *)
Definition septic_crease (t : R) : Line := {| A := t; B := -1; C := -(t*t*t*t*t*t) |}.

Lemma septic_crease_wf : forall t, line_wf (septic_crease t).
Proof. intro t; unfold line_wf, septic_crease; simpl; right; lra. Qed.

(** The septic incidence: reflecting (q,p) across the crease lands on x = -q
    exactly along the Bring-Jerrard septic. *)
Lemma septic_crease_reflects : forall p q t,
  t*t*t*t*t*t*t + p * t + q = 0 ->
  on_line (reflect_point (q, p) (septic_crease t)) {| A := 1; B := 0; C := q |}.
Proof.
  intros p q t Hsept.
  unfold reflect_point, septic_crease, on_line; simpl.
  assert (Ht2 : 0 <= t * t) by apply Rle_0_sqr.
  assert (Hd_nz : t * t + (-1) * (-1) <> 0) by lra.
  field_simplify; [| lra].
  nra.
Qed.

(** OrigamiNum3 is closed under the septic-crease root: the three-fold analogue
    of twofold_root_in_ON2. *)
Lemma septic_root_in_ON3 : forall p q t,
  OrigamiNum3 p -> OrigamiNum3 q -> t*t*t*t*t*t*t + p * t + q = 0 -> OrigamiNum3 t.
Proof.
  intros p q t Hp Hq Hsept.
  apply (ON3_sept 0 0 0 0 0 p q t ON3_0 ON3_0 ON3_0 ON3_0 ON3_0 Hp Hq).
  transitivity (t*t*t*t*t*t*t + p * t + q); [ring | exact Hsept].
Qed.

(** The septic crease has OrigamiNum3 coordinates at any of its roots. *)
Lemma septic_crease_good : forall p q t,
  OrigamiNum3 p -> OrigamiNum3 q -> t*t*t*t*t*t*t + p * t + q = 0 ->
  OrigamiNum3 (A (septic_crease t)) /\
  OrigamiNum3 (B (septic_crease t)) /\
  OrigamiNum3 (C (septic_crease t)).
Proof.
  intros p q t Hp Hq Hsept.
  assert (Ht : OrigamiNum3 t) by (apply (septic_root_in_ON3 p q t); assumption).
  assert (Hm1 : OrigamiNum3 (-1))
    by (replace (-1) with (0 - 1) by ring; apply ON3_sub; [apply ON3_0 | apply ON3_1]).
  unfold septic_crease, A, B, C; simpl.
  repeat split; [exact Ht | exact Hm1 |].
  replace (-(t*t*t*t*t*t)) with (0 - t*t*t*t*t*t) by ring.
  apply ON3_sub; [apply ON3_0 |].
  repeat (apply ON3_mul; [| exact Ht]); exact Ht.
Qed.

(** The simultaneous three-fold Lill system: three creases folded at once, each
    the line of one middle segment of the Lill shooting path for the
    Bring-Jerrard septic, the path running from the origin over the coefficient
    lines x = 1 and y = 0 (three bounce pairs) into (1 - p, -q).  The two middle
    bounce segments couple consecutive creases: each is perpendicular to two
    creases at their marked points, so no crease is determined without its
    neighbours. *)
Definition three_fold_lill (p q : R) (g1 g2 g3 : Line) : Prop :=
  exists B1 B2 B3 B4 B5 B6 : Point,
    on_line B1 line_x1 /\ on_line B2 line_xaxis /\
    on_line B3 line_x1 /\ on_line B4 line_xaxis /\
    on_line B5 line_x1 /\ on_line B6 line_xaxis /\
    on_line B1 g1 /\ on_line B2 g1 /\
    on_line B3 g2 /\ on_line B4 g2 /\
    on_line B5 g3 /\ on_line B6 g3 /\
    line_wf g1 /\ line_wf g2 /\ line_wf g3 /\
    line_perp (line_through point_O B1) g1 /\
    line_perp (line_through B2 B3) g1 /\
    line_perp (line_through B2 B3) g2 /\
    line_perp (line_through B4 B5) g2 /\
    line_perp (line_through B4 B5) g3 /\
    line_perp (line_through B6 (1 - p, - q)) g3.

(** Soundness: every simultaneous three-fold Lill manipulation solves the
    Bring-Jerrard septic. *)
Theorem three_fold_lill_septic : forall p q g1 g2 g3,
  three_fold_lill p q g1 g2 g3 ->
  exists t, t * t * t * t * t * t * t + p * t + q = 0.
Proof.
  intros p q g1 g2 g3
    [[xb1 u] [[x2 y2] [[xb3 y3] [[x4 y4] [[xb5 y5] [[x6 y6] H]]]]]].
  destruct H as [HB1x [HB2x [HB3x [HB4x [HB5x [HB6x [HB1g [HB2g [HB3g [HB4g
                 [HB5g [HB6g [Hwf1 [Hwf2 [Hwf3 [HP1 [HP2 [HP3 [HP4 [HP5 HP6]]]]]]]]]]]]]]]]]]]].
  unfold on_line, line_x1, line_xaxis in HB1x, HB2x, HB3x, HB4x, HB5x, HB6x.
  simpl in HB1x, HB2x, HB3x, HB4x, HB5x, HB6x.
  assert (Exb1 : xb1 = 1) by lra.
  assert (Ey2 : y2 = 0) by lra.
  assert (Exb3 : xb3 = 1) by lra.
  assert (Ey4 : y4 = 0) by lra.
  assert (Exb5 : xb5 = 1) by lra.
  assert (Ey6 : y6 = 0) by lra.
  subst xb1 y2 xb3 y4 xb5 y6.
  unfold point_O in HP1.
  unfold line_perp, line_through in HP1, HP2, HP3, HP4, HP5, HP6.
  destruct (Req_EM_T 0 1) as [H01 | _]; [exfalso; lra |].
  simpl in HP1.
  assert (EB1 : B g1 = u * A g1) by lra.
  unfold on_line in HB1g, HB2g, HB3g, HB4g, HB5g, HB6g.
  simpl in HB1g, HB2g, HB3g, HB4g, HB5g, HB6g.
  rewrite EB1 in HB1g.
  assert (HA1 : A g1 <> 0).
  { intro HA0. destruct Hwf1 as [HA | HB]; [exact (HA HA0) |].
    apply HB. rewrite EB1, HA0. ring. }
  assert (Ex2 : x2 = 1 + u * u).
  { apply (Rmult_eq_reg_l (A g1)); [| exact HA1]. nra. }
  subst x2.
  destruct (Req_EM_T (1 + u * u) 1) as [Hdeg | Hne].
  { exfalso. simpl in HP2. apply HA1. lra. }
  simpl in HP2, HP3.
  rewrite EB1 in HP2.
  assert (Hu : u <> 0) by (intro Hu0; apply Hne; nra).
  assert (Ey3 : y3 = - (u * u * u)).
  { apply (Rmult_eq_reg_l (A g1)); [| exact HA1]. nra. }
  subst y3.
  assert (EB2 : B g2 = u * A g2).
  { apply (Rmult_eq_reg_l (u * u)); [nra | nra]. }
  assert (HA2 : A g2 <> 0).
  { intro HA0. destruct Hwf2 as [HA | HB]; [exact (HA HA0) |].
    apply HB. rewrite EB2, HA0. ring. }
  rewrite EB2 in HB3g.
  assert (Ex4 : x4 = 1 - u * u * u * u).
  { apply (Rmult_eq_reg_l (A g2)); [| exact HA2]. nra. }
  subst x4.
  destruct (Req_EM_T (1 - u * u * u * u) 1) as [Hdeg4 | Hne4].
  { exfalso. assert (Hu4 : u * (u * (u * u)) = 0) by lra.
    apply Rmult_integral in Hu4. destruct Hu4 as [H|Hu3]; [exact (Hu H)|].
    apply Rmult_integral in Hu3. destruct Hu3 as [H|Hu2]; [exact (Hu H)|].
    apply Rmult_integral in Hu2. destruct Hu2 as [H|H]; exact (Hu H). }
  simpl in HP4, HP5.
  rewrite EB2 in HP4.
  assert (Ey5 : y5 = u * u * u * u * u).
  { apply (Rmult_eq_reg_l (A g2)); [| exact HA2]. nra. }
  subst y5.
  assert (EB3 : B g3 = u * A g3).
  { apply (Rmult_eq_reg_l (u * u * u * u)); [nra | nra]. }
  assert (HA3 : A g3 <> 0).
  { intro HA0. destruct Hwf3 as [HA | HB]; [exact (HA HA0) |].
    apply HB. rewrite EB3, HA0. ring. }
  rewrite EB3 in HB5g.
  assert (Ex6 : x6 = 1 + u * u * u * u * u * u).
  { apply (Rmult_eq_reg_l (A g3)); [| exact HA3]. nra. }
  subst x6.
  destruct (Req_EM_T (1 + u * u * u * u * u * u) (1 - p)) as [Hdeg6 | Hne6].
  { exfalso. simpl in HP6. apply HA3. lra. }
  simpl in HP6.
  rewrite EB3 in HP6.
  assert (Hq : q = u * p + u * u * u * u * u * u * u).
  { apply (Rmult_eq_reg_l (A g3)); [| exact HA3]. nra. }
  exists (- u). nra.
Qed.

(** Realizability: every root of the Bring-Jerrard septic with q <> 0 is
    produced by an explicit simultaneous three-fold Lill manipulation, whose
    creases are the parallel mirrors of normal (1, -t). *)
Theorem three_fold_lill_realizable : forall p q t,
  t * t * t * t * t * t * t + p * t + q = 0 -> q <> 0 ->
  three_fold_lill p q
    {| A := 1; B := - t; C := - (1 + t * t) |}
    {| A := 1; B := - t; C := - (1 - t * t * t * t) |}
    {| A := 1; B := - t; C := - (1 + t * t * t * t * t * t) |}.
Proof.
  intros p q t Hsept Hq0.
  assert (Ht : t <> 0) by (intro Ht0; apply Hq0; nra).
  exists (1, - t), (1 + t * t, 0), (1, t * t * t), (1 - t * t * t * t, 0),
         (1, - (t * t * t * t * t)), (1 + t * t * t * t * t * t, 0).
  unfold on_line, line_x1, line_xaxis, line_wf, line_perp, line_through, point_O.
  destruct (Req_EM_T 0 1) as [H01 | _]; [exfalso; lra |].
  destruct (Req_EM_T (1 + t * t) 1) as [Hdeg | _]; [exfalso; nra |].
  assert (Hne4 : (1 - t * t * t * t) <> 1).
  { intro Hc. apply Ht. assert (Hu4 : t * (t * (t * t)) = 0) by lra.
    apply Rmult_integral in Hu4. destruct Hu4 as [H|Hu3]; [exact H|].
    apply Rmult_integral in Hu3. destruct Hu3 as [H|Hu2]; [exact H|].
    apply Rmult_integral in Hu2. destruct Hu2 as [H|H]; exact H. }
  destruct (Req_EM_T (1 - t * t * t * t) 1) as [Hdeg4 | _]; [exfalso; exact (Hne4 Hdeg4) |].
  assert (Hne6 : (1 + t * t * t * t * t * t) <> (1 - p)).
  { intro Heq. apply Hq0. nra. }
  destruct (Req_EM_T (1 + t * t * t * t * t * t) (1 - p)) as [Hdeg6 | _];
    [exfalso; exact (Hne6 Hdeg6) |].
  simpl.
  repeat split; try (left; lra); try nra.
Qed.

(** The three-fold analogue of beloch_fold_satisfies_O6 and
    two_fold_axiom_grounds_crease: every simultaneous three-fold Lill
    manipulation yields a Bring-Jerrard septic root whose crease
    {t, -1, -t^6} carries the septic incidence. *)
Theorem three_fold_axiom_grounds_crease : forall p q g1 g2 g3,
  three_fold_lill p q g1 g2 g3 ->
  exists t, t * t * t * t * t * t * t + p * t + q = 0 /\
    on_line (reflect_point (q, p) (septic_crease t)) {| A := 1; B := 0; C := q |}.
Proof.
  intros p q g1 g2 g3 H.
  destruct (three_fold_lill_septic p q g1 g2 g3 H) as [t Ht].
  exists t. split; [exact Ht |].
  apply septic_crease_reflects. exact Ht.
Qed.

(* ============================================================================
   First-polygon separations.  The 29-gon is three-fold but not two-fold
   constructible (phi(29) = 28 = 2^2 * 7), and is the first such polygon: every
   m-gon with m < 29 is either two-fold constructible or beyond three-fold.
   The 23-gon is the first regular polygon beyond even three-fold origami
   (phi(23) = 22 = 2 * 11).
   ============================================================================ *)

Lemma prime_Z_11 : Znumtheory.prime (Z.of_nat 11).
Proof.
  change (Z.of_nat 11) with 11%Z. apply Znumtheory.prime_intro; [lia|].
  intros n Hn. apply Znumtheory.Zgcd_1_rel_prime.
  assert (Hc : (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7
                \/ n = 8 \/ n = 9 \/ n = 10)%Z) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.
Qed.

Lemma phi_29 : euler_phi 29 = 28%nat. Proof. reflexivity. Qed.
Lemma phi_23 : euler_phi 23 = 22%nat. Proof. reflexivity. Qed.

Lemma not_5_smooth_28 : ~ is_5_smooth 28.
Proof.
  intros [a [b [c H]]].
  assert (Hd : Nat.divide 7 (2 ^ a * 3 ^ b * 5 ^ c)%nat).
  { rewrite <- H. exists 4%nat. reflexivity. }
  destruct (prime_dvd_2a3b5c 7 a b c prime_Z_7 Hd) as [E|[E|E]]; lia.
Qed.

Lemma not_7_smooth_22 : ~ is_7_smooth 22.
Proof.
  intros [a [b [c [d H]]]].
  assert (Hd11 : Nat.divide 11 (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d)%nat).
  { rewrite <- H. exists 2%nat. reflexivity. }
  destruct (prime_dvd_2a3b5c7d 11 a b c d prime_Z_11 Hd11) as [E|[E|[E|E]]]; lia.
Qed.

(** The 29-gon is three-fold constructible ... *)
Theorem ngon_29_three_fold : OrigamiNum3 (cos (2 * PI / INR 29)).
Proof.
  apply (proj2 (ngon_three_fold_iff 29 ltac:(lia))).
  rewrite phi_29. exists 2%nat, 0%nat, 0%nat, 1%nat. reflexivity.
Qed.

(** ... but not two-fold constructible. *)
Theorem ngon_29_not_two_fold : ~ OrigamiNum2 (cos (2 * PI / INR 29)).
Proof.
  apply cos_2pi_n_not_two_fold_clean; [lia|].
  rewrite phi_29. exact not_5_smooth_28.
Qed.

(** The 23-gon is beyond even three-fold origami. *)
Theorem ngon_23_not_three_fold : ~ OrigamiNum3 (cos (2 * PI / INR 23)).
Proof.
  apply cos_2pi_n_not_three_fold_clean; [lia|].
  rewrite phi_23. exact not_7_smooth_22.
Qed.

(** phi(m) is 5-smooth for every 3 <= m < 29 except m = 23. *)
Lemma small_phi_5_smooth : forall m, (3 <= m < 29)%nat -> (m <> 23)%nat ->
  is_5_smooth (euler_phi m).
Proof.
  intros m Hm Hne.
  do 3 (destruct m as [|m]; [lia|]).
  destruct m as [|m]. { exists 1%nat, 0%nat, 0%nat. reflexivity. }
  destruct m as [|m]. { exists 1%nat, 0%nat, 0%nat. reflexivity. }
  destruct m as [|m]. { exists 2%nat, 0%nat, 0%nat. reflexivity. }
  destruct m as [|m]. { exists 1%nat, 0%nat, 0%nat. reflexivity. }
  destruct m as [|m]. { exists 1%nat, 1%nat, 0%nat. reflexivity. }
  destruct m as [|m]. { exists 2%nat, 0%nat, 0%nat. reflexivity. }
  destruct m as [|m]. { exists 1%nat, 1%nat, 0%nat. reflexivity. }
  destruct m as [|m]. { exists 2%nat, 0%nat, 0%nat. reflexivity. }
  destruct m as [|m]. { exists 1%nat, 0%nat, 1%nat. reflexivity. }
  destruct m as [|m]. { exists 2%nat, 0%nat, 0%nat. reflexivity. }
  destruct m as [|m]. { exists 2%nat, 1%nat, 0%nat. reflexivity. }
  destruct m as [|m]. { exists 1%nat, 1%nat, 0%nat. reflexivity. }
  destruct m as [|m]. { exists 3%nat, 0%nat, 0%nat. reflexivity. }
  destruct m as [|m]. { exists 3%nat, 0%nat, 0%nat. reflexivity. }
  destruct m as [|m]. { exists 4%nat, 0%nat, 0%nat. reflexivity. }
  destruct m as [|m]. { exists 1%nat, 1%nat, 0%nat. reflexivity. }
  destruct m as [|m]. { exists 1%nat, 2%nat, 0%nat. reflexivity. }
  destruct m as [|m]. { exists 3%nat, 0%nat, 0%nat. reflexivity. }
  destruct m as [|m]. { exists 2%nat, 1%nat, 0%nat. reflexivity. }
  destruct m as [|m]. { exists 1%nat, 0%nat, 1%nat. reflexivity. }
  destruct m as [|m]. { exfalso. apply Hne. reflexivity. }
  destruct m as [|m]. { exists 3%nat, 0%nat, 0%nat. reflexivity. }
  destruct m as [|m]. { exists 2%nat, 0%nat, 1%nat. reflexivity. }
  destruct m as [|m]. { exists 2%nat, 1%nat, 0%nat. reflexivity. }
  destruct m as [|m]. { exists 1%nat, 2%nat, 0%nat. reflexivity. }
  destruct m as [|m]. { exists 2%nat, 1%nat, 0%nat. reflexivity. }
  lia.
Qed.

(** THE FIRST EXACTLY-THREE-FOLD POLYGON: the 29-gon is three-fold but not
    two-fold constructible, and every smaller polygon is either two-fold
    constructible or beyond three-fold. *)
Theorem ngon_29_first_exactly_three_fold :
  OrigamiNum3 (cos (2 * PI / INR 29)) /\
  ~ OrigamiNum2 (cos (2 * PI / INR 29)) /\
  (forall m, (3 <= m < 29)%nat ->
     OrigamiNum2 (cos (2 * PI / INR m)) \/ ~ OrigamiNum3 (cos (2 * PI / INR m))).
Proof.
  split; [exact ngon_29_three_fold | split; [exact ngon_29_not_two_fold |]].
  intros m Hm.
  destruct (Nat.eq_dec m 23) as [-> | Hne].
  - right. exact ngon_23_not_three_fold.
  - left. apply cos_2pi_n_two_fold_smooth; [lia |].
    apply small_phi_5_smooth; [exact Hm | exact Hne].
Qed.

(* ============================================================================
   The parametric prime rung.  Newton's identities (newton_esym_step) turn the
   K-known power sums of the rho sub-periods into K-known elementary symmetric
   functions; the Vieta polynomial presents the finest period as a root of a
   monic degree-rho polynomial with K coefficients, which one abstract
   degree-rho solver closes.  step2_K, step3_K, step5_K, step7_K are the
   rho = 2, 3, 5, 7 instances of this single rung.
   ============================================================================ *)

Lemma tops_embed : forall K, tower_ops K -> forall x, OrigamiNum x -> K x.
Proof. intros K HK; destruct HK; assumption. Qed.
Lemma tops_add : forall K, tower_ops K -> forall x y, K x -> K y -> K (x + y).
Proof. intros K HK; destruct HK; assumption. Qed.
Lemma tops_sub : forall K, tower_ops K -> forall x y, K x -> K y -> K (x - y).
Proof. intros K HK; destruct HK; assumption. Qed.
Lemma tops_mul : forall K, tower_ops K -> forall x y, K x -> K y -> K (x * y).
Proof. intros K HK; destruct HK; assumption. Qed.
Lemma tops_div : forall K, tower_ops K -> forall x y, K x -> K y -> y <> 0 -> K (x / y).
Proof. intros K HK; destruct HK; assumption. Qed.
Lemma tops_neg : forall K, tower_ops K -> forall x, K x -> K (- x).
Proof. intros K HK; destruct HK; assumption. Qed.

Lemma fsum_K : forall (K : R -> Prop), tower_ops K ->
  forall (m : nat) (f : nat -> R),
  (forall i, (i < m)%nat -> K (f i)) -> K (fsum m f).
Proof.
  intros K HK m f. induction m as [|m IH]; intro H; cbn [fsum].
  - apply (tops_embed K HK), ON_0.
  - apply (tops_add K HK); [apply IH; intros i Hi; apply H; lia | apply H; lia].
Qed.

Lemma pow_m1_cases : forall j, (-1) ^ j = 1 \/ (-1) ^ j = -1.
Proof.
  induction j as [|j IH].
  - left. reflexivity.
  - cbn [pow]. destruct IH as [E|E]; rewrite E; [right | left]; ring.
Qed.

Lemma K_pow_m1 : forall (K : R -> Prop), tower_ops K -> forall j, K ((-1) ^ j).
Proof.
  intros K HK j. destruct (pow_m1_cases j) as [E|E]; rewrite E.
  - apply (tops_embed K HK), ON_1.
  - replace (-1) with (0 - 1) by ring.
    apply (tops_sub K HK); apply (tops_embed K HK); [apply ON_0 | apply ON_1].
Qed.

(** Every elementary symmetric function of a list with K-known power sums is
    itself K-known, by the Newton recurrence in characteristic zero. *)
Lemma esym_K : forall (K : R -> Prop), tower_ops K ->
  forall xs, (forall j, (1 <= j)%nat -> K (powsum xs j)) ->
  forall k, K (esym k xs).
Proof.
  intros K HK xs Hpow k.
  induction k as [k IHk] using (well_founded_induction lt_wf).
  destruct k as [|k'].
  - rewrite esym_0. apply (tops_embed K HK), ON_1.
  - pose proof (newton_esym_step xs (S k') ltac:(lia)) as HN.
    assert (HkR : INR (S k') <> 0) by (apply not_0_INR; lia).
    assert (Heq : esym (S k') xs
      = - (-1) ^ S k'
        * fsum (S k') (fun i => (-1) ^ i * esym i xs * powsum xs (S k' - i))
        / INR (S k')).
    { apply (Rmult_eq_reg_l (INR (S k'))); [| exact HkR].
      rewrite HN. field. exact HkR. }
    rewrite Heq.
    apply (tops_div K HK);
      [| apply (tops_embed K HK), Origami_nat | exact HkR].
    apply (tops_mul K HK).
    + replace (- (-1) ^ S k') with ((-1) ^ S (S k')) by (cbn [pow]; ring).
      apply K_pow_m1; exact HK.
    + apply fsum_K; [exact HK |]. intros i Hi.
      apply (tops_mul K HK);
        [apply (tops_mul K HK); [apply K_pow_m1; exact HK | apply IHk; lia] |].
      apply Hpow. lia.
Qed.

Lemma powsum_map : forall (f : nat -> R) (L : list nat) (k : nat),
  powsum (map f L) k = rsum L (fun l => f l ^ k).
Proof.
  intros f L k. induction L as [|x L IH].
  - reflexivity.
  - cbn [map powsum]. rewrite IH, rsum_consL. reflexivity.
Qed.

Lemma pevalR_nth_sum : forall (ps : list R) (x : R),
  pevalR ps x = fsum (length ps) (fun i => nth i ps 0 * x ^ i).
Proof.
  induction ps as [|c ps' IH]; intro x.
  - reflexivity.
  - cbn [pevalR length]. rewrite fsum_S_shift.
    cbn [nth pow].
    rewrite (fsum_ext (length ps')
               (fun i => nth i ps' 0 * (x * x ^ i))
               (fun i => x * (nth i ps' 0 * x ^ i)))
      by (intros; ring).
    rewrite fsum_scale. rewrite <- IH. ring.
Qed.

(** THE PARAMETRIC PRIME RUNG: one abstract degree-rho solver drives the tower
    step for every prime rung at once. *)
Lemma step_prime_K : forall (P : nat) (g : Z),
  (5 <= P)%nat -> per P g (P - 1) ->
  forall (K : R -> Prop), tower_ops K ->
  forall (rho : nat), (2 <= rho)%nat ->
  (forall (c : nat -> R) (r : R),
     (forall i, (i < rho)%nat -> K (c i)) ->
     fsum rho (fun i => c i * r ^ i) + r ^ rho = 0 -> K r) ->
  forall (D : nat) (w : Z), (1 <= D)%nat -> Nat.divide (D * rho) (P - 1) ->
  (forall v, K (PerV P g v D)) ->
  K (PerV P g w (D * rho)).
Proof.
  intros P g HP5 Hg K HK rho Hrho Hsolver D w HD Hdiv IH.
  set (xs := map (fun l => PerV P g (w * zpn g (D * l))%Z (D * rho)) (seq 0 rho)).
  assert (Hlen : length xs = rho)
    by (unfold xs; rewrite length_map, length_seq; reflexivity).
  assert (Hpow : forall j, (1 <= j)%nat -> K (powsum xs j)).
  { intros j Hj. unfold xs. rewrite powsum_map.
    destruct j as [|j']; [lia |].
    exact (psum_K P g HP5 Hg K HK D rho w j' HD ltac:(lia) Hdiv IH). }
  assert (Hesym : forall k, K (esym k xs)) by (apply esym_K; assumption).
  assert (Hx0in : In (PerV P g (w * zpn g (D * 0))%Z (D * rho)) xs).
  { unfold xs.
    apply (in_map (fun l => PerV P g (w * zpn g (D * l))%Z (D * rho))
             (seq 0 rho) 0%nat).
    apply in_seq. lia. }
  assert (Hx0eq : PerV P g (w * zpn g (D * 0))%Z (D * rho) = PerV P g w (D * rho)).
  { f_equal. rewrite Nat.mul_0_r. cbn [zpn]. ring. }
  set (x0 := PerV P g (w * zpn g (D * 0))%Z (D * rho)) in *.
  pose proof (vieta_root xs x0 Hx0in) as Hroot.
  rewrite pevalR_nth_sum in Hroot.
  rewrite vieta_length, Hlen in Hroot.
  cbn [fsum] in Hroot.
  assert (Htop : nth rho (vieta xs) 0 = 1) by (rewrite <- Hlen; apply vieta_top).
  rewrite Htop in Hroot.
  rewrite <- Hx0eq.
  apply (Hsolver (fun i => nth i (vieta xs) 0) x0).
  - intros i Hi.
    rewrite (vieta_nth xs i) by lia.
    apply (tops_mul K HK); [apply K_pow_m1; exact HK | apply Hesym].
  - cbn beta. lra.
Qed.

(** tower_cos_K driven entirely by the parametric rung: one solver family, one
    per prime divisor of P - 1, closes cos(2*PI/P). *)
Lemma tower_cos_prime_rungs : forall (P : nat) (g : Z),
  Znumtheory.prime (Z.of_nat P) -> (5 <= P)%nat ->
  per P g (P - 1) ->
  (forall k, (1 <= k < P - 1)%nat -> ~ cg (Z.of_nat P) (zpn g k) 1%Z) ->
  (1 <= g < Z.of_nat P)%Z ->
  forall (K : R -> Prop), tower_ops K ->
  (forall rho, Znumtheory.prime (Z.of_nat rho) -> Nat.divide rho (P - 1) ->
     forall (c : nat -> R) (r : R),
       (forall i, (i < rho)%nat -> K (c i)) ->
       fsum rho (fun i => c i * r ^ i) + r ^ rho = 0 -> K r) ->
  K (cos (2 * PI / INR P)).
Proof.
  intros P g HP HP5 Hg Hgord Hgr K HK Hsolvers.
  apply (tower_cos_K P g HP HP5 Hgord Hgr K HK).
  intros q D w Hq Hqn HD HDdiv IHq.
  assert (Hq2 : (2 <= q)%nat) by (destruct Hq as [Hq1 _]; lia).
  exact (step_prime_K P g HP5 Hg K HK q Hq2 (Hsolvers q Hq Hqn) D w HD HDdiv IHq).
Qed.

(* ============================================================================
   OrigamiNumK: the parametric fold-strength class.  The rationals closed under
   field operations, square roots, and roots of monic prime-degree polynomials
   of degree at most 2k+1.  k = 1, 2, 3 recover the single-, two-, and
   three-fold classes exactly.
   ============================================================================ *)

Inductive OrigamiNumK (kk : nat) : R -> Prop :=
| ONK_0 : OrigamiNumK kk 0
| ONK_1 : OrigamiNumK kk 1
| ONK_add : forall x y, OrigamiNumK kk x -> OrigamiNumK kk y -> OrigamiNumK kk (x + y)
| ONK_sub : forall x y, OrigamiNumK kk x -> OrigamiNumK kk y -> OrigamiNumK kk (x - y)
| ONK_mul : forall x y, OrigamiNumK kk x -> OrigamiNumK kk y -> OrigamiNumK kk (x * y)
| ONK_inv : forall x, OrigamiNumK kk x -> x <> 0 -> OrigamiNumK kk (/ x)
| ONK_sqrt : forall x, OrigamiNumK kk x -> 0 <= x -> OrigamiNumK kk (sqrt x)
| ONK_proot : forall (d : nat) (c : nat -> R) (r : R),
    Znumtheory.prime (Z.of_nat d) -> (d <= 2 * kk + 1)%nat ->
    (forall i, (i < d)%nat -> OrigamiNumK kk (c i)) ->
    fsum d (fun i => c i * r ^ i) + r ^ d = 0 ->
    OrigamiNumK kk r.

Lemma ONK_neg : forall kk x, OrigamiNumK kk x -> OrigamiNumK kk (- x).
Proof.
  intros kk x Hx. replace (- x) with (0 - x) by ring.
  apply ONK_sub; [apply ONK_0 | exact Hx].
Qed.

Lemma ONK_div : forall kk x y,
  OrigamiNumK kk x -> OrigamiNumK kk y -> y <> 0 -> OrigamiNumK kk (x / y).
Proof.
  intros kk x y Hx Hy Hne. unfold Rdiv.
  apply ONK_mul; [exact Hx | apply ONK_inv; assumption].
Qed.

(** OrigamiNum embeds into every OrigamiNumK with k >= 1. *)
Lemma Origami_in_ONK : forall kk, (1 <= kk)%nat ->
  forall x, OrigamiNum x -> OrigamiNumK kk x.
Proof.
  intros kk Hkk x Hx. induction Hx.
  - apply ONK_0.
  - apply ONK_1.
  - apply ONK_add; assumption.
  - apply ONK_sub; assumption.
  - apply ONK_mul; assumption.
  - apply ONK_inv; assumption.
  - apply ONK_sqrt; assumption.
  - apply (ONK_proot kk 3
             (fun i => match i with O => b | S O => a | _ => 0 end) r).
    + exact prime_Z_3.
    + lia.
    + intros i Hi.
      destruct i as [|[|[|i]]]; [assumption | assumption | apply ONK_0 | exfalso; lia].
    + cbn [fsum]. nra.
Qed.

Lemma onk_tower_ops : forall kk, (1 <= kk)%nat -> tower_ops (OrigamiNumK kk).
Proof.
  intros kk Hkk. constructor.
  - intros x Hx. apply Origami_in_ONK; assumption.
  - exact (ONK_add kk).
  - exact (ONK_sub kk).
  - exact (ONK_mul kk).
  - exact (ONK_div kk).
  - exact (ONK_neg kk).
Qed.

(** k = 1 is exactly single-fold origami. *)
Lemma ONK_1_sound : forall x, OrigamiNumK 1 x -> OrigamiNum x.
Proof.
  intros x Hx.
  induction Hx as [ | | x y _ IH1 _ IH2 | x y _ IH1 _ IH2 | x y _ IH1 _ IH2
                  | x _ IH Hne | x _ IH Hnn | d c r Hp Hle Hc IHc Heq ].
  - apply ON_0.
  - apply ON_1.
  - apply ON_add; assumption.
  - apply ON_sub; assumption.
  - apply ON_mul; assumption.
  - apply ON_inv; assumption.
  - apply ON_sqrt; assumption.
  - assert (Hd2 : (2 <= d)%nat) by (destruct Hp as [Hgt _]; lia).
    assert (Hcase : (d = 2 \/ d = 3)%nat) by lia.
    destruct Hcase as [-> | ->].
    + apply (origami_general_quadratic (c 1%nat) (c 0%nat) r).
      * apply IHc; lia.
      * apply IHc; lia.
      * cbn [fsum] in Heq. nra.
    + apply (origami_general_cubic (c 2%nat) (c 1%nat) (c 0%nat) r).
      * apply IHc; lia.
      * apply IHc; lia.
      * apply IHc; lia.
      * cbn [fsum] in Heq. nra.
Qed.

Theorem OrigamiNumK_1_iff : forall x, OrigamiNumK 1 x <-> OrigamiNum x.
Proof.
  intro x. split; [apply ONK_1_sound | apply Origami_in_ONK; lia].
Qed.

(** k = 2 is exactly two-fold origami. *)
Lemma ONK_2_sound : forall x, OrigamiNumK 2 x -> OrigamiNum2 x.
Proof.
  intros x Hx.
  induction Hx as [ | | x y _ IH1 _ IH2 | x y _ IH1 _ IH2 | x y _ IH1 _ IH2
                  | x _ IH Hne | x _ IH Hnn | d c r Hp Hle Hc IHc Heq ].
  - apply ON2_0.
  - apply ON2_1.
  - apply ON2_add; assumption.
  - apply ON2_sub; assumption.
  - apply ON2_mul; assumption.
  - apply ON2_inv; assumption.
  - apply ON2_sqrt; assumption.
  - assert (Hd2 : (2 <= d)%nat) by (destruct Hp as [Hgt _]; lia).
    assert (Hd4 : d <> 4%nat).
    { intro E. subst d. pose proof (is_prime_of_Z 4 Hp) as [_ Hdd].
      destruct (Hdd 2%nat ltac:(lia) ltac:(exists 2%nat; reflexivity)) as [E'|E']; lia. }
    assert (Hcase : (d = 2 \/ d = 3 \/ d = 5)%nat) by lia.
    destruct Hcase as [-> | [-> | ->]].
    + apply (ON2_general_quadratic (c 1%nat) (c 0%nat) r).
      * apply IHc; lia.
      * apply IHc; lia.
      * cbn [fsum] in Heq. nra.
    + apply (ON2_general_cubic (c 2%nat) (c 1%nat) (c 0%nat) r).
      * apply IHc; lia.
      * apply IHc; lia.
      * apply IHc; lia.
      * cbn [fsum] in Heq. nra.
    + apply (ON2_quint (c 4%nat) (c 3%nat) (c 2%nat) (c 1%nat) (c 0%nat) r).
      * apply IHc; lia.
      * apply IHc; lia.
      * apply IHc; lia.
      * apply IHc; lia.
      * apply IHc; lia.
      * cbn [fsum] in Heq. nra.
Qed.

Lemma Origami2_in_ONK_2 : forall x, OrigamiNum2 x -> OrigamiNumK 2 x.
Proof.
  intros x Hx. induction Hx.
  - apply ONK_0.
  - apply ONK_1.
  - apply ONK_add; assumption.
  - apply ONK_sub; assumption.
  - apply ONK_mul; assumption.
  - apply ONK_inv; assumption.
  - apply ONK_sqrt; assumption.
  - apply (ONK_proot 2 3
             (fun i => match i with O => b | S O => a | _ => 0 end) r).
    + exact prime_Z_3.
    + lia.
    + intros i Hi.
      destruct i as [|[|[|i]]]; [assumption | assumption | apply ONK_0 | exfalso; lia].
    + cbn [fsum]. nra.
  - apply (ONK_proot 2 5
             (fun i => match i with
                       | O => e | S O => d | S (S O) => c
                       | S (S (S O)) => b | S (S (S (S O))) => a | _ => 0 end) r).
    + exact prime_Z_5.
    + lia.
    + intros i Hi.
      destruct i as [|[|[|[|[|i]]]]];
        [assumption | assumption | assumption | assumption | assumption | exfalso; lia].
    + cbn [fsum]. nra.
Qed.

Theorem OrigamiNumK_2_iff : forall x, OrigamiNumK 2 x <-> OrigamiNum2 x.
Proof.
  intro x. split; [apply ONK_2_sound | apply Origami2_in_ONK_2].
Qed.

(** k = 3 is exactly three-fold origami. *)
Lemma ONK_3_sound : forall x, OrigamiNumK 3 x -> OrigamiNum3 x.
Proof.
  intros x Hx.
  induction Hx as [ | | x y _ IH1 _ IH2 | x y _ IH1 _ IH2 | x y _ IH1 _ IH2
                  | x _ IH Hne | x _ IH Hnn | d c r Hp Hle Hc IHc Heq ].
  - apply ON3_0.
  - apply ON3_1.
  - apply ON3_add; assumption.
  - apply ON3_sub; assumption.
  - apply ON3_mul; assumption.
  - apply ON3_inv; assumption.
  - apply ON3_sqrt; assumption.
  - assert (Hd2 : (2 <= d)%nat) by (destruct Hp as [Hgt _]; lia).
    assert (Hd4 : d <> 4%nat).
    { intro E. subst d. pose proof (is_prime_of_Z 4 Hp) as [_ Hdd].
      destruct (Hdd 2%nat ltac:(lia) ltac:(exists 2%nat; reflexivity)) as [E'|E']; lia. }
    assert (Hd6 : d <> 6%nat).
    { intro E. subst d. pose proof (is_prime_of_Z 6 Hp) as [_ Hdd].
      destruct (Hdd 2%nat ltac:(lia) ltac:(exists 3%nat; reflexivity)) as [E'|E']; lia. }
    assert (Hcase : (d = 2 \/ d = 3 \/ d = 5 \/ d = 7)%nat) by lia.
    destruct Hcase as [-> | [-> | [-> | ->]]].
    + apply (ON3_general_quadratic (c 1%nat) (c 0%nat) r).
      * apply IHc; lia.
      * apply IHc; lia.
      * cbn [fsum] in Heq. nra.
    + apply (ON3_general_cubic (c 2%nat) (c 1%nat) (c 0%nat) r).
      * apply IHc; lia.
      * apply IHc; lia.
      * apply IHc; lia.
      * cbn [fsum] in Heq. nra.
    + apply (ON3_quint (c 4%nat) (c 3%nat) (c 2%nat) (c 1%nat) (c 0%nat) r).
      * apply IHc; lia.
      * apply IHc; lia.
      * apply IHc; lia.
      * apply IHc; lia.
      * apply IHc; lia.
      * cbn [fsum] in Heq. nra.
    + apply (ON3_sept (c 6%nat) (c 5%nat) (c 4%nat) (c 3%nat) (c 2%nat) (c 1%nat) (c 0%nat) r).
      * apply IHc; lia.
      * apply IHc; lia.
      * apply IHc; lia.
      * apply IHc; lia.
      * apply IHc; lia.
      * apply IHc; lia.
      * apply IHc; lia.
      * cbn [fsum] in Heq. nra.
Qed.

Lemma Origami3_in_ONK_3 : forall x, OrigamiNum3 x -> OrigamiNumK 3 x.
Proof.
  intros x Hx. induction Hx.
  - apply ONK_0.
  - apply ONK_1.
  - apply ONK_add; assumption.
  - apply ONK_sub; assumption.
  - apply ONK_mul; assumption.
  - apply ONK_inv; assumption.
  - apply ONK_sqrt; assumption.
  - apply (ONK_proot 3 3
             (fun i => match i with O => b | S O => a | _ => 0 end) r).
    + exact prime_Z_3.
    + lia.
    + intros i Hi.
      destruct i as [|[|[|i]]]; [assumption | assumption | apply ONK_0 | exfalso; lia].
    + cbn [fsum]. nra.
  - apply (ONK_proot 3 5
             (fun i => match i with
                       | O => e | S O => d | S (S O) => c
                       | S (S (S O)) => b | S (S (S (S O))) => a | _ => 0 end) r).
    + exact prime_Z_5.
    + lia.
    + intros i Hi.
      destruct i as [|[|[|[|[|i]]]]];
        [assumption | assumption | assumption | assumption | assumption | exfalso; lia].
    + cbn [fsum]. nra.
  - apply (ONK_proot 3 7
             (fun i => match i with
                       | O => g | S O => f | S (S O) => e
                       | S (S (S O)) => d | S (S (S (S O))) => c
                       | S (S (S (S (S O)))) => b
                       | S (S (S (S (S (S O))))) => a | _ => 0 end) r).
    + exact prime_Z_7.
    + lia.
    + intros i Hi.
      destruct i as [|[|[|[|[|[|[|i]]]]]]];
        [assumption | assumption | assumption | assumption
         | assumption | assumption | assumption | exfalso; lia].
    + cbn [fsum]. nra.
Qed.

Theorem OrigamiNumK_3_iff : forall x, OrigamiNumK 3 x <-> OrigamiNum3 x.
Proof.
  intro x. split; [apply ONK_3_sound | apply Origami3_in_ONK_3].
Qed.

(** The class is monotone in the fold budget. *)
Lemma ONK_mono : forall kk kk', (kk <= kk')%nat ->
  forall x, OrigamiNumK kk x -> OrigamiNumK kk' x.
Proof.
  intros kk kk' Hle x Hx. induction Hx.
  - apply ONK_0.
  - apply ONK_1.
  - apply ONK_add; assumption.
  - apply ONK_sub; assumption.
  - apply ONK_mul; assumption.
  - apply ONK_inv; assumption.
  - apply ONK_sqrt; assumption.
  - apply (ONK_proot kk' d c r); [assumption | lia | assumption | assumption].
Qed.

(* ============================================================================
   The unconditional primitive root.  Every prime p has a primitive root mod p:
   element_order_unitary assembles it by strong induction over the unitary
   divisors of p-1, taking one element per full prime power from
   exists_order_ppow and combining coprime orders with order_coprime_mul.
   primitive_root, primitive_root_5smooth, and primitive_root_7smooth are its
   smoothness-restricted instances.
   ============================================================================ *)

Lemma prime_not_div_coprime : forall q r,
  Znumtheory.prime (Z.of_nat q) -> ~ Nat.divide q r -> Nat.gcd q r = 1%nat.
Proof.
  intros q r Hq Hnd.
  pose proof (is_prime_of_Z q Hq) as [Hq1 Hdd].
  destruct (Nat.eq_dec (Nat.gcd q r) 0) as [Hg0 | Hgne].
  - exfalso. pose proof (Nat.gcd_divide_l q r) as Hl. rewrite Hg0 in Hl.
    apply Nat.divide_0_l in Hl. lia.
  - destruct (Hdd (Nat.gcd q r) ltac:(lia) (Nat.gcd_divide_l q r)) as [E | E].
    + exact E.
    + exfalso. apply Hnd. rewrite <- E. apply Nat.gcd_divide_r.
Qed.

Lemma primes_distinct_coprime : forall q q',
  Znumtheory.prime (Z.of_nat q) -> Znumtheory.prime (Z.of_nat q') -> q <> q' ->
  Nat.gcd q q' = 1%nat.
Proof.
  intros q q' Hq Hq' Hne.
  apply prime_not_div_coprime; [exact Hq |].
  intro Hd. pose proof (is_prime_of_Z q' Hq') as [Hq'1 Hdd].
  pose proof (is_prime_of_Z q Hq) as [Hq1 _].
  destruct (Hdd q ltac:(lia) Hd) as [E|E]; [lia | exact (Hne E)].
Qed.

(** An element of any unitary-divisor order: k divides p-1 and contains each of
    its primes to full multiplicity. *)
Lemma element_order_unitary : forall p, Znumtheory.prime (Z.of_nat p) ->
  forall k, (1 <= k)%nat ->
  Nat.divide k (p - 1) ->
  (forall q, Znumtheory.prime (Z.of_nat q) -> Nat.divide q k ->
     exists e r, (p - 1 = q ^ e * r)%nat /\ Nat.gcd q r = 1%nat /\
                 Nat.divide (q ^ e) k) ->
  exists a, ~ (Z.of_nat p | a)%Z /\ is_order p a k.
Proof.
  intros p Hp.
  induction k as [k IHk] using (well_founded_induction lt_wf).
  intros Hk1 Hkdiv Hfull.
  destruct (Nat.eq_dec k 1) as [-> | Hkne].
  - exists 1%Z. split.
    + intro Hd. destruct Hp as [Hp1 _].
      pose proof (Znumtheory.Zdivide_le (Z.of_nat p) 1 ltac:(lia) ltac:(lia) Hd). lia.
    + split.
      * split; [lia |]. unfold cg. cbn [zpn].
        replace (1 * 1 - 1)%Z with 0%Z by ring. apply Z.divide_0_r.
      * intros k' Hk' [Hge _]. lia.
  - assert (Hk2 : (2 <= k)%nat) by lia.
    destruct (prime_factor_nat k Hk2) as [q [Hq Hqk]].
    pose proof (is_prime_of_Z q Hq) as [Hq1 _].
    destruct (Hfull q Hq Hqk) as [e [r [Hpr [Hgcd Hqek]]]].
    assert (He1 : (1 <= e)%nat).
    { destruct e as [|e']; [exfalso | lia].
      rewrite Nat.pow_0_r, Nat.mul_1_l in Hpr.
      assert (Hqr : Nat.divide q r).
      { rewrite <- Hpr. eapply Nat.divide_trans; [exact Hqk | exact Hkdiv]. }
      assert (Hqg : Nat.divide q (Nat.gcd q r))
        by (apply Nat.gcd_greatest; [apply Nat.divide_refl | exact Hqr]).
      rewrite Hgcd in Hqg. apply Nat.divide_1_r in Hqg. lia. }
    assert (Hqe2 : (2 <= q ^ e)%nat).
    { assert (Hmono : (q ^ 1 <= q ^ e)%nat) by (apply Nat.pow_le_mono_r; lia).
      rewrite Nat.pow_1_r in Hmono. lia. }
    set (k' := (k / q ^ e)%nat).
    assert (Hkeq : (k = q ^ e * k')%nat).
    { unfold k'. destruct Hqek as [z Hz]. rewrite Hz.
      rewrite Nat.div_mul by lia. lia. }
    assert (Hk'1 : (1 <= k')%nat) by nia.
    assert (Hk'lt : (k' < k)%nat) by nia.
    assert (Hqk' : ~ Nat.divide q k').
    { intro Hd.
      destruct Hkdiv as [m Hm].
      assert (Hr : (q ^ e * r = q ^ e * (m * k'))%nat) by nia.
      assert (Hr' : r = (m * k')%nat) by nia.
      assert (Hqr : Nat.divide q r).
      { rewrite Hr'. destruct Hd as [z Hz]. exists (m * z)%nat. lia. }
      assert (Hqg : Nat.divide q (Nat.gcd q r))
        by (apply Nat.gcd_greatest; [apply Nat.divide_refl | exact Hqr]).
      rewrite Hgcd in Hqg. apply Nat.divide_1_r in Hqg. lia. }
    assert (Hk'div : Nat.divide k' (p - 1)).
    { eapply Nat.divide_trans; [| exact Hkdiv]. exists (q ^ e)%nat. lia. }
    assert (Hfull' : forall q0, Znumtheory.prime (Z.of_nat q0) -> Nat.divide q0 k' ->
        exists e0 r0, (p - 1 = q0 ^ e0 * r0)%nat /\ Nat.gcd q0 r0 = 1%nat /\
                      Nat.divide (q0 ^ e0) k').
    { intros q0 Hq0 Hq0k'.
      assert (Hq0k : Nat.divide q0 k).
      { eapply Nat.divide_trans; [exact Hq0k' |]. exists (q ^ e)%nat. lia. }
      destruct (Hfull q0 Hq0 Hq0k) as [e0 [r0 [Hpr0 [Hgcd0 Hq0ek]]]].
      exists e0, r0. split; [exact Hpr0 | split; [exact Hgcd0 |]].
      assert (Hq0q : q0 <> q).
      { intro E. subst q0. exact (Hqk' Hq0k'). }
      assert (Hcop : Nat.gcd (q0 ^ e0) (q ^ e) = 1%nat).
      { apply coprime_pow_l. apply coprime_pow_r.
        apply primes_distinct_coprime; assumption. }
      apply (nat_coprime_divmul (q0 ^ e0) (q ^ e) k' Hcop).
      rewrite <- Hkeq. exact Hq0ek. }
    destruct (IHk k' Hk'lt Hk'1 Hk'div Hfull') as [a' [Ha'nd Ha'ord]].
    destruct (exists_order_ppow p q e r Hp Hq Hpr Hgcd) as [b [Hbnd Hbord]].
    assert (Hcopk : Nat.gcd (q ^ e) k' = 1%nat).
    { apply coprime_pow_l. apply prime_not_div_coprime; [exact Hq | exact Hqk']. }
    exists (b * a')%Z. split.
    + intro Hd. destruct (Znumtheory.prime_mult (Z.of_nat p) Hp b a' Hd) as [Hc|Hc];
        [exact (Hbnd Hc) | exact (Ha'nd Hc)].
    + rewrite Hkeq.
      exact (order_coprime_mul p b a' (q ^ e) k' Hp Hbord Ha'ord Hcopk).
Qed.

(** THE UNCONDITIONAL PRIMITIVE ROOT: no smoothness hypothesis.  The lemmas
    primitive_root, primitive_root_5smooth, primitive_root_7smooth all follow
    by discarding their smoothness arguments. *)
Theorem primitive_root_gen : forall p,
  Znumtheory.prime (Z.of_nat p) -> (5 <= p)%nat ->
  exists g, (1 <= g < Z.of_nat p)%Z /\ per p g (p - 1) /\
    (forall k, (1 <= k < p - 1)%nat -> ~ cg (Z.of_nat p) (zpn g k) 1%Z).
Proof.
  intros p Hp Hp5.
  assert (Hfull : forall q, Znumtheory.prime (Z.of_nat q) -> Nat.divide q (p - 1) ->
      exists e r, (p - 1 = q ^ e * r)%nat /\ Nat.gcd q r = 1%nat /\
                  Nat.divide (q ^ e) (p - 1)).
  { intros q Hq Hqd.
    pose proof (is_prime_of_Z q Hq) as [Hq1 _].
    destruct (ppart_exists q (p - 1) ltac:(lia) ltac:(lia)) as [e [r [Hpr Hnd]]].
    exists e, r. split; [exact Hpr | split].
    - apply prime_not_div_coprime; [exact Hq | exact Hnd].
    - exists r. lia. }
  destruct (element_order_unitary p Hp (p - 1) ltac:(lia) (Nat.divide_refl _) Hfull)
    as [G [HGnd HGord]].
  set (g := (G mod Z.of_nat p)%Z).
  assert (HpZ : (Z.of_nat p <> 0)%Z) by lia.
  assert (Hgcg : cg (Z.of_nat p) G g).
  { unfold cg, g. rewrite Z.mod_eq by exact HpZ.
    exists (G / Z.of_nat p)%Z. ring. }
  assert (Hgord : is_order p g (p - 1))
    by (apply (is_order_cong p G g (p - 1) Hgcg HGord)).
  assert (Hgnd : ~ (Z.of_nat p | g)%Z).
  { intro Hd. apply HGnd. unfold cg in Hgcg.
    replace G with ((G - g) + g)%Z by ring. apply Z.divide_add_r; assumption. }
  assert (Hg0 : (g <> 0)%Z)
    by (intro H0; apply Hgnd; rewrite H0; apply Z.divide_0_r).
  assert (Hgrange : (1 <= g < Z.of_nat p)%Z).
  { unfold g. pose proof (Z.mod_pos_bound G (Z.of_nat p) ltac:(lia)) as Hb.
    unfold g in Hg0. lia. }
  exists g. split; [exact Hgrange | split].
  - exact (proj1 Hgord).
  - intros k [Hk1 Hk2] Hc. apply (proj2 Hgord k Hk2). split; [exact Hk1 | exact Hc].
Qed.

(* ============================================================================
   The general Chebyshev prime-power rung.  cheb_coeffs n is the coefficient
   list of T_n (lowest degree first, leading coefficient 2^(n-1)), so
   cos(2*PI/q^e) is, by induction on e, a root of the monic-ized polynomial
   (T_q(x) - cos(2*PI/q^(e-1))) / 2^(q-1) -- one ONK_proot instance per prime
   q <= 2k+1, subsuming the 5^e and 7^e Chebyshev inductions.
   ============================================================================ *)

Definition psubR (ps qs : list R) : list R := paddR ps (pscaleR (-1) qs).

Fixpoint cheb_coeffs (n : nat) : list R :=
  match n with
  | O => 1 :: nil
  | S n' =>
      match n' with
      | O => 0 :: 1 :: nil
      | S n'' => psubR (pscaleR 2 (0 :: cheb_coeffs n')) (cheb_coeffs n'')
      end
  end.

Lemma fsum_minus : forall n f h,
  fsum n (fun i => f i - h i) = fsum n f - fsum n h.
Proof.
  induction n as [|n IH]; intros f h; cbn [fsum]; [ring | rewrite IH; ring].
Qed.

Lemma fsum_S : forall n f, fsum (S n) f = fsum n f + f n.
Proof. reflexivity. Qed.

Lemma fsum_delta0 : forall m (a x : R),
  fsum (S m) (fun i => (if Nat.eqb i 0 then a else 0) * x ^ i) = a.
Proof.
  intros m a x. rewrite fsum_S_shift.
  rewrite (fsum_ext m (fun i => (if Nat.eqb (S i) 0 then a else 0) * x ^ S i)
             (fun _ => 0)) by (intros; cbn [Nat.eqb]; ring).
  rewrite fsum_zero. cbn [Nat.eqb pow]. ring.
Qed.

Lemma cheb_coeffs_SS : forall n,
  cheb_coeffs (S (S n))
  = psubR (pscaleR 2 (0 :: cheb_coeffs (S n))) (cheb_coeffs n).
Proof. reflexivity. Qed.

Lemma cheb_all : forall n,
  length (cheb_coeffs n) = S n /\
  (forall x, pevalR (cheb_coeffs n) x = chebyshev_T n x).
Proof.
  induction n as [n IH] using (well_founded_induction lt_wf).
  destruct n as [|[|n]].
  - split; [reflexivity |]. intro x. cbn. ring.
  - split; [reflexivity |]. intro x. cbn. ring.
  - destruct (IH (S n) ltac:(lia)) as [HL1 HE1].
    destruct (IH n ltac:(lia)) as [HL0 HE0].
    rewrite cheb_coeffs_SS. split.
    + unfold psubR. rewrite paddR_length. unfold pscaleR.
      rewrite !length_map. cbn [length]. rewrite HL1, HL0. lia.
    + intro x. unfold psubR. rewrite pevalR_padd, !pevalR_pscale.
      cbn [pevalR]. rewrite HE1, HE0, chebyshev_rec. ring.
Qed.

Lemma cheb_top : forall n, nth (S n) (cheb_coeffs (S n)) 0 = 2 ^ n.
Proof.
  induction n as [n IH] using (well_founded_induction lt_wf).
  destruct n as [|n'].
  - reflexivity.
  - rewrite cheb_coeffs_SS. unfold psubR. rewrite nth_paddR, !nth_pscaleR.
    rewrite (nth_overflow (cheb_coeffs n'))
      by (rewrite (proj1 (cheb_all n')); lia).
    cbn [nth]. rewrite (IH n' ltac:(lia)). cbn [pow]. ring.
Qed.

Lemma ON_pow2 : forall m, OrigamiNum (2 ^ m).
Proof.
  induction m as [|m IH]; cbn [pow].
  - apply ON_1.
  - apply ON_mul; [apply Origami_two | exact IH].
Qed.

Lemma cheb_coeffs_ON : forall n i, OrigamiNum (nth i (cheb_coeffs n) 0).
Proof.
  induction n as [n IH] using (well_founded_induction lt_wf).
  destruct n as [|[|n]]; intro i.
  - destruct i as [|i]; [apply ON_1 |]. cbn [nth]. destruct i; apply ON_0.
  - destruct i as [|[|i]]; [apply ON_0 | apply ON_1 |]. cbn [nth]. destruct i; apply ON_0.
  - rewrite cheb_coeffs_SS. unfold psubR. rewrite nth_paddR, !nth_pscaleR.
    apply ON_add.
    + apply ON_mul; [apply Origami_two |].
      destruct i as [|i]; cbn [nth]; [apply ON_0 | apply IH; lia].
    + apply ON_mul; [apply Origami_neg, ON_1 | apply IH; lia].
Qed.

(** THE PRIME-POWER RUNG: cos(2*PI/q^e) lies in OrigamiNumK k for every prime
    q <= 2k+1, by Chebyshev induction on e. *)
Theorem cos_2pi_qe_ONK : forall kk q, (1 <= kk)%nat ->
  Znumtheory.prime (Z.of_nat q) -> (q <= 2 * kk + 1)%nat ->
  forall e, OrigamiNumK kk (cos (2 * PI / INR (q ^ e))).
Proof.
  intros kk q Hkk Hq Hqle e.
  pose proof (is_prime_of_Z q Hq) as [Hq1 _].
  destruct q as [|q']; [lia |].
  induction e as [|e IH].
  - replace (2 * PI / INR (S q' ^ 0)) with (2 * PI)
      by (rewrite Nat.pow_0_r, INR_1; field).
    rewrite cos_2PI. apply ONK_1.
  - set (t := cos (2 * PI / INR (S q' ^ S e))) in *.
    set (cc := cos (2 * PI / INR (S q' ^ e))) in *.
    assert (Hrel : pevalR (cheb_coeffs (S q')) t = cc).
    { destruct (cheb_all (S q')) as [_ HE]. rewrite HE.
      unfold t. rewrite chebyshev_cos. unfold cc. f_equal.
      rewrite Nat.pow_succ_r', mult_INR.
      assert (Hqe : INR (S q' ^ e) <> 0)
        by (apply not_0_INR; apply Nat.pow_nonzero; lia).
      assert (HqR : INR (S q') <> 0) by (apply not_0_INR; lia).
      field. split; assumption. }
    rewrite pevalR_nth_sum in Hrel.
    rewrite (proj1 (cheb_all (S q'))) in Hrel.
    rewrite fsum_S in Hrel.
    rewrite cheb_top in Hrel.
    assert (HL0 : 0 < 2 ^ q') by (apply pow_lt; lra).
    apply (ONK_proot kk (S q')
             (fun i => (nth i (cheb_coeffs (S q')) 0
                        - (if Nat.eqb i 0 then cc else 0)) / 2 ^ q')
             t).
    + exact Hq.
    + exact Hqle.
    + intros i Hi. apply ONK_div; [| | lra].
      * apply ONK_sub.
        -- apply Origami_in_ONK; [exact Hkk | apply cheb_coeffs_ON].
        -- destruct (Nat.eqb i 0); [exact IH | apply ONK_0].
      * apply Origami_in_ONK; [exact Hkk | apply ON_pow2].
    + apply (Rmult_eq_reg_l (2 ^ q')); [| lra].
      rewrite Rmult_0_r, Rmult_plus_distr_l.
      rewrite <- fsum_scale.
      rewrite (fsum_ext (S q')
                 (fun i => 2 ^ q'
                    * ((nth i (cheb_coeffs (S q')) 0
                        - (if Nat.eqb i 0 then cc else 0)) / 2 ^ q' * t ^ i))
                 (fun i => nth i (cheb_coeffs (S q')) 0 * t ^ i
                           - (if Nat.eqb i 0 then cc else 0) * t ^ i))
        by (intros i Hi; field; lra).
      rewrite fsum_minus, fsum_delta0.
      lra.
Qed.

(* ============================================================================
   The list-step degree theory, part 1: smooth_upto, the arbitrary-prime-degree
   extension PolyF generalizing Quint5F and Sept7F, subring and subfield
   closure, and the step basis of length at most the degree via the maximal
   independent prefix of the powers of the root.
   ============================================================================ *)

(** Every prime factor bounded: the divisor-closed smoothness predicate. *)
Definition smooth_upto (b n : nat) : Prop :=
  forall q, Znumtheory.prime (Z.of_nat q) -> Nat.divide q n -> (q <= b)%nat.

Lemma smooth_upto_divisor : forall b n m,
  Nat.divide m n -> smooth_upto b n -> smooth_upto b m.
Proof.
  intros b n m Hdiv Hs q Hq Hqm.
  apply Hs; [exact Hq | eapply Nat.divide_trans; [exact Hqm | exact Hdiv]].
Qed.

Lemma smooth_upto_mul : forall b n m,
  smooth_upto b n -> smooth_upto b m -> smooth_upto b (n * m).
Proof.
  intros b n m Hn Hm q Hq Hqnm.
  destruct (nat_prime_mult q n m Hq Hqnm) as [Hd | Hd]; [apply Hn | apply Hm]; assumption.
Qed.

Lemma smooth_upto_of_le : forall b n, (1 <= n)%nat -> (n <= b)%nat -> smooth_upto b n.
Proof.
  intros b n Hn Hnb q Hq Hqn.
  assert (Hqle : (q <= n)%nat) by (apply Nat.divide_pos_le; [lia | exact Hqn]).
  lia.
Qed.

Lemma smooth_upto_1 : forall b, smooth_upto b 1.
Proof.
  intros b q Hq Hd. apply Nat.divide_1_r in Hd.
  pose proof (is_prime_of_Z q Hq) as [Hq1 _]. lia.
Qed.

Lemma subfield_subring : forall F, is_subfield F -> is_subring F.
Proof.
  intros F HF. destruct HF as [H0 [H1 [Ha [Hs [Hm Hi]]]]].
  repeat split; assumption.
Qed.

Lemma fsum_delta : forall m j (a x : R), (j < m)%nat ->
  fsum m (fun i => (if Nat.eqb i j then a else 0) * x ^ i) = a * x ^ j.
Proof.
  intros m j a x Hj. revert j Hj. induction m as [|m IH]; intros j Hj; [lia |].
  rewrite fsum_S. destruct (Nat.eq_dec j m) as [-> | Hne].
  - rewrite Nat.eqb_refl.
    rewrite (fsum_ext m (fun i => (if Nat.eqb i m then a else 0) * x ^ i) (fun _ => 0)).
    + rewrite fsum_zero. ring.
    + intros i Hi. destruct (Nat.eqb_spec i m) as [E|E]; [lia | ring].
  - destruct (Nat.eqb_spec m j) as [E|E]; [lia |].
    rewrite (IH j ltac:(lia)). ring.
Qed.

(** PolyF: the F-span of the first d powers of r, coefficients as a function. *)
Definition PolyF (F : R -> Prop) (d : nat) (r : R) (x : R) : Prop :=
  exists c : nat -> R, (forall i, (i < d)%nat -> F (c i)) /\
    x = fsum d (fun i => c i * r ^ i).

Lemma PolyF_contains_sr : forall F d r x,
  is_subring F -> (1 <= d)%nat -> F x -> PolyF F d r x.
Proof.
  intros F d r x Hsr Hd Hx.
  exists (fun i => if Nat.eqb i 0 then x else 0). split.
  - intros i Hi. destruct (Nat.eqb i 0); [exact Hx | apply subring_0; exact Hsr].
  - destruct d as [|d']; [lia |]. rewrite fsum_delta0. reflexivity.
Qed.

Lemma PolyF_r : forall F d r, is_subring F -> (2 <= d)%nat -> PolyF F d r r.
Proof.
  intros F d r Hsr Hd.
  exists (fun i => if Nat.eqb i 1 then 1 else 0). split.
  - intros i Hi. destruct (Nat.eqb i 1); [apply subring_1 | apply subring_0]; exact Hsr.
  - rewrite fsum_delta by lia. cbn [pow]. ring.
Qed.

Lemma PolyF_add : forall F d r x y, is_subring F ->
  PolyF F d r x -> PolyF F d r y -> PolyF F d r (x + y).
Proof.
  intros F d r x y Hsr [cx [Hcx Hx]] [cy [Hcy Hy]].
  exists (fun i => cx i + cy i). split.
  - intros i Hi. apply subring_add; [exact Hsr | apply Hcx; lia | apply Hcy; lia].
  - subst. rewrite <- fsum_plus. apply fsum_ext. intros i Hi. ring.
Qed.

Lemma PolyF_sub : forall F d r x y, is_subring F ->
  PolyF F d r x -> PolyF F d r y -> PolyF F d r (x - y).
Proof.
  intros F d r x y Hsr [cx [Hcx Hx]] [cy [Hcy Hy]].
  exists (fun i => cx i - cy i). split.
  - intros i Hi. apply subring_sub; [exact Hsr | apply Hcx; lia | apply Hcy; lia].
  - subst. rewrite <- fsum_minus. apply fsum_ext. intros i Hi. ring.
Qed.

Lemma PolyF_scal : forall F d r a x, is_subring F -> F a ->
  PolyF F d r x -> PolyF F d r (a * x).
Proof.
  intros F d r a x Hsr Ha [c [Hc Hx]].
  exists (fun i => a * c i). split.
  - intros i Hi. apply subring_mul; [exact Hsr | exact Ha | apply Hc; lia].
  - subst. rewrite <- fsum_scale. apply fsum_ext. intros i Hi. ring.
Qed.

(** Multiplication by the root, reduced through the monic relation. *)
Lemma PolyF_mulr : forall F d r (crel : nat -> R), is_subring F -> (1 <= d)%nat ->
  (forall i, (i < d)%nat -> F (crel i)) ->
  fsum d (fun i => crel i * r ^ i) + r ^ d = 0 ->
  forall x, PolyF F d r x -> PolyF F d r (x * r).
Proof.
  intros F d r crel Hsr Hd Hcrel Hrel x [c [Hc Hx]].
  exists (fun j => (if Nat.eqb j 0 then 0 else c (j - 1)%nat) - c (d - 1)%nat * crel j).
  split.
  - intros i Hi. apply subring_sub; [exact Hsr | |].
    + destruct (Nat.eqb i 0); [apply subring_0; exact Hsr | apply Hc; lia].
    + apply subring_mul; [exact Hsr | apply Hc; lia | apply Hcrel; lia].
  - subst x.
    transitivity (fsum d (fun i => c i * r ^ S i)).
    { rewrite (Rmult_comm (fsum d (fun i => c i * r ^ i)) r).
      rewrite <- fsum_scale. apply fsum_ext. intros i Hi. cbn [pow]. ring. }
    transitivity (fsum (S d) (fun j => (if Nat.eqb j 0 then 0 else c (j - 1)%nat) * r ^ j)).
    { rewrite fsum_S_shift.
      rewrite (fsum_ext d
                 (fun i => (if Nat.eqb (S i) 0 then 0 else c (S i - 1)%nat) * r ^ S i)
                 (fun i => c i * r ^ S i)).
      - cbn [Nat.eqb pow]. ring.
      - intros i Hi. replace (S i - 1)%nat with i by lia.
        cbn [Nat.eqb]. reflexivity. }
    rewrite fsum_S.
    assert (Hd0 : Nat.eqb d 0 = false) by (apply Nat.eqb_neq; lia).
    rewrite Hd0.
    rewrite (fsum_ext d
               (fun j => ((if Nat.eqb j 0 then 0 else c (j - 1)%nat) - c (d - 1)%nat * crel j) * r ^ j)
               (fun j => (if Nat.eqb j 0 then 0 else c (j - 1)%nat) * r ^ j
                         - c (d - 1)%nat * (crel j * r ^ j)))
      by (intros j Hj; ring).
    rewrite fsum_minus.
    rewrite fsum_scale.
    assert (HS2 : fsum d (fun j => crel j * r ^ j) = - r ^ d) by lra.
    rewrite HS2. ring.
Qed.

Lemma PolyF_rpow : forall F d r (crel : nat -> R), is_subring F -> (1 <= d)%nat ->
  (forall i, (i < d)%nat -> F (crel i)) ->
  fsum d (fun i => crel i * r ^ i) + r ^ d = 0 ->
  forall j, PolyF F d r (r ^ j).
Proof.
  intros F d r crel Hsr Hd Hcrel Hrel j. induction j as [|j IH].
  - cbn [pow]. apply PolyF_contains_sr; [exact Hsr | lia | apply subring_1; exact Hsr].
  - replace (r ^ S j) with (r ^ j * r) by (cbn [pow]; ring).
    apply (PolyF_mulr F d r crel); assumption.
Qed.

Lemma PolyF_fsum : forall F d r, is_subring F -> (1 <= d)%nat ->
  forall m (f : nat -> R), (forall i, (i < m)%nat -> PolyF F d r (f i)) ->
  PolyF F d r (fsum m f).
Proof.
  intros F d r Hsr Hd m f. induction m as [|m IH]; intro Hf.
  - cbn [fsum]. apply PolyF_contains_sr; [exact Hsr | lia | apply subring_0; exact Hsr].
  - rewrite fsum_S.
    apply PolyF_add; [exact Hsr | apply IH; intros; apply Hf; lia | apply Hf; lia].
Qed.

Lemma PolyF_mul : forall F d r (crel : nat -> R), is_subring F -> (1 <= d)%nat ->
  (forall i, (i < d)%nat -> F (crel i)) ->
  fsum d (fun i => crel i * r ^ i) + r ^ d = 0 ->
  forall x y, PolyF F d r x -> PolyF F d r y -> PolyF F d r (x * y).
Proof.
  intros F d r crel Hsr Hd Hcrel Hrel x y Hx [cy [Hcy Hy]].
  assert (Hxp : forall j, PolyF F d r (x * r ^ j)).
  { induction j as [|j IHj].
    - replace (x * r ^ 0) with x by (cbn [pow]; ring). exact Hx.
    - replace (x * r ^ S j) with ((x * r ^ j) * r) by (cbn [pow]; ring).
      apply (PolyF_mulr F d r crel); assumption. }
  subst y. rewrite <- fsum_scale.
  apply PolyF_fsum; [exact Hsr | exact Hd |].
  intros i Hi.
  replace (x * (cy i * r ^ i)) with (cy i * (x * r ^ i)) by ring.
  apply PolyF_scal; [exact Hsr | apply Hcy; lia | apply Hxp].
Qed.

Lemma PolyF_subring : forall F d r (crel : nat -> R), is_subring F -> (1 <= d)%nat ->
  (forall i, (i < d)%nat -> F (crel i)) ->
  fsum d (fun i => crel i * r ^ i) + r ^ d = 0 ->
  is_subring (PolyF F d r).
Proof.
  intros F d r crel Hsr Hd Hcrel Hrel. repeat split.
  - apply PolyF_contains_sr; [exact Hsr | lia | apply subring_0; exact Hsr].
  - apply PolyF_contains_sr; [exact Hsr | lia | apply subring_1; exact Hsr].
  - intros x y Hx Hy. apply PolyF_add; assumption.
  - intros x y Hx Hy. apply PolyF_sub; assumption.
  - intros x y Hx Hy. apply (PolyF_mul F d r crel); assumption.
Qed.

(* ===== bridges between the function form, Fcomb, and the powers list ===== *)

Lemma Fcomb_map2 : forall (c f : nat -> R) (L : list nat),
  Fcomb (map c L) (map f L) = rsum L (fun i => c i * f i).
Proof.
  intros c f L. induction L as [|x L IH].
  - reflexivity.
  - cbn [map Fcomb]. rewrite IH, rsum_consL. reflexivity.
Qed.

Lemma rsum_seq0_fsum : forall d (f : nat -> R), rsum (seq 0 d) f = fsum d f.
Proof.
  induction d as [|d IH]; intro f.
  - reflexivity.
  - rewrite seq_S, rsum_appL, rsum_singleL, IH, fsum_S. reflexivity.
Qed.

Lemma list_eta_nth : forall (cs : list R),
  cs = map (fun i => nth i cs 0) (seq 0 (length cs)).
Proof.
  induction cs as [|c cs' IH].
  - reflexivity.
  - cbn [length seq map nth].
    f_equal. rewrite <- seq_shift, map_map. cbn [nth].
    exact IH.
Qed.

Lemma PolyF_spans_elt : forall F d r x, PolyF F d r x -> spans F (powers r d) x.
Proof.
  intros F d r x [c [Hc Hx]].
  exists (map c (seq 0 d)). split; [| split].
  - rewrite length_map, length_seq, powers_length. reflexivity.
  - apply Forall_forall. intros z Hz.
    apply in_map_iff in Hz. destruct Hz as [i [Hzi Hin]].
    apply in_seq in Hin. subst z. apply Hc. lia.
  - unfold powers. rewrite Fcomb_map2, rsum_seq0_fsum. symmetry. exact Hx.
Qed.

Lemma PolyF_Fcomb : forall F d r, is_subring F -> (1 <= d)%nat ->
  forall (ds vs : list R), Forall F ds -> Forall (PolyF F d r) vs ->
  PolyF F d r (Fcomb ds vs).
Proof.
  intros F d r Hsr Hd ds. induction ds as [|a ds' IH]; intros vs HFds HPvs.
  - cbn [Fcomb]. apply PolyF_contains_sr; [exact Hsr | lia | apply subring_0; exact Hsr].
  - destruct vs as [|v vs'].
    + cbn [Fcomb]. apply PolyF_contains_sr; [exact Hsr | lia | apply subring_0; exact Hsr].
    + cbn [Fcomb]. inversion HFds; subst. inversion HPvs; subst.
      apply PolyF_add; [exact Hsr | |].
      * apply PolyF_scal; [exact Hsr | assumption | assumption].
      * apply IH; assumption.
Qed.

(** The inverse, via a forced dependency among d+1 powers of u in a d-spanned
    space and inverse_from_relation. *)
Lemma PolyF_inv : forall F d r (crel : nat -> R), is_subfield F -> (1 <= d)%nat ->
  (forall i, (i < d)%nat -> F (crel i)) ->
  fsum d (fun i => crel i * r ^ i) + r ^ d = 0 ->
  forall u, PolyF F d r u -> u <> 0 -> PolyF F d r (/ u).
Proof.
  intros F d r crel HF Hd Hcrel Hrel u Hu Hune.
  assert (Hsr : is_subring F) by (apply subfield_subring; exact HF).
  assert (Hupow : forall j, PolyF F d r (u ^ j)).
  { induction j as [|j IHj].
    - cbn [pow]. apply PolyF_contains_sr; [exact Hsr | lia | apply subring_1; exact Hsr].
    - replace (u ^ S j) with (u ^ j * u) by (cbn [pow]; ring).
      apply (PolyF_mul F d r crel); assumption. }
  assert (Hspanned : Forall (spans F (powers r d)) (powers u (S d))).
  { apply Forall_forall. intros z Hz.
    unfold powers in Hz. apply in_map_iff in Hz. destruct Hz as [j [Hzj _]].
    subst z. apply PolyF_spans_elt. apply Hupow. }
  assert (Hlt : (length (powers r d) < length (powers u (S d)))%nat)
    by (rewrite !powers_length; lia).
  destruct (lin_dep_of_spanned F (powers r d) (powers u (S d)) HF Hspanned Hlt)
    as [cs [Hlen [HFcs [Hzero Hnz]]]].
  rewrite powers_length in Hlen.
  destruct (inverse_from_relation F cs u HF Hune HFcs Hnz
              ltac:(rewrite Hlen; exact Hzero)) as [ds [HFds Hinv]].
  assert (Hinveq : / u = Fcomb ds (powers u (length ds))).
  { apply (Rmult_eq_reg_l u); [| exact Hune]. rewrite Hinv. field. exact Hune. }
  rewrite Hinveq.
  apply PolyF_Fcomb; [exact Hsr | exact Hd | exact HFds |].
  apply Forall_forall. intros z Hz.
  unfold powers in Hz. apply in_map_iff in Hz. destruct Hz as [j [Hzj _]].
  subst z. apply Hupow.
Qed.

Lemma PolyF_subfield : forall F d r (crel : nat -> R), is_subfield F -> (1 <= d)%nat ->
  (forall i, (i < d)%nat -> F (crel i)) ->
  fsum d (fun i => crel i * r ^ i) + r ^ d = 0 ->
  is_subfield (PolyF F d r).
Proof.
  intros F d r crel HF Hd Hcrel Hrel.
  assert (Hsr : is_subring F) by (apply subfield_subring; exact HF).
  repeat split.
  - apply PolyF_contains_sr; [exact Hsr | lia | apply subring_0; exact Hsr].
  - apply PolyF_contains_sr; [exact Hsr | lia | apply subring_1; exact Hsr].
  - intros x y Hx Hy. apply PolyF_add; assumption.
  - intros x y Hx Hy. apply PolyF_sub; assumption.
  - intros x y Hx Hy. apply (PolyF_mul F d r crel); assumption.
  - intros x Hx Hne. apply (PolyF_inv F d r crel); assumption.
Qed.

(* ===== the maximal independent prefix of the powers of the root ===== *)

Lemma powers_snoc : forall (r : R) n, powers r (S n) = powers r n ++ (r ^ n :: nil).
Proof.
  intros r n. unfold powers. rewrite seq_S, map_app. reflexivity.
Qed.

Lemma Fcomb_app_same : forall cs1 vs1 cs2 vs2, length cs1 = length vs1 ->
  Fcomb (cs1 ++ cs2) (vs1 ++ vs2) = Fcomb cs1 vs1 + Fcomb cs2 vs2.
Proof.
  induction cs1 as [|c cs1 IH]; intros vs1 cs2 vs2 Hlen.
  - destruct vs1; [cbn [Fcomb app]; ring | cbn in Hlen; lia].
  - destruct vs1 as [|v vs1]; [cbn in Hlen; lia |].
    cbn [Fcomb app]. rewrite (IH vs1 cs2 vs2) by (cbn in Hlen; lia). ring.
Qed.

Lemma powers_indep_1 : forall (F : R -> Prop) (r : R), lin_indep F (powers r 1).
Proof.
  intros F r cs Hlen HFcs Hcomb.
  rewrite powers_length in Hlen.
  destruct cs as [|k [|? ?]]; [discriminate | | discriminate].
  unfold powers in Hcomb. cbn in Hcomb.
  constructor; [lra | constructor].
Qed.

Lemma not_lin_indep_witness : forall (F : R -> Prop) vs, ~ lin_indep F vs ->
  exists cs, length cs = length vs /\ Forall F cs /\ Fcomb cs vs = 0 /\
             ~ Forall (fun c => c = 0) cs.
Proof.
  intros F vs Hnot.
  destruct (not_all_ex_not _ _ Hnot) as [cs Hcs].
  destruct (imply_to_and _ _ Hcs) as [Hlen Hcs2].
  destruct (imply_to_and _ _ Hcs2) as [HFcs Hcs3].
  destruct (imply_to_and _ _ Hcs3) as [Hcomb Hnz].
  exists cs. repeat split; assumption.
Qed.

Lemma powers_max_prefix : forall (F : R -> Prop) (r : R) d,
  is_subfield F -> (1 <= d)%nat ->
  exists j, (1 <= j <= d)%nat /\ lin_indep F (powers r j) /\
    (j = d \/
     exists c : nat -> R, (forall i, (i < j)%nat -> F (c i)) /\
       fsum j (fun i => c i * r ^ i) + r ^ j = 0).
Proof.
  intros F r d HF Hd. induction d as [|d' IHd]; [lia |].
  destruct (Nat.eq_dec d' 0) as [-> | Hd'].
  - exists 1%nat. split; [lia | split; [apply powers_indep_1 | left; reflexivity]].
  - assert (Hd'1 : (1 <= d')%nat) by lia.
    destruct (IHd Hd'1) as [j [Hjle [Hjind Hjcase]]].
    destruct Hjcase as [-> | Hrel].
    + destruct (classic (lin_indep F (powers r (S d')))) as [Hind | Hdep].
      * exists (S d'). split; [lia | split; [exact Hind | left; reflexivity]].
      * destruct (not_lin_indep_witness F (powers r (S d')) Hdep)
          as [ks [Hklen [HFks [Hkcomb Hknz]]]].
        rewrite powers_length in Hklen.
        destruct (exists_last (l := ks)
                    ltac:(intro E; rewrite E in Hklen; cbn in Hklen; lia))
          as [ks' [kj Hks]].
        subst ks.
        rewrite length_app in Hklen. cbn [length] in Hklen.
        assert (Hks'len : length ks' = d') by lia.
        rewrite powers_snoc in Hkcomb.
        rewrite Fcomb_app_same in Hkcomb
          by (rewrite Hks'len, powers_length; reflexivity).
        cbn [Fcomb] in Hkcomb.
        apply Forall_app in HFks. destruct HFks as [HFks' HFkj].
        pose proof (Forall_inv HFkj) as Fkj.
        destruct (Req_dec kj 0) as [Hkj0 | Hkjne].
        { exfalso. subst kj.
          assert (Hz : Forall (fun c => c = 0) ks').
          { apply Hjind;
              [rewrite Hks'len, powers_length; reflexivity | exact HFks' | lra]. }
          apply Hknz. apply Forall_app.
          split; [exact Hz | constructor; [reflexivity | constructor]]. }
        exists d'. split; [lia | split; [exact Hjind | right]].
        exists (fun i => nth i ks' 0 / kj). split.
        { intros i Hi. apply subfield_div; [exact HF | | exact Fkj | exact Hkjne].
          apply (proj1 (Forall_forall F ks') HFks').
          apply nth_In. lia. }
        { apply (Rmult_eq_reg_l kj); [| exact Hkjne].
          rewrite Rmult_0_r, Rmult_plus_distr_l, <- fsum_scale.
          rewrite (fsum_ext d' (fun i => kj * (nth i ks' 0 / kj * r ^ i))
                     (fun i => nth i ks' 0 * r ^ i)) by (intros; field; exact Hkjne).
          assert (Hbr : Fcomb ks' (powers r d') = fsum d' (fun i => nth i ks' 0 * r ^ i)).
          { rewrite (list_eta_nth ks') at 1. rewrite Hks'len.
            unfold powers. rewrite Fcomb_map2, rsum_seq0_fsum. reflexivity. }
          rewrite Hbr in Hkcomb. lra. }
    + exists j. split; [lia | split; [exact Hjind | right; exact Hrel]].
Qed.

Lemma PolyF_collapse : forall (F : R -> Prop) (r : R) j (cj : nat -> R),
  is_subring F -> (1 <= j)%nat ->
  (forall i, (i < j)%nat -> F (cj i)) ->
  fsum j (fun i => cj i * r ^ i) + r ^ j = 0 ->
  forall d x, PolyF F d r x -> PolyF F j r x.
Proof.
  intros F r j cj Hsr Hj Hcj Hjrel d x [c [Hc Hx]].
  subst x. apply PolyF_fsum; [exact Hsr | exact Hj |].
  intros i Hi.
  apply PolyF_scal; [exact Hsr | apply Hc; lia |].
  apply (PolyF_rpow F j r cj); assumption.
Qed.

(** The step basis: F[r] over F has a basis of size between 1 and d. *)
Lemma PolyF_step_basis : forall (F : R -> Prop) d (r : R) (crel : nat -> R),
  is_subfield F -> (2 <= d)%nat ->
  (forall i, (i < d)%nat -> F (crel i)) ->
  fsum d (fun i => crel i * r ^ i) + r ^ d = 0 ->
  exists Be, basis F Be (PolyF F d r) /\ (1 <= length Be <= d)%nat.
Proof.
  intros F d r crel HF Hd Hcrel Hrel.
  assert (Hsr : is_subring F) by (apply subfield_subring; exact HF).
  destruct (powers_max_prefix F r d HF ltac:(lia)) as [j [Hjle [Hjind Hjcase]]].
  assert (Hjrel : exists cj : nat -> R, (forall i, (i < j)%nat -> F (cj i)) /\
                  fsum j (fun i => cj i * r ^ i) + r ^ j = 0).
  { destruct Hjcase as [-> | Hex]; [exists crel; split; assumption | exact Hex]. }
  destruct Hjrel as [cj [Hcj Hjrel]].
  exists (powers r j). split; [| rewrite powers_length; lia].
  split; [| split].
  - apply Forall_forall. intros z Hz.
    unfold powers in Hz. apply in_map_iff in Hz. destruct Hz as [i [Hzi _]]. subst z.
    apply (PolyF_rpow F d r crel Hsr ltac:(lia) Hcrel Hrel).
  - exact Hjind.
  - intros y Hy. apply PolyF_spans_elt.
    apply (PolyF_collapse F r j cj Hsr ltac:(lia) Hcj Hjrel d). exact Hy.
Qed.

(* ============================================================================
   The list-step degree theory, part 2: the tower with quadratic and
   arbitrary-prime-degree rungs generalizing o5tower and o7tower, the
   OrigamiNumK-to-tower induction, and the smooth rational dimension bound.
   ============================================================================ *)

Inductive okstep : Type :=
| OKQuad : R -> okstep
| OKPrime : nat -> (nat -> R) -> R -> okstep.

Fixpoint oktower (L : list okstep) : R -> Prop :=
  match L with
  | nil => is_rational
  | OKQuad s :: L' => QF (oktower L') s
  | OKPrime d c r :: L' => PolyF (oktower L') d r
  end.

Fixpoint okwf (kk : nat) (L : list okstep) : Prop :=
  match L with
  | nil => True
  | OKQuad s :: L' => oktower L' (s * s) /\ okwf kk L'
  | OKPrime d c r :: L' =>
      (2 <= d)%nat /\ (d <= 2 * kk + 1)%nat /\
      (forall i, (i < d)%nat -> oktower L' (c i)) /\
      (fsum d (fun i => c i * r ^ i) + r ^ d = 0) /\
      okwf kk L'
  end.

Lemma oktower_subfield : forall kk L, okwf kk L -> is_subfield (oktower L).
Proof.
  intros kk L. induction L as [|st L' IH]; intro W.
  - exact is_rational_subfield.
  - destruct st as [s | d c r]; cbn [oktower okwf] in *.
    + destruct W as [Wss W']. apply QF_subfield; [apply IH; exact W' | exact Wss].
    + destruct W as [Hd [Hdle [Hmem [Hrel W']]]].
      apply (PolyF_subfield (oktower L') d r c);
        [apply IH; exact W' | lia | exact Hmem | exact Hrel].
Qed.

Lemma oktower_subring : forall kk L, okwf kk L -> is_subring (oktower L).
Proof.
  intros kk L W. apply subfield_subring. apply (oktower_subfield kk L W).
Qed.

Lemma oktower_contains_rational : forall kk L, okwf kk L ->
  forall x, is_rational x -> oktower L x.
Proof.
  intros kk L. induction L as [|st L' IH]; intros W x Hx.
  - exact Hx.
  - destruct st as [s | d c r]; cbn [oktower okwf] in *.
    + destruct W as [_ W'].
      apply QF_contains_sr; [apply (oktower_subring kk L' W') | apply IH; assumption].
    + destruct W as [Hd [_ [_ [_ W']]]].
      apply PolyF_contains_sr;
        [apply (oktower_subring kk L' W') | lia | apply IH; assumption].
Qed.

Lemma oktower_weaken_base : forall kk L1 L2 x, okwf kk L2 ->
  oktower L1 x -> oktower (L1 ++ L2) x.
Proof.
  intros kk L1. induction L1 as [|st L1' IH]; intros L2 x W2 Tx.
  - cbn [oktower] in Tx. cbn [app].
    apply (oktower_contains_rational kk L2 W2 x Tx).
  - destruct st as [s | d c r]; cbn [oktower app] in *.
    + destruct Tx as [p [q [Tp [Tq Hx]]]].
      exists p, q.
      repeat split; [apply IH; assumption | apply IH; assumption | exact Hx].
    + destruct Tx as [cf [Hcf Hx]].
      exists cf. split; [| exact Hx].
      intros i Hi. apply IH; [exact W2 | apply Hcf; exact Hi].
Qed.

Lemma okwf_app : forall kk L1 L2, okwf kk L1 -> okwf kk L2 -> okwf kk (L1 ++ L2).
Proof.
  intros kk L1. induction L1 as [|st L1' IH]; intros L2 W1 W2.
  - cbn [app]. exact W2.
  - destruct st as [s | d c r]; cbn [okwf app] in *.
    + destruct W1 as [Wss W1']. split.
      * apply (oktower_weaken_base kk); [exact W2 | exact Wss].
      * apply IH; assumption.
    + destruct W1 as [Hd [Hdle [Hmem [Hrel W1']]]].
      split; [exact Hd | split; [exact Hdle | split; [| split]]].
      * intros i Hi. apply (oktower_weaken_base kk); [exact W2 | apply Hmem; exact Hi].
      * exact Hrel.
      * apply IH; assumption.
Qed.

Lemma oktower_weaken_top : forall kk L1 L2 x, okwf kk (L1 ++ L2) ->
  oktower L2 x -> oktower (L1 ++ L2) x.
Proof.
  intros kk L1. induction L1 as [|st L1' IH]; intros L2 x W Tx.
  - exact Tx.
  - destruct st as [s | d c r]; cbn [oktower okwf app] in *.
    + destruct W as [Wss W'].
      apply QF_contains_sr;
        [apply (oktower_subring kk (L1' ++ L2) W') | apply IH; assumption].
    + destruct W as [Hd [_ [_ [_ W']]]].
      apply PolyF_contains_sr;
        [apply (oktower_subring kk (L1' ++ L2) W') | lia | apply IH; assumption].
Qed.

Lemma oktower_merge_family : forall kk m (f : nat -> R),
  (forall i, (i < m)%nat -> exists L, okwf kk L /\ oktower L (f i)) ->
  exists L, okwf kk L /\ (forall i, (i < m)%nat -> oktower L (f i)).
Proof.
  intros kk m f. induction m as [|m IH]; intro Hf.
  - exists nil. split; [exact I | intros i Hi; lia].
  - destruct IH as [L1 [W1 T1]]; [intros; apply Hf; lia |].
    destruct (Hf m ltac:(lia)) as [L2 [W2 T2]].
    exists (L2 ++ L1).
    assert (Wapp : okwf kk (L2 ++ L1)) by (apply okwf_app; assumption).
    split; [exact Wapp |].
    intros i Hi. destruct (Nat.eq_dec i m) as [-> | Hne].
    + apply (oktower_weaken_base kk); [exact W1 | exact T2].
    + apply (oktower_weaken_top kk); [exact Wapp | apply T1; lia].
Qed.

Lemma ONK_in_oktower : forall kk, (1 <= kk)%nat -> forall x, OrigamiNumK kk x ->
  exists L, okwf kk L /\ oktower L x.
Proof.
  intros kk Hkk x H.
  induction H as [ | | x y Hx IHx Hy IHy | x y Hx IHx Hy IHy | x y Hx IHx Hy IHy
                 | x Hx IHx Hxne | x Hx IHx Hxnn | d c r Hp Hle Hc IHc Heq ].
  - exists nil.
    split; [exact I | cbn [oktower]; exists 0%Z, 1%Z; split; [lia | cbn; field]].
  - exists nil.
    split; [exact I | cbn [oktower]; exists 1%Z, 1%Z; split; [lia | cbn; field]].
  - destruct IHx as [L1 [W1 T1]]. destruct IHy as [L2 [W2 T2]].
    exists (L1 ++ L2).
    assert (Wapp : okwf kk (L1 ++ L2)) by (apply okwf_app; assumption).
    split; [exact Wapp |].
    apply subring_add; [apply (oktower_subring kk (L1 ++ L2) Wapp)
      | apply (oktower_weaken_base kk); assumption
      | apply (oktower_weaken_top kk); assumption].
  - destruct IHx as [L1 [W1 T1]]. destruct IHy as [L2 [W2 T2]].
    exists (L1 ++ L2).
    assert (Wapp : okwf kk (L1 ++ L2)) by (apply okwf_app; assumption).
    split; [exact Wapp |].
    apply subring_sub; [apply (oktower_subring kk (L1 ++ L2) Wapp)
      | apply (oktower_weaken_base kk); assumption
      | apply (oktower_weaken_top kk); assumption].
  - destruct IHx as [L1 [W1 T1]]. destruct IHy as [L2 [W2 T2]].
    exists (L1 ++ L2).
    assert (Wapp : okwf kk (L1 ++ L2)) by (apply okwf_app; assumption).
    split; [exact Wapp |].
    apply subring_mul; [apply (oktower_subring kk (L1 ++ L2) Wapp)
      | apply (oktower_weaken_base kk); assumption
      | apply (oktower_weaken_top kk); assumption].
  - destruct IHx as [L [W T]]. exists L. split; [exact W |].
    destruct (oktower_subfield kk L W) as [_ [_ [_ [_ [_ Hinv]]]]].
    apply Hinv; assumption.
  - destruct IHx as [L [W T]].
    exists (OKQuad (sqrt x) :: L). cbn [okwf oktower]. split.
    + split; [| exact W]. rewrite sqrt_sqrt by exact Hxnn. exact T.
    + apply QF_self. apply (oktower_subfield kk L W).
  - destruct (oktower_merge_family kk d c IHc) as [L [W T]].
    exists (OKPrime d c r :: L). cbn [okwf oktower].
    assert (Hd2 : (2 <= d)%nat) by (destruct Hp as [Hp1 _]; lia).
    split.
    + split; [exact Hd2 | split; [exact Hle | split; [exact T | split; [exact Heq | exact W]]]].
    + apply PolyF_r; [apply (oktower_subring kk L W) | exact Hd2].
Qed.

Lemma oktower_dim : forall kk L, okwf kk L -> (1 <= kk)%nat ->
  exists BL, basis is_rational BL (oktower L) /\
    (1 <= length BL)%nat /\ smooth_upto (2 * kk + 1) (length BL).
Proof.
  intros kk L. induction L as [|st L' IH]; intros W Hkk.
  - exists (1 :: nil). split; [| split].
    + split; [| split].
      * constructor; [apply (subfield_1 is_rational is_rational_subfield) | constructor].
      * intros cs Hl Hf Hfc. destruct cs as [|c cs']; [cbn in Hl; lia|].
        destruct cs' as [|c2 cs'']; [| cbn in Hl; lia]. cbn [Fcomb] in Hfc.
        constructor; [lra | constructor].
      * intros y Hy. exists (y :: nil). split; [reflexivity | split].
        -- constructor; [exact Hy | constructor].
        -- cbn [Fcomb]. ring.
    + cbn [length]. lia.
    + cbn [length]. apply smooth_upto_1.
  - destruct st as [s | d c r]; cbn [okwf oktower] in *.
    + destruct W as [Wss W'].
      destruct (IH W' Hkk) as [BL' [HbBL' [Hlen' Hsm']]].
      assert (HsfL' : is_subfield (oktower L')) by (apply (oktower_subfield kk); exact W').
      destruct (QF_step_basis (oktower L') s HsfL' Wss) as [Be [HbBe Hbecard]].
      assert (HsfL : is_subfield (QF (oktower L') s)) by (apply QF_subfield; assumption).
      exists (flat_map (fun ee => map (Rmult ee) BL') Be). split; [| split].
      * apply (product_basis BL' Be (oktower L') (QF (oktower L') s));
          [exact HsfL' | exact HsfL
          | intros z Hz; apply subfield_contains_rational; [exact HsfL' | exact Hz]
          | intros z Hz; apply QF_contains; [exact HsfL' | exact Hz]
          | exact HbBL' | exact HbBe].
      * rewrite product_length. destruct Hbecard as [E|E]; rewrite E; lia.
      * rewrite product_length. apply smooth_upto_mul; [| exact Hsm'].
        destruct Hbecard as [E|E]; rewrite E; apply smooth_upto_of_le; lia.
    + destruct W as [Hd2 [Hdle [Hmem [Hrel W']]]].
      destruct (IH W' Hkk) as [BL' [HbBL' [Hlen' Hsm']]].
      assert (HsfL' : is_subfield (oktower L')) by (apply (oktower_subfield kk); exact W').
      destruct (PolyF_step_basis (oktower L') d r c HsfL' Hd2 Hmem Hrel)
        as [Be [HbBe Hbecard]].
      assert (HsfL : is_subfield (PolyF (oktower L') d r))
        by (apply (PolyF_subfield (oktower L') d r c);
            [exact HsfL' | lia | exact Hmem | exact Hrel]).
      exists (flat_map (fun ee => map (Rmult ee) BL') Be). split; [| split].
      * apply (product_basis BL' Be (oktower L') (PolyF (oktower L') d r));
          [exact HsfL' | exact HsfL
          | intros z Hz; apply subfield_contains_rational; [exact HsfL' | exact Hz]
          | intros z Hz; apply PolyF_contains_sr;
              [apply subfield_subring; exact HsfL' | lia | exact Hz]
          | exact HbBL' | exact HbBe].
      * rewrite product_length. nia.
      * rewrite product_length. apply smooth_upto_mul; [| exact Hsm'].
        apply smooth_upto_of_le; lia.
Qed.

(** THE SMOOTH DEGREE BOUND: every OrigamiNumK k number has algebraic degree
    over Q whose prime factors are all at most 2k+1. *)
Theorem OrigamiNumK_field_degree_smooth : forall kk, (1 <= kk)%nat ->
  forall x, OrigamiNumK kk x ->
  exists d, basis is_rational (powers x d) (Qx x) /\ smooth_upto (2 * kk + 1) d.
Proof.
  intros kk Hkk x Hx.
  destruct (ONK_in_oktower kk Hkk x Hx) as [L [W T]].
  destruct (oktower_dim kk L W Hkk) as [BL [HbBL [Hlen Hsm]]].
  destruct (tower_law_div x (oktower L) BL (oktower_subfield kk L W) T HbBL)
    as [dd [Hbasis Hdiv]].
  exists dd. split; [exact Hbasis |].
  apply (smooth_upto_divisor (2 * kk + 1) (length BL)); assumption.
Qed.

(* ============================================================================
   THE k-FOLD n-GON THEOREM.  For every fold budget k >= 1 and every n >= 3,
   cos(2*PI/n) lies in OrigamiNumK k exactly when every prime factor of phi(n)
   is at most 2k+1.  Constructive direction: prime case by the parametric
   Gaussian-period tower over primitive_root_gen with step_prime_K rungs solved
   by ONK_proot; prime powers by the Chebyshev rung; composites by CRT.
   Necessity: the smooth degree bound against the exact cosine degree phi(n)/2.
   ============================================================================ *)

Lemma sin_ONK_of_cos : forall kk n, (2 <= n)%nat ->
  OrigamiNumK kk (cos (2 * PI / INR n)) -> OrigamiNumK kk (sin (2 * PI / INR n)).
Proof.
  intros kk n Hn Hc.
  pose proof PI_RGT_0 as HPI.
  assert (HnR : INR n <> 0) by (apply not_0_INR; lia).
  assert (HnPos : 0 < INR n) by (apply lt_0_INR; lia).
  assert (Hn2 : 2 <= INR n) by (replace 2 with (INR 2) by (simpl; ring); apply le_INR; lia).
  set (t := 2 * PI / INR n) in *.
  assert (Ht0 : 0 <= t).
  { unfold t, Rdiv. apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; exact HnPos]. }
  assert (Htpi : t <= PI).
  { unfold t. apply Rmult_le_reg_r with (INR n); [exact HnPos |].
    unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by exact HnR.
    rewrite Rmult_1_r. nra. }
  assert (Hsnn : 0 <= sin t) by (apply sin_ge_0; [exact Ht0 | exact Htpi]).
  assert (Hsq : sin t = sqrt (1 - cos t * cos t)).
  { rewrite <- (sqrt_Rsqr (sin t) Hsnn). f_equal. unfold Rsqr.
    pose proof (sin2_cos2 t) as H. unfold Rsqr in H. lra. }
  rewrite Hsq. apply ONK_sqrt.
  - apply ONK_sub; [apply ONK_1 | apply ONK_mul; exact Hc].
  - pose proof (COS_bound t) as [Hlo Hhi]. nra.
Qed.

Lemma vertex_coords_ONK : forall kk theta,
  OrigamiNumK kk (cos theta) -> OrigamiNumK kk (sin theta) ->
  forall k : nat, OrigamiNumK kk (cos (INR k * theta)) /\ OrigamiNumK kk (sin (INR k * theta)).
Proof.
  intros kk theta Hc Hs k. induction k as [|k [IHc IHs]].
  - replace (INR 0) with 0 by reflexivity.
    rewrite Rmult_0_l, cos_0, sin_0. split; [apply ONK_1 | apply ONK_0].
  - replace (INR (S k) * theta) with (INR k * theta + theta) by (rewrite S_INR; ring).
    rewrite cos_plus, sin_plus. split.
    + apply ONK_sub; apply ONK_mul; assumption.
    + apply ONK_add; apply ONK_mul; assumption.
Qed.

Lemma cos_sin_ONK_mul : forall kk m k,
  (1 <= m)%nat -> (1 <= k)%nat -> Nat.gcd m k = 1%nat ->
  OrigamiNumK kk (cos (2 * PI / INR m)) -> OrigamiNumK kk (sin (2 * PI / INR m)) ->
  OrigamiNumK kk (cos (2 * PI / INR k)) -> OrigamiNumK kk (sin (2 * PI / INR k)) ->
  OrigamiNumK kk (cos (2 * PI / INR (m * k))) /\
  OrigamiNumK kk (sin (2 * PI / INR (m * k))).
Proof.
  intros kk m k Hm Hk Hgcd Hcm Hsm Hck Hsk.
  destruct (bezout_coprime m k ltac:(lia) Hgcd) as [u [v Huv]].
  assert (HmR : INR m <> 0) by (apply not_0_INR; lia).
  assert (HkR : INR k <> 0) by (apply not_0_INR; lia).
  assert (HuvR : INR u * INR m = 1 + INR v * INR k).
  { rewrite <- !mult_INR. replace (1:R) with (INR 1) by (simpl; ring).
    rewrite <- plus_INR. apply f_equal. exact Huv. }
  assert (Hone : INR u * INR m - INR v * INR k = 1) by lra.
  assert (Hangle : 2 * PI / INR (m * k)
                   = INR u * (2 * PI / INR k) - INR v * (2 * PI / INR m)).
  { rewrite mult_INR.
    transitivity (2 * PI * (INR u * INR m - INR v * INR k) / (INR m * INR k)).
    - rewrite Hone. field. split; assumption.
    - field. split; assumption. }
  destruct (vertex_coords_ONK kk (2 * PI / INR k) Hck Hsk u) as [Hcuk Hsuk].
  destruct (vertex_coords_ONK kk (2 * PI / INR m) Hcm Hsm v) as [Hcvm Hsvm].
  rewrite Hangle. split.
  - rewrite cos_minus. apply ONK_add; apply ONK_mul; assumption.
  - rewrite sin_minus. apply ONK_sub; apply ONK_mul; assumption.
Qed.

(** The prime case: small primes through the Chebyshev rung at exponent one,
    primes >= 5 through the parametric Gaussian-period tower over the
    unconditional primitive root, every rung solved by ONK_proot. *)
Lemma Hcore_ONK : forall kk, (1 <= kk)%nat -> forall p,
  Znumtheory.prime (Z.of_nat p) -> smooth_upto (2 * kk + 1) (euler_phi p) ->
  OrigamiNumK kk (cos (2 * PI / INR p)).
Proof.
  intros kk Hkk p Hp Hsm.
  destruct (le_lt_dec 5 p) as [Hge | Hlt].
  - destruct (primitive_root_gen p Hp Hge) as [g [Hgr [Hper Hgord]]].
    apply (tower_cos_prime_rungs p g Hp Hge Hper Hgord Hgr
             (OrigamiNumK kk) (onk_tower_ops kk Hkk)).
    intros rho Hrho Hrhodiv c r Hc Heq.
    apply (ONK_proot kk rho c r Hrho); [| exact Hc | exact Heq].
    rewrite <- (euler_phi_prime p Hp) in Hrhodiv.
    exact (Hsm rho Hrho Hrhodiv).
  - pose proof (is_prime_of_Z p Hp) as [Hp1 _].
    assert (Hp4 : p <> 4%nat).
    { intro E. subst p. pose proof (is_prime_of_Z 4 Hp) as [_ Hdd].
      destruct (Hdd 2%nat ltac:(lia) ltac:(exists 2%nat; reflexivity)) as [E'|E']; lia. }
    assert (Hple : (p <= 2 * kk + 1)%nat) by lia.
    pose proof (cos_2pi_qe_ONK kk p Hkk Hp Hple 1) as H1.
    rewrite Nat.pow_1_r in H1. exact H1.
Qed.

(** Constructive direction, all n, by prime-power split and CRT. *)
Theorem cos_sin_smoothK : forall kk, (1 <= kk)%nat ->
  forall n, (1 <= n)%nat -> smooth_upto (2 * kk + 1) (euler_phi n) ->
  OrigamiNumK kk (cos (2 * PI / INR n)) /\ OrigamiNumK kk (sin (2 * PI / INR n)).
Proof.
  intros kk Hkk n.
  induction n as [n IH] using (well_founded_induction lt_wf). intros Hn Hsm.
  destruct (le_lt_dec n 2) as [Hle | Hgt].
  - assert (E : n = 1%nat \/ n = 2%nat) by lia. destruct E as [E|E]; subst n.
    + replace (2 * PI / INR 1) with (2 * PI) by (simpl; field).
      rewrite cos_2PI, sin_2PI. split; [apply ONK_1 | apply ONK_0].
    + replace (2 * PI / INR 2) with PI by (simpl; field).
      rewrite cos_PI, sin_PI. split; [apply ONK_neg; apply ONK_1 | apply ONK_0].
  - assert (Hn2 : (2 <= n)%nat) by lia.
    destruct (prime_factor_nat n ltac:(lia)) as [p [Hp Hpn]].
    assert (Hp2 : (2 <= p)%nat) by (pose proof (is_prime_of_Z p Hp) as [Hp1 _]; lia).
    destruct (ppart_exists p n Hp2 ltac:(lia)) as [e [k [Hnk Hpk]]].
    assert (He1 : (1 <= e)%nat).
    { destruct e as [|e']; [|lia]. exfalso. rewrite Nat.pow_0_r, Nat.mul_1_l in Hnk.
      subst k. apply Hpk; exact Hpn. }
    set (q := (p ^ e)%nat) in *.
    assert (Hple : (p <= q)%nat).
    { unfold q. rewrite <- (Nat.pow_1_r p) at 1. apply Nat.pow_le_mono_r; lia. }
    assert (Hq2 : (2 <= q)%nat) by lia.
    assert (Hgcd : Nat.gcd q k = 1%nat) by (unfold q; apply coprime_pp; assumption).
    assert (Hk1 : (1 <= k)%nat).
    { destruct k as [|k']; [|lia]. rewrite Nat.mul_0_r in Hnk. lia. }
    destruct (le_lt_dec k 1) as [Hkle | Hkgt].
    + assert (Ek : k = 1%nat) by lia. subst k. rewrite Nat.mul_1_r in Hnk.
      assert (Hcosn : OrigamiNumK kk (cos (2 * PI / INR n))).
      { destruct (Nat.eq_dec e 1) as [-> | Hee].
        - unfold q in Hnk. rewrite Nat.pow_1_r in Hnk. subst n.
          apply Hcore_ONK; assumption.
        - assert (Hpphi : Nat.divide p (euler_phi n)).
          { rewrite Hnk. unfold q. apply p_dvd_phi_pp; [exact Hp | lia]. }
          assert (Hpb : (p <= 2 * kk + 1)%nat) by (apply Hsm; assumption).
          rewrite Hnk. unfold q. apply cos_2pi_qe_ONK; assumption. }
      split; [exact Hcosn | apply sin_ONK_of_cos; [exact Hn2 | exact Hcosn]].
    + assert (Hk2 : (2 <= k)%nat) by lia.
      assert (Hqlt : (q < n)%nat) by (rewrite Hnk; nia).
      assert (Hklt : (k < n)%nat) by (rewrite Hnk; nia).
      assert (Hphi_eq : euler_phi n = (euler_phi q * euler_phi k)%nat).
      { rewrite Hnk. apply euler_phi_mult; [lia | lia | exact Hgcd]. }
      assert (Hsmq : smooth_upto (2 * kk + 1) (euler_phi q)).
      { apply (smooth_upto_divisor (2 * kk + 1) (euler_phi n)); [| exact Hsm].
        rewrite Hphi_eq. exists (euler_phi k). ring. }
      assert (Hsmk : smooth_upto (2 * kk + 1) (euler_phi k)).
      { apply (smooth_upto_divisor (2 * kk + 1) (euler_phi n)); [| exact Hsm].
        rewrite Hphi_eq. exists (euler_phi q). ring. }
      destruct (IH q Hqlt ltac:(lia) Hsmq) as [Hcq Hsq].
      destruct (IH k Hklt ltac:(lia) Hsmk) as [Hck Hsk].
      rewrite Hnk.
      apply cos_sin_ONK_mul;
        [lia | lia | exact Hgcd | exact Hcq | exact Hsq | exact Hck | exact Hsk].
Qed.

(** Necessity: non-smooth phi(n) rules out k-fold constructibility, by the
    smooth degree bound against the exact cosine degree. *)
Theorem cos_2pi_n_not_k_fold : forall kk, (1 <= kk)%nat -> forall n m, (3 <= n)%nat ->
  (euler_phi n = 2 * m)%nat -> ~ smooth_upto (2 * kk + 1) m ->
  ~ OrigamiNumK kk (cos (2 * PI / INR n)).
Proof.
  intros kk Hkk n m Hn Hphi Hns HO.
  set (delta := 2 * cos (2 * PI / INR n)).
  assert (Hdelta : OrigamiNumK kk delta).
  { unfold delta.
    replace (2 * cos (2 * PI / INR n))
      with (cos (2 * PI / INR n) + cos (2 * PI / INR n)) by ring.
    apply ONK_add; exact HO. }
  destruct (OrigamiNumK_field_degree_smooth kk Hkk delta Hdelta) as [d [Hbasis Hsmooth]].
  pose proof (cos_2pi_n_degree_exactly n m Hn Hphi) as Hbasism. fold delta in Hbasism.
  destruct Hbasis as [HBd [Hlid Hspd]].
  destruct Hbasism as [HBm [Hlim Hspm]].
  assert (Hdm : (d <= m)%nat).
  { pose proof (indep_le_span is_rational (powers delta d) (powers delta m) (Qx delta)
                  is_rational_subfield Hlid HBd Hspm) as Hle.
    rewrite !powers_length in Hle. exact Hle. }
  assert (Hmd : (m <= d)%nat).
  { pose proof (indep_le_span is_rational (powers delta m) (powers delta d) (Qx delta)
                  is_rational_subfield Hlim HBm Hspd) as Hle.
    rewrite !powers_length in Hle. exact Hle. }
  assert (Hdeq : d = m) by lia. subst d. exact (Hns Hsmooth).
Qed.

Theorem cos_2pi_n_not_k_fold_clean : forall kk, (1 <= kk)%nat -> forall n, (3 <= n)%nat ->
  ~ smooth_upto (2 * kk + 1) (euler_phi n) -> ~ OrigamiNumK kk (cos (2 * PI / INR n)).
Proof.
  intros kk Hkk n Hn Hns HO.
  destruct (euler_phi_even n Hn) as [m Hm].
  assert (Hmk : smooth_upto (2 * kk + 1) m).
  { destruct (classic (smooth_upto (2 * kk + 1) m)) as [Hs|Hns2]; [exact Hs|].
    exfalso. exact (cos_2pi_n_not_k_fold kk Hkk n m Hn Hm Hns2 HO). }
  apply Hns. rewrite Hm.
  apply smooth_upto_mul; [| exact Hmk].
  apply smooth_upto_of_le; lia.
Qed.

(** THE k-FOLD n-GON THEOREM: for every fold budget k >= 1 and every n >= 3,
    cos(2*PI/n) is k-fold-origami constructible exactly when every prime
    factor of phi(n) is at most 2k+1.  ngon_origami_iff, ngon_two_fold_iff,
    and ngon_three_fold_iff are the instances k = 1, 2, 3 through
    OrigamiNumK_1_iff, OrigamiNumK_2_iff, OrigamiNumK_3_iff. *)
Theorem ngon_k_fold_iff : forall kk, (1 <= kk)%nat -> forall n, (3 <= n)%nat ->
  (OrigamiNumK kk (cos (2 * PI / INR n)) <-> smooth_upto (2 * kk + 1) (euler_phi n)).
Proof.
  intros kk Hkk n Hn. split.
  - intro HO. destruct (classic (smooth_upto (2 * kk + 1) (euler_phi n))) as [Hs|Hns].
    + exact Hs.
    + exfalso. exact (cos_2pi_n_not_k_fold_clean kk Hkk n Hn Hns HO).
  - intro Hs. apply (cos_sin_smoothK kk Hkk n); [lia | exact Hs].
Qed.

(* ============================================================================
   The simultaneous k-fold Lill system.  k creases coupled by k-1 middle bounce
   segments solve the degree-(2k+1) Bring-Jerrard trinomial: the shooting path
   leaves the origin, alternates between the coefficient lines x = 1 and y = 0
   (k bounce pairs, segment i running (xv i, 0) -> (1, yv i)), and lands on
   ((-1)^k p + 1, (-1)^k q).  k = 1 is the Beloch fold, k = 2 and k = 3 are the
   two- and three-fold systems.
   ============================================================================ *)

Definition k_fold_lill (k : nat) (p q : R) (gs : nat -> Line) : Prop :=
  exists (yv xv : nat -> R),
    xv 0%nat = 0 /\
    (forall i, (i < k)%nat -> line_wf (gs i)) /\
    (forall i, (i < k)%nat ->
       on_line (1, yv i) (gs i) /\ on_line (xv (S i), 0) (gs i)) /\
    (forall i, (i < k)%nat ->
       line_perp (line_through (xv i, 0) (1, yv i)) (gs i)) /\
    (forall i, (1 <= i < k)%nat ->
       line_perp (line_through (xv i, 0) (1, yv i)) (gs (i - 1)%nat)) /\
    line_perp (line_through (xv k, 0) ((-1) ^ k * p + 1, (-1) ^ k * q))
      (gs (k - 1)%nat).

(** Soundness: every simultaneous k-fold Lill manipulation solves the
    Bring-Jerrard trinomial of degree 2k+1. *)
Theorem k_fold_lill_solves : forall k p q gs, (1 <= k)%nat ->
  k_fold_lill k p q gs ->
  exists t, t ^ (2 * k + 1) + p * t + q = 0.
Proof.
  intros k p q gs Hk [yv [xv [Hx0 [Hwf [Hmem [Hperp [Hcpl Hfin]]]]]]].
  set (u := yv 0%nat).
  assert (HP : forall j, (j < k)%nat ->
    yv j = (-1) ^ j * u ^ (2 * j + 1) /\
    xv (S j) = 1 + (-1) ^ j * u ^ (2 * j + 2) /\
    B (gs j) = u * A (gs j) /\
    A (gs j) <> 0 /\
    ((1 <= j)%nat -> u <> 0)).
  { induction j as [|j IHj]; intro Hjk.
    - pose proof (Hperp 0%nat Hjk) as HP0.
      unfold line_perp, line_through in HP0. rewrite Hx0 in HP0.
      destruct (Req_EM_T 0 1) as [E01 | _]; [lra |].
      cbn [A B] in HP0.
      assert (EB : B (gs 0%nat) = u * A (gs 0%nat)) by (unfold u; lra).
      assert (HA : A (gs 0%nat) <> 0).
      { intro H0. destruct (Hwf 0%nat Hjk) as [HA'|HB']; [exact (HA' H0)|].
        apply HB'. rewrite EB, H0. ring. }
      destruct (Hmem 0%nat Hjk) as [Hm1 Hm2]. unfold on_line in Hm1, Hm2.
      fold u in Hm1. rewrite EB in Hm1.
      assert (Ex : xv 1%nat = 1 + u * u)
        by (apply (Rmult_eq_reg_l (A (gs 0%nat))); [nra | exact HA]).
      split; [unfold u; cbn; ring |].
      split; [rewrite Ex; cbn; ring |].
      split; [exact EB |].
      split; [exact HA |].
      intro Hc. exfalso. lia.
    - assert (Hjk' : (j < k)%nat) by lia.
      destruct (IHj Hjk') as [Hyj [Hxj [HBj [HAj _]]]].
      pose proof (Hcpl (S j) ltac:(lia)) as Hc.
      replace (S j - 1)%nat with j in Hc by lia.
      pose proof (Hperp (S j) Hjk) as Hp'.
      unfold line_perp, line_through in Hc, Hp'.
      rewrite Hxj in Hc, Hp'.
      destruct (Req_EM_T (1 + (-1) ^ j * u ^ (2 * j + 2)) 1) as [Edeg | Hne].
      { exfalso. cbn [A B] in Hc. apply HAj. lra. }
      assert (Hu : u <> 0).
      { intro Hu0. apply Hne. rewrite Hu0.
        rewrite pow_ne_zero by lia. ring. }
      cbn [A B] in Hc, Hp'.
      rewrite HBj in Hc.
      assert (HYl : yv (S j) = - ((-1) ^ j * u ^ (2 * j + 2) * u))
        by (apply (Rmult_eq_reg_l (A (gs j))); [nra | exact HAj]).
      rewrite HYl in Hp'.
      assert (Hfac : (-1) ^ j * u ^ (2 * j + 2)
                     * (u * A (gs (S j)) - B (gs (S j))) = 0) by nra.
      assert (HBSj : B (gs (S j)) = u * A (gs (S j))).
      { destruct (Rmult_integral _ _ Hfac) as [Hf1 | Hf2]; [| lra].
        exfalso. destruct (Rmult_integral _ _ Hf1) as [Hm | Hpz].
        - exact (pow_nonzero (-1) j ltac:(lra) Hm).
        - exact (pow_nonzero u (2*j+2) Hu Hpz). }
      assert (HASj : A (gs (S j)) <> 0).
      { intro H0. destruct (Hwf (S j) Hjk) as [HA'|HB']; [exact (HA' H0)|].
        apply HB'. rewrite HBSj, H0. ring. }
      destruct (Hmem (S j) Hjk) as [Hm1 Hm2]. unfold on_line in Hm1, Hm2.
      rewrite HBSj in Hm1. rewrite HYl in Hm1.
      assert (HxSSj : xv (S (S j)) = 1 + (-1) ^ S j * u ^ (2 * S j + 2)).
      { replace (2 * S j + 2)%nat with ((2 * j + 2) + 2)%nat by lia.
        rewrite pow_add. cbn [pow].
        replace ((-1) ^ S j) with (- (-1) ^ j) by (cbn [pow]; ring).
        apply (Rmult_eq_reg_l (A (gs (S j)))); [nra | exact HASj]. }
      split.
      { rewrite HYl.
        replace (2 * S j + 1)%nat with ((2 * j + 2) + 1)%nat by lia.
        replace ((-1) ^ S j) with (- (-1) ^ j) by (cbn [pow]; ring).
        rewrite !pow_add. cbn [pow].
        generalize (u ^ (2 * j)). intro T.
        generalize ((-1) ^ j). intro M. ring. }
      split; [exact HxSSj |].
      split; [exact HBSj |].
      split; [exact HASj |].
      intros _. exact Hu. }
  assert (Hk1 : (k - 1 < k)%nat) by lia.
  destruct (HP (k - 1)%nat Hk1) as [Hyk [Hxk [HBk [HAk _]]]].
  replace (S (k - 1))%nat with k in Hxk by lia.
  unfold line_perp, line_through in Hfin.
  rewrite Hxk in Hfin.
  destruct (Req_EM_T (1 + (-1) ^ (k - 1) * u ^ (2 * (k - 1) + 2))
              ((-1) ^ k * p + 1)) as [Edeg | Hne].
  { exfalso. cbn [A B] in Hfin. apply HAk. lra. }
  cbn [A B] in Hfin.
  rewrite HBk in Hfin.
  assert (Hsig : (-1) ^ k = - (-1) ^ (k - 1)).
  { destruct k as [|k']; [lia |].
    replace (S k' - 1)%nat with k' by lia. cbn [pow]. ring. }
  rewrite Hsig in Hfin.
  assert (Hq : q = u * p + u * u ^ (2 * (k - 1) + 2)).
  { apply (Rmult_eq_reg_l ((-1) ^ (k - 1) * A (gs (k - 1)%nat))).
    - nra.
    - apply Rmult_integral_contrapositive_currified;
        [apply pow_nonzero; lra | exact HAk]. }
  exists (- u).
  replace ((- u) ^ (2 * k + 1)) with (- (u * u ^ (2 * (k - 1) + 2))).
  - lra.
  - replace (- u) with (-1 * u) by ring.
    rewrite Rpow_mult_distr.
    replace (2 * k + 1)%nat with (S (2 * k))%nat by lia.
    rewrite pow_1_odd.
    replace (S (2 * k))%nat with (S (2 * (k - 1) + 2))%nat by lia.
    cbn [pow]. generalize (u ^ (2 * (k - 1) + 2)). intro T. ring.
Qed.

(** Realizability: every root with q <> 0 is produced by the explicit k-crease
    system whose mirrors all have normal (1, -t). *)
Theorem k_fold_lill_realizable : forall k p q t, (1 <= k)%nat ->
  t ^ (2 * k + 1) + p * t + q = 0 -> q <> 0 ->
  k_fold_lill k p q
    (fun i => {| A := 1; B := - t; C := - (1 + (-1) ^ i * t ^ (2 * i + 2)) |}).
Proof.
  intros k p q t Hk Hroot Hq0.
  assert (Ht : t <> 0).
  { intro Ht0. apply Hq0. rewrite Ht0 in Hroot.
    rewrite pow_ne_zero in Hroot by lia. lra. }
  exists (fun i => - ((-1) ^ i * t ^ (2 * i + 1))),
         (fun i => match i with
                   | O => 0
                   | S i' => 1 + (-1) ^ i' * t ^ (2 * i' + 2)
                   end).
  split; [reflexivity |].
  split. { intros i Hi. left. cbn [A]. lra. }
  split.
  { intros i Hi. unfold on_line. cbn [A B C]. split.
    - rewrite !pow_add. cbn [pow].
      generalize (t ^ (2 * i)). intro T.
      generalize ((-1) ^ i). intro M. ring.
    - rewrite !pow_add. cbn [pow].
      generalize (t ^ (2 * i)). intro T.
      generalize ((-1) ^ i). intro M. ring. }
  split.
  { intros i Hi. unfold line_perp, line_through.
    destruct i as [|i'].
    - destruct (Req_EM_T 0 1) as [E|_]; [lra |].
      cbn. ring.
    - destruct (Req_EM_T (1 + (-1) ^ i' * t ^ (2 * i' + 2)) 1) as [E | _].
      { exfalso.
        assert (HX : (-1) ^ i' * t ^ (2 * i' + 2) = 0) by lra.
        destruct (Rmult_integral _ _ HX) as [Hm|Hp'];
          [exact (pow_nonzero (-1) i' ltac:(lra) Hm)
          | exact (pow_nonzero t (2*i'+2) Ht Hp')]. }
      cbn [A B].
      replace (2 * S i' + 1)%nat with ((2 * i' + 2) + 1)%nat by lia.
      replace ((-1) ^ S i') with (- (-1) ^ i') by (cbn [pow]; ring).
      rewrite !pow_add. cbn [pow].
      generalize (t ^ (2 * i')). intro T.
      generalize ((-1) ^ i'). intro M. ring. }
  split.
  { intros i [Hi1 Hik]. destruct i as [|i']; [lia |].
    replace (S i' - 1)%nat with i' by lia.
    unfold line_perp, line_through.
    destruct (Req_EM_T (1 + (-1) ^ i' * t ^ (2 * i' + 2)) 1) as [E | _].
    { exfalso.
      assert (HX : (-1) ^ i' * t ^ (2 * i' + 2) = 0) by lra.
      destruct (Rmult_integral _ _ HX) as [Hm|Hp'];
        [exact (pow_nonzero (-1) i' ltac:(lra) Hm)
        | exact (pow_nonzero t (2*i'+2) Ht Hp')]. }
    cbn [A B].
    replace (2 * S i' + 1)%nat with ((2 * i' + 2) + 1)%nat by lia.
    replace ((-1) ^ S i') with (- (-1) ^ i') by (cbn [pow]; ring).
    rewrite !pow_add. cbn [pow].
    generalize (t ^ (2 * i')). intro T.
    generalize ((-1) ^ i'). intro M. ring. }
  { destruct k as [|k']; [lia |].
    unfold line_perp, line_through.
    replace (2 * S k' + 1)%nat with ((2 * k' + 2) + 1)%nat in Hroot by lia.
    rewrite pow_add in Hroot. cbn [pow] in Hroot.
    destruct (Req_EM_T (1 + (-1) ^ k' * t ^ (2 * k' + 2))
                ((-1) ^ S k' * p + 1)) as [E | _].
    { exfalso. apply Hq0.
      cbn [pow] in E.
      assert (HE : (-1) ^ k' * (t ^ (2 * k' + 2) + p) = 0) by nra.
      destruct (Rmult_integral _ _ HE) as [Hm | Hsum];
        [exfalso; exact (pow_nonzero (-1) k' ltac:(lra) Hm) | nra]. }
    cbn [A B]. cbn [pow].
    assert (Hq' : q = - (p * t + t ^ (2 * k' + 2) * (t * 1))) by lra.
    rewrite Hq'.
    generalize (t ^ (2 * k' + 2)). intro T.
    generalize ((-1) ^ k'). intro M. ring. }
Qed.

(** The general Bring-Jerrard crease {t, -1, -t^2k}: k = 1 is the Beloch
    crease, k = 2 the two-fold quintic crease, k = 3 the septic crease. *)
Definition bj_crease (kk : nat) (t : R) : Line :=
  {| A := t; B := -1; C := - t ^ (2 * kk) |}.

Lemma bj_crease_reflects : forall kk p q t, (1 <= kk)%nat ->
  t ^ (2 * kk + 1) + p * t + q = 0 ->
  on_line (reflect_point (q, p) (bj_crease kk t)) {| A := 1; B := 0; C := q |}.
Proof.
  intros kk p q t Hk Hroot.
  replace (2 * kk + 1)%nat with ((2 * kk) + 1)%nat in Hroot by lia.
  rewrite pow_add in Hroot. cbn [pow] in Hroot.
  assert (Hq' : q = - (t ^ (2 * kk) * (t * 1) + p * t)) by lra.
  unfold reflect_point, bj_crease, on_line; simpl.
  assert (Ht2 : 0 <= t * t) by apply Rle_0_sqr.
  assert (Hd : t * t + (-1) * (-1) <> 0) by lra.
  rewrite Hq'.
  replace (kk + (kk + 0))%nat with (2 * kk)%nat by lia.
  generalize (t ^ (2 * kk)). intro T.
  field. lra.
Qed.

(** Every k-fold Lill manipulation yields a Bring-Jerrard root whose general
    crease carries the incidence. *)
Theorem k_fold_axiom_grounds_crease : forall k p q gs, (1 <= k)%nat ->
  k_fold_lill k p q gs ->
  exists t, t ^ (2 * k + 1) + p * t + q = 0 /\
    on_line (reflect_point (q, p) (bj_crease k t)) {| A := 1; B := 0; C := q |}.
Proof.
  intros k p q gs Hk H.
  destruct (k_fold_lill_solves k p q gs Hk H) as [t Ht].
  exists t. split; [exact Ht |].
  apply bj_crease_reflects; assumption.
Qed.

(* ============================================================================
   The general-coefficient Lill chain.  For an arbitrary monic polynomial
   sum a_i x^i of odd degree n = 2k+1, the bounce lines sit at the alternating
   partial sums lill_X / lill_Y of the coefficients, and the same k coupled
   mirrors force the Horner value lill_B at -u to vanish: general Lill removes
   the Bring-Jerrard trinomial restriction.
   ============================================================================ *)

(** Horner prefix values of the monic polynomial at -u *)
Fixpoint lill_B (a : nat -> R) (n : nat) (u : R) (m : nat) : R :=
  match m with
  | O => 1
  | S m' => a (n - 1 - m')%nat + (- u) * lill_B a n u m'
  end.

Lemma lill_B_S : forall a n u m,
  lill_B a n u (S m) = a (n - 1 - m)%nat + (- u) * lill_B a n u m.
Proof. reflexivity. Qed.

(** Horner correctness: the full prefix is the polynomial value at -u. *)
Lemma lill_B_fsum : forall (a : nat -> R) n u m, (m <= n)%nat -> a n = 1 ->
  lill_B a n u m = fsum (S m) (fun j => a (n - m + j)%nat * (- u) ^ j).
Proof.
  intros a n u m. induction m as [|m IH]; intros Hm Han.
  - cbn [lill_B]. rewrite fsum_S. cbn [fsum].
    replace (n - 0 + 0)%nat with n by lia. rewrite Han. cbn [pow]. ring.
  - rewrite lill_B_S, (IH ltac:(lia) Han).
    rewrite (fsum_S_shift (S m)).
    replace (n - S m + 0)%nat with (n - 1 - m)%nat by lia.
    rewrite (fsum_ext (S m)
               (fun i => a (n - S m + S i)%nat * (- u) ^ S i)
               (fun i => (- u) * (a (n - m + i)%nat * (- u) ^ i))).
    + rewrite fsum_scale. cbn [pow]. ring.
    + intros i Hi. replace (n - S m + S i)%nat with (n - m + i)%nat by lia.
      cbn [pow]. ring.
Qed.

(** The alternating partial sums giving the bounce-line positions. *)
Definition lill_X (a : nat -> R) (n s : nat) : R :=
  fsum (S s) (fun m => (-1) ^ m * a (n - 2 * m)%nat).
Definition lill_Y (a : nat -> R) (n s : nat) : R :=
  fsum (S s) (fun m => (-1) ^ m * a (n - 1 - 2 * m)%nat).
Definition lill_Yp (a : nat -> R) (n : nat) (i : nat) : R :=
  match i with O => 0 | S i' => lill_Y a n i' end.

Lemma lill_X_S : forall a n s,
  lill_X a n (S s) = lill_X a n s + (-1) ^ S s * a (n - 2 * S s)%nat.
Proof. intros. unfold lill_X. rewrite (fsum_S (S s)). reflexivity. Qed.

Lemma lill_Y_S : forall a n s,
  lill_Y a n (S s) = lill_Y a n s + (-1) ^ S s * a (n - 1 - 2 * S s)%nat.
Proof. intros. unfold lill_Y. rewrite (fsum_S (S s)). reflexivity. Qed.

(** The general Lill system: k coupled mirrors over the coefficient lines of
    an arbitrary monic degree-(2k+1) polynomial. *)
Definition general_lill (k : nat) (a : nat -> R) (gs : nat -> Line) : Prop :=
  exists (yv xv : nat -> R),
    xv 0%nat = 0 /\
    (forall i, (i < k)%nat -> line_wf (gs i)) /\
    (forall i, (i < k)%nat ->
       on_line (lill_X a (2*k+1) i, yv i) (gs i) /\
       on_line (xv (S i), lill_Y a (2*k+1) i) (gs i)) /\
    (forall i, (i < k)%nat ->
       line_perp (line_through (xv i, lill_Yp a (2*k+1) i)
                    (lill_X a (2*k+1) i, yv i)) (gs i)) /\
    (forall i, (1 <= i < k)%nat ->
       line_perp (line_through (xv i, lill_Yp a (2*k+1) i)
                    (lill_X a (2*k+1) i, yv i)) (gs (i - 1)%nat)) /\
    line_perp (line_through (xv k, lill_Yp a (2*k+1) k)
                 (lill_X a (2*k+1) k, lill_Y a (2*k+1) k)) (gs (k - 1)%nat).

(** GENERAL LILL SOUNDNESS: the k coupled mirrors solve the arbitrary monic
    polynomial of degree 2k+1 -- no trinomial restriction. *)
Theorem general_lill_solves : forall k (a : nat -> R) gs, (1 <= k)%nat ->
  a (2 * k + 1)%nat = 1 ->
  general_lill k a gs ->
  exists t, fsum (S (2 * k + 1)) (fun i => a i * t ^ i) = 0.
Proof.
  intros k a gs Hk Hmon Hsys.
  destruct k as [|k']; [lia |].
  destruct Hsys as [yv [xv [Hx0 [Hwf [Hmem [Hperp [Hcpl Hfin]]]]]]].
  set (n := (2 * S k' + 1)%nat) in *.
  set (u := yv 0%nat).
  assert (HP : forall j, (j < S k')%nat ->
    yv j = lill_Y a n j + (-1) ^ S j * lill_B a n u (2 * j + 1) /\
    xv (S j) = lill_X a n j + u * ((-1) ^ S j * lill_B a n u (2 * j + 1)) /\
    B (gs j) = u * A (gs j) /\
    A (gs j) <> 0).
  { induction j as [|j IHj]; intro Hjk.
    - pose proof (Hperp 0%nat Hjk) as HP0.
      unfold line_perp, line_through in HP0. rewrite Hx0 in HP0.
      cbn [lill_Yp] in HP0.
      assert (HX0 : lill_X a n 0%nat = 1).
      { unfold lill_X. cbn [fsum].
        replace (n - 2 * 0)%nat with n by lia.
        rewrite Hmon. cbn [pow]. ring. }
      rewrite HX0 in HP0.
      destruct (Req_EM_T 0 1) as [E01 | _]; [lra |].
      cbn [A B] in HP0.
      assert (EB : B (gs 0%nat) = u * A (gs 0%nat)) by (unfold u; lra).
      assert (HA : A (gs 0%nat) <> 0).
      { intro H0. destruct (Hwf 0%nat Hjk) as [HA'|HB']; [exact (HA' H0)|].
        apply HB'. rewrite EB, H0. ring. }
      destruct (Hmem 0%nat Hjk) as [Hm1 Hm2]. unfold on_line in Hm1, Hm2.
      fold u in Hm1. rewrite HX0 in Hm1. rewrite EB in Hm1, Hm2.
      assert (HY0 : lill_Y a n 0%nat = a (n - 1 - 0)%nat).
      { unfold lill_Y. cbn [fsum].
        replace (n - 1 - 2 * 0)%nat with (n - 1 - 0)%nat by lia.
        cbn [pow]. ring. }
      split.
      { replace (2 * 0 + 1)%nat with 1%nat by lia.
        rewrite lill_B_S. cbn [lill_B]. rewrite HY0.
        replace (n - 1 - 0)%nat with (n - 1 - 0)%nat by lia.
        cbn [pow]. unfold u. lra. }
      split.
      { replace (2 * 0 + 1)%nat with 1%nat by lia.
        rewrite lill_B_S. cbn [lill_B]. rewrite HX0.
        rewrite HY0 in Hm2. cbn [pow].
        apply (Rmult_eq_reg_l (A (gs 0%nat))); [| exact HA].
        nra. }
      split; [exact EB | exact HA].
    - assert (Hjk' : (j < S k')%nat) by lia.
      destruct (IHj Hjk') as [Hyj [Hxj [HBj HAj]]].
      pose proof (Hcpl (S j) ltac:(lia)) as Hc.
      replace (S j - 1)%nat with j in Hc by lia.
      pose proof (Hperp (S j) Hjk) as Hp'.
      unfold line_perp, line_through in Hc, Hp'.
      cbn [lill_Yp] in Hc, Hp'.
      destruct (Req_EM_T (xv (S j)) (lill_X a n (S j))) as [Edeg | Hne].
      { exfalso. cbn [A B] in Hc. apply HAj. lra. }
      cbn [A B] in Hc, Hp'.
      rewrite HBj in Hc.
      assert (HY : yv (S j) = lill_Y a n j
                   + u * (lill_X a n (S j) - xv (S j)))
        by (apply (Rmult_eq_reg_l (A (gs j))); [nra | exact HAj]).
      assert (Hfac : (lill_X a n (S j) - xv (S j))
                     * (u * A (gs (S j)) - B (gs (S j))) = 0).
      { rewrite HY in Hp'. nra. }
      assert (HBSj : B (gs (S j)) = u * A (gs (S j))).
      { destruct (Rmult_integral _ _ Hfac) as [Hf1 | Hf2]; [lra | lra]. }
      assert (HASj : A (gs (S j)) <> 0).
      { intro H0. destruct (Hwf (S j) Hjk) as [HA'|HB']; [exact (HA' H0)|].
        apply HB'. rewrite HBSj, H0. ring. }
      destruct (Hmem (S j) Hjk) as [Hm1 Hm2]. unfold on_line in Hm1, Hm2.
      rewrite HBSj in Hm1, Hm2.
      assert (HrS : (-1) ^ S (S j) * lill_B a n u (2 * S j + 1)
                    = (lill_Y a n j - lill_Y a n (S j))
                      + u * (lill_X a n (S j) - lill_X a n j)
                      - u * (u * ((-1) ^ S j * lill_B a n u (2 * j + 1)))).
      { replace (2 * S j + 1)%nat with (S (S (2 * j + 1)))%nat by lia.
        rewrite !lill_B_S.
        rewrite lill_X_S, lill_Y_S.
        replace (n - 1 - S (2 * j + 1))%nat with (n - 1 - 2 * S j)%nat by lia.
        replace (n - 1 - (2 * j + 1))%nat with (n - 2 * S j)%nat by lia.
        replace ((-1) ^ S (S j)) with (- (-1) ^ S j) by (cbn [pow]; ring).
        generalize (lill_B a n u (2 * j + 1)). intro Bv.
        generalize ((-1) ^ S j). intro M.
        generalize (a (n - 1 - 2 * S j)%nat). intro a0.
        generalize (a (n - 2 * S j)%nat). intro a1.
        ring. }
      split.
      { rewrite HY, Hxj, HrS.
        generalize ((-1) ^ S j * lill_B a n u (2 * j + 1)). intro rv. ring. }
      split.
      { assert (Hxx : xv (S (S j)) = lill_X a n (S j)
                      + u * (yv (S j) - lill_Y a n (S j)))
          by (apply (Rmult_eq_reg_l (A (gs (S j)))); [nra | exact HASj]).
        rewrite Hxx, HY, Hxj, HrS.
        generalize ((-1) ^ S j * lill_B a n u (2 * j + 1)). intro rv. ring. }
      split; [exact HBSj | exact HASj]. }
  assert (Hk1 : (k' < S k')%nat) by lia.
  destruct (HP k' Hk1) as [Hyk [Hxk [HBk HAk]]].
  unfold line_perp, line_through in Hfin.
  cbn [lill_Yp] in Hfin.
  replace (S k' - 1)%nat with k' in Hfin by lia.
  destruct (Req_EM_T (xv (S k')) (lill_X a n (S k'))) as [Edeg | Hne].
  { exfalso. cbn [A B] in Hfin. apply HAk. lra. }
  cbn [A B] in Hfin.
  rewrite HBk in Hfin.
  assert (HBn : lill_B a n u n = 0).
  { assert (Hlin : (lill_Y a n k' - lill_Y a n (S k'))
                   + u * (lill_X a n (S k') - xv (S k')) = 0)
      by (apply (Rmult_eq_reg_l (A (gs k'))); [nra | exact HAk]).
    assert (Hneq : n = S (S (2 * k' + 1))) by (unfold n; lia).
    rewrite Hneq at 2.
    rewrite !lill_B_S.
    rewrite lill_X_S, lill_Y_S in Hlin.
    rewrite Hxk in Hlin.
    replace (n - 1 - S (2 * k' + 1))%nat with (n - 1 - 2 * S k')%nat by lia.
    replace (n - 1 - (2 * k' + 1))%nat with (n - 2 * S k')%nat by lia.
    assert (HMM : (-1) ^ S k' * (-1) ^ S k' = 1)
      by (rewrite <- Rpow_mult_distr; replace (-1 * -1) with 1 by ring; apply pow1).
    revert Hlin HMM.
    generalize (lill_B a n u (2 * k' + 1)). intro Bv.
    generalize ((-1) ^ S k'). intro M.
    generalize (a (n - 1 - 2 * S k')%nat). intro a0.
    generalize (a (n - 2 * S k')%nat). intro a1.
    intros Hlin HMM.
    assert (HM0 : M <> 0) by (intro E; rewrite E in HMM; lra).
    assert (Hlin' : a0 - u * a1 + u * (u * Bv) = 0).
    { apply (Rmult_eq_reg_l M); [| exact HM0].
      rewrite Rmult_0_r. nra. }
    nra. }
  exists (- u).
  pose proof (lill_B_fsum a n u n (Nat.le_refl n) Hmon) as Hbr.
  rewrite (fsum_ext (S n) (fun j => a (n - n + j)%nat * (- u) ^ j)
             (fun j => a j * (- u) ^ j)) in Hbr
    by (intros j Hj; replace (n - n + j)%nat with j by lia; reflexivity).
  rewrite <- Hbr. exact HBn.
Qed.

(* ============================================================================
   The coupled-catalog elimination core, part 1: polynomial multiplication on
   coefficient lists, its evaluation homomorphism, and OrigamiNum2 closure of
   the list operations -- the elimination arithmetic for coupled crease pairs.
   ============================================================================ *)

Fixpoint pmulR (ps qs : list R) : list R :=
  match ps with
  | nil => nil
  | p :: ps' => paddR (pscaleR p qs) (0 :: pmulR ps' qs)
  end.

Lemma pevalR_pmul : forall ps qs x,
  pevalR (pmulR ps qs) x = pevalR ps x * pevalR qs x.
Proof.
  induction ps as [|p ps' IH]; intros qs x.
  - cbn [pmulR pevalR]. ring.
  - cbn [pmulR pevalR]. rewrite pevalR_padd, pevalR_pscale.
    cbn [pevalR]. rewrite IH. ring.
Qed.

Lemma Forall_paddR : forall (P : R -> Prop) ps qs,
  (forall x y, P x -> P y -> P (x + y)) ->
  Forall P ps -> Forall P qs -> Forall P (paddR ps qs).
Proof.
  intros P ps. induction ps as [|p ps' IH]; intros qs Hadd Hps Hqs.
  - exact Hqs.
  - destruct qs as [|q qs'].
    + exact Hps.
    + cbn [paddR]. inversion Hps; subst. inversion Hqs; subst.
      constructor; [apply Hadd; assumption | apply IH; assumption].
Qed.

Lemma Forall_pscaleR : forall (P : R -> Prop) a ps,
  (forall x y, P x -> P y -> P (x * y)) ->
  P a -> Forall P ps -> Forall P (pscaleR a ps).
Proof.
  intros P a ps Hmul Ha Hps. induction Hps as [|p ps' Hp Hps' IH].
  - constructor.
  - cbn [pscaleR map]. constructor; [apply Hmul; assumption | exact IH].
Qed.

Lemma Forall_pmulR : forall (P : R -> Prop) ps qs,
  (forall x y, P x -> P y -> P (x + y)) ->
  (forall x y, P x -> P y -> P (x * y)) ->
  P 0 -> Forall P ps -> Forall P qs -> Forall P (pmulR ps qs).
Proof.
  intros P ps. induction ps as [|p ps' IH]; intros qs Hadd Hmul H0 Hps Hqs.
  - constructor.
  - cbn [pmulR]. inversion Hps; subst.
    apply Forall_paddR; [exact Hadd | |].
    + apply Forall_pscaleR; assumption.
    + constructor; [exact H0 | apply IH; assumption].
Qed.

Lemma pevalR_ON2 : forall ps s,
  Forall OrigamiNum2 ps -> OrigamiNum2 s -> OrigamiNum2 (pevalR ps s).
Proof.
  intros ps s Hps Hs. induction Hps as [|p ps' Hp Hps' IH].
  - cbn [pevalR]. apply ON2_0.
  - cbn [pevalR]. apply ON2_add; [exact Hp | apply ON2_mul; [exact Hs | exact IH]].
Qed.

Lemma nth_Forall_ON2 : forall ps i,
  Forall OrigamiNum2 ps -> OrigamiNum2 (nth i ps 0).
Proof.
  intros ps i Hps.
  destruct (le_lt_dec (length ps) i) as [Hge | Hlt].
  - rewrite nth_overflow by exact Hge. apply ON2_0.
  - apply (proj1 (Forall_forall OrigamiNum2 ps) Hps).
    apply nth_In. exact Hlt.
Qed.

(* ============================================================================
   The coupled-catalog elimination core, part 2.  The mutually coupled two-fold
   alignment -- crease 1 through P1 carrying Q1 onto crease 2, crease 2 through
   P2 carrying Q2 onto crease 1 -- is the genuinely coupled shape of the
   Alperin-Lang two-fold catalog: neither crease is determined without the
   other.  Because carrying a point onto a crease is linear in the receiving
   crease, eliminating one slope is a substitution, and the elimination
   polynomial mpG has degree exactly 5 in the remaining slope: in general
   position both creases lie in OrigamiNum2.
   ============================================================================ *)

(** The pencil of lines through (px, py), parametrized by slope. *)
Definition pencil (px py s : R) : Line := {| A := s; B := -1; C := py - s * px |}.

Lemma pencil_wf : forall px py s, line_wf (pencil px py s).
Proof. intros. right. cbn [B pencil]. lra. Qed.

Lemma pencil_through : forall px py s, on_line (px, py) (pencil px py s).
Proof. intros. unfold on_line, pencil. cbn [A B C]. ring. Qed.

(** The cleared transfer polynomials: w * mpD(s) = mpN(s) expresses that the
    g1-image of Q1 lies on the slope-w pencil through P2. *)
Definition mpN (p1x p1y q1x q1y p2y : R) : list R :=
  (q1y - 2 * (q1y - p1y) - p2y) :: (2 * (q1x - p1x)) :: (q1y - p2y) :: nil.
Definition mpD (p1x p1y q1x q1y p2x : R) : list R :=
  (q1x - p2x) :: (2 * (q1y - p1y)) :: (2 * p1x - q1x - p2x) :: nil.

(** The degree-5 elimination polynomial of the mutually coupled system. *)
Definition mpG (p1x p1y q1x q1y p2x p2y q2x q2y : R) : list R :=
  psubR
    (0 :: paddR (pscaleR (nth 2 (mpD p2x p2y q2x q2y p1x) 0)
                   (pmulR (mpN p1x p1y q1x q1y p2y) (mpN p1x p1y q1x q1y p2y)))
            (paddR (pscaleR (nth 1 (mpD p2x p2y q2x q2y p1x) 0)
                      (pmulR (mpN p1x p1y q1x q1y p2y) (mpD p1x p1y q1x q1y p2x)))
               (pscaleR (nth 0 (mpD p2x p2y q2x q2y p1x) 0)
                  (pmulR (mpD p1x p1y q1x q1y p2x) (mpD p1x p1y q1x q1y p2x)))))
    (paddR (pscaleR (nth 2 (mpN p2x p2y q2x q2y p1y) 0)
              (pmulR (mpN p1x p1y q1x q1y p2y) (mpN p1x p1y q1x q1y p2y)))
       (paddR (pscaleR (nth 1 (mpN p2x p2y q2x q2y p1y) 0)
                 (pmulR (mpN p1x p1y q1x q1y p2y) (mpD p1x p1y q1x q1y p2x)))
          (pscaleR (nth 0 (mpN p2x p2y q2x q2y p1y) 0)
             (pmulR (mpD p1x p1y q1x q1y p2x) (mpD p1x p1y q1x q1y p2x))))).

Lemma mpG_length : forall p1x p1y q1x q1y p2x p2y q2x q2y,
  length (mpG p1x p1y q1x q1y p2x p2y q2x q2y) = 6%nat.
Proof. reflexivity. Qed.

Lemma mpN_ON2 : forall p1x p1y q1x q1y p2y,
  OrigamiNum2 p1x -> OrigamiNum2 p1y -> OrigamiNum2 q1x -> OrigamiNum2 q1y ->
  OrigamiNum2 p2y -> Forall OrigamiNum2 (mpN p1x p1y q1x q1y p2y).
Proof.
  intros. unfold mpN.
  assert (Htwo2 : OrigamiNum2 2)
    by (replace 2 with (1 + 1) by ring; apply ON2_add; apply ON2_1).
  repeat constructor;
    repeat (apply ON2_sub || apply ON2_add || apply ON2_mul); assumption.
Qed.

Lemma mpD_ON2 : forall p1x p1y q1x q1y p2x,
  OrigamiNum2 p1x -> OrigamiNum2 p1y -> OrigamiNum2 q1x -> OrigamiNum2 q1y ->
  OrigamiNum2 p2x -> Forall OrigamiNum2 (mpD p1x p1y q1x q1y p2x).
Proof.
  intros. unfold mpD.
  assert (Htwo2 : OrigamiNum2 2)
    by (replace 2 with (1 + 1) by ring; apply ON2_add; apply ON2_1).
  repeat constructor;
    repeat (apply ON2_sub || apply ON2_add || apply ON2_mul); assumption.
Qed.

Lemma mpG_ON2 : forall p1x p1y q1x q1y p2x p2y q2x q2y,
  OrigamiNum2 p1x -> OrigamiNum2 p1y -> OrigamiNum2 q1x -> OrigamiNum2 q1y ->
  OrigamiNum2 p2x -> OrigamiNum2 p2y -> OrigamiNum2 q2x -> OrigamiNum2 q2y ->
  Forall OrigamiNum2 (mpG p1x p1y q1x q1y p2x p2y q2x q2y).
Proof.
  intros.
  assert (HN1 : Forall OrigamiNum2 (mpN p1x p1y q1x q1y p2y))
    by (apply mpN_ON2; assumption).
  assert (HD1 : Forall OrigamiNum2 (mpD p1x p1y q1x q1y p2x))
    by (apply mpD_ON2; assumption).
  assert (HN2 : Forall OrigamiNum2 (mpN p2x p2y q2x q2y p1y))
    by (apply mpN_ON2; assumption).
  assert (HD2 : Forall OrigamiNum2 (mpD p2x p2y q2x q2y p1x))
    by (apply mpD_ON2; assumption).
  unfold mpG, psubR.
  apply Forall_paddR; [exact ON2_add | |].
  - constructor; [apply ON2_0 |].
    apply Forall_paddR; [exact ON2_add | |].
    + apply Forall_pscaleR; [exact ON2_mul | apply nth_Forall_ON2; exact HD2 |].
      apply Forall_pmulR;
        [exact ON2_add | exact ON2_mul | apply ON2_0 | exact HN1 | exact HN1].
    + apply Forall_paddR; [exact ON2_add | |].
      * apply Forall_pscaleR; [exact ON2_mul | apply nth_Forall_ON2; exact HD2 |].
        apply Forall_pmulR;
          [exact ON2_add | exact ON2_mul | apply ON2_0 | exact HN1 | exact HD1].
      * apply Forall_pscaleR; [exact ON2_mul | apply nth_Forall_ON2; exact HD2 |].
        apply Forall_pmulR;
          [exact ON2_add | exact ON2_mul | apply ON2_0 | exact HD1 | exact HD1].
  - apply Forall_pscaleR; [exact ON2_mul | |].
    + apply ON2_neg, ON2_1.
    + apply Forall_paddR; [exact ON2_add | |].
      * apply Forall_pscaleR; [exact ON2_mul | apply nth_Forall_ON2; exact HN2 |].
        apply Forall_pmulR;
          [exact ON2_add | exact ON2_mul | apply ON2_0 | exact HN1 | exact HN1].
      * apply Forall_paddR; [exact ON2_add | |].
        -- apply Forall_pscaleR; [exact ON2_mul | apply nth_Forall_ON2; exact HN2 |].
           apply Forall_pmulR;
             [exact ON2_add | exact ON2_mul | apply ON2_0 | exact HN1 | exact HD1].
        -- apply Forall_pscaleR; [exact ON2_mul | apply nth_Forall_ON2; exact HN2 |].
           apply Forall_pmulR;
             [exact ON2_add | exact ON2_mul | apply ON2_0 | exact HD1 | exact HD1].
Qed.

(** THE COUPLED ELIMINATION-DEGREE BOUND: in general position (the linear
    transfer solvable, the elimination exactly quintic) the mutually coupled
    two-fold alignment forces both slopes -- hence both creases -- into
    OrigamiNum2, through the degree-5 elimination polynomial mpG solved by the
    two-fold quintic fold. *)
Theorem mutual_pencil_two_fold_ON2 :
  forall p1x p1y q1x q1y p2x p2y q2x q2y s w,
  OrigamiNum2 p1x -> OrigamiNum2 p1y -> OrigamiNum2 q1x -> OrigamiNum2 q1y ->
  OrigamiNum2 p2x -> OrigamiNum2 p2y -> OrigamiNum2 q2x -> OrigamiNum2 q2y ->
  on_line (reflect_point (q1x, q1y) (pencil p1x p1y s)) (pencil p2x p2y w) ->
  on_line (reflect_point (q2x, q2y) (pencil p2x p2y w)) (pencil p1x p1y s) ->
  pevalR (mpD p1x p1y q1x q1y p2x) s <> 0 ->
  nth 5 (mpG p1x p1y q1x q1y p2x p2y q2x q2y) 0 <> 0 ->
  OrigamiNum2 s /\ OrigamiNum2 w.
Proof.
  intros p1x p1y q1x q1y p2x p2y q2x q2y s w
         HP1x HP1y HQ1x HQ1y HP2x HP2y HQ2x HQ2y Hon1 Hon2 HED Hlead.
  unfold on_line, reflect_point, pencil in Hon1, Hon2.
  cbn [fst snd A B C] in Hon1, Hon2.
  match type of Hon1 with
  | context [?num / ?den] =>
      set (v1 := num / den) in Hon1;
      assert (Hv1 : v1 * den = num)
        by (unfold v1; field;
            assert (Hsq : 0 <= s * s) by apply Rle_0_sqr; lra)
  end.
  match type of Hon2 with
  | context [?num / ?den] =>
      set (v2 := num / den) in Hon2;
      assert (Hv2 : v2 * den = num)
        by (unfold v2; field;
            assert (Hsq : 0 <= w * w) by apply Rle_0_sqr; lra)
  end.
  pose proof (f_equal (Rmult s) Hv1) as Hv1s.
  pose proof (f_equal (Rmult w) Hv1) as Hv1w.
  pose proof (f_equal (Rmult (w * s)) Hv1) as Hv1ws.
  pose proof (f_equal (Rmult (s * s)) Hon1) as Hon1s2.
  pose proof (f_equal (Rmult w) Hv2) as Hv2w.
  pose proof (f_equal (Rmult s) Hv2) as Hv2s.
  pose proof (f_equal (Rmult (s * w)) Hv2) as Hv2sw.
  pose proof (f_equal (Rmult (w * w)) Hon2) as Hon2w2.
  assert (HT1 : w * pevalR (mpD p1x p1y q1x q1y p2x) s
              = pevalR (mpN p1x p1y q1x q1y p2y) s).
  { cbn [pevalR mpD mpN]. nra. }
  assert (HT2 : s * pevalR (mpD p2x p2y q2x q2y p1x) w
              = pevalR (mpN p2x p2y q2x q2y p1y) w).
  { cbn [pevalR mpD mpN]. nra. }
  set (EN := pevalR (mpN p1x p1y q1x q1y p2y) s) in *.
  set (ED := pevalR (mpD p1x p1y q1x q1y p2x) s) in *.
  assert (Hroot : pevalR (mpG p1x p1y q1x q1y p2x p2y q2x q2y) s = 0).
  { unfold mpG, psubR.
    rewrite pevalR_padd, pevalR_pscale.
    cbn [pevalR].
    rewrite !pevalR_padd, !pevalR_pscale, !pevalR_pmul.
    fold EN ED.
    cbn [pevalR mpD mpN] in HT2.
    cbn [mpD mpN nth].
    pose proof (f_equal (Rmult (ED * ED)) HT2) as HT2c.
    rewrite <- HT1.
    nra. }
  set (G := mpG p1x p1y q1x q1y p2x p2y q2x q2y) in *.
  assert (HGON2 : Forall OrigamiNum2 G) by (unfold G; apply mpG_ON2; assumption).
  assert (HlenG : length G = 6%nat) by reflexivity.
  rewrite pevalR_nth_sum, HlenG in Hroot.
  cbn [fsum] in Hroot.
  set (c0 := nth 0 G 0) in *. set (c1 := nth 1 G 0) in *.
  set (c2 := nth 2 G 0) in *. set (c3 := nth 3 G 0) in *.
  set (c4 := nth 4 G 0) in *. set (c5 := nth 5 G 0) in *.
  assert (Hc0 : OrigamiNum2 c0) by (unfold c0; apply nth_Forall_ON2; exact HGON2).
  assert (Hc1 : OrigamiNum2 c1) by (unfold c1; apply nth_Forall_ON2; exact HGON2).
  assert (Hc2 : OrigamiNum2 c2) by (unfold c2; apply nth_Forall_ON2; exact HGON2).
  assert (Hc3 : OrigamiNum2 c3) by (unfold c3; apply nth_Forall_ON2; exact HGON2).
  assert (Hc4 : OrigamiNum2 c4) by (unfold c4; apply nth_Forall_ON2; exact HGON2).
  assert (Hc5 : OrigamiNum2 c5) by (unfold c5; apply nth_Forall_ON2; exact HGON2).
  assert (HsON : OrigamiNum2 s).
  { apply (ON2_quint (c4 / c5) (c3 / c5) (c2 / c5) (c1 / c5) (c0 / c5) s).
    - apply ON2_div; assumption.
    - apply ON2_div; assumption.
    - apply ON2_div; assumption.
    - apply ON2_div; assumption.
    - apply ON2_div; assumption.
    - apply (Rmult_eq_reg_l c5); [| exact Hlead].
      rewrite Rmult_0_r.
      transitivity (c0 * s ^ 0 + c1 * s ^ 1 + c2 * s ^ 2
                    + c3 * s ^ 3 + c4 * s ^ 4 + c5 * s ^ 5).
      + field. exact Hlead.
      + lra. }
  assert (HwON : OrigamiNum2 w).
  { assert (Hweq : w = EN / ED).
    { apply (Rmult_eq_reg_r ED); [| exact HED].
      transitivity EN; [exact HT1 | field; exact HED]. }
    rewrite Hweq. apply ON2_div.
    - unfold EN. apply pevalR_ON2; [apply mpN_ON2; assumption | exact HsON].
    - unfold ED. apply pevalR_ON2; [apply mpD_ON2; assumption | exact HsON].
    - exact HED. }
  exact (conj HsON HwON).
Qed.

(** The catalog-facing form: the coupled creases themselves have OrigamiNum2
    coordinates. *)
Corollary mutual_pencil_creases_ON2 :
  forall p1x p1y q1x q1y p2x p2y q2x q2y s w,
  OrigamiNum2 p1x -> OrigamiNum2 p1y -> OrigamiNum2 q1x -> OrigamiNum2 q1y ->
  OrigamiNum2 p2x -> OrigamiNum2 p2y -> OrigamiNum2 q2x -> OrigamiNum2 q2y ->
  on_line (reflect_point (q1x, q1y) (pencil p1x p1y s)) (pencil p2x p2y w) ->
  on_line (reflect_point (q2x, q2y) (pencil p2x p2y w)) (pencil p1x p1y s) ->
  pevalR (mpD p1x p1y q1x q1y p2x) s <> 0 ->
  nth 5 (mpG p1x p1y q1x q1y p2x p2y q2x q2y) 0 <> 0 ->
  (OrigamiNum2 (A (pencil p1x p1y s)) /\ OrigamiNum2 (B (pencil p1x p1y s)) /\
   OrigamiNum2 (C (pencil p1x p1y s))) /\
  (OrigamiNum2 (A (pencil p2x p2y w)) /\ OrigamiNum2 (B (pencil p2x p2y w)) /\
   OrigamiNum2 (C (pencil p2x p2y w))).
Proof.
  intros p1x p1y q1x q1y p2x p2y q2x q2y s w
         HP1x HP1y HQ1x HQ1y HP2x HP2y HQ2x HQ2y Hon1 Hon2 HED Hlead.
  destruct (mutual_pencil_two_fold_ON2 p1x p1y q1x q1y p2x p2y q2x q2y s w
              HP1x HP1y HQ1x HQ1y HP2x HP2y HQ2x HQ2y Hon1 Hon2 HED Hlead)
    as [HsON HwON].
  assert (Hm1 : OrigamiNum2 (-1))
    by (replace (-1) with (0 - 1) by ring; apply ON2_sub; [apply ON2_0 | apply ON2_1]).
  cbn [A B C pencil]. repeat split;
    repeat (apply ON2_sub || apply ON2_mul); assumption.
Qed.
