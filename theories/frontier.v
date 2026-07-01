(* frontier.v -- staging ground for results beyond established origami and
   constructibility mathematics: open conjectures and theorems not yet proved on
   paper.  A result already in the literature belongs in the settled core
   (foundations / cyclotomic / geometry) at the file its dependencies dictate;
   matured frontier results migrate there.

   Sibling of extraction.v; both build on the settled core and neither depends on
   the other.  Never Require extraction: it rebinds sqrt to the primitive machine
   float.

   Current campaign: the three-fold geometric layer and the k-fold program --
   the septic crease {t,-1,-t^6}, the simultaneous three-fold Lill system, and
   the first-polygon separations (29-gon, 23-gon).  These are not-yet-on-paper
   analogues of the settled two-fold theory in geometry.v and migrate down once
   established. *)
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
