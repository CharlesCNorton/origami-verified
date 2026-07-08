(* frontier.v -- results beyond the settled core (foundations/cyclotomic/geometry): open conjectures and not-yet-on-paper theorems; sibling of extraction.v, never Require it (it rebinds sqrt to the machine float); matured results migrate down. *)
From Stdlib Require Import Reals Lra Field R_sqr Psatz Nsatz Ring Ranalysis1 RingMicromega List ProofIrrelevance ClassicalDescription PeanoNat ZArith Classical Permutation Bool Arith.Wf_nat.
From Stdlib Require Znumtheory.
Import ListNotations.
Require Import foundations cyclotomic geometry.
Open Scope R_scope.

(* The three-fold geometric layer: the septic crease {t, -1, -t^6} solves the Bring-Jerrard septic as the Beloch crease solves the cubic, and three_fold_lill couples three creases by two shared-perpendicular bounce segments. *)

(** The three-fold crease with parameter t *)
Definition septic_crease (t : R) : Line := {| A := t; B := -1; C := -(t*t*t*t*t*t) |}.

Lemma septic_crease_wf : forall t, line_wf (septic_crease t).
Proof. intro t; unfold line_wf, septic_crease; simpl; right; lra. Qed.

(** Reflecting (q,p) across the crease lands on x = -q exactly along the Bring-Jerrard septic. *)
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

(** OrigamiNum3 is closed under the septic-crease root, the three-fold analogue of twofold_root_in_ON2. *)
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

(** The simultaneous three-fold Lill system: three creases over the Lill path of the septic, coupled by two middle bounce segments each perpendicular to two creases. *)
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

(** Soundness: every simultaneous three-fold Lill manipulation solves the Bring-Jerrard septic. *)
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

(** Realizability: every septic root with q <> 0 arises from an explicit three-fold Lill manipulation with mirrors of normal (1, -t). *)
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

(** Every simultaneous three-fold Lill manipulation yields a septic root whose crease {t, -1, -t^6} carries the incidence. *)
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

(* First-polygon separations: the 29-gon is the first three-fold-not-two-fold polygon (phi(29) = 2^2 * 7); the 23-gon is the first beyond three-fold (phi(23) = 2 * 11). *)

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

(** THE FIRST EXACTLY-THREE-FOLD POLYGON: the 29-gon, every smaller polygon being two-fold constructible or beyond three-fold. *)
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

(* The simultaneous k-fold Lill system: k creases coupled by k-1 middle bounce segments solve the degree-(2k+1) Bring-Jerrard trinomial; k = 1 is the Beloch fold. *)

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

(** Soundness: every simultaneous k-fold Lill manipulation solves the Bring-Jerrard trinomial of degree 2k+1. *)
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

(** Realizability: every root with q <> 0 arises from the explicit k-crease system with mirrors of normal (1, -t). *)
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

(** The general Bring-Jerrard crease {t, -1, -t^2k}: k = 1 Beloch, k = 2 the quintic crease, k = 3 the septic. *)
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

(** Every k-fold Lill manipulation yields a Bring-Jerrard root whose general crease carries the incidence. *)
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

(* The general-coefficient Lill chain: for any monic odd-degree polynomial the bounce lines sit at the alternating partial sums lill_X/lill_Y, and the k coupled mirrors force the Horner value lill_B at -u to vanish. *)

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

(** The general Lill system: k coupled mirrors over the coefficient lines of an arbitrary monic degree-(2k+1) polynomial. *)
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

(** GENERAL LILL SOUNDNESS: the k coupled mirrors solve the arbitrary monic polynomial of degree 2k+1. *)
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

(* Coupled-catalog elimination core: coefficient-list multiplication, its evaluation homomorphism, and OrigamiNum2 closure of the list operations. *)

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

(* Coupled-catalog elimination core: the mutually coupled two-fold alignment eliminates by substitution (the transfer is linear in the receiving crease) to the exactly-quintic mpG, so in general position both creases lie in OrigamiNum2. *)

(** The pencil of lines through (px, py), parametrized by slope. *)
Definition pencil (px py s : R) : Line := {| A := s; B := -1; C := py - s * px |}.

Lemma pencil_wf : forall px py s, line_wf (pencil px py s).
Proof. intros. right. cbn [B pencil]. lra. Qed.

Lemma pencil_through : forall px py s, on_line (px, py) (pencil px py s).
Proof. intros. unfold on_line, pencil. cbn [A B C]. ring. Qed.

(** The cleared transfer polynomials: w * mpD(s) = mpN(s) puts the g1-image of Q1 on the slope-w pencil through P2. *)
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

(** THE COUPLED ELIMINATION-DEGREE BOUND: in general position the mutual coupling forces both slopes into OrigamiNum2 through the quintic mpG. *)
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

(** The catalog-facing form: the coupled creases themselves have OrigamiNum2 coordinates. *)
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

(* THE COUPLED-CATALOG CLASSIFICATION AND REFUTATION: elimination degrees pencil*pencil 3, pencil*translate 3, translate*translate 1, translate*tangent 4, pencil*tangent 6, tangent*tangent 10; the positive cells are machine-checked, the sextic has Galois group S6 and the decic at least A10, so the conjecture that the coupled catalog stays inside OrigamiNum2 is FALSE -- general-position coupling exceeds the quintic closure, and the S6/A10 cells are exactly the negative side. *)

(* Ferrari quartic closure of OrigamiNum2: a real root of the resolvent cubic splits the depressed quartic as a difference of squares, reducing to quadratics. *)

Lemma ON2_two : OrigamiNum2 2.
Proof. replace 2 with (1 + 1) by ring. apply ON2_add; apply ON2_1. Qed.

Lemma ON2_four : OrigamiNum2 4.
Proof. replace 4 with (2 + 2) by ring. apply ON2_add; apply ON2_two. Qed.

Lemma ON2_depressed_quartic : forall p q r t,
  OrigamiNum2 p -> OrigamiNum2 q -> OrigamiNum2 r ->
  t ^ 4 + p * t ^ 2 + q * t + r = 0 ->
  OrigamiNum2 t.
Proof.
  intros p q r t Hp Hq Hr Hroot.
  destruct (general_cubic_root_exists 1 (- p) (- (4 * r)) (4 * p * r - q * q)
              ltac:(lra)) as [y Hy].
  assert (HyON : OrigamiNum2 y).
  { apply (ON2_general_cubic (- p) (- (4 * r)) (4 * p * r - q * q) y).
    - apply ON2_neg; exact Hp.
    - apply ON2_neg. apply ON2_mul; [exact ON2_four | exact Hr].
    - apply ON2_sub; [| apply ON2_mul; exact Hq].
      apply ON2_mul; [apply ON2_mul; [exact ON2_four | exact Hp] | exact Hr].
    - nra. }
  destruct (Req_dec (y - p) 0) as [Hyp0 | Hypne].
  - assert (Hq0 : q = 0) by nra.
    set (z := t * t).
    assert (HzON : OrigamiNum2 z).
    { apply (ON2_general_quadratic p r z); [exact Hp | exact Hr |].
      unfold z. nra. }
    assert (Hznn : 0 <= z) by (unfold z; nra).
    destruct (Rle_dec 0 t) as [Ht0 | Ht0].
    + replace t with (sqrt z)
        by (unfold z; rewrite sqrt_square by exact Ht0; reflexivity).
      apply ON2_sqrt; assumption.
    + replace t with (- sqrt z).
      * apply ON2_neg. apply ON2_sqrt; assumption.
      * unfold z. replace (t * t) with ((- t) * (- t)) by ring.
        rewrite sqrt_square by lra. ring.
  - set (c := q / (2 * (y - p))).
    assert (HcON : OrigamiNum2 c).
    { unfold c. apply ON2_div; [exact Hq | | lra].
      apply ON2_mul; [exact ON2_two |].
      apply ON2_sub; [exact HyON | exact Hp]. }
    assert (Hc2 : 2 * (y - p) * c = q) by (unfold c; field; lra).
    assert (Hkey : (y - p) * (c * c) = y * y / 4 - r).
    { apply (Rmult_eq_reg_l (4 * (y - p))); [| lra].
      transitivity (q * q); [| nra].
      transitivity ((2 * (y - p) * c) * (2 * (y - p) * c)); [ring |].
      rewrite Hc2. ring. }
    assert (Hident : (t * t + y / 2) ^ 2 = (y - p) * ((t - c) ^ 2)).
    { transitivity ((y - p) * (t * t) - q * t + (y * y / 4 - r)); [nra |].
      rewrite <- Hkey. nra. }
    destruct (Rtotal_order (y - p) 0) as [Hneg | [Hzero | Hpos]]; [| lra |].
    + pose proof (pow2_ge_0 (t - c)) as Hs1.
      pose proof (pow2_ge_0 (t * t + y / 2)) as Hs2.
      assert (Htc : (t - c) ^ 2 = 0) by nra.
      assert (Htc0 : t - c = 0) by (apply Rsqr_0_uniq; unfold Rsqr; nra).
      replace t with c by lra. exact HcON.
    + set (sq := sqrt (y - p)).
      assert (HsqON : OrigamiNum2 sq).
      { unfold sq. apply ON2_sqrt; [apply ON2_sub; [exact HyON | exact Hp] | lra]. }
      assert (Hsq2 : sq * sq = y - p) by (unfold sq; apply sqrt_sqrt; lra).
      assert (Hfac : (t * t + y / 2 - sq * (t - c)) * (t * t + y / 2 + sq * (t - c)) = 0).
      { transitivity ((t * t + y / 2) ^ 2 - (sq * sq) * ((t - c) ^ 2)); [ring |].
        rewrite Hsq2, Hident. ring. }
      assert (Hy2ON : OrigamiNum2 (y / 2))
        by (apply ON2_div; [exact HyON | exact ON2_two | lra]).
      destruct (Rmult_integral _ _ Hfac) as [Hf | Hf].
      * apply (ON2_general_quadratic (- sq) (y / 2 + sq * c) t).
        -- apply ON2_neg; exact HsqON.
        -- apply ON2_add; [exact Hy2ON | apply ON2_mul; [exact HsqON | exact HcON]].
        -- nra.
      * apply (ON2_general_quadratic sq (y / 2 - sq * c) t).
        -- exact HsqON.
        -- apply ON2_sub; [exact Hy2ON | apply ON2_mul; [exact HsqON | exact HcON]].
        -- nra.
Qed.

(** FERRARI QUARTIC CLOSURE: OrigamiNum2 contains every real root of a monic quartic with OrigamiNum2 coefficients. *)
Theorem ON2_general_quartic : forall a b c d t,
  OrigamiNum2 a -> OrigamiNum2 b -> OrigamiNum2 c -> OrigamiNum2 d ->
  t ^ 4 + a * t ^ 3 + b * t ^ 2 + c * t + d = 0 ->
  OrigamiNum2 t.
Proof.
  intros a b c d t Ha Hb Hc Hd Hroot.
  set (u := t + a / 4).
  set (P := b - 3 * (a * a) / 8).
  set (Q := c - a * b / 2 + (a * a * a) / 8).
  set (RR := d - a * c / 4 + (a * a) * b / 16 - 3 * (a * a * (a * a)) / 256).
  assert (HPON : OrigamiNum2 P).
  { unfold P. apply ON2_sub; [exact Hb |].
    apply ON2_div; [| | lra].
    - apply ON2_mul; [| apply ON2_mul; exact Ha].
      replace 3 with (2 + 1) by ring. apply ON2_add; [exact ON2_two | apply ON2_1].
    - replace 8 with (4 + 4) by ring. apply ON2_add; apply ON2_four. }
  assert (H8 : OrigamiNum2 8)
    by (replace 8 with (4 + 4) by ring; apply ON2_add; apply ON2_four).
  assert (H16 : OrigamiNum2 16)
    by (replace 16 with (8 + 8) by ring; apply ON2_add; exact H8).
  assert (HQON : OrigamiNum2 Q).
  { unfold Q. apply ON2_add.
    - apply ON2_sub; [exact Hc |].
      apply ON2_div; [apply ON2_mul; [exact Ha | exact Hb] | exact ON2_two | lra].
    - apply ON2_div; [| exact H8 | lra].
      apply ON2_mul; [apply ON2_mul; exact Ha | exact Ha]. }
  assert (HRON : OrigamiNum2 RR).
  { unfold RR. apply ON2_sub.
    - apply ON2_add.
      + apply ON2_sub; [exact Hd |].
        apply ON2_div; [apply ON2_mul; [exact Ha | exact Hc] | exact ON2_four | lra].
      + apply ON2_div; [| exact H16 | lra].
        apply ON2_mul; [apply ON2_mul; exact Ha | exact Hb].
    - apply ON2_div; [| | lra].
      + apply ON2_mul.
        * replace 3 with (2 + 1) by ring. apply ON2_add; [exact ON2_two | apply ON2_1].
        * apply ON2_mul; apply ON2_mul; exact Ha.
      + replace 256 with (16 * 16) by ring. apply ON2_mul; exact H16. }
  assert (Hdep : u ^ 4 + P * u ^ 2 + Q * u + RR = 0).
  { unfold u, P, Q, RR.
    transitivity (t ^ 4 + a * t ^ 3 + b * t ^ 2 + c * t + d); [field | exact Hroot]. }
  assert (HuON : OrigamiNum2 u) by (apply (ON2_depressed_quartic P Q RR u); assumption).
  replace t with (u - a / 4) by (unfold u; ring).
  apply ON2_sub; [exact HuON |].
  apply ON2_div; [exact Ha | exact ON2_four | lra].
Qed.

(* The translate-receiver mutual couplings: parallel mirrors make both transfers linear in the offsets -- a 2 x 2 linear solve, elimination degree 1. *)

Theorem mutual_translate_two_fold_ON2 :
  forall a1 b1 q1x q1y a2 b2 q2x q2y s w,
  OrigamiNum2 a1 -> OrigamiNum2 b1 -> OrigamiNum2 q1x -> OrigamiNum2 q1y ->
  OrigamiNum2 a2 -> OrigamiNum2 b2 -> OrigamiNum2 q2x -> OrigamiNum2 q2y ->
  a1 * a1 + b1 * b1 <> 0 -> a2 * a2 + b2 * b2 <> 0 ->
  on_line (reflect_point (q1x, q1y) {| A := a1; B := b1; C := s |})
          {| A := a2; B := b2; C := w |} ->
  on_line (reflect_point (q2x, q2y) {| A := a2; B := b2; C := w |})
          {| A := a1; B := b1; C := s |} ->
  4 * (a1 * a2 + b1 * b2) * (a1 * a2 + b1 * b2)
    - (a1 * a1 + b1 * b1) * (a2 * a2 + b2 * b2) <> 0 ->
  OrigamiNum2 s /\ OrigamiNum2 w.
Proof.
  intros a1 b1 q1x q1y a2 b2 q2x q2y s w
         Ha1 Hb1 Hq1x Hq1y Ha2 Hb2 Hq2x Hq2y HD1 HD2 Hon1 Hon2 Hdel.
  unfold on_line, reflect_point in Hon1, Hon2.
  cbn [fst snd A B C] in Hon1, Hon2.
  match type of Hon1 with
  | context [?num / ?den] =>
      set (v1 := num / den) in Hon1;
      assert (Hv1 : v1 * den = num) by (unfold v1; field; exact HD1)
  end.
  match type of Hon2 with
  | context [?num / ?den] =>
      set (v2 := num / den) in Hon2;
      assert (Hv2 : v2 * den = num) by (unfold v2; field; exact HD2)
  end.
  pose proof (f_equal (Rmult (a1 * a1 + b1 * b1)) Hon1) as Hon1c.
  pose proof (f_equal (Rmult (2 * (a1 * a2 + b1 * b2))) Hv1) as Hv1c.
  pose proof (f_equal (Rmult (a2 * a2 + b2 * b2)) Hon2) as Hon2c.
  pose proof (f_equal (Rmult (2 * (a1 * a2 + b1 * b2))) Hv2) as Hv2c.
  assert (HT1 : (a1 * a1 + b1 * b1) * w
                = 2 * (a1 * a2 + b1 * b2) * s
                  + (2 * (a1 * a2 + b1 * b2) * (a1 * q1x + b1 * q1y)
                     - (a1 * a1 + b1 * b1) * (a2 * q1x + b2 * q1y))) by nra.
  assert (HT2 : (a2 * a2 + b2 * b2) * s
                = 2 * (a1 * a2 + b1 * b2) * w
                  + (2 * (a1 * a2 + b1 * b2) * (a2 * q2x + b2 * q2y)
                     - (a2 * a2 + b2 * b2) * (a1 * q2x + b1 * q2y))) by nra.
  pose proof (f_equal (Rmult (a1 * a1 + b1 * b1)) HT2) as HT2c.
  pose proof (f_equal (Rmult (2 * (a1 * a2 + b1 * b2))) HT1) as HT1c.
  set (SE := 2 * (a1 * a2 + b1 * b2)
               * (2 * (a1 * a2 + b1 * b2) * (a1 * q1x + b1 * q1y)
                  - (a1 * a1 + b1 * b1) * (a2 * q1x + b2 * q1y))
             + (a1 * a1 + b1 * b1)
               * (2 * (a1 * a2 + b1 * b2) * (a2 * q2x + b2 * q2y)
                  - (a2 * a2 + b2 * b2) * (a1 * q2x + b1 * q2y))).
  set (DE := (a1 * a1 + b1 * b1) * (a2 * a2 + b2 * b2)
             - 4 * (a1 * a2 + b1 * b2) * (a1 * a2 + b1 * b2)).
  assert (HDE : DE <> 0) by (unfold DE; lra).
  assert (HsD : DE * s = SE) by (unfold DE, SE; nra).
  assert (Htwo : OrigamiNum2 2) by exact ON2_two.
  assert (HSEon : OrigamiNum2 SE).
  { unfold SE.
    repeat (apply ON2_sub || apply ON2_add || apply ON2_mul);
      (assumption || exact ON2_1). }
  assert (HDEon : OrigamiNum2 DE).
  { unfold DE.
    repeat (apply ON2_sub || apply ON2_add || apply ON2_mul);
      (assumption || exact ON2_1). }
  assert (HsON : OrigamiNum2 s).
  { replace s with (SE / DE)
      by (apply (Rmult_eq_reg_l DE); [rewrite <- HsD; field; exact HDE | exact HDE]).
    apply ON2_div; assumption. }
  split; [exact HsON |].
  assert (HwE : w = (2 * (a1 * a2 + b1 * b2) * s
                     + (2 * (a1 * a2 + b1 * b2) * (a1 * q1x + b1 * q1y)
                        - (a1 * a1 + b1 * b1) * (a2 * q1x + b2 * q1y)))
                    / (a1 * a1 + b1 * b1)).
  { apply (Rmult_eq_reg_l (a1 * a1 + b1 * b1)); [| exact HD1].
    rewrite HT1. field. exact HD1. }
  rewrite HwE.
  apply ON2_div; [| | exact HD1].
  - repeat (apply ON2_sub || apply ON2_add || apply ON2_mul);
      (assumption || exact ON2_1).
  - repeat (apply ON2_sub || apply ON2_add || apply ON2_mul);
      (assumption || exact ON2_1).
Qed.

(* The pencil x translate mutual coupling: the transfer onto the translate crease is linear in the offset, so elimination substitutes to the cubic ptG -- single-fold strength. *)

Definition ptU (a2 b2 : R) : list R := (2 * b2) :: (- (2 * a2)) :: nil.

Definition ptV (p1x p1y q2x q2y a2 b2 : R) : list R :=
  (2 * b2 * (a2 * q2x + b2 * q2y) - (a2 * a2 + b2 * b2) * q2y
     + (a2 * a2 + b2 * b2) * p1y)
  :: ((a2 * a2 + b2 * b2) * q2x - 2 * a2 * (a2 * q2x + b2 * q2y)
     - (a2 * a2 + b2 * b2) * p1x) :: nil.

Definition ptWN (p1x p1y q1x q1y a2 b2 : R) : list R :=
  pscaleR (-1) (paddR (pscaleR a2 (mpD p1x p1y q1x q1y 0))
                      (pscaleR b2 (mpN p1x p1y q1x q1y 0))).

(** The degree-3 elimination polynomial of the pencil x translate system. *)
Definition ptG (p1x p1y q1x q1y a2 b2 q2x q2y : R) : list R :=
  paddR (pmulR (ptU a2 b2) (ptWN p1x p1y q1x q1y a2 b2))
        (pmulR (ptV p1x p1y q2x q2y a2 b2) (1 :: 0 :: 1 :: nil)).

Theorem pencil_translate_two_fold_ON2 :
  forall p1x p1y q1x q1y a2 b2 q2x q2y s w,
  OrigamiNum2 p1x -> OrigamiNum2 p1y -> OrigamiNum2 q1x -> OrigamiNum2 q1y ->
  OrigamiNum2 a2 -> OrigamiNum2 b2 -> OrigamiNum2 q2x -> OrigamiNum2 q2y ->
  a2 * a2 + b2 * b2 <> 0 ->
  on_line (reflect_point (q1x, q1y) (pencil p1x p1y s))
          {| A := a2; B := b2; C := w |} ->
  on_line (reflect_point (q2x, q2y) {| A := a2; B := b2; C := w |})
          (pencil p1x p1y s) ->
  nth 3 (ptG p1x p1y q1x q1y a2 b2 q2x q2y) 0 <> 0 ->
  OrigamiNum2 s /\ OrigamiNum2 w.
Proof.
  intros p1x p1y q1x q1y a2 b2 q2x q2y s w
         HP1x HP1y HQ1x HQ1y Ha2 Hb2 HQ2x HQ2y HD2 Hon1 Hon2 Hlead.
  unfold on_line, reflect_point, pencil in Hon1, Hon2.
  cbn [fst snd A B C] in Hon1, Hon2.
  assert (Hden1 : s * s + -1 * -1 <> 0)
    by (assert (Hsq : 0 <= s * s) by apply Rle_0_sqr; lra).
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
      assert (Hv2 : v2 * den = num) by (unfold v2; field; exact HD2)
  end.
  pose proof (f_equal (Rmult (s * s)) Hon1) as C1.
  pose proof (f_equal (Rmult (2 * a2 * s)) Hv1) as C2.
  pose proof (f_equal (Rmult (2 * b2)) Hv1) as C3.
  pose proof (f_equal (Rmult (a2 * a2 + b2 * b2)) Hon2) as C4.
  pose proof (f_equal (Rmult (2 * a2 * s)) Hv2) as C5.
  pose proof (f_equal (Rmult (2 * b2)) Hv2) as C6.
  assert (HT1 : w * (s * s + -1 * -1)
              = pevalR (ptWN p1x p1y q1x q1y a2 b2) s).
  { unfold ptWN. rewrite pevalR_pscale, pevalR_padd, !pevalR_pscale.
    cbn [pevalR mpD mpN]. nra. }
  assert (HT2 : pevalR (ptU a2 b2) s * w
                + pevalR (ptV p1x p1y q2x q2y a2 b2) s = 0).
  { cbn [pevalR ptU ptV]. nra. }
  assert (Hroot : pevalR (ptG p1x p1y q1x q1y a2 b2 q2x q2y) s = 0).
  { unfold ptG. rewrite pevalR_padd, !pevalR_pmul.
    rewrite <- HT1.
    pose proof (f_equal (Rmult (s * s)) HT2) as C7.
    cbn [pevalR]. nra. }
  set (G := ptG p1x p1y q1x q1y a2 b2 q2x q2y) in *.
  assert (HGON2 : Forall OrigamiNum2 G).
  { unfold G, ptG.
    assert (HUon : Forall OrigamiNum2 (ptU a2 b2)).
    { unfold ptU. repeat constructor;
        repeat (apply ON2_neg || apply ON2_sub || apply ON2_add || apply ON2_mul);
        (assumption || exact ON2_1). }
    assert (HVon : Forall OrigamiNum2 (ptV p1x p1y q2x q2y a2 b2)).
    { unfold ptV. repeat constructor;
        repeat (apply ON2_neg || apply ON2_sub || apply ON2_add || apply ON2_mul);
        (assumption || exact ON2_1). }
    assert (HWNon : Forall OrigamiNum2 (ptWN p1x p1y q1x q1y a2 b2)).
    { unfold ptWN.
      apply Forall_pscaleR; [exact ON2_mul | apply ON2_neg, ON2_1 |].
      apply Forall_paddR; [exact ON2_add | |].
      - apply Forall_pscaleR; [exact ON2_mul | exact Ha2 |].
        apply mpD_ON2; (assumption || exact ON2_0).
      - apply Forall_pscaleR; [exact ON2_mul | exact Hb2 |].
        apply mpN_ON2; (assumption || exact ON2_0). }
    apply Forall_paddR; [exact ON2_add | |].
    - apply Forall_pmulR;
        [exact ON2_add | exact ON2_mul | apply ON2_0 | exact HUon | exact HWNon].
    - apply Forall_pmulR;
        [exact ON2_add | exact ON2_mul | apply ON2_0 | exact HVon |].
      repeat constructor; (exact ON2_1 || exact ON2_0). }
  assert (HlenG : length G = 4%nat) by reflexivity.
  rewrite pevalR_nth_sum, HlenG in Hroot.
  cbn [fsum] in Hroot.
  set (c0 := nth 0 G 0) in *. set (c1 := nth 1 G 0) in *.
  set (c2 := nth 2 G 0) in *. set (c3 := nth 3 G 0) in *.
  assert (Hc0 : OrigamiNum2 c0) by (unfold c0; apply nth_Forall_ON2; exact HGON2).
  assert (Hc1 : OrigamiNum2 c1) by (unfold c1; apply nth_Forall_ON2; exact HGON2).
  assert (Hc2 : OrigamiNum2 c2) by (unfold c2; apply nth_Forall_ON2; exact HGON2).
  assert (Hc3 : OrigamiNum2 c3) by (unfold c3; apply nth_Forall_ON2; exact HGON2).
  assert (HsON : OrigamiNum2 s).
  { apply (ON2_general_cubic (c2 / c3) (c1 / c3) (c0 / c3) s).
    - apply ON2_div; assumption.
    - apply ON2_div; assumption.
    - apply ON2_div; assumption.
    - apply (Rmult_eq_reg_l c3); [| exact Hlead].
      rewrite Rmult_0_r.
      transitivity (c0 * s ^ 0 + c1 * s ^ 1 + c2 * s ^ 2 + c3 * s ^ 3).
      + field. exact Hlead.
      + lra. }
  split; [exact HsON |].
  assert (HwE : w = pevalR (ptWN p1x p1y q1x q1y a2 b2) s / (s * s + -1 * -1)).
  { apply (Rmult_eq_reg_r (s * s + -1 * -1)); [| exact Hden1].
    rewrite HT1. field.
    assert (Hsq : 0 <= s * s) by apply Rle_0_sqr. lra. }
  rewrite HwE. apply ON2_div; [| | exact Hden1].
  - apply pevalR_ON2; [| exact HsON].
    unfold ptWN.
    apply Forall_pscaleR; [exact ON2_mul | apply ON2_neg, ON2_1 |].
    apply Forall_paddR; [exact ON2_add | |].
    + apply Forall_pscaleR; [exact ON2_mul | exact Ha2 |].
      apply mpD_ON2; (assumption || exact ON2_0).
    + apply Forall_pscaleR; [exact ON2_mul | exact Hb2 |].
      apply mpN_ON2; (assumption || exact ON2_0).
  - repeat (apply ON2_neg || apply ON2_add || apply ON2_mul);
      (assumption || exact ON2_1).
Qed.

(* The translate x tangent mutual coupling: the transfer onto the translate crease is linear in its offset, so elimination substitutes to the quartic ttG, closed by Ferrari. *)

Definition tangent_line (p2x p2y x02 y02 la lb w : R) : Line :=
  {| A := 2 * (x02 + lb * w - p2x);
     B := 2 * (y02 - la * w - p2y);
     C := p2x * p2x + p2y * p2y - (x02 + lb * w) * (x02 + lb * w)
          - (y02 - la * w) * (y02 - la * w) |}.

Definition ttA2 (p2x x02 lb : R) : list R :=
  (2 * (x02 - p2x)) :: (2 * lb) :: nil.
Definition ttB2 (p2y y02 la : R) : list R :=
  (2 * (y02 - p2y)) :: (- (2 * la)) :: nil.
Definition ttC2 (p2x p2y x02 y02 la lb : R) : list R :=
  (p2x * p2x + p2y * p2y - x02 * x02 - y02 * y02)
  :: (2 * (y02 * la - x02 * lb)) :: (- (la * la + lb * lb)) :: nil.

Definition ttD2 (p2x p2y x02 y02 la lb : R) : list R :=
  paddR (pmulR (ttA2 p2x x02 lb) (ttA2 p2x x02 lb))
        (pmulR (ttB2 p2y y02 la) (ttB2 p2y y02 la)).

Definition ttF2 (p2x p2y x02 y02 la lb q2x q2y : R) : list R :=
  paddR (pscaleR q2x (ttA2 p2x x02 lb))
        (paddR (pscaleR q2y (ttB2 p2y y02 la)) (ttC2 p2x p2y x02 y02 la lb)).

Definition ttN (a1 b1 p2x p2y x02 y02 la lb q2x q2y : R) : list R :=
  paddR (pscaleR (- (a1 * q2x + b1 * q2y)) (ttD2 p2x p2y x02 y02 la lb))
        (pscaleR 2 (paddR
           (pmulR (pscaleR a1 (ttA2 p2x x02 lb))
                  (ttF2 p2x p2y x02 y02 la lb q2x q2y))
           (pmulR (pscaleR b1 (ttB2 p2y y02 la))
                  (ttF2 p2x p2y x02 y02 la lb q2x q2y)))).

Definition ttAl (a1 b1 q1x q1y p2x p2y x02 y02 la lb : R) : list R :=
  paddR (pscaleR ((a1 * a1 + b1 * b1) * q1x - 2 * a1 * (a1 * q1x + b1 * q1y))
                 (ttA2 p2x x02 lb))
        (paddR (pscaleR ((a1 * a1 + b1 * b1) * q1y - 2 * b1 * (a1 * q1x + b1 * q1y))
                        (ttB2 p2y y02 la))
               (pscaleR (a1 * a1 + b1 * b1) (ttC2 p2x p2y x02 y02 la lb))).

Definition ttBe (a1 b1 p2x p2y x02 y02 la lb : R) : list R :=
  pscaleR (- 2) (paddR (pscaleR a1 (ttA2 p2x x02 lb))
                       (pscaleR b1 (ttB2 p2y y02 la))).

(** The degree-4 elimination polynomial of the translate x tangent system. *)
Definition ttG (a1 b1 q1x q1y p2x p2y x02 y02 la lb q2x q2y : R) : list R :=
  paddR (pmulR (ttAl a1 b1 q1x q1y p2x p2y x02 y02 la lb)
               (ttD2 p2x p2y x02 y02 la lb))
        (pmulR (ttBe a1 b1 p2x p2y x02 y02 la lb)
               (ttN a1 b1 p2x p2y x02 y02 la lb q2x q2y)).

Theorem translate_tangent_two_fold_ON2 :
  forall a1 b1 q1x q1y p2x p2y x02 y02 la lb q2x q2y s w,
  OrigamiNum2 a1 -> OrigamiNum2 b1 -> OrigamiNum2 q1x -> OrigamiNum2 q1y ->
  OrigamiNum2 p2x -> OrigamiNum2 p2y -> OrigamiNum2 x02 -> OrigamiNum2 y02 ->
  OrigamiNum2 la -> OrigamiNum2 lb -> OrigamiNum2 q2x -> OrigamiNum2 q2y ->
  a1 * a1 + b1 * b1 <> 0 ->
  A (tangent_line p2x p2y x02 y02 la lb w) * A (tangent_line p2x p2y x02 y02 la lb w)
    + B (tangent_line p2x p2y x02 y02 la lb w) * B (tangent_line p2x p2y x02 y02 la lb w)
    <> 0 ->
  on_line (reflect_point (q1x, q1y) {| A := a1; B := b1; C := s |})
          (tangent_line p2x p2y x02 y02 la lb w) ->
  on_line (reflect_point (q2x, q2y) (tangent_line p2x p2y x02 y02 la lb w))
          {| A := a1; B := b1; C := s |} ->
  nth 4 (ttG a1 b1 q1x q1y p2x p2y x02 y02 la lb q2x q2y) 0 <> 0 ->
  OrigamiNum2 w /\ OrigamiNum2 s.
Proof.
  intros a1 b1 q1x q1y p2x p2y x02 y02 la lb q2x q2y s w
         Ha1 Hb1 HQ1x HQ1y HP2x HP2y HX0 HY0 Hla Hlb HQ2x HQ2y HD1 HDT
         Hon1 Hon2 Hlead.
  assert (HDeq : pevalR (ttD2 p2x p2y x02 y02 la lb) w
                 = A (tangent_line p2x p2y x02 y02 la lb w)
                   * A (tangent_line p2x p2y x02 y02 la lb w)
                   + B (tangent_line p2x p2y x02 y02 la lb w)
                     * B (tangent_line p2x p2y x02 y02 la lb w)).
  { unfold ttD2, ttA2, ttB2. cbn [A B tangent_line].
    rewrite pevalR_padd, !pevalR_pmul. cbn [pevalR]. ring. }
  assert (HD2e : pevalR (ttD2 p2x p2y x02 y02 la lb) w <> 0)
    by (rewrite HDeq; exact HDT).
  unfold on_line, reflect_point, tangent_line in Hon1, Hon2.
  cbn [fst snd A B C] in Hon1, Hon2.
  match type of Hon1 with
  | context [?num / ?den] =>
      set (v1 := num / den) in Hon1;
      assert (Hv1 : v1 * den = num)
        by (unfold v1, Rdiv; rewrite Rmult_assoc, (Rinv_l _ HD1), Rmult_1_r;
            reflexivity)
  end.
  match type of Hon2 with
  | context [?num / ?den] =>
      set (v2 := num / den) in Hon2;
      assert (Hden2 : den <> 0)
        by (intro E; apply HDT; cbn [A B tangent_line]; exact E);
      assert (Hv2 : v2 * den = num)
        by (unfold v2, Rdiv; rewrite Rmult_assoc, (Rinv_l _ Hden2), Rmult_1_r;
            reflexivity)
  end.
  pose proof (f_equal (Rmult (a1 * a1 + b1 * b1)) Hon1) as C1.
  pose proof (f_equal (Rmult (2 * a1 * A (tangent_line p2x p2y x02 y02 la lb w)
                              + 2 * b1 * B (tangent_line p2x p2y x02 y02 la lb w)))
                Hv1) as C2.
  cbn [A B tangent_line] in C2.
  pose proof (f_equal (Rmult (A (tangent_line p2x p2y x02 y02 la lb w)
                              * A (tangent_line p2x p2y x02 y02 la lb w)
                              + B (tangent_line p2x p2y x02 y02 la lb w)
                                * B (tangent_line p2x p2y x02 y02 la lb w)))
                Hon2) as C4.
  cbn [A B tangent_line] in C4.
  pose proof (f_equal (Rmult (2 * a1 * A (tangent_line p2x p2y x02 y02 la lb w)
                              + 2 * b1 * B (tangent_line p2x p2y x02 y02 la lb w)))
                Hv2) as C5.
  cbn [A B tangent_line] in C5.
  assert (HT1 : pevalR (ttAl a1 b1 q1x q1y p2x p2y x02 y02 la lb) w
                + pevalR (ttBe a1 b1 p2x p2y x02 y02 la lb) w * s = 0).
  { unfold ttAl, ttBe, ttA2, ttB2, ttC2.
    repeat first [rewrite pevalR_padd | rewrite pevalR_pmul | rewrite pevalR_pscale].
    cbn [pevalR].
    clear C4 C5 Hon2 Hv2 Hden2 HD2e HDeq HDT Hlead Hon1 Hv1. nra. }
  assert (HT2 : s * pevalR (ttD2 p2x p2y x02 y02 la lb) w
                = pevalR (ttN a1 b1 p2x p2y x02 y02 la lb q2x q2y) w).
  { unfold ttN, ttD2, ttF2, ttA2, ttB2, ttC2.
    repeat first [rewrite pevalR_padd | rewrite pevalR_pmul | rewrite pevalR_pscale].
    cbn [pevalR].
    clear C1 C2 Hon1 Hv1 HT1 HD2e HDeq HDT Hlead Hon2 Hv2 Hden2. nra. }
  assert (Hroot : pevalR (ttG a1 b1 q1x q1y p2x p2y x02 y02 la lb q2x q2y) w = 0).
  { unfold ttG. rewrite pevalR_padd, !pevalR_pmul.
    pose proof (f_equal (Rmult (pevalR (ttD2 p2x p2y x02 y02 la lb) w)) HT1) as C7.
    pose proof (f_equal (Rmult (pevalR (ttBe a1 b1 p2x p2y x02 y02 la lb) w)) HT2) as C8.
    clear C1 C2 C4 C5 Hon1 Hon2 Hv1 Hv2 Hden2 HD2e HDeq HDT Hlead HT1 HT2. nra. }
  set (G := ttG a1 b1 q1x q1y p2x p2y x02 y02 la lb q2x q2y) in *.
  assert (Htt2on : Forall OrigamiNum2 (ttA2 p2x x02 lb)).
  { unfold ttA2. repeat constructor;
      repeat (apply ON2_neg || apply ON2_sub || apply ON2_add || apply ON2_mul);
      (assumption || exact ON2_1). }
  assert (HttB2on : Forall OrigamiNum2 (ttB2 p2y y02 la)).
  { unfold ttB2. repeat constructor;
      repeat (apply ON2_neg || apply ON2_sub || apply ON2_add || apply ON2_mul);
      (assumption || exact ON2_1). }
  assert (HttC2on : Forall OrigamiNum2 (ttC2 p2x p2y x02 y02 la lb)).
  { unfold ttC2. repeat constructor;
      repeat (apply ON2_neg || apply ON2_sub || apply ON2_add || apply ON2_mul);
      (assumption || exact ON2_1). }
  assert (HttD2on : Forall OrigamiNum2 (ttD2 p2x p2y x02 y02 la lb)).
  { unfold ttD2. apply Forall_paddR; [exact ON2_add | |];
      apply Forall_pmulR;
      (exact ON2_add || exact ON2_mul || apply ON2_0 || assumption). }
  assert (HttF2on : Forall OrigamiNum2 (ttF2 p2x p2y x02 y02 la lb q2x q2y)).
  { unfold ttF2.
    apply Forall_paddR; [exact ON2_add | |].
    - apply Forall_pscaleR; [exact ON2_mul | exact HQ2x | exact Htt2on].
    - apply Forall_paddR; [exact ON2_add | |].
      + apply Forall_pscaleR; [exact ON2_mul | exact HQ2y | exact HttB2on].
      + exact HttC2on. }
  assert (HttNon : Forall OrigamiNum2 (ttN a1 b1 p2x p2y x02 y02 la lb q2x q2y)).
  { unfold ttN.
    apply Forall_paddR; [exact ON2_add | |].
    - apply Forall_pscaleR; [exact ON2_mul | | exact HttD2on].
      apply ON2_neg.
      repeat (apply ON2_add || apply ON2_mul); assumption.
    - apply Forall_pscaleR; [exact ON2_mul | exact ON2_two |].
      apply Forall_paddR; [exact ON2_add | |].
      + apply Forall_pmulR;
          [exact ON2_add | exact ON2_mul | apply ON2_0 | | exact HttF2on].
        apply Forall_pscaleR; [exact ON2_mul | exact Ha1 | exact Htt2on].
      + apply Forall_pmulR;
          [exact ON2_add | exact ON2_mul | apply ON2_0 | | exact HttF2on].
        apply Forall_pscaleR; [exact ON2_mul | exact Hb1 | exact HttB2on]. }
  assert (HGON2 : Forall OrigamiNum2 G).
  { unfold G, ttG.
    apply Forall_paddR; [exact ON2_add | |].
    - apply Forall_pmulR;
        [exact ON2_add | exact ON2_mul | apply ON2_0 | | exact HttD2on].
      unfold ttAl.
      apply Forall_paddR; [exact ON2_add | |].
      + apply Forall_pscaleR; [exact ON2_mul | | exact Htt2on].
        repeat (apply ON2_sub || apply ON2_add || apply ON2_mul);
          (assumption || exact ON2_1).
      + apply Forall_paddR; [exact ON2_add | |].
        * apply Forall_pscaleR; [exact ON2_mul | | exact HttB2on].
          repeat (apply ON2_sub || apply ON2_add || apply ON2_mul);
            (assumption || exact ON2_1).
        * apply Forall_pscaleR; [exact ON2_mul | | exact HttC2on].
          repeat (apply ON2_add || apply ON2_mul); assumption.
    - apply Forall_pmulR;
        [exact ON2_add | exact ON2_mul | apply ON2_0 | | exact HttNon].
      unfold ttBe.
      apply Forall_pscaleR; [exact ON2_mul | apply ON2_neg; exact ON2_two |].
      apply Forall_paddR; [exact ON2_add | |].
      + apply Forall_pscaleR; [exact ON2_mul | exact Ha1 | exact Htt2on].
      + apply Forall_pscaleR; [exact ON2_mul | exact Hb1 | exact HttB2on]. }
  assert (HlenG : length G = 5%nat) by reflexivity.
  rewrite pevalR_nth_sum, HlenG in Hroot.
  cbn [fsum] in Hroot.
  set (c0 := nth 0 G 0) in *. set (c1 := nth 1 G 0) in *.
  set (c2 := nth 2 G 0) in *. set (c3 := nth 3 G 0) in *.
  set (c4 := nth 4 G 0) in *.
  assert (Hc0 : OrigamiNum2 c0) by (unfold c0; apply nth_Forall_ON2; exact HGON2).
  assert (Hc1 : OrigamiNum2 c1) by (unfold c1; apply nth_Forall_ON2; exact HGON2).
  assert (Hc2 : OrigamiNum2 c2) by (unfold c2; apply nth_Forall_ON2; exact HGON2).
  assert (Hc3 : OrigamiNum2 c3) by (unfold c3; apply nth_Forall_ON2; exact HGON2).
  assert (Hc4 : OrigamiNum2 c4) by (unfold c4; apply nth_Forall_ON2; exact HGON2).
  assert (HwON : OrigamiNum2 w).
  { apply (ON2_general_quartic (c3 / c4) (c2 / c4) (c1 / c4) (c0 / c4) w).
    - apply ON2_div; assumption.
    - apply ON2_div; assumption.
    - apply ON2_div; assumption.
    - apply ON2_div; assumption.
    - apply (Rmult_eq_reg_l c4); [| exact Hlead].
      rewrite Rmult_0_r.
      transitivity (c0 * w ^ 0 + c1 * w ^ 1 + c2 * w ^ 2 + c3 * w ^ 3 + c4 * w ^ 4).
      + field. exact Hlead.
      + lra. }
  split; [exact HwON |].
  assert (HsE : s = pevalR (ttN a1 b1 p2x p2y x02 y02 la lb q2x q2y) w
                    / pevalR (ttD2 p2x p2y x02 y02 la lb) w).
  { apply (Rmult_eq_reg_r (pevalR (ttD2 p2x p2y x02 y02 la lb) w)); [| exact HD2e].
    transitivity (pevalR (ttN a1 b1 p2x p2y x02 y02 la lb q2x q2y) w);
      [exact HT2 | field; exact HD2e]. }
  rewrite HsE. apply ON2_div; [| | exact HD2e].
  - apply pevalR_ON2; [exact HttNon | exact HwON].
  - apply pevalR_ON2; [exact HttD2on | exact HwON].
Qed.


(* The subfield-parametric polynomial core: normalization, monic division, extended Euclid, and minimal-polynomial divisibility over an abstract decidable field; the real and complex layers are its two instances. *)

Section FieldPolyCore.

Variables (FC : Type) (fO fI : FC).
Variables (fadd fmul fsub : FC -> FC -> FC) (fopp : FC -> FC).
Variables (fdiv : FC -> FC -> FC) (finv : FC -> FC).
Hypothesis Fth : field_theory fO fI fadd fmul fsub fopp fdiv finv (@eq FC).
Hypothesis feq_dec : forall x y : FC, {x = y} + {x <> y}.

Add Field FPCfield : Fth.

Let kI_neq_kO : fI <> fO := F_1_neq_0 Fth.

(* the constant-first polynomial layer *)

Fixpoint kpeval (p : list FC) (z : FC) : FC :=
  match p with
  | nil => fO
  | c :: p' => fadd c (fmul z (kpeval p' z))
  end.

Fixpoint kpadd (p q : list FC) : list FC :=
  match p, q with
  | nil, _ => q
  | _, nil => p
  | a :: p', b :: q' => fadd a b :: kpadd p' q'
  end.

Definition kpscale (a : FC) (p : list FC) : list FC := map (fmul a) p.

Fixpoint kpmul (p q : list FC) : list FC :=
  match p with
  | nil => nil
  | a :: p' => kpadd (kpscale a q) (fO :: kpmul p' q)
  end.

Fixpoint kpow (z : FC) (n : nat) : FC :=
  match n with O => fI | S n' => fmul z (kpow z n') end.

Lemma kpeval_kpadd : forall p q z,
  kpeval (kpadd p q) z = fadd (kpeval p z) (kpeval q z).
Proof.
  induction p as [|a p IH]; intros q z; cbn [kpadd kpeval].
  - ring.
  - destruct q as [|b q]; cbn [kpeval]; [ring | rewrite IH; ring].
Qed.

Lemma kpeval_kpscale : forall a p z,
  kpeval (kpscale a p) z = fmul a (kpeval p z).
Proof.
  induction p as [|c p IH]; intro z; cbn [kpscale map kpeval].
  - ring.
  - rewrite IH. ring.
Qed.

Lemma kpeval_kpmul : forall p q z,
  kpeval (kpmul p q) z = fmul (kpeval p z) (kpeval q z).
Proof.
  induction p as [|a p IH]; intros q z; cbn [kpmul kpeval].
  - ring.
  - rewrite kpeval_kpadd, kpeval_kpscale. cbn [kpeval]. rewrite IH. ring.
Qed.

(* the leading-first layer *)

Fixpoint kpeval_lf (p : list FC) (z : FC) : FC :=
  match p with
  | nil => fO
  | a :: p' => fadd (fmul a (kpow z (length p'))) (kpeval_lf p' z)
  end.

Lemma kpeval_lf_rev : forall p z, kpeval_lf p z = kpeval (rev p) z.
Proof.
  induction p as [|a p IH]; intro z.
  - reflexivity.
  - cbn [kpeval_lf rev].
    assert (Happ : forall l1 l2 w, kpeval (l1 ++ l2) w
                   = fadd (kpeval l1 w) (fmul (kpow w (length l1)) (kpeval l2 w))).
    { induction l1 as [|x l1 IHl]; intros l2 w; cbn [app kpeval length kpow].
      - ring.
      - rewrite IHl. ring. }
    rewrite Happ, IH, length_rev. cbn [kpeval]. ring.
Qed.

Lemma kpadd_length : forall p q, length (kpadd p q) = Nat.max (length p) (length q).
Proof.
  induction p as [|a p IH]; intros q; cbn [kpadd length].
  - lia.
  - destruct q as [|b q]; cbn [length]; [lia | rewrite IH; lia].
Qed.

Lemma kpscale_length : forall a p, length (kpscale a p) = length p.
Proof. intros. unfold kpscale. apply length_map. Qed.

Lemma kpscale_cons : forall a c p, kpscale a (c :: p) = fmul a c :: kpscale a p.
Proof. reflexivity. Qed.

Lemma kpow_add : forall z a b, kpow z (a + b) = fmul (kpow z a) (kpow z b).
Proof.
  intros z a b. induction a as [|a IH]; cbn [kpow Nat.add].
  - ring.
  - rewrite IH. ring.
Qed.

(* division by a monic divisor, leading-first *)

Fixpoint kpdiv_lf (fuel : nat) (p dtail : list FC) : list FC * list FC :=
  match fuel with
  | O => (nil, p)
  | S f =>
      if Nat.leb (length p) (length dtail) then (nil, p)
      else match p with
           | nil => (nil, nil)
           | a :: p' =>
               let p'' := kpadd p' (kpscale (fopp fI) (kpscale a dtail)) in
               (a :: fst (kpdiv_lf f p'' dtail), snd (kpdiv_lf f p'' dtail))
           end
  end.

Lemma kpdiv_lf_rlen : forall fuel p dtail, (length p <= fuel)%nat ->
  (length (snd (kpdiv_lf fuel p dtail)) <= length dtail)%nat.
Proof.
  induction fuel as [|f IH]; intros p dtail Hfuel.
  - cbn [kpdiv_lf snd]. assert (length p = 0)%nat by lia. lia.
  - cbn [kpdiv_lf].
    destruct (Nat.leb_spec (length p) (length dtail)) as [Hle | Hgt].
    + cbn [snd]. exact Hle.
    + destruct p as [|a p']; [cbn [length] in Hgt; lia |].
      cbn [snd].
      apply IH.
      rewrite kpadd_length, !kpscale_length.
      cbn [length] in Hfuel, Hgt |- *. lia.
Qed.

Lemma kpeval_lf_psub_top : forall q p z, (length q <= length p)%nat ->
  kpeval_lf (kpadd p (kpscale (fopp fI) q)) z
  = fsub (kpeval_lf p z) (fmul (kpeval_lf q z) (kpow z (length p - length q))).
Proof.
  induction q as [|b q' IH]; intros p z Hle.
  - destruct p; cbn [kpscale map kpadd kpeval_lf]; ring.
  - destruct p as [|a p']; [cbn [length] in Hle; lia |].
    cbn [length] in Hle.
    rewrite kpscale_cons. cbn [kpadd kpeval_lf].
    rewrite IH by lia.
    assert (Hlen : length (kpadd p' (kpscale (fopp fI) q')) = length p').
    { rewrite kpadd_length, kpscale_length. lia. }
    rewrite Hlen.
    cbn [length].
    replace (S (length p') - S (length q'))%nat
      with (length p' - length q')%nat by lia.
    assert (Hpow : kpow z (length p')
                   = fmul (kpow z (length p' - length q')) (kpow z (length q'))).
    { replace (length p') with ((length p' - length q') + length q')%nat at 1 by lia.
      apply kpow_add. }
    rewrite Hpow.
    generalize (kpow z (length p' - length q')). intro T.
    generalize (kpow z (length q')). intro U.
    ring.
Qed.

Lemma kpdiv_lf_qlen : forall fuel p dtail, (length p <= fuel)%nat ->
  length (fst (kpdiv_lf fuel p dtail)) = (length p - length dtail)%nat.
Proof.
  induction fuel as [|f IH]; intros p dtail Hfuel.
  - cbn [kpdiv_lf fst]. cbn [length]. lia.
  - cbn [kpdiv_lf].
    destruct (Nat.leb_spec (length p) (length dtail)) as [Hle | Hgt].
    + cbn [fst length]. lia.
    + destruct p as [|a p']; [cbn [length] in Hgt; lia |].
      cbn [fst length].
      rewrite IH.
      * rewrite kpadd_length, !kpscale_length. cbn [length] in Hgt |- *. lia.
      * rewrite kpadd_length, !kpscale_length.
        cbn [length] in Hfuel, Hgt |- *. lia.
Qed.

Lemma kpdiv_lf_eval : forall fuel p dtail, (length p <= fuel)%nat ->
  forall z,
  kpeval_lf p z
  = fadd (fmul (kpeval_lf (fst (kpdiv_lf fuel p dtail)) z)
               (fadd (kpow z (length dtail)) (kpeval_lf dtail z)))
         (kpeval_lf (snd (kpdiv_lf fuel p dtail)) z).
Proof.
  induction fuel as [|f IH]; intros p dtail Hfuel z.
  - assert (Hp : length p = 0%nat) by lia.
    destruct p; [| cbn [length] in Hp; lia].
    cbn [kpdiv_lf fst snd kpeval_lf]. ring.
  - cbn [kpdiv_lf].
    destruct (Nat.leb_spec (length p) (length dtail)) as [Hle | Hgt].
    + cbn [fst snd kpeval_lf]. ring.
    + destruct p as [|a p']; [cbn [length] in Hgt; lia |].
      cbn [fst snd kpeval_lf].
      set (p'' := kpadd p' (kpscale (fopp fI) (kpscale a dtail))) in *.
      assert (Hlp'' : length p'' = length p').
      { unfold p''. rewrite kpadd_length, !kpscale_length.
        cbn [length] in Hgt. lia. }
      assert (Hfp'' : (length p'' <= f)%nat)
        by (rewrite Hlp''; cbn [length] in Hfuel; lia).
      rewrite (kpdiv_lf_qlen f p'' dtail Hfp''), Hlp''.
      assert (Hsub : kpeval_lf p'' z
                     = fsub (kpeval_lf p' z)
                            (fmul (fmul a (kpeval_lf dtail z))
                                  (kpow z (length p' - length dtail)))).
      { unfold p''.
        rewrite (kpeval_lf_psub_top (kpscale a dtail) p' z)
          by (rewrite kpscale_length; cbn [length] in Hgt; lia).
        rewrite kpscale_length.
        assert (Hsc : kpeval_lf (kpscale a dtail) z = fmul a (kpeval_lf dtail z)).
        { rewrite !kpeval_lf_rev.
          unfold kpscale. rewrite <- map_rev. fold (kpscale a (rev dtail)).
          apply kpeval_kpscale. }
        rewrite Hsc. ring. }
      pose proof (IH p'' dtail Hfp'' z) as Hrec.
      rewrite Hsub in Hrec.
      cbn [length] in Hgt.
      assert (Hpow : kpow z (length p')
                     = fmul (kpow z (length p' - length dtail))
                            (kpow z (length dtail))).
      { replace (length p')
          with ((length p' - length dtail) + length dtail)%nat at 1 by lia.
        apply kpow_add. }
      rewrite Hpow.
      set (T := kpow z (length p' - length dtail)) in *.
      set (K := kpow z (length dtail)) in *.
      set (D := kpeval_lf dtail z) in *.
      set (QV := kpeval_lf (fst (kpdiv_lf f p'' dtail)) z) in *.
      set (RV := kpeval_lf (snd (kpdiv_lf f p'' dtail)) z) in *.
      assert (Hgoal : fsub (kpeval_lf p' z) (fmul (fmul a D) T)
                      = fadd (fmul QV (fadd K D)) RV)
        by exact Hrec.
      assert (Hp'z : kpeval_lf p' z
                     = fadd (fadd (fmul QV (fadd K D)) RV) (fmul (fmul a D) T)).
      { rewrite <- Hgoal. ring. }
      rewrite Hp'z. ring.
Qed.

(* normalization *)

Fixpoint klnorm (p : list FC) : list FC :=
  match p with
  | nil => nil
  | a :: p' => if feq_dec a fO then klnorm p' else p
  end.

Lemma klnorm_eval : forall p z, kpeval_lf (klnorm p) z = kpeval_lf p z.
Proof.
  induction p as [|a p' IH]; intro z; cbn [klnorm].
  - reflexivity.
  - destruct (feq_dec a fO) as [-> | Hne].
    + cbn [kpeval_lf]. rewrite IH. ring.
    + reflexivity.
Qed.

Lemma klnorm_Forall : forall (P : FC -> Prop) p, Forall P p -> Forall P (klnorm p).
Proof.
  intros P p HP. induction HP as [|a p' Ha Hp' IH]; cbn [klnorm].
  - constructor.
  - destruct (feq_dec a fO); [exact IH | constructor; assumption].
Qed.

Lemma klnorm_length : forall p, (length (klnorm p) <= length p)%nat.
Proof.
  induction p as [|a p' IH]; cbn [klnorm length].
  - lia.
  - destruct (feq_dec a fO); cbn [length]; lia.
Qed.

Lemma klnorm_head : forall p, klnorm p = nil \/ hd fO (klnorm p) <> fO.
Proof.
  induction p as [|a p' IH]; cbn [klnorm].
  - left; reflexivity.
  - destruct (feq_dec a fO); [exact IH | right; cbn [hd]; assumption].
Qed.

Lemma klnorm_nonzero : forall p, ~ Forall (fun c => c = fO) p -> klnorm p <> nil.
Proof.
  induction p as [|a p' IH]; intro Hnz; cbn [klnorm].
  - exfalso. apply Hnz. constructor.
  - destruct (feq_dec a fO) as [-> | Hne].
    + apply IH. intro Hall. apply Hnz. constructor; [reflexivity | exact Hall].
    + discriminate.
Qed.

Lemma klnorm_id_of_head : forall p, p <> nil -> hd fO p <> fO -> klnorm p = p.
Proof.
  intros p Hnil Hhd. destruct p as [|a p']; [contradiction |].
  cbn [klnorm hd] in *. destruct (feq_dec a fO); [contradiction | reflexivity].
Qed.

Lemma klnorm_nil_eval : forall g z, klnorm g = nil -> kpeval_lf g z = fO.
Proof.
  intros g z Hg. rewrite <- (klnorm_eval g z), Hg. reflexivity.
Qed.

(* leading-first arithmetic through the constant-first layer *)

Definition kpmul_lf (a b : list FC) : list FC := rev (kpmul (rev a) (rev b)).
Definition kpsub_lf (a b : list FC) : list FC :=
  rev (kpadd (rev a) (kpscale (fopp fI) (rev b))).
Definition kpadd_lf (a b : list FC) : list FC := rev (kpadd (rev a) (rev b)).

Lemma kpmul_lf_eval : forall a b z,
  kpeval_lf (kpmul_lf a b) z = fmul (kpeval_lf a z) (kpeval_lf b z).
Proof.
  intros a b z. unfold kpmul_lf.
  rewrite kpeval_lf_rev, rev_involutive, kpeval_kpmul, <- !kpeval_lf_rev.
  reflexivity.
Qed.

Lemma kpsub_lf_eval : forall a b z,
  kpeval_lf (kpsub_lf a b) z = fsub (kpeval_lf a z) (kpeval_lf b z).
Proof.
  intros a b z. unfold kpsub_lf.
  rewrite kpeval_lf_rev, rev_involutive, kpeval_kpadd, kpeval_kpscale,
    <- !kpeval_lf_rev.
  ring.
Qed.

Lemma kpadd_lf_eval : forall a b z,
  kpeval_lf (kpadd_lf a b) z = fadd (kpeval_lf a z) (kpeval_lf b z).
Proof.
  intros a b z. unfold kpadd_lf.
  rewrite kpeval_lf_rev, rev_involutive, kpeval_kpadd, <- !kpeval_lf_rev.
  reflexivity.
Qed.

Lemma kForall_add : forall (P : FC -> Prop) a b,
  (forall x y, P x -> P y -> P (fadd x y)) ->
  Forall P a -> Forall P b -> Forall P (kpadd a b).
Proof.
  intros P a. induction a as [|u a IH]; intros b Hadd Ha Hb.
  - exact Hb.
  - destruct b as [|v b]; [exact Ha |].
    cbn [kpadd]. inversion Ha; subst. inversion Hb; subst.
    constructor; [apply Hadd; assumption | apply IH; assumption].
Qed.

Lemma kForall_scale : forall (P : FC -> Prop) c a,
  (forall x y, P x -> P y -> P (fmul x y)) ->
  P c -> Forall P a -> Forall P (kpscale c a).
Proof.
  intros P c a Hmul Hc Ha. induction Ha as [|u a Hu Ha IH].
  - constructor.
  - cbn [kpscale map]. constructor; [apply Hmul; assumption | exact IH].
Qed.

Lemma kForall_mul : forall (P : FC -> Prop) a b,
  (forall x y, P x -> P y -> P (fadd x y)) ->
  (forall x y, P x -> P y -> P (fmul x y)) ->
  P fO -> Forall P a -> Forall P b -> Forall P (kpmul a b).
Proof.
  intros P a. induction a as [|u a IH]; intros b Hadd Hmul H0 Ha Hb.
  - constructor.
  - cbn [kpmul]. inversion Ha; subst.
    apply kForall_add; [exact Hadd | |].
    + apply kForall_scale; assumption.
    + constructor; [exact H0 | apply IH; assumption].
Qed.

(* the predicate subfield *)

Definition kis_subfield (P : FC -> Prop) : Prop :=
  P fO /\ P fI /\
  (forall x y, P x -> P y -> P (fadd x y)) /\
  (forall x y, P x -> P y -> P (fsub x y)) /\
  (forall x y, P x -> P y -> P (fmul x y)) /\
  (forall x, P x -> x <> fO -> P (finv x)).

Lemma ksubfield_0 : forall P, kis_subfield P -> P fO.
Proof. intros P H; apply H. Qed.
Lemma ksubfield_1 : forall P, kis_subfield P -> P fI.
Proof. intros P H; apply H. Qed.
Lemma ksubfield_add : forall P x y, kis_subfield P -> P x -> P y -> P (fadd x y).
Proof. intros P x y H; apply H. Qed.
Lemma ksubfield_sub : forall P x y, kis_subfield P -> P x -> P y -> P (fsub x y).
Proof. intros P x y H; apply H. Qed.
Lemma ksubfield_mul : forall P x y, kis_subfield P -> P x -> P y -> P (fmul x y).
Proof. intros P x y H; apply H. Qed.
Lemma ksubfield_inv : forall P x, kis_subfield P -> P x -> x <> fO -> P (finv x).
Proof. intros P x H; apply H. Qed.
Lemma ksubfield_opp : forall P x, kis_subfield P -> P x -> P (fopp x).
Proof.
  intros P x H Hx.
  replace (fopp x) with (fsub fO x) by ring.
  apply ksubfield_sub; [exact H | apply ksubfield_0; exact H | exact Hx].
Qed.

Lemma kpdiv_lf_Forall : forall (P : FC -> Prop) fuel p dtail,
  (forall x y, P x -> P y -> P (fadd x y)) ->
  (forall x y, P x -> P y -> P (fmul x y)) ->
  P (fopp fI) ->
  Forall P p -> Forall P dtail ->
  Forall P (fst (kpdiv_lf fuel p dtail)) /\
  Forall P (snd (kpdiv_lf fuel p dtail)).
Proof.
  intros P fuel. induction fuel as [|f IH]; intros p dtail Hadd Hmul Hopp1 Hp Hd.
  - cbn [kpdiv_lf fst snd]. split; [constructor | exact Hp].
  - cbn [kpdiv_lf].
    destruct (Nat.leb (length p) (length dtail)).
    + cbn [fst snd]. split; [constructor | exact Hp].
    + destruct p as [|a p']; [cbn [fst snd]; split; constructor |].
      cbn [fst snd].
      inversion Hp; subst.
      assert (Hp'' : Forall P (kpadd p' (kpscale (fopp fI) (kpscale a dtail)))).
      { apply kForall_add; [exact Hadd | assumption |].
        apply kForall_scale; [exact Hmul | exact Hopp1 |].
        apply kForall_scale; [exact Hmul | assumption | exact Hd]. }
      destruct (IH (kpadd p' (kpscale (fopp fI) (kpscale a dtail))) dtail
                  Hadd Hmul Hopp1 Hp'' Hd) as [Hq Hr].
      split; [constructor; assumption | exact Hr].
Qed.

Lemma kpdiv_lf_Forall_sf : forall (P : FC -> Prop) fuel p dtail, kis_subfield P ->
  Forall P p -> Forall P dtail ->
  Forall P (fst (kpdiv_lf fuel p dtail)) /\
  Forall P (snd (kpdiv_lf fuel p dtail)).
Proof.
  intros P fuel p dtail HP Hp Hd.
  apply kpdiv_lf_Forall;
    [intros u v Hu Hv; apply (ksubfield_add P u v HP Hu Hv)
    | intros u v Hu Hv; apply (ksubfield_mul P u v HP Hu Hv)
    | apply (ksubfield_opp P fI HP (ksubfield_1 P HP))
    | exact Hp | exact Hd].
Qed.

Lemma kpmul_lf_Forall : forall (P : FC -> Prop) a b, kis_subfield P ->
  Forall P a -> Forall P b -> Forall P (kpmul_lf a b).
Proof.
  intros P a b HP Ha Hb. unfold kpmul_lf.
  apply Forall_rev, kForall_mul;
    [intros u v Hu Hv; apply (ksubfield_add P u v HP Hu Hv)
    | intros u v Hu Hv; apply (ksubfield_mul P u v HP Hu Hv)
    | apply (ksubfield_0 P HP)
    | apply Forall_rev; exact Ha
    | apply Forall_rev; exact Hb].
Qed.

Lemma kpsub_lf_Forall : forall (P : FC -> Prop) a b, kis_subfield P ->
  Forall P a -> Forall P b -> Forall P (kpsub_lf a b).
Proof.
  intros P a b HP Ha Hb. unfold kpsub_lf.
  apply Forall_rev, kForall_add;
    [intros u v Hu Hv; apply (ksubfield_add P u v HP Hu Hv)
    | apply Forall_rev; exact Ha |].
  apply kForall_scale;
    [intros u v Hu Hv; apply (ksubfield_mul P u v HP Hu Hv)
    | apply (ksubfield_opp P fI HP (ksubfield_1 P HP))
    | apply Forall_rev; exact Hb].
Qed.

Lemma kpadd_lf_Forall : forall (P : FC -> Prop) a b, kis_subfield P ->
  Forall P a -> Forall P b -> Forall P (kpadd_lf a b).
Proof.
  intros P a b HP Ha Hb. unfold kpadd_lf.
  apply Forall_rev, kForall_add;
    [intros u v Hu Hv; apply (ksubfield_add P u v HP Hu Hv)
    | apply Forall_rev; exact Ha | apply Forall_rev; exact Hb].
Qed.

(* general division: divide by the monicization of the normalized divisor *)

Definition kpdivg (p g : list FC) : list FC * list FC :=
  match klnorm g with
  | nil => (nil, p)
  | c :: dt0 =>
      let dt := kpscale (finv c) dt0 in
      (kpscale (finv c) (fst (kpdiv_lf (length p) p dt)),
       snd (kpdiv_lf (length p) p dt))
  end.

Lemma kpdivg_spec : forall (P : FC -> Prop) p g, kis_subfield P ->
  Forall P p -> Forall P g ->
  klnorm g <> nil ->
  Forall P (fst (kpdivg p g)) /\ Forall P (snd (kpdivg p g)) /\
  (length (snd (kpdivg p g)) < length (klnorm g))%nat /\
  (forall z, kpeval_lf p z
     = fadd (fmul (kpeval_lf (fst (kpdivg p g)) z) (kpeval_lf g z))
            (kpeval_lf (snd (kpdivg p g)) z)).
Proof.
  intros P p g HP HPp HPg Hgnz.
  unfold kpdivg.
  destruct (klnorm g) as [|c dt0] eqn:Eg; [contradiction |].
  destruct (klnorm_head g) as [Hnil | Hhd]; [rewrite Eg in Hnil; discriminate |].
  rewrite Eg in Hhd. cbn [hd] in Hhd.
  assert (HPn : Forall P (c :: dt0)) by (rewrite <- Eg; apply klnorm_Forall; exact HPg).
  inversion HPn; subst.
  assert (HPc : P (finv c)) by (apply (ksubfield_inv P c HP); assumption).
  assert (HPdt : Forall P (kpscale (finv c) dt0)).
  { apply kForall_scale;
      [intros u v Hu Hv; apply (ksubfield_mul P u v HP Hu Hv) | exact HPc | assumption]. }
  destruct (kpdiv_lf_Forall_sf P (length p) p (kpscale (finv c) dt0) HP HPp HPdt)
    as [HPq HPr].
  cbn [fst snd].
  split.
  { apply kForall_scale;
      [intros u v Hu Hv; apply (ksubfield_mul P u v HP Hu Hv) | exact HPc | exact HPq]. }
  split; [exact HPr |].
  split.
  { pose proof (kpdiv_lf_rlen (length p) p (kpscale (finv c) dt0) (Nat.le_refl _)) as Hr.
    rewrite kpscale_length in Hr. cbn [length]. lia. }
  intro z.
  pose proof (kpdiv_lf_eval (length p) p (kpscale (finv c) dt0) (Nat.le_refl _) z) as Hs.
  rewrite kpscale_length in Hs.
  assert (Hsc : kpeval_lf (kpscale (finv c) (fst (kpdiv_lf (length p) p (kpscale (finv c) dt0)))) z
                = fmul (finv c) (kpeval_lf (fst (kpdiv_lf (length p) p (kpscale (finv c) dt0))) z)).
  { rewrite !kpeval_lf_rev.
    unfold kpscale. rewrite <- map_rev.
    fold (kpscale (finv c) (rev (fst (kpdiv_lf (length p) p (kpscale (finv c) dt0))))).
    apply kpeval_kpscale. }
  rewrite Hsc.
  assert (Hgz : kpeval_lf g z
                = fmul c (fadd (kpow z (length dt0)) (kpeval_lf (kpscale (finv c) dt0) z))).
  { rewrite <- (klnorm_eval g z), Eg. cbn [kpeval_lf].
    assert (Hsc2 : kpeval_lf (kpscale (finv c) dt0) z
                   = fmul (finv c) (kpeval_lf dt0 z)).
    { rewrite !kpeval_lf_rev. unfold kpscale. rewrite <- map_rev.
      fold (kpscale (finv c) (rev dt0)). apply kpeval_kpscale. }
    rewrite Hsc2. field. exact Hhd. }
  rewrite Hgz, Hs. field. exact Hhd.
Qed.

(* extended Euclid on leading-first lists *)

Fixpoint kbezout_lf (fuel : nat) (p g : list FC) : (list FC * list FC) * list FC :=
  match fuel with
  | O => ((fI :: nil, nil), klnorm p)
  | S fu =>
      match klnorm g with
      | nil => ((fI :: nil, nil), klnorm p)
      | _ :: _ =>
          let q := fst (kpdivg p g) in
          let r := snd (kpdivg p g) in
          let ud := kbezout_lf fu g r in
          ((snd (fst ud), kpsub_lf (fst (fst ud)) (kpmul_lf (snd (fst ud)) q)),
           snd ud)
      end
  end.

Lemma kbezout_lf_spec : forall (P : FC -> Prop) fuel p g, kis_subfield P ->
  Forall P p -> Forall P g -> (length (klnorm g) <= fuel)%nat ->
  Forall P (fst (fst (kbezout_lf fuel p g))) /\
  Forall P (snd (fst (kbezout_lf fuel p g))) /\
  Forall P (snd (kbezout_lf fuel p g)) /\
  (forall z, fadd (fmul (kpeval_lf (fst (fst (kbezout_lf fuel p g))) z) (kpeval_lf p z))
                  (fmul (kpeval_lf (snd (fst (kbezout_lf fuel p g))) z) (kpeval_lf g z))
             = kpeval_lf (snd (kbezout_lf fuel p g)) z) /\
  (exists qp, Forall P qp /\ forall z,
      kpeval_lf p z = fmul (kpeval_lf qp z) (kpeval_lf (snd (kbezout_lf fuel p g)) z)) /\
  (exists qg, Forall P qg /\ forall z,
      kpeval_lf g z = fmul (kpeval_lf qg z) (kpeval_lf (snd (kbezout_lf fuel p g)) z)) /\
  (klnorm g <> nil ->
     (length (snd (kbezout_lf fuel p g)) <= length (klnorm g))%nat) /\
  (snd (kbezout_lf fuel p g) = nil \/ hd fO (snd (kbezout_lf fuel p g)) <> fO).
Proof.
  intros P fuel. induction fuel as [|fu IH]; intros p g HP HPp HPg Hfuel.
  - assert (Hgnil : klnorm g = nil)
      by (destruct (klnorm g); [reflexivity | cbn [length] in Hfuel; lia]).
    cbn [kbezout_lf fst snd].
    split; [repeat constructor; apply (ksubfield_1 P HP) |].
    split; [constructor |].
    split; [apply klnorm_Forall; exact HPp |].
    split.
    { intro z. cbn [kpeval_lf length kpow].
      rewrite (klnorm_eval p z). ring. }
    split.
    { exists (fI :: nil). split; [repeat constructor; apply (ksubfield_1 P HP) |].
      intro z. cbn [kpeval_lf length kpow]. rewrite (klnorm_eval p z). ring. }
    split.
    { exists nil. split; [constructor |].
      intro z. cbn [kpeval_lf]. rewrite (klnorm_nil_eval g z Hgnil). ring. }
    split; [intro Hc; contradiction |].
    apply klnorm_head.
  - cbn [kbezout_lf].
    destruct (klnorm g) as [|c dt0] eqn:Eg.
    + cbn [fst snd].
      split; [repeat constructor; apply (ksubfield_1 P HP) |].
      split; [constructor |].
      split; [apply klnorm_Forall; exact HPp |].
      split.
      { intro z. cbn [kpeval_lf length kpow].
        rewrite (klnorm_eval p z). ring. }
      split.
      { exists (fI :: nil). split; [repeat constructor; apply (ksubfield_1 P HP) |].
        intro z. cbn [kpeval_lf length kpow]. rewrite (klnorm_eval p z). ring. }
      split.
      { exists nil. split; [constructor |].
        intro z. cbn [kpeval_lf]. rewrite (klnorm_nil_eval g z Eg). ring. }
      split; [intro Hc; contradiction |].
      apply klnorm_head.
    + assert (Hgnz : klnorm g <> nil) by (rewrite Eg; discriminate).
      destruct (kpdivg_spec P p g HP HPp HPg Hgnz) as [HPq [HPr [Hrlen Hdiv]]].
      set (q := fst (kpdivg p g)) in *.
      set (r := snd (kpdivg p g)) in *.
      assert (Hrfu : (length (klnorm r) <= fu)%nat).
      { pose proof (klnorm_length r). rewrite Eg in Hrlen.
        cbn [length] in Hrlen, Hfuel. lia. }
      destruct (IH g r HP HPg HPr Hrfu) as
        [HPu' [HPv' [HPd [Hbez [Hqg [Hqr [Hdlen Hdnorm]]]]]]].
      destruct (kbezout_lf fu g r) as [[u' v'] d] eqn:Ebez.
      cbn [fst snd] in *.
      split; [exact HPv' |].
      split.
      { apply kpsub_lf_Forall; [exact HP | exact HPu' |].
        apply kpmul_lf_Forall; [exact HP | exact HPv' | exact HPq]. }
      split; [exact HPd |].
      split.
      { intro z. rewrite kpsub_lf_eval, kpmul_lf_eval.
        rewrite (Hdiv z). rewrite <- (Hbez z). ring. }
      split.
      { destruct Hqg as [qg [HPqg Hqgev]].
        destruct Hqr as [qr [HPqr Hqrev]].
        exists (kpadd_lf (kpmul_lf q qg) qr).
        split.
        { apply kpadd_lf_Forall; [exact HP | | exact HPqr].
          apply kpmul_lf_Forall; [exact HP | exact HPq | exact HPqg]. }
        intro z. rewrite kpadd_lf_eval, kpmul_lf_eval.
        rewrite (Hdiv z), (Hqgev z), (Hqrev z). ring. }
      split.
      { destruct Hqg as [qg [HPqg Hqgev]].
        exists qg. split; [exact HPqg | exact Hqgev]. }
      split; [| exact Hdnorm].
      intros _.
      destruct (klnorm r) as [|cr dtr] eqn:Er.
      * assert (Hdg : d = klnorm g).
        { destruct fu as [|fu']; cbn [kbezout_lf] in Ebez.
          - injection Ebez as _ _ E. rewrite <- E. reflexivity.
          - rewrite Er in Ebez. injection Ebez as _ _ E. rewrite <- E. reflexivity. }
        rewrite Hdg, Eg. lia.
      * pose proof (Hdlen ltac:(discriminate)) as Hd1.
        pose proof (klnorm_length r) as Hd2. rewrite Er in Hd2.
        rewrite Eg in Hrlen. cbn [length] in Hrlen |- *. cbn [length] in Hd1, Hd2. lia.
Qed.

(* independence of the powers below n over a predicate subfield, list form *)

Definition kindep_pows (P : FC -> Prop) (z : FC) (n : nat) : Prop :=
  forall cs : list FC, length cs = n -> Forall P cs ->
  kpeval cs z = fO -> Forall (fun c => c = fO) cs.

Hypothesis kmonic_lf_nonzero : forall fl, hd fO fl = fI -> (2 <= length fl)%nat ->
  ~ (forall z, kpeval_lf fl z = fO).

Lemma kForall_zero_eval : forall (p : list FC),
  Forall (fun c => c = fO) p -> forall z, kpeval_lf p z = fO.
Proof.
  intros p Hp. induction Hp as [|a p' Ha Hp' IH]; intro z; cbn [kpeval_lf].
  - reflexivity.
  - rewrite Ha, (IH z). ring.
Qed.

(* IRREDUCIBLE MEANS INDEPENDENT, parametric *)
Lemma kirreducible_root_lin_indep :
  forall (P : FC -> Prop) (fl : list FC) (z0 : FC),
  kis_subfield P ->
  (2 <= length fl)%nat ->
  hd fO fl = fI ->
  Forall P fl ->
  kpeval_lf fl z0 = fO ->
  (forall dl ql, Forall P dl -> Forall P ql ->
     (2 <= length dl)%nat -> (length dl < length fl)%nat ->
     hd fO dl = fI ->
     (forall z, kpeval_lf fl z = fmul (kpeval_lf dl z) (kpeval_lf ql z)) -> False) ->
  kindep_pows P z0 (length fl - 1).
Proof.
  intros P fl z0 HP Hlen Hmon HPf Hroot Hirr.
  intros ks Hklen HPks Hkcomb.
  destruct (Forall_dec (fun c => c = fO) (fun c => feq_dec c fO) ks) as [Hz | Hnz];
    [exact Hz | exfalso].
  set (g := klnorm (rev ks)).
  assert (Hgnz : g <> nil).
  { apply klnorm_nonzero. intro Hall. apply Hnz.
    rewrite <- (rev_involutive ks). apply Forall_rev. exact Hall. }
  assert (HPg : Forall P g) by (apply klnorm_Forall, Forall_rev; exact HPks).
  assert (Hglen : (length g <= length ks)%nat).
  { pose proof (klnorm_length (rev ks)) as Hl. rewrite length_rev in Hl. exact Hl. }
  assert (Hghd : hd fO g <> fO).
  { destruct (klnorm_head (rev ks)) as [Hc | Hc]; [contradiction | exact Hc]. }
  assert (Hgev : kpeval_lf g z0 = fO).
  { unfold g. rewrite klnorm_eval, kpeval_lf_rev, rev_involutive. exact Hkcomb. }
  destruct (kbezout_lf_spec P (length (klnorm g)) fl g HP HPf HPg (Nat.le_refl _)) as
    [HPu [HPv [HPd [Hbez [[qp [HPqp Hqp]] [[qg [HPqg Hqg]] [Hdlen Hdnorm]]]]]]].
  set (d := snd (kbezout_lf (length (klnorm g)) fl g)) in *.
  assert (Hdz0 : kpeval_lf d z0 = fO)
    by (rewrite <- (Hbez z0), Hroot, Hgev; ring).
  destruct Hdnorm as [Hdnil | Hdhd].
  - apply (kmonic_lf_nonzero fl Hmon Hlen).
    intro z. rewrite (Hqp z), Hdnil. cbn [kpeval_lf]. ring.
  - destruct d as [|c dt] eqn:Ed; [cbn [hd] in Hdhd; congruence |].
    cbn [hd] in Hdhd.
    destruct dt as [|c2 dt2].
    + apply Hdhd.
      cbn [kpeval_lf length kpow] in Hdz0.
      assert (E : fadd (fmul c fI) fO = c) by ring.
      rewrite <- E. exact Hdz0.
    + set (dm := kpscale (finv c) (c :: c2 :: dt2)).
      assert (Hlg : klnorm g = g) by (apply klnorm_id_of_head; assumption).
      apply (Hirr dm (kpscale c qp)).
      * unfold dm. apply kForall_scale;
          [intros u v Hu Hv; apply (ksubfield_mul P u v HP Hu Hv)
          | apply (ksubfield_inv P c HP);
              [apply (Forall_inv HPd) | exact Hdhd]
          | exact HPd].
      * apply kForall_scale;
          [intros u v Hu Hv; apply (ksubfield_mul P u v HP Hu Hv)
          | apply (Forall_inv HPd) | exact HPqp].
      * unfold dm. rewrite kpscale_length. cbn [length]. lia.
      * unfold dm. rewrite kpscale_length.
        pose proof (Hdlen ltac:(rewrite Hlg; exact Hgnz)) as Hd1.
        rewrite Hlg in Hd1. cbn [length] in Hd1 |- *. lia.
      * unfold dm. rewrite kpscale_cons. cbn [hd]. field. exact Hdhd.
      * intro z. unfold dm.
        assert (Hs1 : kpeval_lf (kpscale (finv c) (c :: c2 :: dt2)) z
                      = fmul (finv c) (kpeval_lf (c :: c2 :: dt2) z)).
        { rewrite !kpeval_lf_rev. unfold kpscale. rewrite <- map_rev.
          fold (kpscale (finv c) (rev (c :: c2 :: dt2))). apply kpeval_kpscale. }
        assert (Hs2 : kpeval_lf (kpscale c qp) z = fmul c (kpeval_lf qp z)).
        { rewrite !kpeval_lf_rev. unfold kpscale. rewrite <- map_rev.
          fold (kpscale c (rev qp)). apply kpeval_kpscale. }
        rewrite Hs1, Hs2, (Hqp z).
        field. exact Hdhd.
Qed.

(* THE MINIMAL RELATION DIVIDES, parametric list form *)
Lemma kminpoly_divides : forall (P : FC -> Prop) (r : FC) (j : nat) (dtcf : list FC),
  kis_subfield P -> (1 <= j)%nat ->
  length dtcf = j -> Forall P dtcf ->
  fadd (kpeval dtcf r) (kpow r j) = fO ->
  kindep_pows P r j ->
  forall g : list FC, Forall P g -> kpeval g r = fO ->
  Forall P (fst (kpdiv_lf (length (rev g)) (rev g) (rev dtcf))) /\
  (forall z, kpeval g z
     = fmul (kpeval_lf (fst (kpdiv_lf (length (rev g)) (rev g) (rev dtcf))) z)
            (fadd (kpow z j) (kpeval dtcf z))).
Proof.
  intros P r j dtcf HP Hj Hlen HPdt Hrel Hindep g HPg Hgr.
  set (dt := rev dtcf) in *.
  assert (Hlen_dt : length dt = j) by (unfold dt; rewrite length_rev; exact Hlen).
  assert (HPdtl : Forall P dt) by (unfold dt; apply Forall_rev; exact HPdt).
  assert (HPrevg : Forall P (rev g)) by (apply Forall_rev; exact HPg).
  set (q := fst (kpdiv_lf (length (rev g)) (rev g) dt)) in *.
  set (rr := snd (kpdiv_lf (length (rev g)) (rev g) dt)) in *.
  destruct (kpdiv_lf_Forall_sf P (length (rev g)) (rev g) dt HP HPrevg HPdtl)
    as [HPq HPr].
  pose proof (kpdiv_lf_rlen (length (rev g)) (rev g) dt (Nat.le_refl _)) as Hrlen.
  rewrite Hlen_dt in Hrlen.
  pose proof (kpdiv_lf_eval (length (rev g)) (rev g) dt (Nat.le_refl _)) as Hspec.
  rewrite Hlen_dt in Hspec.
  fold q rr in Hspec, HPq, HPr, Hrlen.
  assert (Hdt_eval : forall y, kpeval_lf dt y = kpeval dtcf y).
  { intro y. unfold dt. rewrite kpeval_lf_rev, rev_involutive. reflexivity. }
  assert (Hgr' : kpeval_lf (rev g) r = fO)
    by (rewrite kpeval_lf_rev, rev_involutive; exact Hgr).
  assert (Hrrr : kpeval_lf rr r = fO).
  { pose proof (Hspec r) as Hb.
    rewrite Hdt_eval in Hb.
    assert (Hz : fadd (kpow r j) (kpeval dtcf r) = fO)
      by (rewrite <- Hrel; ring).
    rewrite Hz in Hb.
    rewrite Hgr' in Hb.
    assert (E : kpeval_lf rr r
                = fsub (fadd (fmul (kpeval_lf q r) fO) (kpeval_lf rr r))
                       (fmul (kpeval_lf q r) fO)) by ring.
    rewrite E, <- Hb. ring. }
  assert (Hrrzero : Forall (fun c => c = fO) rr).
  { set (cs' := rev rr ++ repeat fO (j - length rr)).
    assert (Hlcs' : length cs' = j)
      by (unfold cs'; rewrite length_app, length_rev, repeat_length; lia).
    assert (HPcs' : Forall P cs').
    { unfold cs'. apply Forall_app. split; [apply Forall_rev; exact HPr |].
      apply Forall_forall. intros z Hz.
      apply repeat_spec in Hz. subst z. apply (ksubfield_0 P HP). }
    assert (Hpadeval : forall n y, kpeval (repeat fO n) y = fO).
    { induction n as [|n IHn]; intro y; cbn [repeat kpeval].
      - reflexivity.
      - rewrite IHn. ring. }
    assert (Happ : forall l1 l2 w, kpeval (l1 ++ l2) w
                   = fadd (kpeval l1 w) (fmul (kpow w (length l1)) (kpeval l2 w))).
    { induction l1 as [|x l1 IHl]; intros l2 w; cbn [app kpeval length kpow].
      - ring.
      - rewrite IHl. ring. }
    assert (Hcs'r : kpeval cs' r = fO).
    { unfold cs'. rewrite Happ, Hpadeval.
      assert (Hbr : kpeval (rev rr) r = kpeval_lf rr r)
        by (rewrite kpeval_lf_rev; reflexivity).
      rewrite Hbr, Hrrr. ring. }
    pose proof (Hindep cs' Hlcs' HPcs' Hcs'r) as Hall.
    unfold cs' in Hall.
    apply Forall_app in Hall.
    rewrite <- (rev_involutive rr).
    apply Forall_rev. exact (proj1 Hall). }
  split; [exact HPq |].
  intro z.
  pose proof (Hspec z) as Hs.
  assert (Hgz : kpeval_lf (rev g) z = kpeval g z)
    by (rewrite kpeval_lf_rev, rev_involutive; reflexivity).
  rewrite Hgz, Hdt_eval in Hs.
  rewrite (kForall_zero_eval rr Hrrzero z) in Hs.
  rewrite Hs. ring.
Qed.

End FieldPolyCore.

(* Galois keystone: division with remainder by a monic divisor over a predicate subfield on leading-first lists -- no inversion, quotient and remainder stay in any subring containing the inputs. *)

Fixpoint peval_lf (p : list R) (x : R) : R :=
  match p with
  | nil => 0
  | a :: p' => a * x ^ (length p') + peval_lf p' x
  end.

Lemma peval_lf_app : forall p q x,
  peval_lf (p ++ q) x = peval_lf p x * x ^ (length q) + peval_lf q x.
Proof.
  induction p as [|a p' IH]; intros q x.
  - cbn [app peval_lf]. ring.
  - cbn [app peval_lf]. rewrite IH, length_app, pow_add. ring.
Qed.

(** Leading-first evaluation of the reversal is constant-first evaluation. *)
Lemma pevalR_rev : forall l x, pevalR l x = peval_lf (rev l) x.
Proof.
  induction l as [|c l' IH]; intro x.
  - reflexivity.
  - cbn [pevalR rev]. rewrite peval_lf_app. cbn [peval_lf length pow].
    rewrite <- IH. ring.
Qed.

Lemma paddR_nil_r : forall p : list R, paddR p nil = p.
Proof. intro p. destruct p; reflexivity. Qed.

Lemma pscaleR_length : forall a (p : list R), length (pscaleR a p) = length p.
Proof. intros a p. unfold pscaleR. apply length_map. Qed.

Lemma peval_lf_pscale : forall a l x,
  peval_lf (pscaleR a l) x = a * peval_lf l x.
Proof.
  intros a l x. unfold pscaleR. induction l as [|c l' IH].
  - cbn [map peval_lf]. ring.
  - cbn [map peval_lf]. rewrite IH, length_map. ring.
Qed.

Lemma pscaleR_cons : forall a c (l : list R),
  pscaleR a (c :: l) = (a * c) :: pscaleR a l.
Proof. reflexivity. Qed.

Lemma pscaleR_nil : forall a, pscaleR a nil = nil.
Proof. reflexivity. Qed.

(** Top-aligned subtraction: pointwise subtraction of a shorter leading-first list cancels the leading terms. *)
Lemma peval_lf_psub_top : forall q p x, (length q <= length p)%nat ->
  peval_lf (paddR p (pscaleR (-1) q)) x
  = peval_lf p x - peval_lf q x * x ^ (length p - length q).
Proof. exact (kpeval_lf_psub_top _ _ _ _ _ _ _ _ _ RealField.Rfield). Qed.

(** Division by the monic divisor X^(length dtail) + dtail, leading-first. *)
Fixpoint pdiv_lf (fuel : nat) (p dtail : list R) : list R * list R :=
  match fuel with
  | O => (nil, p)
  | S f =>
      if Nat.leb (length p) (length dtail) then (nil, p)
      else match p with
           | nil => (nil, nil)
           | a :: p' =>
               let p'' := paddR p' (pscaleR (-1) (pscaleR a dtail)) in
               (a :: fst (pdiv_lf f p'' dtail), snd (pdiv_lf f p'' dtail))
           end
  end.

Lemma pdiv_lf_qlen : forall fuel p dtail, (length p <= fuel)%nat ->
  length (fst (pdiv_lf fuel p dtail)) = (length p - length dtail)%nat.
Proof. exact (kpdiv_lf_qlen R 1 Rplus Rmult Ropp). Qed.

Lemma pdiv_lf_rlen : forall fuel p dtail, (length p <= fuel)%nat ->
  (length (snd (pdiv_lf fuel p dtail)) <= length dtail)%nat.
Proof. exact (kpdiv_lf_rlen R 1 Rplus Rmult Ropp). Qed.

(** THE DIVISION SPECIFICATION: p = q * (X^k + dtail) + r as polynomial functions at every real point. *)
Lemma pdiv_lf_eval : forall fuel p dtail, (length p <= fuel)%nat ->
  forall x,
  peval_lf p x
  = peval_lf (fst (pdiv_lf fuel p dtail)) x
      * (x ^ (length dtail) + peval_lf dtail x)
    + peval_lf (snd (pdiv_lf fuel p dtail)) x.
Proof. exact (kpdiv_lf_eval _ _ _ _ _ _ _ _ _ RealField.Rfield). Qed.

(** Closure: quotient and remainder stay inside any predicate closed under addition, multiplication, and containing -1. *)
Lemma pdiv_lf_Forall : forall (P : R -> Prop) fuel p dtail,
  (forall x y, P x -> P y -> P (x + y)) ->
  (forall x y, P x -> P y -> P (x * y)) ->
  P (- 1) ->
  Forall P p -> Forall P dtail ->
  Forall P (fst (pdiv_lf fuel p dtail)) /\
  Forall P (snd (pdiv_lf fuel p dtail)).
Proof. exact (kpdiv_lf_Forall R 1 Rplus Rmult Ropp). Qed.

(* Galois keystone: minimal polynomials -- the maximal independent power prefix gives a monic relation, and division forces every vanishing F-polynomial to factor through it. *)

Lemma pevalR_map_seq : forall (c : nat -> R) j x,
  pevalR (map c (seq 0 j)) x = fsum j (fun i => c i * x ^ i).
Proof.
  intros c j x.
  rewrite pevalR_nth_sum, length_map, length_seq.
  apply fsum_ext. intros i Hi.
  rewrite (nth_indep _ 0 (c 0%nat))
    by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia.
  reflexivity.
Qed.

Lemma peval_lf_zero : forall (r : list R) x,
  Forall (fun z => z = 0) r -> peval_lf r x = 0.
Proof.
  intros r x Hr. induction Hr as [|a r' Ha Hr' IH].
  - reflexivity.
  - cbn [peval_lf]. rewrite Ha, IH. ring.
Qed.

Lemma pevalR_app : forall (l1 l2 : list R) x,
  pevalR (l1 ++ l2) x = pevalR l1 x + x ^ (length l1) * pevalR l2 x.
Proof.
  induction l1 as [|a l1' IH]; intros l2 x.
  - cbn [app pevalR length pow]. ring.
  - cbn [app pevalR length]. rewrite IH. cbn [pow]. ring.
Qed.

Lemma pevalR_repeat0 : forall n x, pevalR (repeat 0 n) x = 0.
Proof.
  induction n as [|n IH]; intro x; cbn [repeat pevalR]; [ring | rewrite IH; ring].
Qed.

Lemma Forall_app_intro : forall (P : R -> Prop) (l1 l2 : list R),
  Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  intros P l1 l2 H1 H2. induction H1 as [|a l1' Ha H1' IH].
  - exact H2.
  - cbn [app]. constructor; assumption.
Qed.

Lemma Forall_app_left : forall (P : R -> Prop) (l1 l2 : list R),
  Forall P (l1 ++ l2) -> Forall P l1.
Proof.
  intros P l1 l2 H. induction l1 as [|a l1' IH].
  - constructor.
  - cbn [app] in H. inversion H; subst. constructor; [assumption | apply IH; assumption].
Qed.

Lemma Fcomb_powers_pevalR : forall (cs : list R) (x : R),
  Fcomb cs (powers x (length cs)) = pevalR cs x.
Proof.
  intros cs x.
  rewrite (list_eta_nth cs) at 1.
  unfold powers. rewrite Fcomb_map2, rsum_seq0_fsum, pevalR_nth_sum.
  reflexivity.
Qed.

(** THE MINIMAL RELATION DIVIDES: every F-polynomial vanishing at x factors through the monic minimal relation with an F-quotient. *)
Lemma minpoly_divides_lf : forall (F : R -> Prop) (x : R) (j : nat) (c : nat -> R),
  is_subfield F -> (1 <= j)%nat ->
  (forall i, (i < j)%nat -> F (c i)) ->
  fsum j (fun i => c i * x ^ i) + x ^ j = 0 ->
  lin_indep F (powers x j) ->
  forall g : list R, Forall F g -> peval_lf g x = 0 ->
  Forall F (fst (pdiv_lf (length g) g (rev (map c (seq 0 j))))) /\
  (forall y, peval_lf g y
     = peval_lf (fst (pdiv_lf (length g) g (rev (map c (seq 0 j))))) y
       * (y ^ j + peval_lf (rev (map c (seq 0 j))) y)).
Proof.
  intros F x j c HF Hj Hc Hrel Hindep g HFg Hgx.
  assert (Hlen : length (map c (seq 0 j)) = j)
    by (rewrite length_map, length_seq; reflexivity).
  assert (HFdt : Forall F (map c (seq 0 j))).
  { apply Forall_forall. intros z Hz.
    apply in_map_iff in Hz. destruct Hz as [i [Hzi Hin]].
    apply in_seq in Hin. subst z. apply Hc. lia. }
  assert (Hrel' : pevalR (map c (seq 0 j)) x + x ^ j = 0)
    by (rewrite pevalR_map_seq; exact Hrel).
  assert (Hindep' : kindep_pows R 0 Rplus Rmult F x j).
  { intros cs Hl HFcs Hev.
    apply (Hindep cs).
    - rewrite powers_length. exact Hl.
    - exact HFcs.
    - rewrite <- Hl, Fcomb_powers_pevalR. exact Hev. }
  assert (HFrevg : Forall F (rev g)) by (apply Forall_rev; exact HFg).
  assert (Hgr' : pevalR (rev g) x = 0)
    by (rewrite pevalR_rev, rev_involutive; exact Hgx).
  destruct (kminpoly_divides _ _ _ _ _ _ _ _ _ RealField.Rfield F x j
              (map c (seq 0 j)) HF Hj Hlen HFdt Hrel' Hindep'
              (rev g) HFrevg Hgr') as [H1 H2].
  rewrite (rev_involutive g) in H1, H2.
  split; [exact H1 |].
  intro y.
  rewrite <- (rev_involutive g) at 1.
  rewrite <- pevalR_rev.
  rewrite <- (pevalR_rev (map c (seq 0 j)) y).
  exact (H2 y).
Qed.

(* Galois keystone: every monic real polynomial of odd degree has a real root, by coefficient-sum bounds and the IVT -- with the degree <= 4 formulas this splits every real tower-step polynomial. *)

Lemma continuity_pow : forall n, continuity (fun x => x ^ n).
Proof.
  induction n as [|n IH].
  - apply continuity_const. intros x y. reflexivity.
  - assert (Hid : continuity (fun x : R => x))
      by (apply derivable_continuous, derivable_id).
    exact (continuity_mult _ _ Hid IH).
Qed.

Lemma peval_lf_continuity : forall p, continuity (fun x => peval_lf p x).
Proof.
  induction p as [|a p' IH].
  - apply continuity_const. intros x y. reflexivity.
  - assert (Hc : continuity (fun _ : R => a))
      by (apply continuity_const; intros x y; reflexivity).
    exact (continuity_plus _ _
             (continuity_mult _ _ Hc (continuity_pow (length p'))) IH).
Qed.

Definition sum_abs (l : list R) : R := fold_right (fun a s => Rabs a + s) 0 l.

Lemma sum_abs_nonneg : forall l, 0 <= sum_abs l.
Proof.
  induction l as [|a l' IH]; cbn [sum_abs fold_right].
  - lra.
  - pose proof (Rabs_pos a). unfold sum_abs in IH. lra.
Qed.

Lemma peval_lf_abs_bound : forall (l : list R) y, 1 <= Rabs y ->
  Rabs (peval_lf l y) <= sum_abs l * Rabs y ^ (length l - 1).
Proof.
  induction l as [|a l' IH]; intros y Hy.
  - cbn [peval_lf sum_abs fold_right length]. rewrite Rabs_R0. cbn [pow]. lra.
  - cbn [peval_lf sum_abs fold_right length].
    fold (sum_abs l').
    replace (S (length l') - 1)%nat with (length l') by lia.
    eapply Rle_trans; [apply Rabs_triang |].
    rewrite Rabs_mult, <- RPow_abs.
    assert (Htail : Rabs (peval_lf l' y) <= sum_abs l' * Rabs y ^ (length l')).
    { eapply Rle_trans; [apply IH; exact Hy |].
      apply Rmult_le_compat_l; [apply sum_abs_nonneg |].
      apply Rle_pow; [exact Hy | lia]. }
    assert (Hpownn : 0 <= Rabs y ^ (length l'))
      by (apply pow_le; pose proof (Rabs_pos y); lra).
    pose proof (Rabs_pos a). nra.
Qed.

(** ODD-DEGREE REAL ROOT: the monic polynomial X^n + dtail with n odd has a real root. *)
Theorem odd_monic_real_root : forall (dt : list R), Nat.Odd (length dt) ->
  exists x, x ^ (length dt) + peval_lf dt x = 0.
Proof.
  intros dt Hodd.
  destruct Hodd as [k Hk].
  set (n := length dt) in *.
  assert (Hn1 : (1 <= n)%nat) by lia.
  set (S0 := sum_abs dt).
  assert (HS0 : 0 <= S0) by apply sum_abs_nonneg.
  set (M := 1 + S0).
  assert (HM1 : 1 <= M) by (unfold M; lra).
  assert (HM0 : 0 < M) by lra.
  set (g := fun y : R => y ^ n + peval_lf dt y).
  assert (Hgcont : continuity g).
  { unfold g.
    exact (continuity_plus _ _ (continuity_pow n) (peval_lf_continuity dt)). }
  assert (Hpow_pos : 0 < M ^ (n - 1)) by (apply pow_lt; exact HM0).
  assert (HMn : M ^ n = M * M ^ (n - 1)).
  { replace n with (Datatypes.S (n - 1)) at 1 by lia. cbn [pow]. reflexivity. }
  assert (HboundM : Rabs (peval_lf dt M) <= S0 * M ^ (n - 1)).
  { pose proof (peval_lf_abs_bound dt M) as Hb.
    rewrite (Rabs_right M) in Hb by lra.
    apply Hb. lra. }
  assert (HboundmM : Rabs (peval_lf dt (- M)) <= S0 * M ^ (n - 1)).
  { pose proof (peval_lf_abs_bound dt (- M)) as Hb.
    rewrite (Rabs_left (- M)) in Hb by lra.
    replace (- - M) with M in Hb by ring.
    apply Hb. lra. }
  assert (HgM : 0 < g M).
  { unfold g.
    assert (Hlow : - (S0 * M ^ (n - 1)) <= peval_lf dt M).
    { pose proof (Rle_abs (- peval_lf dt M)) as Habs.
      rewrite Rabs_Ropp in Habs. lra. }
    rewrite HMn. unfold M in Hlow, Hpow_pos |- *. nra. }
  assert (HgmM : g (- M) < 0).
  { unfold g.
    assert (Hupp : peval_lf dt (- M) <= S0 * M ^ (n - 1)).
    { pose proof (Rle_abs (peval_lf dt (- M))) as Habs. lra. }
    assert (HmMn : (- M) ^ n = - (M ^ n)).
    { replace (- M) with (-1 * M) by ring.
      rewrite Rpow_mult_distr.
      rewrite Hk. replace (2 * k + 1)%nat with (Datatypes.S (2 * k)) by lia.
      rewrite pow_1_odd. ring. }
    rewrite HmMn, HMn. unfold M in Hupp, Hpow_pos |- *. nra. }
  destruct (IVT g (- M) M Hgcont ltac:(lra) HgmM HgM) as [z [_ Hz]].
  exists z. exact Hz.
Qed.

(* Galois keystone: complex splitting through degree five (quadratic, Cardano, Ferrari, and the odd-root reduction for quintics); Cardano_C shadows the Line projection C from here on. *)

Import Cardano_C.
Open Scope R_scope.

Lemma RtoC_2_neq_0 : RtoC 2 <> C0.
Proof. apply RtoC_neq_0. lra. Qed.

Lemma RtoC_4_neq_0 : RtoC 4 <> C0.
Proof. apply RtoC_neq_0. lra. Qed.

Lemma RtoC_4_split : RtoC 4 = (RtoC 2 * RtoC 2)%C.
Proof. rewrite <- RtoC_mul. f_equal; lra. Qed.

(** The complex two: written C1 + C1 so the ring tactic computes with it. *)
Lemma Ctwo_neq_0 : (C1 + C1)%C <> C0.
Proof. unfold C1, C0, Cadd. cbn. intro H. inversion H. lra. Qed.

(** COMPLEX QUADRATIC SPLITTING. *)
Lemma Cquadratic_split : forall b c : C, exists z1 z2 : C,
  forall z : C, (z * z + b * z + c)%C = ((z - z1) * (z - z2))%C.
Proof.
  intros b c.
  set (two := (C1 + C1)%C).
  assert (Htwo : two <> C0) by exact Ctwo_neq_0.
  assert (Hfour : (two * two)%C <> C0) by (apply Cmul_neq_0; exact Htwo).
  destruct (C_sqrt_exists ((b * b - (two * two) * c)%C)) as [d Hd].
  exists (((- b + d) / two)%C), (((- b - d) / two)%C).
  intro z.
  apply (Cmul_eq_reg_l ((two * two)%C)); [exact Hfour |].
  transitivity (((two * z + b) * (two * z + b) - d * d)%C).
  { rewrite Hd. unfold two. ring. }
  symmetry.
  transitivity (((two * (z - (- b + d) / two)) * (two * (z - (- b - d) / two)))%C).
  { ring. }
  assert (H1 : (two * (z - (- b + d) / two))%C = (two * z + b - d)%C)
    by (field; exact Htwo).
  assert (H2 : (two * (z - (- b - d) / two))%C = (two * z + b + d)%C)
    by (field; exact Htwo).
  rewrite H1, H2. ring.
Qed.

Lemma Cthree_neq_0 : (C1 + C1 + C1)%C <> C0.
Proof. unfold C1, C0, Cadd. cbn. intro H. inversion H. lra. Qed.

(** COMPLEX CUBIC SPLITTING: shift away the quadratic term and factor by the complex Cardano theorem. *)
Lemma Ccubic_split : forall b c d : C, exists z1 z2 z3 : C,
  forall z : C, (z * z * z + b * (z * z) + c * z + d)%C
                = ((z - z1) * ((z - z2) * (z - z3)))%C.
Proof.
  intros b c d.
  set (three := (C1 + C1 + C1)%C).
  assert (Hthree : three <> C0) by exact Cthree_neq_0.
  set (sh := (b / three)%C).
  set (P := (c - b * sh)%C).
  set (Q := ((C1 + C1) * (sh * (sh * sh)) - c * sh + d)%C).
  destruct (cardano_complex P Q) as [w1 [w2 [w3 [Hfac _]]]].
  exists ((w1 - sh)%C), ((w2 - sh)%C), ((w3 - sh)%C).
  intro z.
  pose proof (Hfac ((z + sh)%C)) as Hz.
  transitivity (Cadd (Cadd (Ccube ((z + sh)%C)) (Cmul P ((z + sh)%C))) Q).
  { unfold Ccube, P, Q, sh, three. field.
    intro H. inversion H. lra. }
  rewrite Hz. ring.
Qed.
(** The Ferrari two-quadratic factorization core: a ring identity modulo the square and resolvent relations, numerals written C1 + C1 for the ring tactic. *)
Lemma Cferrari_core : forall (z s u ya P R : C),
  (s * s)%C = (ya - P)%C ->
  ((C1 + C1) * (C1 + C1) * (u * u))%C
    = (ya * ya - (C1 + C1) * (C1 + C1) * R)%C ->
  ((z * z - s * z + ya / (C1 + C1) + u) * (z * z + s * z + ya / (C1 + C1) - u))%C
  = (z * z * (z * z) + P * (z * z) + ((C1 + C1) * (s * u)) * z + R)%C.
Proof.
  intros z s u ya P R Hs Huu.
  assert (Htwo : (C1 + C1)%C <> C0) by exact Ctwo_neq_0.
  assert (Hfour : ((C1 + C1) * (C1 + C1))%C <> C0) by (apply Cmul_neq_0; exact Htwo).
  apply (Cmul_eq_reg_l (((C1 + C1) * (C1 + C1))%C)); [exact Hfour |].
  assert (Hc1 : ((C1 + C1) * (z * z - s * z + ya / (C1 + C1) + u))%C
                = ((C1 + C1) * (z * z) - (C1 + C1) * (s * z) + ya + (C1 + C1) * u)%C)
    by (field; exact Ctwo_neq_0).
  assert (Hc2 : ((C1 + C1) * (z * z + s * z + ya / (C1 + C1) - u))%C
                = ((C1 + C1) * (z * z) + (C1 + C1) * (s * z) + ya - (C1 + C1) * u)%C)
    by (field; exact Ctwo_neq_0).
  transitivity ((((C1 + C1) * (z * z - s * z + ya / (C1 + C1) + u))
                 * ((C1 + C1) * (z * z + s * z + ya / (C1 + C1) - u)))%C); [ring |].
  rewrite Hc1, Hc2.
  transitivity (((C1 + C1) * (C1 + C1) * ((z * z) * (z * z))
                + (C1 + C1) * (C1 + C1) * (ya - s * s) * (z * z)
                + (C1 + C1) * (C1 + C1) * ((C1 + C1) * (s * u)) * z
                + (ya * ya - (C1 + C1) * (C1 + C1) * (u * u)))%C); [ring |].
  rewrite Hs, Huu. ring.
Qed.

(** COMPLEX DEPRESSED QUARTIC SPLITTING (Ferrari over C). *)
Lemma Cquartic_depressed_split : forall p q r : C, exists z1 z2 z3 z4 : C,
  forall z : C, (z * z * (z * z) + p * (z * z) + q * z + r)%C
                = ((z - z1) * ((z - z2) * ((z - z3) * (z - z4))))%C.
Proof.
  intros p q r.
  assert (Htwo : (C1 + C1)%C <> C0) by exact Ctwo_neq_0.
  assert (Hfour : ((C1 + C1) * (C1 + C1))%C <> C0) by (apply Cmul_neq_0; exact Htwo).
  destruct (Ccubic_split ((- p)%C) ((- ((C1 + C1) * (C1 + C1) * r))%C)
              (((C1 + C1) * (C1 + C1) * (p * r) - q * q)%C))
    as [ya [yb [yc Hres]]].
  assert (Hy : (ya * ya * ya + (- p) * (ya * ya)
                + (- ((C1 + C1) * (C1 + C1) * r)) * ya
                + ((C1 + C1) * (C1 + C1) * (p * r) - q * q))%C = C0)
    by (rewrite (Hres ya); ring).
  assert (Hkey : ((ya - p) * (ya * ya - (C1 + C1) * (C1 + C1) * r))%C = (q * q)%C).
  { apply Csub_eq_0.
    transitivity ((ya * ya * ya + (- p) * (ya * ya)
                   + (- ((C1 + C1) * (C1 + C1) * r)) * ya
                   + ((C1 + C1) * (C1 + C1) * (p * r) - q * q))%C);
      [ring | exact Hy]. }
  destruct (Ceq_dec ((ya - p)%C) C0) as [Hyp0 | Hypne].
  - (* degenerate: q = 0, biquadratic *)
    assert (Hq0 : q = C0).
    { assert (Hqq : (q * q)%C = C0) by (rewrite <- Hkey, Hyp0; ring).
      destruct (Cmul_integral _ _ Hqq); assumption. }
    destruct (Cquadratic_split p r) as [u1 [u2 Hw]].
    destruct (C_sqrt_exists u1) as [s1 Hs1].
    destruct (C_sqrt_exists u2) as [s2 Hs2].
    exists s1, ((- s1)%C), s2, ((- s2)%C).
    intro z.
    rewrite Hq0.
    transitivity (((z * z) * (z * z) + p * (z * z) + r)%C); [ring |].
    rewrite (Hw ((z * z)%C)).
    rewrite <- Hs1, <- Hs2. ring.
  - (* general: difference of squares through sqrt(ya - p) *)
    destruct (C_sqrt_exists ((ya - p)%C)) as [s Hs].
    assert (Hsne : s <> C0).
    { intro E. apply Hypne. rewrite <- Hs, E. ring. }
    assert (H2s : ((C1 + C1) * s)%C <> C0) by (apply Cmul_neq_0; assumption).
    set (u := (q / ((C1 + C1) * s))%C).
    assert (Hq : q = ((C1 + C1) * (s * u))%C)
      by (unfold u; field; split; [exact Hsne | intro H; inversion H; lra]).
    assert (Huu : ((C1 + C1) * (C1 + C1) * (u * u))%C
                  = (ya * ya - (C1 + C1) * (C1 + C1) * r)%C).
    { assert (Hfac : ((ya - p) * ((C1 + C1) * (C1 + C1) * (u * u)))%C
                     = ((ya - p) * (ya * ya - (C1 + C1) * (C1 + C1) * r))%C).
      { rewrite Hkey.
        transitivity ((((C1 + C1) * (s * u)) * ((C1 + C1) * (s * u)))%C).
        - rewrite <- Hs. ring.
        - rewrite <- Hq. reflexivity. }
      destruct (Ceq_dec (((C1 + C1) * (C1 + C1) * (u * u))
                         - (ya * ya - (C1 + C1) * (C1 + C1) * r))%C C0) as [E | NE].
      - apply Csub_eq_0 in E. exact E.
      - exfalso.
        assert (Hz : ((ya - p) * (((C1 + C1) * (C1 + C1) * (u * u))
                                  - (ya * ya - (C1 + C1) * (C1 + C1) * r)))%C = C0).
        { transitivity (((ya - p) * ((C1 + C1) * (C1 + C1) * (u * u)))
                        - ((ya - p) * (ya * ya - (C1 + C1) * (C1 + C1) * r)))%C;
            [ring | rewrite Hfac; ring]. }
        destruct (Cmul_integral _ _ Hz) as [E | E]; [exact (Hypne E) | exact (NE E)]. }
    pose proof (fun z0 => Cferrari_core z0 s u ya p r Hs Huu) as Hmaster.
    destruct (Cquadratic_split ((- s)%C) ((ya / (C1 + C1) + u)%C)) as [z1 [z2 Hq1]].
    destruct (Cquadratic_split s ((ya / (C1 + C1) - u)%C)) as [z3 [z4 Hq2]].
    exists z1, z2, z3, z4.
    intro z.
    rewrite Hq.
    rewrite <- (Hmaster z).
    assert (Hshape1 : (z * z - s * z + ya / (C1 + C1) + u)%C
                      = (z * z + (- s) * z + (ya / (C1 + C1) + u))%C) by ring.
    rewrite Hshape1, (Hq1 z).
    assert (Hshape2 : (z * z + s * z + ya / (C1 + C1) - u)%C
                      = (z * z + s * z + (ya / (C1 + C1) - u))%C) by ring.
    rewrite Hshape2, (Hq2 z).
    ring.
Qed.

(** COMPLEX QUARTIC SPLITTING, general coefficients, by the quarter shift. *)
Lemma Cquartic_split : forall b c d e : C, exists z1 z2 z3 z4 : C,
  forall z : C, (z * z * (z * z) + b * (z * z * z) + c * (z * z) + d * z + e)%C
                = ((z - z1) * ((z - z2) * ((z - z3) * (z - z4))))%C.
Proof.
  intros b c d e.
  assert (Hfour : ((C1 + C1) * (C1 + C1))%C <> C0)
    by (apply Cmul_neq_0; exact Ctwo_neq_0).
  set (sh := (b / ((C1 + C1) * (C1 + C1)))%C).
  set (P := ((C1 + C1 + C1 + C1 + C1 + C1) * (sh * sh)
             - (C1 + C1 + C1) * (b * sh) + c)%C).
  set (Q := (- ((C1 + C1) * (C1 + C1) * (sh * (sh * sh)))
             + (C1 + C1 + C1) * (b * (sh * sh))
             - (C1 + C1) * (c * sh) + d)%C).
  set (RR := ((sh * sh) * (sh * sh) - b * (sh * (sh * sh))
              + c * (sh * sh) - d * sh + e)%C).
  destruct (Cquartic_depressed_split P Q RR) as [w1 [w2 [w3 [w4 Hdep]]]].
  exists ((w1 - sh)%C), ((w2 - sh)%C), ((w3 - sh)%C), ((w4 - sh)%C).
  intro z.
  transitivity (((z + sh) * (z + sh) * ((z + sh) * (z + sh))
                 + P * ((z + sh) * (z + sh)) + Q * (z + sh) + RR)%C).
  { unfold P, Q, RR, sh. field.
    intro H. inversion H. lra. }
  rewrite (Hdep ((z + sh)%C)). ring.
Qed.

(** REAL QUINTIC SPLITTING OVER C: the odd-degree real root plus the four Ferrari roots of the synthetic-division quartic quotient. *)
Theorem Rquintic_split_C : forall a4 a3 a2 a1 a0 : R,
  exists (rho : R) (w1 w2 w3 w4 : C),
  forall z : C,
    (z * z * (z * z) * z + RtoC a4 * (z * z * (z * z)) + RtoC a3 * (z * z * z)
     + RtoC a2 * (z * z) + RtoC a1 * z + RtoC a0)%C
    = ((z - RtoC rho) * ((z - w1) * ((z - w2) * ((z - w3) * (z - w4)))))%C.
Proof.
  intros a4 a3 a2 a1 a0.
  destruct (odd_monic_real_root (a4 :: a3 :: a2 :: a1 :: a0 :: nil)
              ltac:(exists 2%nat; reflexivity)) as [rho Hrho].
  cbn [peval_lf length] in Hrho.
  set (b3 := a4 + rho).
  set (b2 := a3 + rho * b3).
  set (b1 := a2 + rho * b2).
  set (b0 := a1 + rho * b1).
  assert (Hrem : a0 + rho * b0 = 0).
  { unfold b0, b1, b2, b3. nra. }
  assert (HB3 : RtoC b3 = (RtoC a4 + RtoC rho)%C)
    by (unfold b3; rewrite RtoC_add; reflexivity).
  assert (HB2 : RtoC b2 = (RtoC a3 + RtoC rho * RtoC b3)%C)
    by (unfold b2 at 1; rewrite RtoC_add, RtoC_mul; reflexivity).
  assert (HB1 : RtoC b1 = (RtoC a2 + RtoC rho * RtoC b2)%C)
    by (unfold b1 at 1; rewrite RtoC_add, RtoC_mul; reflexivity).
  assert (HB0 : RtoC b0 = (RtoC a1 + RtoC rho * RtoC b1)%C)
    by (unfold b0 at 1; rewrite RtoC_add, RtoC_mul; reflexivity).
  destruct (Cquartic_split (RtoC b3) (RtoC b2) (RtoC b1) (RtoC b0))
    as [w1 [w2 [w3 [w4 Hq]]]].
  exists rho, w1, w2, w3, w4.
  intro z.
  assert (Hmaster :
    (z * z * (z * z) * z + RtoC a4 * (z * z * (z * z)) + RtoC a3 * (z * z * z)
     + RtoC a2 * (z * z) + RtoC a1 * z + RtoC a0)%C
    = ((z - RtoC rho)
       * (z * z * (z * z) + RtoC b3 * (z * z * z) + RtoC b2 * (z * z)
          + RtoC b1 * z + RtoC b0)
       + RtoC (a0 + rho * b0))%C).
  { rewrite RtoC_add, RtoC_mul, HB0, HB1, HB2, HB3. ring. }
  rewrite Hmaster, Hrem, C0_eq.
  rewrite (Hq z). ring.
Qed.

(* Galois keystone: evaluation identities become coefficient identities (a polynomial function vanishing on R has zero coefficients), transporting the division facts through RtoC. *)

Lemma peval_lf_zero_coeffs : forall p : list R,
  (forall x, peval_lf p x = 0) -> Forall (fun c => c = 0) p.
Proof.
  induction p as [|a p' IH]; intro Hall.
  - constructor.
  - assert (Ha : a = 0).
    { destruct (Req_dec a 0) as [E | Hne]; [exact E | exfalso].
      set (M := 1 + sum_abs p' / Rabs a).
      assert (Habs : 0 < Rabs a) by (apply Rabs_pos_lt; exact Hne).
      assert (HS : 0 <= sum_abs p') by apply sum_abs_nonneg.
      assert (HM1 : 1 <= M) by (unfold M; pose proof (Rmult_le_pos (sum_abs p') (/ Rabs a)); unfold Rdiv in *; pose proof (Rlt_le _ _ (Rinv_0_lt_compat _ Habs)); nra).
      pose proof (Hall M) as HM.
      cbn [peval_lf] in HM.
      assert (Hb : Rabs (peval_lf p' M) <= sum_abs p' * Rabs M ^ (length p' - 1)).
      { apply peval_lf_abs_bound. rewrite Rabs_right by lra. lra. }
      rewrite (Rabs_right M) in Hb by lra.
      assert (HMp : a * M ^ (length p') = - peval_lf p' M) by lra.
      assert (Hup : Rabs (a * M ^ (length p')) <= sum_abs p' * M ^ (length p' - 1)).
      { rewrite HMp, Rabs_Ropp. exact Hb. }
      rewrite Rabs_mult in Hup.
      rewrite (Rabs_right (M ^ (length p'))) in Hup
        by (apply Rle_ge, pow_le; lra).
      destruct (length p') as [|k] eqn:Ek.
      - apply length_zero_iff_nil in Ek. subst p'.
        cbn [peval_lf] in HMp. cbn [pow] in HMp.
        apply Hne. lra.
      - replace (Datatypes.S k - 1)%nat with k in Hup by lia.
        cbn [pow] in Hup.
        assert (Hpk : 0 < M ^ k) by (apply pow_lt; lra).
        assert (Hchain : Rabs a * M <= sum_abs p').
        { apply (Rmult_le_reg_r (M ^ k)); [exact Hpk | nra]. }
        unfold M in Hchain. unfold Rdiv in Hchain.
        assert (Hfin : Rabs a * (1 + sum_abs p' * / Rabs a)
                       = Rabs a + sum_abs p') by (field; lra).
        nra. }
    subst a.
    constructor; [reflexivity |].
    apply IH. intro x.
    pose proof (Hall x) as Hx. cbn [peval_lf] in Hx. lra.
Qed.

(** Equal-length lists with the same polynomial function are equal. *)
Lemma peval_lf_ext_coeffs : forall p q : list R, length p = length q ->
  (forall x, peval_lf p x = peval_lf q x) ->
  p = q.
Proof.
  induction p as [|a p' IH]; intros q Hlen Hall.
  - destruct q; [reflexivity | cbn [length] in Hlen; lia].
  - destruct q as [|b q']; [cbn [length] in Hlen; lia |].
    cbn [length] in Hlen.
    assert (Hq : length q' = length p') by lia.
    assert (Hdiff : Forall (fun c => c = 0)
                      (paddR (a :: p') (pscaleR (-1) (b :: q')))).
    { apply peval_lf_zero_coeffs. intro x.
      rewrite (peval_lf_psub_top (b :: q') (a :: p') x)
        by (cbn [length]; lia).
      cbn [length].
      replace (Datatypes.S (length p') - Datatypes.S (length q'))%nat
        with 0%nat by lia.
      cbn [pow]. rewrite (Hall x). ring. }
    rewrite pscaleR_cons in Hdiff. cbn [paddR] in Hdiff.
    inversion Hdiff; subst.
    assert (Hab : a = b) by lra.
    assert (Hdiff' : Forall (fun c => c = 0) (paddR p' (pscaleR (-1) q'))).
    { assumption. }
    assert (Hp'q' : p' = q').
    { apply IH; [lia |].
      intro x.
      pose proof (peval_lf_psub_top q' p' x ltac:(lia)) as Hsub.
      rewrite (peval_lf_zero _ x Hdiff') in Hsub.
      replace (length p' - length q')%nat with 0%nat in Hsub by lia.
      cbn [pow] in Hsub. lra. }
    rewrite Hab, Hp'q'. reflexivity.
Qed.

(** Complex evaluation of a real-coefficient list, leading-first. *)
Fixpoint Cpow (z : C) (n : nat) : C :=
  match n with O => C1 | Datatypes.S n' => (z * Cpow z n')%C end.

Fixpoint Ceval_lf (p : list R) (z : C) : C :=
  match p with
  | nil => C0
  | a :: p' => (RtoC a * Cpow z (length p') + Ceval_lf p' z)%C
  end.

Lemma Cpow_RtoC : forall (x : R) n, Cpow (RtoC x) n = RtoC (x ^ n).
Proof.
  intros x n. induction n as [|n IH]; cbn [Cpow pow].
  - reflexivity.
  - rewrite IH, RtoC_mul. reflexivity.
Qed.

(** At real points, complex evaluation is the real evaluation. *)
Lemma Ceval_lf_RtoC : forall p (x : R), Ceval_lf p (RtoC x) = RtoC (peval_lf p x).
Proof.
  induction p as [|a p' IH]; intro x; cbn [Ceval_lf peval_lf].
  - reflexivity.
  - rewrite IH, Cpow_RtoC, RtoC_add, RtoC_mul. reflexivity.
Qed.

Lemma Ceval_lf_app : forall p q z,
  Ceval_lf (p ++ q) z = (Ceval_lf p z * Cpow z (length q) + Ceval_lf q z)%C.
Proof.
  induction p as [|a p' IH]; intros q z.
  - cbn [app Ceval_lf]. ring.
  - cbn [app Ceval_lf]. rewrite IH, length_app.
    assert (Hpow : Cpow z (length p' + length q)
                   = (Cpow z (length p') * Cpow z (length q))%C).
    { induction (length p') as [|k IHk]; cbn [Cpow Nat.add].
      - ring.
      - rewrite IHk. ring. }
    rewrite Hpow. ring.
Qed.

(* Galois keystone: divisibility transports to complex points -- CevalR is a ring homomorphism, so real product identities hold at every complex point and complex roots distribute over minimal-relation factors. *)

Fixpoint CevalR (p : list R) (z : C) : C :=
  match p with
  | nil => C0
  | c :: p' => (RtoC c + z * CevalR p' z)%C
  end.

Lemma CevalR_RtoC : forall p (x : R), CevalR p (RtoC x) = RtoC (pevalR p x).
Proof.
  induction p as [|c p' IH]; intro x; cbn [CevalR pevalR].
  - reflexivity.
  - rewrite IH, RtoC_add, RtoC_mul. reflexivity.
Qed.

Lemma CevalR_padd : forall ps qs z,
  CevalR (paddR ps qs) z = (CevalR ps z + CevalR qs z)%C.
Proof.
  induction ps as [|p ps' IH]; intros qs z.
  - cbn [paddR CevalR]. ring.
  - destruct qs as [|q qs'].
    + cbn [paddR CevalR]. ring.
    + cbn [paddR CevalR]. rewrite IH, RtoC_add. ring.
Qed.

Lemma CevalR_pscale : forall a ps z,
  CevalR (pscaleR a ps) z = (RtoC a * CevalR ps z)%C.
Proof.
  induction ps as [|p ps' IH]; intro z.
  - cbn [pscaleR map CevalR]. ring.
  - rewrite pscaleR_cons. cbn [CevalR]. rewrite IH, RtoC_mul. ring.
Qed.

Lemma CevalR_pmul : forall ps qs z,
  CevalR (pmulR ps qs) z = (CevalR ps z * CevalR qs z)%C.
Proof.
  induction ps as [|p ps' IH]; intros qs z.
  - cbn [pmulR CevalR]. ring.
  - cbn [pmulR]. rewrite CevalR_padd, CevalR_pscale.
    cbn [CevalR]. rewrite IH.
    replace (RtoC 0) with C0 by reflexivity. ring.
Qed.


Lemma CevalR_app : forall (l1 l2 : list R) z,
  CevalR (l1 ++ l2) z = (CevalR l1 z + Cpow z (length l1) * CevalR l2 z)%C.
Proof.
  induction l1 as [|a l1' IH]; intros l2 z.
  - cbn [app CevalR length Cpow]. ring.
  - cbn [app CevalR length Cpow]. rewrite IH. ring.
Qed.

(** Leading-first complex evaluation is constant-first evaluation of the reversal. *)
Lemma Ceval_lf_rev : forall p z, Ceval_lf p z = CevalR (rev p) z.
Proof.
  induction p as [|a p' IH]; intro z.
  - reflexivity.
  - cbn [Ceval_lf rev]. rewrite CevalR_app, IH, length_rev.
    cbn [CevalR]. ring.
Qed.

Lemma pmulR_cons : forall (x : R) (a b : list R),
  pmulR (x :: a) b = paddR (pscaleR x b) (0 :: pmulR a b).
Proof. reflexivity. Qed.

Lemma pmulR_length : forall (a b : list R),
  (1 <= length a)%nat -> (1 <= length b)%nat ->
  length (pmulR a b) = (length a + length b - 1)%nat.
Proof.
  induction a as [|x a' IHa]; intros b Ha Hb.
  - cbn [length] in Ha. lia.
  - rewrite pmulR_cons, paddR_length, pscaleR_length.
    cbn [length].
    destruct a' as [|y a''].
    + cbn [pmulR length]. lia.
    + rewrite (IHa b) by (cbn [length]; lia).
      cbn [length]. lia.
Qed.

(** THE COMPLEX TRANSPORT: a real product identity at every real point holds at every complex point. *)
Theorem Ceval_lf_of_real_identity : forall (g q m : list R),
  (forall x : R, peval_lf g x = peval_lf q x * peval_lf m x) ->
  length g = (length q + length m - 1)%nat ->
  (1 <= length q)%nat -> (1 <= length m)%nat ->
  forall z : C, Ceval_lf g z = (Ceval_lf q z * Ceval_lf m z)%C.
Proof.
  intros g q m Hid Hlen Hq1 Hm1 z.
  set (prod_cf := pmulR (rev q) (rev m)).
  assert (Hprodlen : length prod_cf = (length q + length m - 1)%nat).
  { unfold prod_cf.
    rewrite pmulR_length by (rewrite length_rev; lia).
    rewrite !length_rev. reflexivity. }
  assert (Hgeq : g = rev prod_cf).
  { apply peval_lf_ext_coeffs.
    - rewrite length_rev, Hprodlen. exact Hlen.
    - intro x. rewrite <- pevalR_rev. unfold prod_cf.
      rewrite pevalR_pmul, !pevalR_rev, !rev_involutive.
      apply Hid. }
  rewrite Hgeq.
  rewrite Ceval_lf_rev, rev_involutive.
  unfold prod_cf. rewrite CevalR_pmul.
  rewrite <- (rev_involutive q) at 2. rewrite <- (rev_involutive m) at 2.
  rewrite !Ceval_lf_rev, !rev_involutive.
  reflexivity.
Qed.

(* Galois keystone: embeddings of a subfield into C and their evaluators -- the CevalR homomorphism lemmas with the embedding in place of RtoC. *)

Definition Cembeds (F : R -> Prop) (sigma : R -> C) : Prop :=
  sigma 0 = C0 /\ sigma 1 = C1 /\
  (forall x y, F x -> F y -> sigma (x + y) = (sigma x + sigma y)%C) /\
  (forall x y, F x -> F y -> sigma (x * y) = (sigma x * sigma y)%C).

Lemma Cembeds_RtoC : forall F, Cembeds F RtoC.
Proof.
  intro F. repeat split.
  - intros x y _ _. apply RtoC_add.
  - intros x y _ _. apply RtoC_mul.
Qed.

Fixpoint CevalMap (f : R -> C) (p : list R) (z : C) : C :=
  match p with
  | nil => C0
  | c :: p' => (f c + z * CevalMap f p' z)%C
  end.

Lemma CevalMap_RtoC : forall p z, CevalMap RtoC p z = CevalR p z.
Proof.
  induction p as [|c p' IH]; intro z; cbn [CevalMap CevalR].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma CevalMap_padd : forall (F : R -> Prop) sigma, Cembeds F sigma ->
  forall ps qs z, Forall F ps -> Forall F qs ->
  CevalMap sigma (paddR ps qs) z = (CevalMap sigma ps z + CevalMap sigma qs z)%C.
Proof.
  intros F sigma [H0 [H1 [Hadd Hmul]]].
  induction ps as [|p ps' IH]; intros qs z Hps Hqs.
  - cbn [paddR CevalMap]. ring.
  - destruct qs as [|q qs'].
    + cbn [paddR CevalMap]. ring.
    + cbn [paddR CevalMap].
      inversion Hps; subst. inversion Hqs; subst.
      rewrite IH by assumption.
      rewrite Hadd by assumption. ring.
Qed.

Lemma CevalMap_pscale : forall (F : R -> Prop) sigma, Cembeds F sigma ->
  forall a ps z, F a -> Forall F ps ->
  CevalMap sigma (pscaleR a ps) z = (sigma a * CevalMap sigma ps z)%C.
Proof.
  intros F sigma [H0 [H1 [Hadd Hmul]]].
  induction ps as [|p ps' IH]; intros z Ha Hps.
  - cbn [pscaleR map CevalMap]. ring.
  - rewrite pscaleR_cons. cbn [CevalMap].
    inversion Hps; subst.
    rewrite IH by assumption.
    rewrite Hmul by assumption. ring.
Qed.

Lemma CevalMap_pmul : forall (F : R -> Prop) sigma, Cembeds F sigma ->
  (forall x y, F x -> F y -> F (x + y)) ->
  (forall x y, F x -> F y -> F (x * y)) ->
  F 0 ->
  forall ps qs z, Forall F ps -> Forall F qs ->
  CevalMap sigma (pmulR ps qs) z = (CevalMap sigma ps z * CevalMap sigma qs z)%C.
Proof.
  intros F sigma Hemb HFadd HFmul HF0.
  pose proof Hemb as [Hs0 [Hs1 [Hsadd Hsmul]]].
  induction ps as [|p ps' IH]; intros qs z Hps Hqs.
  - cbn [pmulR CevalMap]. ring.
  - rewrite pmulR_cons.
    inversion Hps; subst.
    assert (Hscale : Forall F (pscaleR p qs))
      by (apply Forall_pscaleR; assumption).
    assert (Htail : Forall F (0 :: pmulR ps' qs))
      by (constructor; [exact HF0 | apply Forall_pmulR; assumption]).
    rewrite (CevalMap_padd F sigma Hemb _ _ z Hscale Htail).
    rewrite (CevalMap_pscale F sigma Hemb) by assumption.
    cbn [CevalMap].
    rewrite IH by assumption.
    rewrite Hs0. ring.
Qed.

Lemma CevalMap_app : forall (f : R -> C) (l1 l2 : list R) z,
  CevalMap f (l1 ++ l2) z
  = (CevalMap f l1 z + Cpow z (length l1) * CevalMap f l2 z)%C.
Proof.
  induction l1 as [|a l1' IH]; intros l2 z.
  - cbn [app CevalMap length Cpow]. ring.
  - cbn [app CevalMap length Cpow]. rewrite IH. ring.
Qed.

Lemma CevalMap_zeros : forall (sigma : R -> C), sigma 0 = C0 ->
  forall n z, CevalMap sigma (repeat 0 n) z = C0.
Proof.
  intros sigma Hs0. induction n as [|n IH]; intro z; cbn [repeat CevalMap].
  - reflexivity.
  - rewrite Hs0, IH. ring.
Qed.

(** Constant-first lists of equal length with the same polynomial function are equal. *)
Lemma pevalR_ext_coeffs : forall p q : list R, length p = length q ->
  (forall x, pevalR p x = pevalR q x) ->
  p = q.
Proof.
  intros p q Hlen Hall.
  rewrite <- (rev_involutive p), <- (rev_involutive q).
  f_equal.
  apply peval_lf_ext_coeffs; [rewrite !length_rev; exact Hlen |].
  intro x. rewrite <- !pevalR_rev. apply Hall.
Qed.

(** UNIQUE REPRESENTATION: independence of the powers of beta below j forces the length-j F-coefficient representation to be unique. *)
Lemma PolyF_unique_rep : forall (F : R -> Prop) (beta : R) (j : nat),
  is_subfield F ->
  lin_indep F (powers beta j) ->
  forall cs ds : list R, length cs = j -> length ds = j ->
  Forall F cs -> Forall F ds ->
  pevalR cs beta = pevalR ds beta ->
  cs = ds.
Proof.
  intros F beta j HF Hindep cs ds Hlc Hld HFc HFd Hev.
  set (e := paddR cs (pscaleR (-1) ds)).
  assert (Hle : length e = j)
    by (unfold e; rewrite paddR_length, pscaleR_length; lia).
  assert (HFe : Forall F e).
  { unfold e. apply Forall_paddR;
      [intros a b Ha Hb; apply (subfield_add F a b HF Ha Hb) | exact HFc |].
    apply Forall_pscaleR;
      [intros a b Ha Hb; apply (subfield_mul F a b HF Ha Hb) | | exact HFd].
    apply (subfield_opp F 1 HF (subfield_1 F HF)). }
  assert (Heval : pevalR e beta = 0).
  { unfold e. rewrite pevalR_padd, pevalR_pscale, Hev. ring. }
  assert (Hzero : Forall (fun z => z = 0) e).
  { apply Hindep.
    - rewrite powers_length. exact Hle.
    - exact HFe.
    - replace j with (length e) by exact Hle.
      rewrite Fcomb_powers_pevalR. exact Heval. }
  unfold e in Hzero.
  assert (Hlen2 : length cs = length ds) by lia.
  clear - Hzero Hlen2.
  revert ds Hlen2 Hzero.
  induction cs as [|a cs' IH]; intros ds Hlen2 Hzero.
  - destruct ds; [reflexivity | cbn [length] in Hlen2; lia].
  - destruct ds as [|b ds']; [cbn [length] in Hlen2; lia |].
    rewrite pscaleR_cons in Hzero. cbn [paddR] in Hzero.
    inversion Hzero; subst.
    cbn [length] in Hlen2.
    f_equal; [lra |].
    apply IH; [lia | assumption].
Qed.

(** THE REDUCTION LEMMA: division by the minimal relation collapses identically under the sigma-w evaluation and under real evaluation at beta, leaving the remainder on both sides. *)
Lemma CevalMap_reduction : forall (F : R -> Prop) (sigma : R -> C),
  Cembeds F sigma -> is_subfield F ->
  forall (j : nat) (c : nat -> R) (beta : R) (w : C), (1 <= j)%nat ->
  (forall i, (i < j)%nat -> F (c i)) ->
  fsum j (fun i => c i * beta ^ i) + beta ^ j = 0 ->
  (CevalMap sigma (map c (seq 0 j)) w + Cpow w j)%C = C0 ->
  forall g : list R, Forall F g ->
  Forall F (snd (pdiv_lf (length (rev g)) (rev g) (rev (map c (seq 0 j))))) /\
  (length (snd (pdiv_lf (length (rev g)) (rev g) (rev (map c (seq 0 j))))) <= j)%nat /\
  pevalR g beta
    = peval_lf (snd (pdiv_lf (length (rev g)) (rev g) (rev (map c (seq 0 j))))) beta /\
  CevalMap sigma g w
    = CevalMap sigma
        (rev (snd (pdiv_lf (length (rev g)) (rev g) (rev (map c (seq 0 j)))))) w.
Proof.
  intros F sigma Hemb HF j c beta w Hj Hc Hrel Hw g HFg.
  pose proof Hemb as [Hs0 [Hs1 [Hsadd Hsmul]]].
  set (dt := rev (map c (seq 0 j))) in *.
  assert (Hlen_dt : length dt = j)
    by (unfold dt; rewrite length_rev, length_map, length_seq; reflexivity).
  assert (HFdt : Forall F dt).
  { unfold dt. apply Forall_rev.
    apply Forall_forall. intros z Hz.
    apply in_map_iff in Hz. destruct Hz as [i [Hzi Hin]].
    apply in_seq in Hin. subst z. apply Hc. lia. }
  assert (HFrevg : Forall F (rev g)) by (apply Forall_rev; exact HFg).
  set (q := fst (pdiv_lf (length (rev g)) (rev g) dt)) in *.
  set (r := snd (pdiv_lf (length (rev g)) (rev g) dt)) in *.
  destruct (pdiv_lf_Forall F (length (rev g)) (rev g) dt
              (fun a b Ha Hb => subfield_add F a b HF Ha Hb)
              (fun a b Ha Hb => subfield_mul F a b HF Ha Hb)
              (subfield_opp F 1 HF (subfield_1 F HF)) HFrevg HFdt) as [HFq HFr].
  pose proof (pdiv_lf_rlen (length (rev g)) (rev g) dt (Nat.le_refl _)) as Hrlen.
  rewrite Hlen_dt in Hrlen.
  pose proof (pdiv_lf_eval (length (rev g)) (rev g) dt (Nat.le_refl _)) as Hspec.
  rewrite Hlen_dt in Hspec.
  fold q r in Hspec, HFq, HFr, Hrlen.
  assert (Hdt_eval : forall y, peval_lf dt y = fsum j (fun i => c i * y ^ i)).
  { intro y. unfold dt. rewrite <- pevalR_rev. apply pevalR_map_seq. }
  split; [exact HFr | split; [exact Hrlen | split]].
  - (* real evaluation at beta *)
    pose proof (Hspec beta) as Hb.
    rewrite Hdt_eval in Hb.
    assert (Hz : beta ^ j + fsum j (fun i => c i * beta ^ i) = 0) by lra.
    rewrite Hz in Hb.
    rewrite pevalR_rev. lra.
  - (* sigma-w evaluation *)
    set (Mcf := map c (seq 0 j) ++ 1 :: nil).
    assert (HlenM : length Mcf = Datatypes.S j)
      by (unfold Mcf; rewrite length_app, length_map, length_seq; cbn [length]; lia).
    assert (HFM : Forall F Mcf).
    { unfold Mcf. apply Forall_app_intro.
      - apply Forall_forall. intros z Hz.
        apply in_map_iff in Hz. destruct Hz as [i [Hzi Hin]].
        apply in_seq in Hin. subst z. apply Hc. lia.
      - constructor; [apply (subfield_1 F HF) | constructor]. }
    assert (HMw : CevalMap sigma Mcf w = C0).
    { unfold Mcf. rewrite CevalMap_app.
      rewrite length_map, length_seq.
      cbn [CevalMap]. rewrite Hs1.
      transitivity ((CevalMap sigma (map c (seq 0 j)) w + Cpow w j)%C);
        [ring | exact Hw]. }
    set (pad := repeat 0 (length g - length r)).
    assert (HFpad : Forall F pad).
    { apply Forall_forall. intros z Hz.
      apply repeat_spec in Hz. subst z. apply (subfield_0 F HF). }
    assert (Hrg : (length r <= length g)%nat).
    { pose proof (pdiv_lf_rlen (length (rev g)) (rev g) dt (Nat.le_refl _)) as H2.
      fold r in H2.
      destruct (le_lt_dec (length (rev g)) (length dt)) as [Hle | Hgt].
      - unfold r. cbn.
        assert (Hnodiv : pdiv_lf (length (rev g)) (rev g) dt = (nil, rev g)).
        { destruct (length (rev g)) as [|f] eqn:Ef.
          - cbn [pdiv_lf].
            destruct (rev g); [reflexivity | cbn [length] in Ef; lia].
          - cbn [pdiv_lf].
            destruct (Nat.leb_spec (length (rev g)) (length dt)) as [_ | Habs];
              [reflexivity | lia]. }
        rewrite Hnodiv. cbn [snd]. rewrite length_rev. lia.
      - rewrite length_rev in Hgt. lia. }
    assert (Hcoeff : g = paddR (pmulR (rev q) Mcf) (rev r ++ pad)).
    { apply pevalR_ext_coeffs.
      - unfold pad.
        rewrite paddR_length, length_app, length_rev, repeat_length.
        pose proof (pdiv_lf_qlen (length (rev g)) (rev g) dt (Nat.le_refl _)) as Hql.
        fold q in Hql. rewrite Hlen_dt, length_rev in Hql.
        destruct (le_lt_dec (length g) j) as [Hle | Hgt].
        + assert (Hq0 : length (rev q) = 0%nat) by (rewrite length_rev; lia).
          apply length_zero_iff_nil in Hq0. rewrite Hq0.
          cbn [pmulR length]. lia.
        + rewrite pmulR_length by (rewrite ?length_rev, ?HlenM; lia).
          rewrite length_rev, HlenM, Hql. lia.
      - intro x. unfold pad.
        rewrite pevalR_padd, pevalR_pmul, pevalR_app, pevalR_repeat0.
        assert (HMx : pevalR Mcf x = x ^ j + peval_lf dt x).
        { unfold Mcf. rewrite pevalR_app, length_map, length_seq.
          cbn [pevalR]. rewrite pevalR_map_seq, Hdt_eval. ring. }
        rewrite HMx.
        assert (Hqx : pevalR (rev q) x = peval_lf q x)
          by (rewrite pevalR_rev, rev_involutive; reflexivity).
        assert (Hrx : pevalR (rev r) x = peval_lf r x)
          by (rewrite pevalR_rev, rev_involutive; reflexivity).
        rewrite Hqx, Hrx.
        pose proof (Hspec x) as Hx.
        rewrite pevalR_rev. lra. }
    rewrite Hcoeff.
    rewrite (CevalMap_padd F sigma Hemb).
    + rewrite (CevalMap_pmul F sigma Hemb
                 (fun a b Ha Hb => subfield_add F a b HF Ha Hb)
                 (fun a b Ha Hb => subfield_mul F a b HF Ha Hb)
                 (subfield_0 F HF));
        [| apply Forall_rev; exact HFq | exact HFM].
      rewrite HMw.
      rewrite CevalMap_app.
      unfold pad. rewrite (CevalMap_zeros sigma Hs0).
      ring.
    + apply Forall_pmulR;
        [ intros a b Ha Hb; apply (subfield_add F a b HF Ha Hb)
        | intros a b Ha Hb; apply (subfield_mul F a b HF Ha Hb)
        | apply (subfield_0 F HF)
        | apply Forall_rev; exact HFq
        | exact HFM ].
    + apply Forall_app_intro; [apply Forall_rev; exact HFr | exact HFpad].
Qed.

Lemma Forall_map_seq : forall (F : R -> Prop) (cf : nat -> R) (j : nat),
  (forall i, (i < j)%nat -> F (cf i)) -> Forall F (map cf (seq 0 j)).
Proof.
  intros F cf j Hcf. apply Forall_forall. intros z Hz.
  apply in_map_iff in Hz. destruct Hz as [i [Hzi Hin]].
  apply in_seq in Hin. subst z. apply Hcf. lia.
Qed.

Lemma Forall_nth_F : forall (F : R -> Prop) (cs : list R) (i : nat),
  Forall F cs -> (i < length cs)%nat -> F (nth i cs 0).
Proof.
  intros F cs i HF Hi.
  apply (proj1 (Forall_forall F cs) HF).
  apply nth_In. exact Hi.
Qed.

(** THE EMBEDDING EXTENSION THEOREM: an embedding of F extends to F(beta) by sending beta to any complex root of the image of the minimal relation. *)
Theorem Cembeds_extend_step :
  forall (F : R -> Prop) (beta : R) (j : nat) (c : nat -> R)
         (sigma : R -> C) (w : C),
  is_subfield F -> (2 <= j)%nat ->
  (forall i, (i < j)%nat -> F (c i)) ->
  fsum j (fun i => c i * beta ^ i) + beta ^ j = 0 ->
  lin_indep F (powers beta j) ->
  Cembeds F sigma ->
  (CevalMap sigma (map c (seq 0 j)) w + Cpow w j)%C = C0 ->
  exists sigma' : R -> C,
    Cembeds (PolyF F j beta) sigma' /\
    (forall x, F x -> sigma' x = sigma x) /\
    sigma' beta = w.
Proof.
  intros F beta j c sigma w HF Hj Hc Hrel Hindep Hemb Hw.
  pose proof Hemb as [Hs0 [Hs1 [Hsadd Hsmul]]].
  assert (Hj1 : (1 <= j)%nat) by lia.
  assert (Hrepex : forall x, PolyF F j beta x ->
    exists! cs : list R, length cs = j /\ Forall F cs /\ x = pevalR cs beta).
  { intros x [cf [Hcf Hx]].
    exists (map cf (seq 0 j)).
    split.
    - split; [rewrite length_map, length_seq; reflexivity |].
      split; [apply Forall_map_seq; exact Hcf |].
      rewrite pevalR_map_seq. exact Hx.
    - intros ds [Hld [HFd Hevd]].
      apply (PolyF_unique_rep F beta j HF Hindep);
        [rewrite length_map, length_seq; reflexivity | exact Hld
         | apply Forall_map_seq; exact Hcf | exact HFd |].
      rewrite pevalR_map_seq, <- Hx. exact Hevd. }
  set (sigma' := fun x : R =>
    match excluded_middle_informative (PolyF F j beta x) with
    | left H => CevalMap sigma
        (proj1_sig (constructive_definite_description _ (Hrepex x H))) w
    | right _ => C0
    end).
  assert (Hchar : forall x (cs : list R), length cs = j -> Forall F cs ->
            x = pevalR cs beta -> sigma' x = CevalMap sigma cs w).
  { intros x cs Hl HFcs Hx.
    unfold sigma'.
    destruct (excluded_middle_informative (PolyF F j beta x)) as [Hin | Hout].
    - destruct (constructive_definite_description _ (Hrepex x Hin))
        as [ds [Hld [HFd Hevd]]].
      cbn [proj1_sig].
      assert (Heq : ds = cs).
      { apply (PolyF_unique_rep F beta j HF Hindep);
          [exact Hld | exact Hl | exact HFd | exact HFcs |].
        rewrite <- Hevd, <- Hx. reflexivity. }
      rewrite Heq. reflexivity.
    - exfalso. apply Hout.
      exists (fun i => nth i cs 0).
      split.
      + intros i Hi. apply Forall_nth_F; [exact HFcs | lia].
      + rewrite Hx, pevalR_nth_sum, Hl. reflexivity. }
  exists sigma'.
  assert (Hzero_rep : sigma' 0 = C0).
  { rewrite (Hchar 0 (repeat 0 j)).
    - apply (CevalMap_zeros sigma Hs0).
    - apply repeat_length.
    - apply Forall_forall. intros z Hz.
      apply repeat_spec in Hz. subst z. apply (subfield_0 F HF).
    - rewrite pevalR_repeat0. reflexivity. }
  assert (Hagree : forall x, F x -> sigma' x = sigma x).
  { intros x Hx.
    rewrite (Hchar x (x :: repeat 0 (j - 1))).
    - cbn [CevalMap]. rewrite (CevalMap_zeros sigma Hs0). ring.
    - cbn [length]. rewrite repeat_length. lia.
    - constructor; [exact Hx |].
      apply Forall_forall. intros z Hz.
      apply repeat_spec in Hz. subst z. apply (subfield_0 F HF).
    - cbn [pevalR]. rewrite pevalR_repeat0. ring. }
  split; [| split].
  - (* Cembeds (PolyF F j beta) sigma' *)
    split; [exact Hzero_rep |].
    split.
    { rewrite (Hagree 1 (subfield_1 F HF)). exact Hs1. }
    split.
    + (* additivity *)
      intros x y Hx Hy.
      destruct Hx as [cf [Hcf Hxe]]. destruct Hy as [df [Hdf Hye]].
      set (csx := map cf (seq 0 j)). set (csy := map df (seq 0 j)).
      assert (Hlx : length csx = j) by (unfold csx; rewrite length_map, length_seq; reflexivity).
      assert (Hly : length csy = j) by (unfold csy; rewrite length_map, length_seq; reflexivity).
      assert (HFx : Forall F csx) by (apply Forall_map_seq; exact Hcf).
      assert (HFy : Forall F csy) by (apply Forall_map_seq; exact Hdf).
      assert (Hxr : x = pevalR csx beta) by (unfold csx; rewrite pevalR_map_seq; exact Hxe).
      assert (Hyr : y = pevalR csy beta) by (unfold csy; rewrite pevalR_map_seq; exact Hye).
      rewrite (Hchar (x + y) (paddR csx csy)).
      * rewrite (CevalMap_padd F sigma Hemb _ _ w HFx HFy).
        rewrite (Hchar x csx Hlx HFx Hxr), (Hchar y csy Hly HFy Hyr).
        reflexivity.
      * rewrite paddR_length. lia.
      * apply Forall_paddR;
          [intros a b Ha Hb; apply (subfield_add F a b HF Ha Hb) | exact HFx | exact HFy].
      * rewrite pevalR_padd, <- Hxr, <- Hyr. reflexivity.
    + (* multiplicativity *)
      intros x y Hx Hy.
      destruct Hx as [cf [Hcf Hxe]]. destruct Hy as [df [Hdf Hye]].
      set (csx := map cf (seq 0 j)). set (csy := map df (seq 0 j)).
      assert (Hlx : length csx = j) by (unfold csx; rewrite length_map, length_seq; reflexivity).
      assert (Hly : length csy = j) by (unfold csy; rewrite length_map, length_seq; reflexivity).
      assert (HFx : Forall F csx) by (apply Forall_map_seq; exact Hcf).
      assert (HFy : Forall F csy) by (apply Forall_map_seq; exact Hdf).
      assert (Hxr : x = pevalR csx beta) by (unfold csx; rewrite pevalR_map_seq; exact Hxe).
      assert (Hyr : y = pevalR csy beta) by (unfold csy; rewrite pevalR_map_seq; exact Hye).
      set (g := pmulR csx csy).
      assert (HFg : Forall F g).
      { unfold g. apply Forall_pmulR;
          [intros a b Ha Hb; apply (subfield_add F a b HF Ha Hb)
          | intros a b Ha Hb; apply (subfield_mul F a b HF Ha Hb)
          | apply (subfield_0 F HF) | exact HFx | exact HFy]. }
      destruct (CevalMap_reduction F sigma Hemb HF j c beta w Hj1 Hc Hrel Hw g HFg)
        as [HFr [Hrlen [Hreal Hcplx]]].
      set (r := snd (pdiv_lf (length (rev g)) (rev g) (rev (map c (seq 0 j))))) in *.
      rewrite (Hchar (x * y) (rev r ++ repeat 0 (j - length r))).
      * rewrite CevalMap_app.
        rewrite (CevalMap_zeros sigma Hs0).
        rewrite (Hchar x csx Hlx HFx Hxr), (Hchar y csy Hly HFy Hyr).
        transitivity (CevalMap sigma (rev r) w); [ring |].
        rewrite <- Hcplx. unfold g.
        rewrite (CevalMap_pmul F sigma Hemb
                   (fun a b Ha Hb => subfield_add F a b HF Ha Hb)
                   (fun a b Ha Hb => subfield_mul F a b HF Ha Hb)
                   (subfield_0 F HF) _ _ w HFx HFy).
        reflexivity.
      * rewrite length_app, length_rev, repeat_length. lia.
      * apply Forall_app_intro; [apply Forall_rev; exact HFr |].
        apply Forall_forall. intros z Hz.
        apply repeat_spec in Hz. subst z. apply (subfield_0 F HF).
      * rewrite pevalR_app, pevalR_repeat0.
        rewrite pevalR_rev, rev_involutive.
        rewrite <- Hreal.
        unfold g. rewrite pevalR_pmul, <- Hxr, <- Hyr. ring.
  - exact Hagree.
  - (* sigma' beta = w *)
    rewrite (Hchar beta (0 :: 1 :: repeat 0 (j - 2))).
    + cbn [CevalMap]. rewrite (CevalMap_zeros sigma Hs0), Hs0, Hs1. ring.
    + cbn [length]. rewrite repeat_length. lia.
    + constructor; [apply (subfield_0 F HF) |].
      constructor; [apply (subfield_1 F HF) |].
      apply Forall_forall. intros z Hz.
      apply repeat_spec in Hz. subst z. apply (subfield_0 F HF).
    + cbn [pevalR]. rewrite pevalR_repeat0. ring.
Qed.

(* Galois keystone: extended Euclid over a predicate subfield on leading-first lists -- Bezout certifies gcds, and an irreducible with a root forces independent lower powers. *)

(** Strip leading zeros of a leading-first list. *)
Fixpoint lnorm (p : list R) : list R :=
  match p with
  | nil => nil
  | a :: p' => if Req_EM_T a 0 then lnorm p' else p
  end.

Lemma lnorm_eval : forall p x, peval_lf (lnorm p) x = peval_lf p x.
Proof. exact (klnorm_eval _ _ _ _ _ _ _ _ _ RealField.Rfield Req_EM_T). Qed.

Lemma lnorm_Forall : forall (P : R -> Prop) p, Forall P p -> Forall P (lnorm p).
Proof. exact (klnorm_Forall R 0 Req_EM_T). Qed.

Lemma lnorm_length : forall p, (length (lnorm p) <= length p)%nat.
Proof. exact (klnorm_length R 0 Req_EM_T). Qed.

Lemma lnorm_head : forall p, lnorm p = nil \/ hd 0 (lnorm p) <> 0.
Proof. exact (klnorm_head R 0 Req_EM_T). Qed.

(** A list with some nonzero entry normalizes to a nonempty list. *)
Lemma lnorm_nonzero : forall p, ~ Forall (fun c => c = 0) p -> lnorm p <> nil.
Proof. exact (klnorm_nonzero R 0 Req_EM_T). Qed.

(** Leading-first product and difference through the constant-first layer. *)
Definition pmul_lf (a b : list R) : list R := rev (pmulR (rev a) (rev b)).
Definition psub_lf (a b : list R) : list R :=
  rev (paddR (rev a) (pscaleR (-1) (rev b))).

Lemma pmul_lf_eval : forall a b y,
  peval_lf (pmul_lf a b) y = peval_lf a y * peval_lf b y.
Proof.
  intros a b y. unfold pmul_lf.
  rewrite <- pevalR_rev, pevalR_pmul, !pevalR_rev, !rev_involutive.
  reflexivity.
Qed.

Lemma psub_lf_eval : forall a b y,
  peval_lf (psub_lf a b) y = peval_lf a y - peval_lf b y.
Proof.
  intros a b y. unfold psub_lf.
  rewrite <- pevalR_rev, pevalR_padd, pevalR_pscale, !pevalR_rev, !rev_involutive.
  ring.
Qed.

Lemma pmul_lf_Forall : forall (P : R -> Prop) a b,
  (forall x y, P x -> P y -> P (x + y)) ->
  (forall x y, P x -> P y -> P (x * y)) ->
  P 0 -> Forall P a -> Forall P b -> Forall P (pmul_lf a b).
Proof.
  intros P a b Hadd Hmul H0 Ha Hb. unfold pmul_lf.
  apply Forall_rev, Forall_pmulR; try assumption; apply Forall_rev; assumption.
Qed.

Lemma psub_lf_Forall : forall (F : R -> Prop) a b, is_subfield F ->
  Forall F a -> Forall F b -> Forall F (psub_lf a b).
Proof.
  intros F a b HF Ha Hb. unfold psub_lf.
  apply Forall_rev, Forall_paddR;
    [intros u v Hu Hv; apply (subfield_add F u v HF Hu Hv)
    | apply Forall_rev; exact Ha |].
  apply Forall_pscaleR;
    [intros u v Hu Hv; apply (subfield_mul F u v HF Hu Hv)
    | apply (subfield_opp F 1 HF (subfield_1 F HF))
    | apply Forall_rev; exact Hb].
Qed.

(** General division: divide by the monicization of the (normalized) divisor. *)
Definition pdivg (p g : list R) : list R * list R :=
  match lnorm g with
  | nil => (nil, p)
  | c :: dt0 =>
      let dt := pscaleR (/ c) dt0 in
      (pscaleR (/ c) (fst (pdiv_lf (length p) p dt)),
       snd (pdiv_lf (length p) p dt))
  end.

Lemma pdivg_spec : forall (F : R -> Prop) p g, is_subfield F ->
  Forall F p -> Forall F g ->
  lnorm g <> nil ->
  Forall F (fst (pdivg p g)) /\ Forall F (snd (pdivg p g)) /\
  (length (snd (pdivg p g)) < length (lnorm g))%nat /\
  (forall y, peval_lf p y
     = peval_lf (fst (pdivg p g)) y * peval_lf g y + peval_lf (snd (pdivg p g)) y).
Proof.
  intros F p g HF HFp HFg Hgnz.
  exact (kpdivg_spec _ _ _ _ _ _ _ _ _ RealField.Rfield Req_EM_T F p g
           HF HFp HFg Hgnz).
Qed.

Definition padd_lf (a b : list R) : list R := rev (paddR (rev a) (rev b)).

Lemma padd_lf_eval : forall a b y,
  peval_lf (padd_lf a b) y = peval_lf a y + peval_lf b y.
Proof.
  intros a b y. unfold padd_lf.
  rewrite <- pevalR_rev, pevalR_padd, !pevalR_rev, !rev_involutive.
  reflexivity.
Qed.

Lemma padd_lf_Forall : forall (P : R -> Prop) a b,
  (forall x y, P x -> P y -> P (x + y)) ->
  Forall P a -> Forall P b -> Forall P (padd_lf a b).
Proof.
  intros P a b Hadd Ha Hb. unfold padd_lf.
  apply Forall_rev, Forall_paddR; try assumption; apply Forall_rev; assumption.
Qed.

Lemma lnorm_nil_eval : forall g y, lnorm g = nil -> peval_lf g y = 0.
Proof. exact (klnorm_nil_eval _ _ _ _ _ _ _ _ _ RealField.Rfield Req_EM_T). Qed.

(** Extended Euclid on leading-first lists: ((u, v), d) with u p + v g = d pointwise, d dividing both, normalized. *)
Fixpoint bezout_lf (fuel : nat) (p g : list R) : (list R * list R) * list R :=
  match fuel with
  | O => ((1 :: nil, nil), lnorm p)
  | Datatypes.S fu =>
      match lnorm g with
      | nil => ((1 :: nil, nil), lnorm p)
      | _ :: _ =>
          let q := fst (pdivg p g) in
          let r := snd (pdivg p g) in
          let ud := bezout_lf fu g r in
          ((snd (fst ud), psub_lf (fst (fst ud)) (pmul_lf (snd (fst ud)) q)),
           snd ud)
      end
  end.

Lemma bezout_lf_spec : forall (F : R -> Prop) fuel p g, is_subfield F ->
  Forall F p -> Forall F g -> (length (lnorm g) <= fuel)%nat ->
  Forall F (fst (fst (bezout_lf fuel p g))) /\
  Forall F (snd (fst (bezout_lf fuel p g))) /\
  Forall F (snd (bezout_lf fuel p g)) /\
  (forall y, peval_lf (fst (fst (bezout_lf fuel p g))) y * peval_lf p y
             + peval_lf (snd (fst (bezout_lf fuel p g))) y * peval_lf g y
             = peval_lf (snd (bezout_lf fuel p g)) y) /\
  (exists qp, Forall F qp /\ forall y,
      peval_lf p y = peval_lf qp y * peval_lf (snd (bezout_lf fuel p g)) y) /\
  (exists qg, Forall F qg /\ forall y,
      peval_lf g y = peval_lf qg y * peval_lf (snd (bezout_lf fuel p g)) y) /\
  (lnorm g <> nil ->
     (length (snd (bezout_lf fuel p g)) <= length (lnorm g))%nat) /\
  (snd (bezout_lf fuel p g) = nil \/ hd 0 (snd (bezout_lf fuel p g)) <> 0).
Proof.
  intros F fuel p g HF HFp HFg Hfuel.
  exact (kbezout_lf_spec _ _ _ _ _ _ _ _ _ RealField.Rfield Req_EM_T F fuel p g
           HF HFp HFg Hfuel).
Qed.

Lemma lnorm_id_of_head : forall p, p <> nil -> hd 0 p <> 0 -> lnorm p = p.
Proof. exact (klnorm_id_of_head R 0 Req_EM_T). Qed.

(** Monic leading-first lists of positive degree are nonzero as functions. *)
Lemma monic_lf_nonzero : forall fl, hd 0 fl = 1 -> (2 <= length fl)%nat ->
  ~ (forall y, peval_lf fl y = 0).
Proof.
  intros fl Hhd Hlen Hall.
  pose proof (peval_lf_zero_coeffs fl Hall) as Hz.
  destruct fl as [|a fl']; [cbn [length] in Hlen; lia |].
  cbn [hd] in Hhd. inversion Hz; subst. lra.
Qed.

(** Constant-first evaluation of the reversal against the monic head. *)
Lemma peval_lf_monic_fsum : forall (a : R) (tl0 : list R) x,
  peval_lf (a :: tl0) x
  = a * x ^ (length tl0) + fsum (length tl0) (fun i => nth i (rev tl0) 0 * x ^ i).
Proof.
  intros a tl0 x. cbn [peval_lf]. f_equal.
  rewrite <- (rev_involutive tl0) at 1.
  rewrite <- pevalR_rev, pevalR_nth_sum, length_rev.
  reflexivity.
Qed.

(** IRREDUCIBLE MEANS INDEPENDENT: a monic F-polynomial with no proper monic F-factorization and a root x0 forces the lower powers of x0 to be F-independent. *)
Lemma irreducible_root_lin_indep :
  forall (F : R -> Prop) (fl : list R) (x0 : R),
  is_subfield F ->
  (2 <= length fl)%nat ->
  hd 0 fl = 1 ->
  Forall F fl ->
  peval_lf fl x0 = 0 ->
  (forall dl ql, Forall F dl -> Forall F ql ->
     (2 <= length dl)%nat -> (length dl < length fl)%nat ->
     hd 0 dl = 1 ->
     (forall y, peval_lf fl y = peval_lf dl y * peval_lf ql y) -> False) ->
  lin_indep F (powers x0 (length fl - 1)).
Proof.
  intros F fl x0 HF Hlen Hmon HFf Hroot Hirr.
  intros ks Hklen HFks Hkcomb.
  rewrite powers_length in Hklen.
  apply (kirreducible_root_lin_indep _ _ _ _ _ _ _ _ _ RealField.Rfield Req_EM_T
           monic_lf_nonzero F fl x0 HF Hlen Hmon HFf Hroot Hirr ks Hklen HFks).
  rewrite <- Hklen in Hkcomb.
  rewrite Fcomb_powers_pevalR in Hkcomb.
  exact Hkcomb.
Qed.

(** THE MINIMAL-RELATION PACKAGE: irreducibility of fl with root x0 yields the relation and independence data the embedding extension consumes. *)
Lemma irreducible_minimal_relation :
  forall (F : R -> Prop) (fl : list R) (x0 : R),
  is_subfield F ->
  (2 <= length fl)%nat ->
  hd 0 fl = 1 ->
  Forall F fl ->
  peval_lf fl x0 = 0 ->
  (forall dl ql, Forall F dl -> Forall F ql ->
     (2 <= length dl)%nat -> (length dl < length fl)%nat ->
     hd 0 dl = 1 ->
     (forall y, peval_lf fl y = peval_lf dl y * peval_lf ql y) -> False) ->
  (forall i, (i < length fl - 1)%nat -> F (nth i (rev (tl fl)) 0)) /\
  fsum (length fl - 1) (fun i => nth i (rev (tl fl)) 0 * x0 ^ i)
    + x0 ^ (length fl - 1) = 0 /\
  lin_indep F (powers x0 (length fl - 1)).
Proof.
  intros F fl x0 HF Hlen Hmon HFf Hroot Hirr.
  destruct fl as [|a tl0]; [cbn [length] in Hlen; lia |].
  cbn [hd] in Hmon. subst a.
  cbn [tl]. cbn [length].
  replace (Datatypes.S (length tl0) - 1)%nat with (length tl0) by lia.
  split; [| split].
  - intros i Hi. apply Forall_nth_F; [| rewrite length_rev; exact Hi].
    apply Forall_rev. apply (Forall_inv_tail HFf).
  - pose proof (peval_lf_monic_fsum 1 tl0 x0) as Hb.
    rewrite Hroot in Hb. lra.
  - pose proof (irreducible_root_lin_indep F (1 :: tl0) x0 HF Hlen
                  ltac:(reflexivity) HFf Hroot Hirr) as Hind.
    cbn [length] in Hind.
    replace (Datatypes.S (length tl0) - 1)%nat with (length tl0) in Hind by lia.
    exact Hind.
Qed.

(* mod-m factor exclusion -- a monic rational factorization descends to integers (monic Gauss) and to congruences mod m, where division certificates refute each monic candidate and a vm sweep refutes the degree. *)

Open Scope Z_scope.

Definition Zlcong (m : Z) (u v : list Z) : Prop :=
  forall k, (m | nth k u 0 - nth k v 0).

Lemma Zconv_Zpadd_r : forall p u v k,
  Zconv p (Zpadd u v) k = Zconv p u k + Zconv p v k.
Proof.
  induction p as [|a p IH]; intros u v k; cbn [Zconv].
  - ring.
  - rewrite nth_Zpadd.
    destruct k as [|k']; [ring | rewrite IH; ring].
Qed.

Lemma Zconv_scale_r : forall p c v k,
  Zconv p (map (Z.mul c) v) k = c * Zconv p v k.
Proof.
  induction p as [|a p IH]; intros c v k; cbn [Zconv].
  - ring.
  - rewrite nth_map_Zmul.
    destruct k as [|k']; [ring | rewrite IH; ring].
Qed.

Lemma Zconv_div_r : forall (m : Z) p v k,
  (forall j, (m | nth j v 0)) -> (m | Zconv p v k).
Proof.
  intros m p. induction p as [|a p IH]; intros v k Hv; cbn [Zconv].
  - apply Z.divide_0_r.
  - destruct k as [|k'].
    + replace (a * nth 0 v 0 + 0) with (a * nth 0 v 0) by ring.
      apply Z.divide_mul_r. apply Hv.
    + apply Z.divide_add_r; [apply Z.divide_mul_r; apply Hv | apply IH; exact Hv].
Qed.

(** THE TOP-COEFFICIENT UNIQUENESS: a factorization congruence against a monic candidate forces the certified remainder to vanish mod m. *)
Lemma monic_mod_remainder_zero :
  forall (m : Z) (d : nat) (dl q Q Rr : list Z),
  (1 < m)%Z ->
  (forall i, (d < i)%nat -> (m | nth i dl 0)) ->
  (m | nth d dl 0 - 1) ->
  (forall k, (d <= k)%nat -> nth k Rr 0 = 0) ->
  Zlcong m (Zpmul dl q) (Zpadd (Zpmul dl Q) Rr) ->
  forall k, (m | nth k Rr 0).
Proof.
  intros m d dl q Q Rr Hm Hdlhigh Hdlmon HRlow Hcong.
  set (E := Zpadd q (map (Z.mul (-1)) Q)).
  assert (HconvE : forall k, Zconv dl E k = Zconv dl q k - Zconv dl Q k).
  { intro k. unfold E. rewrite Zconv_Zpadd_r, Zconv_scale_r. ring. }
  assert (HB : forall k, (m | Zconv dl E k - nth k Rr 0)).
  { intro k. pose proof (Hcong k) as Hk.
    rewrite nth_Zpadd, !nth_Zpmul in Hk.
    rewrite HconvE.
    replace (Zconv dl q k - Zconv dl Q k - nth k Rr 0)
      with (Zconv dl q k - (Zconv dl Q k + nth k Rr 0)) by ring.
    exact Hk. }
  assert (HE : forall fuel t, (length E <= t + fuel)%nat -> (m | nth t E 0)).
  { induction fuel as [|fu IH]; intros t Hle.
    - rewrite nth_overflow by lia. apply Z.divide_0_r.
    - assert (Hhigh : forall j, (t < j)%nat -> (m | nth j E 0))
        by (intros j Hj; apply IH; lia).
      pose proof (Zconv_top_mod m dl E d t Hdlhigh Hhigh) as Htop.
      pose proof (HB (d + t)%nat) as HBk.
      rewrite (HRlow (d + t)%nat ltac:(lia)) in HBk.
      replace (Zconv dl E (d + t) - 0) with (Zconv dl E (d + t)) in HBk by ring.
      assert (Hprod : (m | nth d dl 0 * nth t E 0)).
      { replace (nth d dl 0 * nth t E 0)
          with (Zconv dl E (d + t) - (Zconv dl E (d + t) - nth d dl 0 * nth t E 0))
          by ring.
        apply Z.divide_sub_r; assumption. }
      replace (nth t E 0)
        with (nth d dl 0 * nth t E 0 - (nth d dl 0 - 1) * nth t E 0) by ring.
      apply Z.divide_sub_r; [exact Hprod |].
      apply Z.divide_mul_l. exact Hdlmon. }
  intro k.
  assert (HEall : forall j, (m | nth j E 0))
    by (intro j; apply (HE (length E) j); lia).
  pose proof (HB k) as HBk.
  pose proof (Zconv_div_r m dl E k HEall) as Hdiv.
  replace (nth k Rr 0)
    with (Zconv dl E k - (Zconv dl E k - nth k Rr 0)) by ring.
  apply Z.divide_sub_r; assumption.
Qed.

Lemma Zconv_div_l : forall (m : Z) p v k,
  (forall j, (m | nth j p 0)) -> (m | Zconv p v k).
Proof.
  intros m p. induction p as [|a p IH]; intros v k Hp; cbn [Zconv].
  - apply Z.divide_0_r.
  - destruct k as [|k'].
    + replace (a * nth 0 v 0 + 0) with (a * nth 0 v 0) by ring.
      apply Z.divide_mul_l. apply (Hp 0%nat).
    + apply Z.divide_add_r.
      * apply Z.divide_mul_l. apply (Hp 0%nat).
      * apply IH. intro j. apply (Hp (Datatypes.S j)).
Qed.

Lemma Zconv_cong_l : forall (m : Z) p p' v k,
  (forall i, (m | nth i p 0 - nth i p' 0)) ->
  (m | Zconv p v k - Zconv p' v k).
Proof.
  intros m p. induction p as [|a p IH]; intros p' v k Hpp.
  - cbn [Zconv].
    replace (0 - Zconv p' v k) with (- Zconv p' v k) by ring.
    apply Z.divide_opp_r.
    apply Zconv_div_l. intro j.
    pose proof (Hpp j) as Hj.
    rewrite nth_overflow in Hj by (cbn [length]; lia).
    replace (nth j p' 0) with (- (0 - nth j p' 0)) by ring.
    apply Z.divide_opp_r. exact Hj.
  - destruct p' as [|b p'].
    + replace (Zconv (a :: p) v k - Zconv nil v k)
        with (Zconv (a :: p) v k) by (cbn [Zconv]; ring).
      apply Zconv_div_l. intro j.
      pose proof (Hpp j) as Hj.
      rewrite (nth_overflow nil) in Hj by (cbn [length]; lia).
      replace (nth j (a :: p) 0) with (nth j (a :: p) 0 - 0) by ring.
      exact Hj.
    + cbn [Zconv].
      assert (Hhd : (m | a - b)) by (apply (Hpp 0%nat)).
      assert (Htl : forall i, (m | nth i p 0 - nth i p' 0))
        by (intro i; apply (Hpp (Datatypes.S i))).
      destruct k as [|k'].
      * replace (a * nth 0 v 0 + 0 - (b * nth 0 v 0 + 0))
          with ((a - b) * nth 0 v 0) by ring.
        apply Z.divide_mul_l. exact Hhd.
      * replace (a * nth (Datatypes.S k') v 0 + Zconv p v k'
                 - (b * nth (Datatypes.S k') v 0 + Zconv p' v k'))
          with ((a - b) * nth (Datatypes.S k') v 0 + (Zconv p v k' - Zconv p' v k'))
          by ring.
        apply Z.divide_add_r; [apply Z.divide_mul_l; exact Hhd | apply IH; exact Htl].
Qed.

Lemma Zlcong_pmul_l : forall m u u' v,
  Zlcong m u u' -> Zlcong m (Zpmul u v) (Zpmul u' v).
Proof.
  intros m u u' v Hc k. rewrite !nth_Zpmul.
  apply Zconv_cong_l. exact Hc.
Qed.

Lemma Zlcong_trans : forall m u v t,
  Zlcong m u v -> Zlcong m v t -> Zlcong m u t.
Proof.
  intros m u v t H1 H2 k.
  replace (nth k u 0 - nth k t 0)
    with ((nth k u 0 - nth k v 0) + (nth k v 0 - nth k t 0)) by ring.
  apply Z.divide_add_r; [apply H1 | apply H2].
Qed.

Lemma Zlcong_sym : forall m u v, Zlcong m u v -> Zlcong m v u.
Proof.
  intros m u v H k.
  replace (nth k v 0 - nth k u 0) with (- (nth k u 0 - nth k v 0)) by ring.
  apply Z.divide_opp_r. apply H.
Qed.

Lemma length_Zpadd : forall u v,
  length (Zpadd u v) = Nat.max (length u) (length v).
Proof.
  induction u as [|a u IH]; intros v; cbn [Zpadd length].
  - lia.
  - destruct v as [|b v]; cbn [length]; [lia | rewrite IH; lia].
Qed.

Lemma length_Zpmul_le : forall u v,
  (length (Zpmul u v) <= length u + length v)%nat.
Proof.
  induction u as [|a u IH]; intros v; cbn [Zpmul length].
  - lia.
  - rewrite length_Zpadd, length_map. cbn [length].
    pose proof (IH v). lia.
Qed.

(** Boolean divisibility and the bounded congruence checker. *)
Definition zdivb (m z : Z) : bool := Z.eqb (z mod m) 0.

Lemma zdivb_sound : forall m z, m <> 0 -> zdivb m z = true -> (m | z).
Proof.
  intros m z Hm Hb. unfold zdivb in Hb.
  apply Z.eqb_eq in Hb. apply Z.mod_divide; assumption.
Qed.

Lemma zdivb_complete : forall m z, m <> 0 -> (m | z) -> zdivb m z = true.
Proof.
  intros m z Hm Hd. unfold zdivb.
  apply Z.eqb_eq. apply Z.mod_divide; assumption.
Qed.

Definition zcong_upto (m : Z) (bound : nat) (u v : list Z) : bool :=
  forallb (fun k => zdivb m (nth k u 0 - nth k v 0)) (seq 0 bound).

Lemma zcong_upto_sound : forall m bound u v,
  m <> 0 -> (length u <= bound)%nat -> (length v <= bound)%nat ->
  zcong_upto m bound u v = true -> Zlcong m u v.
Proof.
  intros m bound u v Hm Hu Hv Hb k.
  destruct (le_lt_dec bound k) as [Hge | Hlt].
  - rewrite !nth_overflow by lia.
    replace (0 - 0) with 0 by ring. apply Z.divide_0_r.
  - apply zdivb_sound; [exact Hm |].
    apply (proj1 (forallb_forall _ _) Hb).
    apply in_seq. lia.
Qed.

(** The division routine mod m on leading-first lists, an oracle whose output the checker certifies. *)
Fixpoint zdiv_lf_m (m : Z) (fuel : nat) (p dt : list Z) : list Z * list Z :=
  match fuel with
  | O => (nil, p)
  | Datatypes.S f =>
      if Nat.leb (length p) (length dt) then (nil, p)
      else match p with
           | nil => (nil, nil)
           | a :: p' =>
               let p'' := map (fun z => Z.modulo z m) (Zpadd p' (map (Z.mul (- a)) dt)) in
               let qr := zdiv_lf_m m f p'' dt in
               ((a mod m) :: fst qr, snd qr)
           end
  end.

Lemma zdiv_lf_m_qlen : forall m fuel p dt,
  (length (fst (zdiv_lf_m m fuel p dt)) <= fuel)%nat.
Proof.
  intros m fuel. induction fuel as [|f IH]; intros p dt; cbn [zdiv_lf_m].
  - cbn [fst length]. lia.
  - destruct (Nat.leb (length p) (length dt)); [cbn [fst length]; lia |].
    destruct p as [|a p']; [cbn [fst length]; lia |].
    cbn [fst length]. pose proof (IH (map (fun z => Z.modulo z m) (Zpadd p' (map (Z.mul (- a)) dt))) dt). lia.
Qed.

(** One-candidate refuter: certified division output with nonzero remainder. *)
Definition refute_factor (m : Z) (Fz dl : list Z) : bool :=
  let dt := tl (rev dl) in
  let qr := zdiv_lf_m m (length (rev Fz)) (rev Fz) dt in
  zcong_upto m (length Fz + length dl)%nat Fz
    (Zpadd (Zpmul dl (rev (fst qr))) (rev (snd qr)))
  && Nat.ltb (length (snd qr)) (length dl)
  && negb (forallb (zdivb m) (rev (snd qr))).

(** entrywise-equal lists are congruent *)
Lemma nth_eq_lcong : forall m u v,
  (forall i, nth i u 0 = nth i v 0) -> Zlcong m u v.
Proof.
  intros m u v H k.
  rewrite (H k).
  replace (nth k v 0 - nth k v 0) with 0 by ring.
  apply Z.divide_0_r.
Qed.

Lemma refute_factor_sound_cong : forall (m : Z) (Fz' dl : list Z) (d : nat)
                                        muZ qZ,
  (1 < m) -> length dl = Datatypes.S d -> nth d dl 0 = 1 ->
  Zlcong m muZ dl ->
  Zlcong m (Zpmul muZ qZ) Fz' ->
  refute_factor m Fz' dl = true -> False.
Proof.
  intros m Fz' dl d muZ qZ Hm Hlen Hmon Hred Hfactc Href.
  unfold refute_factor in Href.
  apply andb_prop in Href. destruct Href as [Href Hnz].
  apply andb_prop in Href. destruct Href as [Hid Hrlen].
  set (dt := tl (rev dl)) in *.
  set (qr := zdiv_lf_m m (length (rev Fz')) (rev Fz') dt) in *.
  set (Q := rev (fst qr)) in *.
  set (Rr := rev (snd qr)) in *.
  apply Nat.ltb_lt in Hrlen.
  assert (Hm0 : m <> 0) by lia.
  assert (Hcong1 : Zlcong m Fz' (Zpadd (Zpmul dl Q) Rr)).
  { apply (zcong_upto_sound m (length Fz' + length dl) _ _ Hm0); [lia | | exact Hid].
    rewrite length_Zpadd.
    pose proof (length_Zpmul_le dl Q) as H1.
    assert (HQ : (length Q <= length Fz')%nat).
    { unfold Q, qr. rewrite length_rev.
      eapply Nat.le_trans; [apply zdiv_lf_m_qlen | rewrite length_rev; lia]. }
    assert (HR : (length Rr < length dl)%nat)
      by (unfold Rr; rewrite length_rev; exact Hrlen).
    lia. }
  assert (Hcong2 : Zlcong m (Zpmul dl qZ) (Zpadd (Zpmul dl Q) Rr)).
  { apply (Zlcong_trans m _ (Zpmul muZ qZ)).
    - apply Zlcong_pmul_l. apply Zlcong_sym. exact Hred.
    - apply (Zlcong_trans m _ Fz'); [exact Hfactc | exact Hcong1]. }
  assert (Hzero : forall k, (m | nth k Rr 0)).
  { apply (monic_mod_remainder_zero m d dl qZ Q Rr Hm).
    - intros i Hi. rewrite nth_overflow by lia. apply Z.divide_0_r.
    - rewrite Hmon. replace (1 - 1) with 0 by ring. apply Z.divide_0_r.
    - intros k Hk. apply nth_overflow.
      unfold Rr. rewrite length_rev. lia.
    - exact Hcong2. }
  rewrite negb_true_iff in Hnz.
  assert (Hall : forallb (zdivb m) Rr = true).
  { apply forallb_forall. intros z Hz.
    apply zdivb_complete; [exact Hm0 |].
    destruct (In_nth Rr z 0 Hz) as [i [Hi Hnth]].
    rewrite <- Hnth. apply Hzero. }
  rewrite Hall in Hnz. discriminate.
Qed.

(** the pointwise-factorization instance of the congruence refuter *)
Lemma refute_factor_sound : forall (m : Z) (Fz dl : list Z) (d : nat) muZ qZ,
  (1 < m) -> length dl = Datatypes.S d -> nth d dl 0 = 1 ->
  Zlcong m muZ dl ->
  (forall k, nth k (Zpmul muZ qZ) 0 = nth k Fz 0) ->
  refute_factor m Fz dl = true -> False.
Proof.
  intros m Fz dl d muZ qZ Hm Hlen Hmon Hred Hfact Href.
  apply (refute_factor_sound_cong m Fz dl d muZ qZ Hm Hlen Hmon Hred
           (nth_eq_lcong m (Zpmul muZ qZ) Fz Hfact) Href).
Qed.

(** All length-d lists over [0, m). *)
Fixpoint all_mod_lists (m : Z) (d : nat) : list (list Z) :=
  match d with
  | O => nil :: nil
  | Datatypes.S d' =>
      flat_map (fun t => map (fun c => Z.of_nat c :: t) (seq 0 (Z.to_nat m)))
        (all_mod_lists m d')
  end.

Lemma all_mod_lists_complete : forall (m : Z) (d : nat) (l : list Z),
  (0 < m) -> length l = d -> Forall (fun z => 0 <= z < m) l ->
  In l (all_mod_lists m d).
Proof.
  intros m d. induction d as [|d IH]; intros l Hm Hlen Hb.
  - destruct l; [cbn; left; reflexivity | cbn [length] in Hlen; lia].
  - destruct l as [|a l']; [cbn [length] in Hlen; lia |].
    cbn [length] in Hlen.
    inversion Hb; subst.
    cbn [all_mod_lists].
    apply in_flat_map. exists l'.
    split; [apply IH; [exact Hm | lia | assumption] |].
    apply in_map_iff. exists (Z.to_nat a).
    split; [rewrite Z2Nat.id by lia; reflexivity |].
    apply in_seq. split; [lia |].
    assert (Ha : (Z.to_nat a < Z.to_nat m)%nat) by (apply Z2Nat.inj_lt; lia).
    lia.
Qed.

Definition monic_candidates (m : Z) (d : nat) : list (list Z) :=
  map (fun t => t ++ 1 :: nil) (all_mod_lists m d).

(** A length-(S d) list splits as its low part and its top entry. *)
Lemma list_split_top : forall (l : list Z) (d : nat),
  length l = Datatypes.S d -> l = firstn d l ++ (nth d l 0 :: nil).
Proof.
  intros l d. revert l. induction d as [|d IH]; intros l Hlen.
  - destruct l as [|a [|b l']]; cbn [length] in Hlen; try lia.
    reflexivity.
  - destruct l as [|a l']; cbn [length] in Hlen; [lia |].
    cbn [firstn nth app].
    f_equal. apply IH. lia.
Qed.

(** The mod-m reduction of a monic integer list is a monic candidate. *)
Lemma reduction_in_candidates : forall (m : Z) (d : nat) (muZ : list Z),
  (1 < m) -> length muZ = Datatypes.S d -> nth d muZ 0 = 1 ->
  In (map (fun z => Z.modulo z m) muZ) (monic_candidates m d).
Proof.
  intros m d muZ Hm Hlen Hmon.
  unfold monic_candidates.
  apply in_map_iff.
  exists (map (fun z => Z.modulo z m) (firstn d muZ)).
  split.
  - rewrite (list_split_top muZ d Hlen) at 2.
    rewrite map_app. cbn [map].
    rewrite Hmon.
    replace (1 mod m) with 1 by (symmetry; apply Z.mod_small; lia).
    reflexivity.
  - apply all_mod_lists_complete; [lia | |].
    + rewrite length_map, firstn_length. lia.
    + apply Forall_forall. intros z Hz.
      apply in_map_iff in Hz. destruct Hz as [w [Hzw _]]. subst z.
      apply Z.mod_pos_bound. lia.
Qed.

Lemma all_mod_lists_length : forall m d t,
  In t (all_mod_lists m d) -> length t = d.
Proof.
  intros m d. induction d as [|d IH]; intros t Hin.
  - cbn [all_mod_lists] in Hin. destruct Hin as [<- | []]. reflexivity.
  - cbn [all_mod_lists] in Hin.
    apply in_flat_map in Hin. destruct Hin as [t' [Ht' Hin]].
    apply in_map_iff in Hin. destruct Hin as [c [Hc _]]. subst t.
    cbn [length]. rewrite (IH t' Ht'). reflexivity.
Qed.

(** Monic candidates carry their shape. *)
Lemma monic_candidates_shape : forall m d dl,
  In dl (monic_candidates m d) ->
  length dl = Datatypes.S d /\ nth d dl 0 = 1.
Proof.
  intros m d dl Hin.
  unfold monic_candidates in Hin.
  apply in_map_iff in Hin. destruct Hin as [t [Ht Hint]]. subst dl.
  pose proof (all_mod_lists_length m d t Hint) as Hlt.
  split.
  - rewrite length_app, Hlt. cbn [length]. lia.
  - rewrite app_nth2 by lia.
    rewrite Hlt, Nat.sub_diag. reflexivity.
Qed.

(** THE SWEEP EXCLUSION: a passing vm sweep over all monic mod-m candidates of degree d refutes every monic rational factorization with a degree-d factor. *)
Theorem sweep_excludes_degree :
  forall (Fz : list Z) (N : nat) (m : Z) (d : nat),
  length Fz = Datatypes.S N -> nth N Fz 0 = 1 -> Zcontent Fz = 1 -> (1 < m) ->
  (d <= N)%nat ->
  forallb (refute_factor m Fz) (monic_candidates m d) = true ->
  forall mu q, Forall is_rational mu -> Forall is_rational q ->
    length mu = Datatypes.S d -> nth d mu 0%R = 1%R ->
    (forall y, pe (map IZR Fz) y = (pe mu y * pe q y)%R) -> False.
Proof.
  intros Fz N m d HlenF HmonF HcontF Hm Hd Hsweep mu q Hmurat Hqrat Hmulen Hmumon Hfact.
  destruct (monic_gauss_factor_gen Fz N mu q d HlenF HmonF HcontF
              Hmurat Hqrat Hmulen Hmumon Hd Hfact)
    as [muZ [qZ [Hmu [HmuZlen [HmuZmon [Hq Hpev]]]]]].
  assert (Hnth : forall k, nth k (Zpmul muZ qZ) 0 = nth k Fz 0)
    by (apply peval_eq_nth; exact Hpev).
  set (dl := map (fun z => Z.modulo z m) muZ).
  assert (Hin : In dl (monic_candidates m d))
    by (apply reduction_in_candidates; assumption).
  assert (Href : refute_factor m Fz dl = true)
    by (apply (proj1 (forallb_forall _ _) Hsweep); exact Hin).
  destruct (monic_candidates_shape m d dl Hin) as [Hdllen Hdlmon].
  apply (refute_factor_sound m Fz dl d muZ qZ Hm Hdllen Hdlmon); [| exact Hnth | exact Href].
  intro k. unfold dl.
  replace (nth k (map (fun z => Z.modulo z m) muZ) 0)
    with ((nth k muZ 0) mod m).
  - rewrite Z.mod_eq by lia.
    replace (nth k muZ 0 - (nth k muZ 0 - m * (nth k muZ 0 / m)))
      with (m * (nth k muZ 0 / m)) by ring.
    apply Z.divide_factor_l.
  - replace 0 with (Z.modulo 0 m) at 2 by (apply Zmod_0_l).
    symmetry. exact (map_nth (fun z => Z.modulo z m) muZ 0 k).
Qed.

Close Scope Z_scope.

(* the polynomial layer over list C, with root-peeling (a nonzero degree-n polynomial has at most n roots) replacing the order-based vanishing argument. *)

Fixpoint cpeval (p : list C) (z : C) : C :=
  match p with
  | nil => C0
  | c :: p' => (c + z * cpeval p' z)%C
  end.

Fixpoint cpadd (p q : list C) : list C :=
  match p, q with
  | nil, _ => q
  | _, nil => p
  | a :: p', b :: q' => (a + b)%C :: cpadd p' q'
  end.

Definition cpscale (a : C) (p : list C) : list C := map (Cmul a) p.

Fixpoint cpmul (p q : list C) : list C :=
  match p with
  | nil => nil
  | a :: p' => cpadd (cpscale a q) (C0 :: cpmul p' q)
  end.

Lemma cpeval_cpadd : forall p q z, cpeval (cpadd p q) z = (cpeval p z + cpeval q z)%C.
Proof.
  induction p as [|a p IH]; intros q z; cbn [cpadd cpeval].
  - ring.
  - destruct q as [|b q]; cbn [cpeval]; [ring | rewrite IH; ring].
Qed.

Lemma cpeval_cpscale : forall a p z, cpeval (cpscale a p) z = (a * cpeval p z)%C.
Proof.
  induction p as [|c p IH]; intro z; cbn [cpscale map cpeval].
  - ring.
  - rewrite IH. ring.
Qed.

Lemma cpeval_cpmul : forall p q z, cpeval (cpmul p q) z = (cpeval p z * cpeval q z)%C.
Proof.
  induction p as [|a p IH]; intros q z; cbn [cpmul cpeval].
  - ring.
  - rewrite cpeval_cpadd, cpeval_cpscale. cbn [cpeval]. rewrite IH. ring.
Qed.

(** Leading-first evaluation over C. *)
Fixpoint cpeval_lf (p : list C) (z : C) : C :=
  match p with
  | nil => C0
  | a :: p' => (a * Cpow z (length p') + cpeval_lf p' z)%C
  end.

Lemma cpeval_lf_rev_c : forall p z, cpeval_lf p z = cpeval (rev p) z.
Proof.
  induction p as [|a p IH]; intro z.
  - reflexivity.
  - cbn [cpeval_lf rev].
    assert (Happ : forall l1 l2 w, cpeval (l1 ++ l2) w
                   = (cpeval l1 w + Cpow w (length l1) * cpeval l2 w)%C).
    { induction l1 as [|x l1 IHl]; intros l2 w; cbn [app cpeval length Cpow].
      - ring.
      - rewrite IHl. ring. }
    rewrite Happ, IH, length_rev. cbn [cpeval]. ring.
Qed.

Lemma cpadd_length : forall p q, length (cpadd p q) = Nat.max (length p) (length q).
Proof.
  induction p as [|a p IH]; intros q; cbn [cpadd length].
  - lia.
  - destruct q as [|b q]; cbn [length]; [lia | rewrite IH; lia].
Qed.

Lemma cpscale_length : forall a p, length (cpscale a p) = length p.
Proof. intros. unfold cpscale. apply length_map. Qed.

Lemma cpscale_cons : forall a c p, cpscale a (c :: p) = (a * c)%C :: cpscale a p.
Proof. reflexivity. Qed.

(** The complex layer is an instance of the parametric core: the bridges. *)
Lemma cpeval_k : forall p z, cpeval p z = kpeval C C0 Cadd Cmul p z.
Proof.
  induction p as [|c p IH]; intro z; cbn [cpeval kpeval].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma cpadd_k : forall p q, cpadd p q = kpadd C Cadd p q.
Proof.
  induction p as [|a p IH]; intros q.
  - reflexivity.
  - destruct q as [|b q]; cbn [cpadd kpadd]; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma cpscale_k : forall a p, cpscale a p = kpscale C Cmul a p.
Proof. intros a p. reflexivity. Qed.

Lemma cpmul_k : forall p q, cpmul p q = kpmul C C0 Cadd Cmul p q.
Proof.
  induction p as [|a p IH]; intros q; cbn [cpmul kpmul].
  - reflexivity.
  - rewrite IH, cpadd_k, cpscale_k. reflexivity.
Qed.

Lemma Cpow_k : forall z n, Cpow z n = kpow C C1 Cmul z n.
Proof.
  induction n as [|n IH]; cbn [Cpow kpow].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma cpeval_lf_k : forall p z, cpeval_lf p z = kpeval_lf C C0 C1 Cadd Cmul p z.
Proof.
  induction p as [|a p IH]; intro z; cbn [cpeval_lf kpeval_lf].
  - reflexivity.
  - rewrite IH, Cpow_k. reflexivity.
Qed.

(** Division by the monic divisor over C, leading-first (mirror of pdiv_lf). *)
Fixpoint cpdiv_lf (fuel : nat) (p dtail : list C) : list C * list C :=
  match fuel with
  | O => (nil, p)
  | Datatypes.S f =>
      if Nat.leb (length p) (length dtail) then (nil, p)
      else match p with
           | nil => (nil, nil)
           | a :: p' =>
               let p'' := cpadd p' (cpscale (Copp C1) (cpscale a dtail)) in
               (a :: fst (cpdiv_lf f p'' dtail), snd (cpdiv_lf f p'' dtail))
           end
  end.

Lemma cpdiv_lf_k : forall fuel p dt,
  cpdiv_lf fuel p dt = kpdiv_lf C C1 Cadd Cmul Copp fuel p dt.
Proof.
  induction fuel as [|f IH]; intros p dt; cbn [cpdiv_lf kpdiv_lf].
  - reflexivity.
  - destruct (Nat.leb (length p) (length dt)); [reflexivity |].
    destruct p as [|a p']; [reflexivity |].
    rewrite IH, cpadd_k, !cpscale_k. reflexivity.
Qed.

Lemma cpdiv_lf_rlen : forall fuel p dtail, (length p <= fuel)%nat ->
  (length (snd (cpdiv_lf fuel p dtail)) <= length dtail)%nat.
Proof.
  intros fuel p dtail Hfuel.
  rewrite cpdiv_lf_k.
  apply kpdiv_lf_rlen. exact Hfuel.
Qed.

Lemma cpeval_lf_psub_top : forall q p z, (length q <= length p)%nat ->
  cpeval_lf (cpadd p (cpscale (Copp C1) q)) z
  = (cpeval_lf p z - cpeval_lf q z * Cpow z (length p - length q))%C.
Proof.
  intros q p z Hle.
  rewrite !cpeval_lf_k, cpadd_k, cpscale_k, Cpow_k.
  apply (kpeval_lf_psub_top _ _ _ _ _ _ _ _ _ C_field). exact Hle.
Qed.

Lemma cpdiv_lf_qlen : forall fuel p dtail, (length p <= fuel)%nat ->
  length (fst (cpdiv_lf fuel p dtail)) = (length p - length dtail)%nat.
Proof.
  intros fuel p dtail Hfuel.
  rewrite cpdiv_lf_k.
  apply kpdiv_lf_qlen. exact Hfuel.
Qed.

Lemma cpdiv_lf_eval : forall fuel p dtail, (length p <= fuel)%nat ->
  forall z,
  cpeval_lf p z
  = (cpeval_lf (fst (cpdiv_lf fuel p dtail)) z
     * (Cpow z (length dtail) + cpeval_lf dtail z)
     + cpeval_lf (snd (cpdiv_lf fuel p dtail)) z)%C.
Proof.
  intros fuel p dtail Hfuel z.
  rewrite !cpeval_lf_k, !cpdiv_lf_k, Cpow_k.
  apply (kpdiv_lf_eval _ _ _ _ _ _ _ _ _ C_field). exact Hfuel.
Qed.

(** Root-peeling: a root factors off as the monic linear divisor with tail (Copp z0 :: nil). *)
Lemma cp_root_factor : forall (p : list C) (z0 : C),
  cpeval_lf p z0 = C0 ->
  forall z, cpeval_lf p z
  = (cpeval_lf (fst (cpdiv_lf (length p) p (Copp z0 :: nil))) z * (z - z0))%C.
Proof.
  intros p z0 Hroot z.
  pose proof (cpdiv_lf_eval (length p) p (Copp z0 :: nil) (Nat.le_refl _)) as Hs.
  pose proof (cpdiv_lf_rlen (length p) p (Copp z0 :: nil) (Nat.le_refl _)) as Hr.
  cbn [length] in Hr, Hs.
  set (q := fst (cpdiv_lf (length p) p (Copp z0 :: nil))) in *.
  set (r := snd (cpdiv_lf (length p) p (Copp z0 :: nil))) in *.
  assert (Hr0 : cpeval_lf r z0 = C0).
  { pose proof (Hs z0) as H0. rewrite Hroot in H0.
    transitivity ((cpeval_lf q z0
                   * (Cpow z0 1 + cpeval_lf (Copp z0 :: nil) z0)
                   + cpeval_lf r z0)
                  - cpeval_lf q z0
                    * (Cpow z0 1 + cpeval_lf (Copp z0 :: nil) z0))%C.
    { cbn [cpeval_lf length Cpow]. ring. }
    rewrite <- H0. cbn [cpeval_lf length Cpow]. ring. }
  assert (Hrz : forall w, cpeval_lf r w = C0).
  { destruct r as [|r0 [|r1 rr]]; [intro w; reflexivity | | cbn [length] in Hr; lia].
    intro w. cbn [cpeval_lf length Cpow] in Hr0 |- *.
    exact Hr0. }
  pose proof (Hs z) as Hz.
  rewrite Hz, (Hrz z).
  cbn [cpeval_lf length Cpow]. ring.
Qed.

(** The quotient of the linear peel keeps the leading coefficient. *)
Lemma cpdiv_head_linear : forall (a c : C) (p' : list C), (1 <= length p')%nat ->
  fst (cpdiv_lf (length (a :: p')) (a :: p') (c :: nil))
  = a :: fst (cpdiv_lf (length p')
                (cpadd p' (cpscale (Copp C1) (cpscale a (c :: nil)))) (c :: nil)).
Proof.
  intros a c p' Hlen.
  cbn [length cpdiv_lf].
  destruct (Nat.leb_spec (Datatypes.S (length p')) 1) as [Hle | Hgt].
  - lia.
  - cbn [fst]. reflexivity.
Qed.

Lemma Forall_zero_cpeval : forall (p : list C),
  Forall (fun c => c = C0) p -> forall z, cpeval_lf p z = C0.
Proof.
  intros p Hp. induction Hp as [|a p' Ha Hp' IH]; intro z; cbn [cpeval_lf].
  - reflexivity.
  - rewrite Ha, (IH z). ring.
Qed.

Lemma RtoC_INR_inj : forall a b : nat, RtoC (INR a) = RtoC (INR b) -> a = b.
Proof.
  intros a b H. unfold RtoC in H.
  inversion H. apply INR_eq. assumption.
Qed.

(** VANISHING AT THE NATURALS FORCES ZERO COEFFICIENTS: the complex substitute for the real coefficient-bound argument. *)
Lemma cp_vanish_zero_gen : forall (n : nat) (p : list C) (off : nat),
  length p = n ->
  (forall k : nat, cpeval_lf p (RtoC (INR (k + off))) = C0) ->
  Forall (fun c => c = C0) p.
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros p off Hlen Hvan. subst n.
  destruct p as [|a p']; [constructor |].
  destruct p' as [|b p''].
  - constructor; [| constructor].
    pose proof (Hvan 0%nat) as H0.
    cbn [cpeval_lf length Cpow] in H0.
    transitivity ((a * C1 + C0)%C); [ring | exact H0].
  - set (z0 := RtoC (INR off)).
    assert (Hroot : cpeval_lf (a :: b :: p'') z0 = C0)
      by (pose proof (Hvan 0%nat) as H0; cbn [Nat.add] in H0; exact H0).
    set (q := fst (cpdiv_lf (length (a :: b :: p'')) (a :: b :: p'') (Copp z0 :: nil))).
    assert (Hqlen : length q = Datatypes.S (length p'')).
    { unfold q. rewrite (cpdiv_lf_qlen _ _ _ (Nat.le_refl _)).
      cbn [length]. lia. }
    assert (Hqvan : forall k : nat, cpeval_lf q (RtoC (INR (k + Datatypes.S off))) = C0).
    { intro k.
      pose proof (cp_root_factor (a :: b :: p'') z0 Hroot (RtoC (INR (k + Datatypes.S off)))) as Hf.
      fold q in Hf.
      pose proof (Hvan (Datatypes.S k)) as Hv.
      replace (Datatypes.S k + off)%nat with (k + Datatypes.S off)%nat in Hv by lia.
      rewrite Hv in Hf.
      assert (Hne : (RtoC (INR (k + Datatypes.S off)) - z0)%C <> C0).
      { intro He. unfold z0 in He.
        assert (Heq : RtoC (INR (k + Datatypes.S off)) = RtoC (INR off)).
        { transitivity ((RtoC (INR (k + Datatypes.S off)) - RtoC (INR off))
                        + RtoC (INR off))%C; [ring |].
          rewrite He. ring. }
        apply RtoC_INR_inj in Heq. lia. }
      destruct (Ceq_dec (cpeval_lf q (RtoC (INR (k + Datatypes.S off)))) C0)
        as [E | NE]; [exact E | exfalso].
      apply Hne.
      destruct (Cmul_integral _ _ (eq_sym Hf)) as [E | E]; [contradiction | exact E]. }
    assert (Hqzero : Forall (fun c => c = C0) q).
    { apply (IHn (Datatypes.S (length p'')) ltac:(cbn [length]; lia) q (Datatypes.S off) Hqlen Hqvan). }
    assert (Ha0 : a = C0).
    { assert (Hhead : q = a :: fst (cpdiv_lf (length (b :: p''))
                 (cpadd (b :: p'') (cpscale (Copp C1) (cpscale a (Copp z0 :: nil))))
                 (Copp z0 :: nil))).
      { unfold q. apply (cpdiv_head_linear a (Copp z0) (b :: p'')).
        cbn [length]. lia. }
      rewrite Hhead in Hqzero.
      exact (Forall_inv Hqzero). }
    constructor; [exact Ha0 |].
    apply (IHn (Datatypes.S (length p'')) ltac:(cbn [length]; lia) (b :: p'') off
             ltac:(reflexivity)).
    intro k.
    pose proof (Hvan k) as Hv.
    cbn [cpeval_lf] in Hv.
    rewrite Ha0 in Hv.
    transitivity ((C0 * Cpow (RtoC (INR (k + off))) (length (b :: p''))
                   + cpeval_lf (b :: p'') (RtoC (INR (k + off))))%C);
      [ring | exact Hv].
Qed.

(** Equal-length complex lists with the same polynomial function are equal. *)
Lemma cpeval_lf_ext_coeffs : forall p q : list C, length p = length q ->
  (forall z, cpeval_lf p z = cpeval_lf q z) -> p = q.
Proof.
  induction p as [|a p' IH]; intros q Hlen Hall.
  - destruct q; [reflexivity | cbn [length] in Hlen; lia].
  - destruct q as [|b q']; [cbn [length] in Hlen; lia |].
    cbn [length] in Hlen.
    assert (Hdiff : Forall (fun c => c = C0)
                      (cpadd (a :: p') (cpscale (Copp C1) (b :: q')))).
    { apply (cp_vanish_zero_gen (length (cpadd (a :: p') (cpscale (Copp C1) (b :: q'))))
               _ 0%nat eq_refl).
      intro k.
      rewrite (cpeval_lf_psub_top (b :: q') (a :: p'))
        by (cbn [length]; lia).
      cbn [length].
      replace (Datatypes.S (length p') - Datatypes.S (length q'))%nat
        with 0%nat by lia.
      cbn [Cpow].
      rewrite (Hall (RtoC (INR (k + 0)))). ring. }
    rewrite cpscale_cons in Hdiff. cbn [cpadd] in Hdiff.
    inversion Hdiff; subst.
    assert (Hab : a = b).
    { transitivity ((a + Copp C1 * b) + b)%C; [ | rewrite H1 ]; ring. }
    f_equal; [exact Hab |].
    apply IH; [lia |].
    intro z.
    pose proof (Hall z) as Hz. cbn [cpeval_lf] in Hz.
    rewrite Hab in Hz.
    assert (Hpow : Cpow z (length p') = Cpow z (length q'))
      by (replace (length p') with (length q') by lia; reflexivity).
    rewrite Hpow in Hz.
    transitivity ((b * Cpow z (length q') + cpeval_lf p' z) - b * Cpow z (length q'))%C;
      [ring |].
    rewrite Hz. ring.
Qed.

(* complex subfields and adjunction -- the subfield calculus, power independence, Euclid, and minimal-relation extraction mirrored over predicates on C. *)

Definition is_Csubfield (K : C -> Prop) : Prop :=
  K C0 /\ K C1 /\
  (forall x y, K x -> K y -> K (x + y)%C) /\
  (forall x y, K x -> K y -> K (x - y)%C) /\
  (forall x y, K x -> K y -> K (x * y)%C) /\
  (forall x, K x -> x <> C0 -> K (Cinv x)).

Lemma Csubfield_0 : forall K, is_Csubfield K -> K C0.
Proof. intros K H; apply H. Qed.
Lemma Csubfield_1 : forall K, is_Csubfield K -> K C1.
Proof. intros K H; apply H. Qed.
Lemma Csubfield_add : forall K x y, is_Csubfield K -> K x -> K y -> K (x + y)%C.
Proof. intros K x y H; apply H. Qed.
Lemma Csubfield_sub : forall K x y, is_Csubfield K -> K x -> K y -> K (x - y)%C.
Proof. intros K x y H; apply H. Qed.
Lemma Csubfield_mul : forall K x y, is_Csubfield K -> K x -> K y -> K (x * y)%C.
Proof. intros K x y H; apply H. Qed.
Lemma Csubfield_inv : forall K x, is_Csubfield K -> K x -> x <> C0 -> K (Cinv x).
Proof. intros K x H; apply H. Qed.
Lemma Csubfield_opp : forall K x, is_Csubfield K -> K x -> K (- x)%C.
Proof.
  intros K x H Hx.
  replace (- x)%C with (C0 - x)%C by ring.
  apply Csubfield_sub; [exact H | apply Csubfield_0; exact H | exact Hx].
Qed.
Lemma Csubfield_div : forall K x y, is_Csubfield K -> K x -> K y -> y <> C0 ->
  K (x / y)%C.
Proof.
  intros K x y H Hx Hy Hne. unfold Cdiv.
  apply Csubfield_mul; [exact H | exact Hx | apply Csubfield_inv; assumption].
Qed.

(** Independence of the powers of z below n over a complex subfield: no nontrivial K-list of length n annihilates z. *)
Definition Cindep_pows (K : C -> Prop) (z : C) (n : nat) : Prop :=
  forall cs : list C, length cs = n -> Forall K cs ->
  cpeval cs z = C0 -> Forall (fun c => c = C0) cs.

(** Normalization, general division, and extended Euclid over C, with Ceq_dec in place of real case splits. *)
Fixpoint clnorm (p : list C) : list C :=
  match p with
  | nil => nil
  | a :: p' => if Ceq_dec a C0 then clnorm p' else p
  end.

Lemma clnorm_k : forall p, clnorm p = klnorm C C0 Ceq_dec p.
Proof.
  induction p as [|a p IH]; cbn [clnorm klnorm].
  - reflexivity.
  - destruct (Ceq_dec a C0); [exact IH | reflexivity].
Qed.

Lemma clnorm_eval : forall p z, cpeval_lf (clnorm p) z = cpeval_lf p z.
Proof.
  intros p z.
  rewrite clnorm_k, !cpeval_lf_k.
  apply (klnorm_eval _ _ _ _ _ _ _ _ _ C_field).
Qed.

Lemma clnorm_Forall : forall (P : C -> Prop) p, Forall P p -> Forall P (clnorm p).
Proof.
  intros P p HP.
  rewrite clnorm_k.
  apply klnorm_Forall. exact HP.
Qed.

Lemma clnorm_length : forall p, (length (clnorm p) <= length p)%nat.
Proof.
  intro p. rewrite clnorm_k. apply klnorm_length.
Qed.

Lemma clnorm_head : forall p, clnorm p = nil \/ hd C0 (clnorm p) <> C0.
Proof.
  intro p. rewrite clnorm_k. apply klnorm_head.
Qed.

Lemma clnorm_nonzero : forall p, ~ Forall (fun c => c = C0) p -> clnorm p <> nil.
Proof.
  intros p Hnz. rewrite clnorm_k. apply klnorm_nonzero. exact Hnz.
Qed.

Lemma clnorm_id_of_head : forall p, p <> nil -> hd C0 p <> C0 -> clnorm p = p.
Proof.
  intros p Hnil Hhd. rewrite clnorm_k.
  apply klnorm_id_of_head; assumption.
Qed.

Lemma clnorm_nil_eval : forall g z, clnorm g = nil -> cpeval_lf g z = C0.
Proof.
  intros g z Hg.
  rewrite clnorm_k in Hg.
  rewrite cpeval_lf_k.
  apply (klnorm_nil_eval _ _ _ _ _ _ _ _ _ C_field Ceq_dec). exact Hg.
Qed.

Definition cpmul_lf (a b : list C) : list C := rev (cpmul (rev a) (rev b)).
Definition cpsub_lf (a b : list C) : list C :=
  rev (cpadd (rev a) (cpscale (Copp C1) (rev b))).
Definition cpadd_lf (a b : list C) : list C := rev (cpadd (rev a) (rev b)).

Lemma cpmul_lf_k : forall a b, cpmul_lf a b = kpmul_lf C C0 Cadd Cmul a b.
Proof.
  intros a b. unfold cpmul_lf, kpmul_lf. rewrite cpmul_k. reflexivity.
Qed.

Lemma cpsub_lf_k : forall a b, cpsub_lf a b = kpsub_lf C C1 Cadd Cmul Copp a b.
Proof.
  intros a b. unfold cpsub_lf, kpsub_lf. rewrite cpadd_k, cpscale_k. reflexivity.
Qed.

Lemma cpadd_lf_k : forall a b, cpadd_lf a b = kpadd_lf C Cadd a b.
Proof.
  intros a b. unfold cpadd_lf, kpadd_lf. rewrite cpadd_k. reflexivity.
Qed.

Lemma cpmul_lf_eval : forall a b z,
  cpeval_lf (cpmul_lf a b) z = (cpeval_lf a z * cpeval_lf b z)%C.
Proof.
  intros a b z. unfold cpmul_lf.
  rewrite cpeval_lf_rev_c, rev_involutive, cpeval_cpmul, <- !cpeval_lf_rev_c.
  reflexivity.
Qed.

Lemma cpsub_lf_eval : forall a b z,
  cpeval_lf (cpsub_lf a b) z = (cpeval_lf a z - cpeval_lf b z)%C.
Proof.
  intros a b z. unfold cpsub_lf.
  rewrite cpeval_lf_rev_c, rev_involutive, cpeval_cpadd, cpeval_cpscale,
    <- !cpeval_lf_rev_c.
  ring.
Qed.

Lemma cpadd_lf_eval : forall a b z,
  cpeval_lf (cpadd_lf a b) z = (cpeval_lf a z + cpeval_lf b z)%C.
Proof.
  intros a b z. unfold cpadd_lf.
  rewrite cpeval_lf_rev_c, rev_involutive, cpeval_cpadd, <- !cpeval_lf_rev_c.
  reflexivity.
Qed.

Lemma Forall_cpadd : forall (P : C -> Prop) a b,
  (forall x y, P x -> P y -> P (x + y)%C) ->
  Forall P a -> Forall P b -> Forall P (cpadd a b).
Proof.
  intros P a. induction a as [|u a IH]; intros b Hadd Ha Hb.
  - exact Hb.
  - destruct b as [|v b]; [exact Ha |].
    cbn [cpadd]. inversion Ha; subst. inversion Hb; subst.
    constructor; [apply Hadd; assumption | apply IH; assumption].
Qed.

Lemma Forall_cpscale : forall (P : C -> Prop) c a,
  (forall x y, P x -> P y -> P (x * y)%C) ->
  P c -> Forall P a -> Forall P (cpscale c a).
Proof.
  intros P c a Hmul Hc Ha. induction Ha as [|u a Hu Ha IH].
  - constructor.
  - cbn [cpscale map]. constructor; [apply Hmul; assumption | exact IH].
Qed.

Lemma Forall_cpmul : forall (P : C -> Prop) a b,
  (forall x y, P x -> P y -> P (x + y)%C) ->
  (forall x y, P x -> P y -> P (x * y)%C) ->
  P C0 -> Forall P a -> Forall P b -> Forall P (cpmul a b).
Proof.
  intros P a. induction a as [|u a IH]; intros b Hadd Hmul H0 Ha Hb.
  - constructor.
  - cbn [cpmul]. inversion Ha; subst.
    apply Forall_cpadd; [exact Hadd | |].
    + apply Forall_cpscale; assumption.
    + constructor; [exact H0 | apply IH; assumption].
Qed.

Lemma cpmul_lf_Forall : forall (K : C -> Prop) a b, is_Csubfield K ->
  Forall K a -> Forall K b -> Forall K (cpmul_lf a b).
Proof.
  intros K a b HK Ha Hb. unfold cpmul_lf.
  apply Forall_rev, Forall_cpmul;
    [intros u v Hu Hv; apply (Csubfield_add K u v HK Hu Hv)
    | intros u v Hu Hv; apply (Csubfield_mul K u v HK Hu Hv)
    | apply (Csubfield_0 K HK)
    | apply Forall_rev; exact Ha
    | apply Forall_rev; exact Hb].
Qed.

Lemma cpsub_lf_Forall : forall (K : C -> Prop) a b, is_Csubfield K ->
  Forall K a -> Forall K b -> Forall K (cpsub_lf a b).
Proof.
  intros K a b HK Ha Hb. unfold cpsub_lf.
  apply Forall_rev, Forall_cpadd;
    [intros u v Hu Hv; apply (Csubfield_add K u v HK Hu Hv)
    | apply Forall_rev; exact Ha |].
  apply Forall_cpscale;
    [intros u v Hu Hv; apply (Csubfield_mul K u v HK Hu Hv)
    | apply (Csubfield_opp K C1 HK (Csubfield_1 K HK))
    | apply Forall_rev; exact Hb].
Qed.

Lemma cpadd_lf_Forall : forall (K : C -> Prop) a b, is_Csubfield K ->
  Forall K a -> Forall K b -> Forall K (cpadd_lf a b).
Proof.
  intros K a b HK Ha Hb. unfold cpadd_lf.
  apply Forall_rev, Forall_cpadd;
    [intros u v Hu Hv; apply (Csubfield_add K u v HK Hu Hv)
    | apply Forall_rev; exact Ha | apply Forall_rev; exact Hb].
Qed.

Lemma cpdiv_lf_Forall : forall (K : C -> Prop) fuel p dtail, is_Csubfield K ->
  Forall K p -> Forall K dtail ->
  Forall K (fst (cpdiv_lf fuel p dtail)) /\
  Forall K (snd (cpdiv_lf fuel p dtail)).
Proof.
  intros K fuel p dtail HK Hp Hd.
  rewrite !cpdiv_lf_k.
  apply (kpdiv_lf_Forall_sf _ _ _ _ _ _ _ _ _ C_field);
    [exact HK | exact Hp | exact Hd].
Qed.

Definition cpdivg (p g : list C) : list C * list C :=
  match clnorm g with
  | nil => (nil, p)
  | c :: dt0 =>
      let dt := cpscale (Cinv c) dt0 in
      (cpscale (Cinv c) (fst (cpdiv_lf (length p) p dt)),
       snd (cpdiv_lf (length p) p dt))
  end.

Lemma cpdivg_k : forall p g,
  cpdivg p g = kpdivg C C0 C1 Cadd Cmul Copp Cinv Ceq_dec p g.
Proof. intros p g. reflexivity. Qed.

Lemma cpdivg_spec : forall (K : C -> Prop) p g, is_Csubfield K ->
  Forall K p -> Forall K g ->
  clnorm g <> nil ->
  Forall K (fst (cpdivg p g)) /\ Forall K (snd (cpdivg p g)) /\
  (length (snd (cpdivg p g)) < length (clnorm g))%nat /\
  (forall z, cpeval_lf p z
     = (cpeval_lf (fst (cpdivg p g)) z * cpeval_lf g z
        + cpeval_lf (snd (cpdivg p g)) z)%C).
Proof.
  intros K p g HK HKp HKg Hgnz.
  rewrite clnorm_k in Hgnz.
  destruct (kpdivg_spec _ _ _ _ _ _ _ _ _ C_field Ceq_dec K p g HK HKp HKg Hgnz)
    as [H1 [H2 [H3 H4]]].
  rewrite <- cpdivg_k in H1, H2, H3.
  rewrite <- clnorm_k in H3.
  split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  intro z.
  rewrite !cpeval_lf_k, cpdivg_k.
  exact (H4 z).
Qed.

(** Extended Euclid over C on leading-first lists. *)
Fixpoint cbezout_lf (fuel : nat) (p g : list C) : (list C * list C) * list C :=
  match fuel with
  | O => ((C1 :: nil, nil), clnorm p)
  | Datatypes.S fu =>
      match clnorm g with
      | nil => ((C1 :: nil, nil), clnorm p)
      | _ :: _ =>
          let q := fst (cpdivg p g) in
          let r := snd (cpdivg p g) in
          let ud := cbezout_lf fu g r in
          ((snd (fst ud), cpsub_lf (fst (fst ud)) (cpmul_lf (snd (fst ud)) q)),
           snd ud)
      end
  end.

Lemma cbezout_lf_k : forall fuel p g,
  cbezout_lf fuel p g = kbezout_lf C C0 C1 Cadd Cmul Copp Cinv Ceq_dec fuel p g.
Proof. intros fuel p g. reflexivity. Qed.

Lemma cbezout_lf_spec : forall (K : C -> Prop) fuel p g, is_Csubfield K ->
  Forall K p -> Forall K g -> (length (clnorm g) <= fuel)%nat ->
  Forall K (fst (fst (cbezout_lf fuel p g))) /\
  Forall K (snd (fst (cbezout_lf fuel p g))) /\
  Forall K (snd (cbezout_lf fuel p g)) /\
  (forall z, (cpeval_lf (fst (fst (cbezout_lf fuel p g))) z * cpeval_lf p z
              + cpeval_lf (snd (fst (cbezout_lf fuel p g))) z * cpeval_lf g z)%C
             = cpeval_lf (snd (cbezout_lf fuel p g)) z) /\
  (exists qp, Forall K qp /\ forall z,
      cpeval_lf p z = (cpeval_lf qp z * cpeval_lf (snd (cbezout_lf fuel p g)) z)%C) /\
  (exists qg, Forall K qg /\ forall z,
      cpeval_lf g z = (cpeval_lf qg z * cpeval_lf (snd (cbezout_lf fuel p g)) z)%C) /\
  (clnorm g <> nil ->
     (length (snd (cbezout_lf fuel p g)) <= length (clnorm g))%nat) /\
  (snd (cbezout_lf fuel p g) = nil \/ hd C0 (snd (cbezout_lf fuel p g)) <> C0).
Proof.
  intros K fuel p g HK HKp HKg Hfuel.
  rewrite clnorm_k in Hfuel.
  destruct (kbezout_lf_spec _ _ _ _ _ _ _ _ _ C_field Ceq_dec K fuel p g
              HK HKp HKg Hfuel)
    as [H1 [H2 [H3 [H4 [[qp [Hqp Hqpe]] [[qg [Hqg Hqge]] [H7 H8]]]]]]].
  rewrite <- cbezout_lf_k in H1, H2, H3, H8.
  split; [exact H1 |].
  split; [exact H2 |].
  split; [exact H3 |].
  split.
  { intro z. rewrite !cpeval_lf_k, !cbezout_lf_k. exact (H4 z). }
  split.
  { exists qp. split; [exact Hqp |].
    intro z. rewrite !cpeval_lf_k, cbezout_lf_k. exact (Hqpe z). }
  split.
  { exists qg. split; [exact Hqg |].
    intro z. rewrite !cpeval_lf_k, cbezout_lf_k. exact (Hqge z). }
  split; [| exact H8].
  intro Hgnz.
  rewrite clnorm_k in Hgnz.
  rewrite cbezout_lf_k, clnorm_k.
  exact (H7 Hgnz).
Qed.

Lemma C1_neq_C0 : C1 <> C0.
Proof. unfold C1, C0. intro H. inversion H. lra. Qed.

(** Monic complex lists of positive degree are nonzero as functions. *)
Lemma cmonic_lf_nonzero : forall fl, hd C0 fl = C1 -> (2 <= length fl)%nat ->
  ~ (forall z, cpeval_lf fl z = C0).
Proof.
  intros fl Hhd Hlen Hall.
  assert (Hz : Forall (fun c => c = C0) fl).
  { apply (cp_vanish_zero_gen (length fl) fl 0%nat eq_refl).
    intro k. apply Hall. }
  destruct fl as [|a fl']; [cbn [length] in Hlen; lia |].
  cbn [hd] in Hhd. inversion Hz; subst.
  exact (C1_neq_C0 H1).
Qed.

(** IRREDUCIBLE MEANS INDEPENDENT, over C. *)
Lemma cirreducible_root_lin_indep :
  forall (K : C -> Prop) (fl : list C) (z0 : C),
  is_Csubfield K ->
  (2 <= length fl)%nat ->
  hd C0 fl = C1 ->
  Forall K fl ->
  cpeval_lf fl z0 = C0 ->
  (forall dl ql, Forall K dl -> Forall K ql ->
     (2 <= length dl)%nat -> (length dl < length fl)%nat ->
     hd C0 dl = C1 ->
     (forall z, cpeval_lf fl z = (cpeval_lf dl z * cpeval_lf ql z)%C) -> False) ->
  Cindep_pows K z0 (length fl - 1).
Proof.
  intros K fl z0 HK Hlen Hmon HKf Hroot Hirr.
  rewrite cpeval_lf_k in Hroot.
  assert (Hkmono : forall fl0, hd C0 fl0 = C1 -> (2 <= length fl0)%nat ->
            ~ (forall z, kpeval_lf C C0 C1 Cadd Cmul fl0 z = C0)).
  { intros fl0 Hh Hl2 Hall.
    apply (cmonic_lf_nonzero fl0 Hh Hl2).
    intro z. rewrite cpeval_lf_k. apply Hall. }
  assert (Hirr' : forall dl ql, Forall K dl -> Forall K ql ->
     (2 <= length dl)%nat -> (length dl < length fl)%nat ->
     hd C0 dl = C1 ->
     (forall z, kpeval_lf C C0 C1 Cadd Cmul fl z
                = (kpeval_lf C C0 C1 Cadd Cmul dl z
                   * kpeval_lf C C0 C1 Cadd Cmul ql z)%C) -> False).
  { intros dl ql Hdl Hql Hl2 Hlt Hhd Hfac.
    apply (Hirr dl ql Hdl Hql Hl2 Hlt Hhd).
    intro z. rewrite !cpeval_lf_k. apply Hfac. }
  intros cs Hl HF Hev.
  rewrite cpeval_k in Hev.
  exact (kirreducible_root_lin_indep _ _ _ _ _ _ _ _ _ C_field Ceq_dec Hkmono
           K fl z0 HK Hlen Hmon HKf Hroot Hirr' cs Hl HF Hev).
Qed.

(* embeddings over complex subfields and the extension theorem, mirroring the real-subfield embedding theory with a complex source field. *)

Definition CCembeds (K : C -> Prop) (sigma : C -> C) : Prop :=
  sigma C0 = C0 /\ sigma C1 = C1 /\
  (forall x y, K x -> K y -> sigma (x + y)%C = (sigma x + sigma y)%C) /\
  (forall x y, K x -> K y -> sigma (x * y)%C = (sigma x * sigma y)%C).

Lemma CCembeds_id : forall K, CCembeds K (fun z => z).
Proof. intro K. repeat split. Qed.

Fixpoint CCevalMap (f : C -> C) (p : list C) (z : C) : C :=
  match p with
  | nil => C0
  | c :: p' => (f c + z * CCevalMap f p' z)%C
  end.

Lemma CCevalMap_cpadd : forall (K : C -> Prop) sigma, CCembeds K sigma ->
  forall ps qs z, Forall K ps -> Forall K qs ->
  CCevalMap sigma (cpadd ps qs) z = (CCevalMap sigma ps z + CCevalMap sigma qs z)%C.
Proof.
  intros K sigma [H0 [H1 [Hadd Hmul]]].
  induction ps as [|p ps' IH]; intros qs z Hps Hqs.
  - cbn [cpadd CCevalMap]. ring.
  - destruct qs as [|q qs'].
    + cbn [cpadd CCevalMap]. ring.
    + cbn [cpadd CCevalMap].
      inversion Hps; subst. inversion Hqs; subst.
      rewrite IH by assumption.
      rewrite Hadd by assumption. ring.
Qed.

Lemma CCevalMap_cpscale : forall (K : C -> Prop) sigma, CCembeds K sigma ->
  forall a ps z, K a -> Forall K ps ->
  CCevalMap sigma (cpscale a ps) z = (sigma a * CCevalMap sigma ps z)%C.
Proof.
  intros K sigma [H0 [H1 [Hadd Hmul]]].
  induction ps as [|p ps' IH]; intros z Ha Hps.
  - cbn [cpscale map CCevalMap]. ring.
  - rewrite cpscale_cons. cbn [CCevalMap].
    inversion Hps; subst.
    rewrite IH by assumption.
    rewrite Hmul by assumption. ring.
Qed.

Lemma CCevalMap_cpmul : forall (K : C -> Prop) sigma, CCembeds K sigma ->
  is_Csubfield K ->
  forall ps qs z, Forall K ps -> Forall K qs ->
  CCevalMap sigma (cpmul ps qs) z = (CCevalMap sigma ps z * CCevalMap sigma qs z)%C.
Proof.
  intros K sigma Hemb HK.
  pose proof Hemb as [Hs0 [Hs1 [Hsadd Hsmul]]].
  induction ps as [|p ps' IH]; intros qs z Hps Hqs.
  - cbn [cpmul CCevalMap]. ring.
  - cbn [cpmul].
    inversion Hps; subst.
    assert (Hscale : Forall K (cpscale p qs)).
    { apply Forall_cpscale;
        [intros u v Hu Hv; apply (Csubfield_mul K u v HK Hu Hv) | assumption | assumption]. }
    assert (Htail : Forall K (C0 :: cpmul ps' qs)).
    { constructor; [apply (Csubfield_0 K HK) |].
      apply Forall_cpmul;
        [intros u v Hu Hv; apply (Csubfield_add K u v HK Hu Hv)
        | intros u v Hu Hv; apply (Csubfield_mul K u v HK Hu Hv)
        | apply (Csubfield_0 K HK) | assumption | assumption]. }
    rewrite (CCevalMap_cpadd K sigma Hemb _ _ z Hscale Htail).
    rewrite (CCevalMap_cpscale K sigma Hemb) by assumption.
    cbn [CCevalMap].
    rewrite IH by assumption.
    rewrite Hs0. ring.
Qed.

Lemma CCevalMap_app : forall (f : C -> C) (l1 l2 : list C) z,
  CCevalMap f (l1 ++ l2) z
  = (CCevalMap f l1 z + Cpow z (length l1) * CCevalMap f l2 z)%C.
Proof.
  induction l1 as [|a l1' IH]; intros l2 z.
  - cbn [app CCevalMap length Cpow]. ring.
  - cbn [app CCevalMap length Cpow]. rewrite IH. ring.
Qed.

Lemma CCevalMap_zeros : forall (sigma : C -> C), sigma C0 = C0 ->
  forall n z, CCevalMap sigma (repeat C0 n) z = C0.
Proof.
  intros sigma Hs0. induction n as [|n IH]; intro z; cbn [repeat CCevalMap].
  - reflexivity.
  - rewrite Hs0, IH. ring.
Qed.

(** The complex adjunction span, in list form. *)
Definition CPolyF (K : C -> Prop) (d : nat) (r : C) (x : C) : Prop :=
  exists cs : list C, length cs = d /\ Forall K cs /\ x = cpeval cs r.

(** Unique representation over independent powers. *)
Lemma CPolyF_unique_rep : forall (K : C -> Prop) (r : C) (j : nat),
  is_Csubfield K ->
  Cindep_pows K r j ->
  forall cs ds : list C, length cs = j -> length ds = j ->
  Forall K cs -> Forall K ds ->
  cpeval cs r = cpeval ds r ->
  cs = ds.
Proof.
  intros K r j HK Hindep cs ds Hlc Hld HKc HKd Hev.
  set (e := cpadd cs (cpscale (Copp C1) ds)).
  assert (Hle : length e = j)
    by (unfold e; rewrite cpadd_length, cpscale_length; lia).
  assert (HKe : Forall K e).
  { unfold e. apply Forall_cpadd;
      [intros u v Hu Hv; apply (Csubfield_add K u v HK Hu Hv) | exact HKc |].
    apply Forall_cpscale;
      [intros u v Hu Hv; apply (Csubfield_mul K u v HK Hu Hv)
      | apply (Csubfield_opp K C1 HK (Csubfield_1 K HK)) | exact HKd]. }
  assert (Heval : cpeval e r = C0).
  { unfold e. rewrite cpeval_cpadd, cpeval_cpscale, Hev. ring. }
  pose proof (Hindep e Hle HKe Heval) as Hzero.
  unfold e in Hzero.
  assert (Hlen2 : length cs = length ds) by lia.
  clear - Hzero Hlen2.
  revert ds Hlen2 Hzero.
  induction cs as [|a cs' IH]; intros ds Hlen2 Hzero.
  - destruct ds; [reflexivity | cbn [length] in Hlen2; lia].
  - destruct ds as [|b ds']; [cbn [length] in Hlen2; lia |].
    rewrite cpscale_cons in Hzero. cbn [cpadd] in Hzero.
    inversion Hzero; subst.
    cbn [length] in Hlen2.
    f_equal.
    + transitivity ((a + Copp C1 * b) + b)%C; [ | rewrite H1 ]; ring.
    + apply IH; [lia | assumption].
Qed.

Lemma cpeval_app : forall (l1 l2 : list C) z,
  cpeval (l1 ++ l2) z = (cpeval l1 z + Cpow z (length l1) * cpeval l2 z)%C.
Proof.
  induction l1 as [|a l1' IH]; intros l2 z.
  - cbn [app cpeval length Cpow]. ring.
  - cbn [app cpeval length Cpow]. rewrite IH. ring.
Qed.

Lemma cpeval_repeatC0 : forall n z, cpeval (repeat C0 n) z = C0.
Proof.
  induction n as [|n IH]; intro z; cbn [repeat cpeval]; [reflexivity | rewrite IH; ring].
Qed.

Lemma cpeval_ext_coeffs : forall p q : list C, length p = length q ->
  (forall z, cpeval p z = cpeval q z) -> p = q.
Proof.
  intros p q Hlen Hall.
  rewrite <- (rev_involutive p), <- (rev_involutive q).
  f_equal.
  apply cpeval_lf_ext_coeffs; [rewrite !length_rev; exact Hlen |].
  intro z. rewrite !cpeval_lf_rev_c, !rev_involutive. apply Hall.
Qed.

Lemma Forall_app_intro_c : forall (P : C -> Prop) (l1 l2 : list C),
  Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  intros P l1 l2 H1 H2. induction H1 as [|a l1' Ha H1' IH].
  - exact H2.
  - cbn [app]. constructor; assumption.
Qed.

Lemma cpmul_cons : forall (x : C) (a b : list C),
  cpmul (x :: a) b = cpadd (cpscale x b) (C0 :: cpmul a b).
Proof. reflexivity. Qed.

Lemma cpmul_length : forall (a b : list C),
  (1 <= length a)%nat -> (1 <= length b)%nat ->
  length (cpmul a b) = (length a + length b - 1)%nat.
Proof.
  induction a as [|x a' IHa]; intros b Ha Hb.
  - cbn [length] in Ha. lia.
  - rewrite cpmul_cons, cpadd_length, cpscale_length.
    cbn [length].
    destruct a' as [|y a''].
    + cbn [cpmul length]. lia.
    + rewrite (IHa b) by (cbn [length]; lia).
      cbn [length]. lia.
Qed.

(** THE COMPLEX REDUCTION LEMMA: division by the minimal relation collapses identically under the sigma-w evaluation and at the root itself. *)
Lemma CCevalMap_reduction : forall (K : C -> Prop) (sigma : C -> C),
  CCembeds K sigma -> is_Csubfield K ->
  forall (j : nat) (dtcf : list C) (r w : C), (1 <= j)%nat ->
  length dtcf = j -> Forall K dtcf ->
  (cpeval dtcf r + Cpow r j)%C = C0 ->
  (CCevalMap sigma dtcf w + Cpow w j)%C = C0 ->
  forall g : list C, Forall K g ->
  Forall K (snd (cpdiv_lf (length (rev g)) (rev g) (rev dtcf))) /\
  (length (snd (cpdiv_lf (length (rev g)) (rev g) (rev dtcf))) <= j)%nat /\
  cpeval g r = cpeval_lf (snd (cpdiv_lf (length (rev g)) (rev g) (rev dtcf))) r /\
  CCevalMap sigma g w
    = CCevalMap sigma (rev (snd (cpdiv_lf (length (rev g)) (rev g) (rev dtcf)))) w.
Proof.
  intros K sigma Hemb HK j dtcf r w Hj Hlen HKdt Hrel Hw g HKg.
  pose proof Hemb as [Hs0 [Hs1 [Hsadd Hsmul]]].
  set (dt := rev dtcf) in *.
  assert (Hlen_dt : length dt = j) by (unfold dt; rewrite length_rev; exact Hlen).
  assert (HKdtl : Forall K dt) by (unfold dt; apply Forall_rev; exact HKdt).
  assert (HKrevg : Forall K (rev g)) by (apply Forall_rev; exact HKg).
  set (q := fst (cpdiv_lf (length (rev g)) (rev g) dt)) in *.
  set (rr := snd (cpdiv_lf (length (rev g)) (rev g) dt)) in *.
  destruct (cpdiv_lf_Forall K (length (rev g)) (rev g) dt HK HKrevg HKdtl) as [HKq HKr].
  pose proof (cpdiv_lf_rlen (length (rev g)) (rev g) dt (Nat.le_refl _)) as Hrlen.
  rewrite Hlen_dt in Hrlen.
  pose proof (cpdiv_lf_eval (length (rev g)) (rev g) dt (Nat.le_refl _)) as Hspec.
  rewrite Hlen_dt in Hspec.
  fold q rr in Hspec, HKq, HKr, Hrlen.
  assert (Hdt_eval : forall y, cpeval_lf dt y = cpeval dtcf y).
  { intro y. unfold dt. rewrite cpeval_lf_rev_c, rev_involutive. reflexivity. }
  split; [exact HKr | split; [exact Hrlen | split]].
  - pose proof (Hspec r) as Hb.
    rewrite Hdt_eval in Hb.
    assert (Hz : (Cpow r j + cpeval dtcf r)%C = C0)
      by (rewrite <- Hrel; ring).
    rewrite Hz in Hb.
    assert (Hgr : cpeval_lf (rev g) r = cpeval g r)
      by (rewrite cpeval_lf_rev_c, rev_involutive; reflexivity).
    rewrite Hgr in Hb. rewrite Hb. ring.
  - set (Mcf := dtcf ++ C1 :: nil).
    assert (HlenM : length Mcf = Datatypes.S j)
      by (unfold Mcf; rewrite length_app, Hlen; cbn [length]; lia).
    assert (HKM : Forall K Mcf).
    { unfold Mcf. apply Forall_app_intro_c; [exact HKdt |].
      constructor; [apply (Csubfield_1 K HK) | constructor]. }
    assert (HMw : CCevalMap sigma Mcf w = C0).
    { unfold Mcf. rewrite CCevalMap_app, Hlen.
      cbn [CCevalMap]. rewrite Hs1.
      transitivity ((CCevalMap sigma dtcf w + Cpow w j)%C); [ring | exact Hw]. }
    set (pad := repeat C0 (length g - length rr)).
    assert (HKpad : Forall K pad).
    { apply Forall_forall. intros z Hz.
      apply repeat_spec in Hz. subst z. apply (Csubfield_0 K HK). }
    assert (Hrg : (length rr <= length g)%nat).
    { destruct (le_lt_dec (length (rev g)) (length dt)) as [Hle | Hgt].
      - unfold rr.
        assert (Hnodiv : cpdiv_lf (length (rev g)) (rev g) dt = (nil, rev g)).
        { destruct (length (rev g)) as [|f] eqn:Ef.
          - cbn [cpdiv_lf].
            destruct (rev g); [reflexivity | cbn [length] in Ef; lia].
          - cbn [cpdiv_lf].
            destruct (Nat.leb_spec (length (rev g)) (length dt)) as [_ | Habs];
              [reflexivity | lia]. }
        rewrite Hnodiv. cbn [snd]. rewrite length_rev. lia.
      - rewrite length_rev in Hgt. lia. }
    assert (Hcoeff : g = cpadd (cpmul (rev q) Mcf) (rev rr ++ pad)).
    { apply cpeval_ext_coeffs.
      - unfold pad.
        rewrite cpadd_length, length_app, length_rev, repeat_length.
        pose proof (cpdiv_lf_qlen (length (rev g)) (rev g) dt (Nat.le_refl _)) as Hql.
        fold q in Hql. rewrite Hlen_dt, length_rev in Hql.
        destruct (le_lt_dec (length g) j) as [Hle | Hgt].
        + assert (Hq0 : length (rev q) = 0%nat) by (rewrite length_rev; lia).
          apply length_zero_iff_nil in Hq0. rewrite Hq0.
          cbn [cpmul length]. lia.
        + rewrite cpmul_length by (rewrite ?length_rev, ?HlenM; lia).
          rewrite length_rev, HlenM, Hql. lia.
      - intro z. unfold pad.
        rewrite cpeval_cpadd, cpeval_cpmul, cpeval_app, cpeval_repeatC0.
        assert (HMz : cpeval Mcf z = (Cpow z j + cpeval_lf dt z)%C).
        { unfold Mcf. rewrite cpeval_app, Hlen.
          cbn [cpeval]. rewrite Hdt_eval. ring. }
        rewrite HMz.
        assert (Hqz : cpeval (rev q) z = cpeval_lf q z)
          by (rewrite cpeval_lf_rev_c; reflexivity).
        assert (Hrz : cpeval (rev rr) z = cpeval_lf rr z)
          by (rewrite cpeval_lf_rev_c; reflexivity).
        rewrite Hqz, Hrz.
        pose proof (Hspec z) as Hx.
        assert (Hgz : cpeval_lf (rev g) z = cpeval g z)
          by (rewrite cpeval_lf_rev_c, rev_involutive; reflexivity).
        rewrite Hgz in Hx. rewrite Hx. ring. }
    rewrite Hcoeff.
    rewrite (CCevalMap_cpadd K sigma Hemb).
    + rewrite (CCevalMap_cpmul K sigma Hemb HK);
        [| apply Forall_rev; exact HKq | exact HKM].
      rewrite HMw.
      rewrite CCevalMap_app.
      unfold pad. rewrite (CCevalMap_zeros sigma Hs0).
      ring.
    + apply Forall_cpmul;
        [ intros u v Hu Hv; apply (Csubfield_add K u v HK Hu Hv)
        | intros u v Hu Hv; apply (Csubfield_mul K u v HK Hu Hv)
        | apply (Csubfield_0 K HK)
        | apply Forall_rev; exact HKq
        | exact HKM ].
    + apply Forall_app_intro_c; [apply Forall_rev; exact HKr | exact HKpad].
Qed.

(** THE COMPLEX EMBEDDING EXTENSION THEOREM: an embedding of K extends to K(r) by sending r to any root of the image of the minimal relation. *)
Theorem CCembeds_extend_step :
  forall (K : C -> Prop) (r : C) (j : nat) (dtcf : list C)
         (sigma : C -> C) (w : C),
  is_Csubfield K -> (2 <= j)%nat ->
  length dtcf = j -> Forall K dtcf ->
  (cpeval dtcf r + Cpow r j)%C = C0 ->
  Cindep_pows K r j ->
  CCembeds K sigma ->
  (CCevalMap sigma dtcf w + Cpow w j)%C = C0 ->
  exists sigma' : C -> C,
    CCembeds (CPolyF K j r) sigma' /\
    (forall x, K x -> sigma' x = sigma x) /\
    sigma' r = w.
Proof.
  intros K r j dtcf sigma w HK Hj Hlen HKdt Hrel Hindep Hemb Hw.
  pose proof Hemb as [Hs0 [Hs1 [Hsadd Hsmul]]].
  assert (Hj1 : (1 <= j)%nat) by lia.
  assert (Hrepex : forall x, CPolyF K j r x ->
    exists! cs : list C, length cs = j /\ Forall K cs /\ x = cpeval cs r).
  { intros x [cs [Hl [HKcs Hx]]].
    exists cs.
    split; [exact (conj Hl (conj HKcs Hx)) |].
    intros ds [Hld [HKd Hevd]].
    apply (CPolyF_unique_rep K r j HK Hindep);
      [exact Hl | exact Hld | exact HKcs | exact HKd |].
    rewrite <- Hx. exact Hevd. }
  set (sigma' := fun x : C =>
    match excluded_middle_informative (CPolyF K j r x) with
    | left H => CCevalMap sigma
        (proj1_sig (constructive_definite_description _ (Hrepex x H))) w
    | right _ => C0
    end).
  assert (Hchar : forall x (cs : list C), length cs = j -> Forall K cs ->
            x = cpeval cs r -> sigma' x = CCevalMap sigma cs w).
  { intros x cs Hl HKcs Hx.
    unfold sigma'.
    destruct (excluded_middle_informative (CPolyF K j r x)) as [Hin | Hout].
    - destruct (constructive_definite_description _ (Hrepex x Hin))
        as [ds [Hld [HKd Hevd]]].
      cbn [proj1_sig].
      assert (Heq : ds = cs).
      { apply (CPolyF_unique_rep K r j HK Hindep);
          [exact Hld | exact Hl | exact HKd | exact HKcs |].
        rewrite <- Hevd, <- Hx. reflexivity. }
      rewrite Heq. reflexivity.
    - exfalso. apply Hout.
      exists cs. exact (conj Hl (conj HKcs Hx)). }
  exists sigma'.
  assert (HKzeros : forall n, Forall K (repeat C0 n)).
  { intro n. apply Forall_forall. intros z Hz.
    apply repeat_spec in Hz. subst z. apply (Csubfield_0 K HK). }
  assert (Hzero_rep : sigma' C0 = C0).
  { rewrite (Hchar C0 (repeat C0 j)).
    - apply (CCevalMap_zeros sigma Hs0).
    - apply repeat_length.
    - apply HKzeros.
    - rewrite cpeval_repeatC0. reflexivity. }
  assert (Hagree : forall x, K x -> sigma' x = sigma x).
  { intros x Hx.
    rewrite (Hchar x (x :: repeat C0 (j - 1))).
    - cbn [CCevalMap]. rewrite (CCevalMap_zeros sigma Hs0). ring.
    - cbn [length]. rewrite repeat_length. lia.
    - constructor; [exact Hx | apply HKzeros].
    - cbn [cpeval]. rewrite cpeval_repeatC0. ring. }
  split; [| split].
  - split; [exact Hzero_rep |].
    split.
    { rewrite (Hagree C1 (Csubfield_1 K HK)). exact Hs1. }
    split.
    + (* additivity *)
      intros x y Hx Hy.
      destruct Hx as [csx [Hlx [HKx Hxr]]]. destruct Hy as [csy [Hly [HKy Hyr]]].
      rewrite (Hchar (x + y)%C (cpadd csx csy)).
      * rewrite (CCevalMap_cpadd K sigma Hemb _ _ w HKx HKy).
        rewrite (Hchar x csx Hlx HKx Hxr), (Hchar y csy Hly HKy Hyr).
        reflexivity.
      * rewrite cpadd_length. lia.
      * apply Forall_cpadd;
          [intros u v Hu Hv; apply (Csubfield_add K u v HK Hu Hv)
          | exact HKx | exact HKy].
      * rewrite cpeval_cpadd, <- Hxr, <- Hyr. reflexivity.
    + (* multiplicativity *)
      intros x y Hx Hy.
      destruct Hx as [csx [Hlx [HKx Hxr]]]. destruct Hy as [csy [Hly [HKy Hyr]]].
      set (g := cpmul csx csy).
      assert (HKg : Forall K g).
      { unfold g. apply Forall_cpmul;
          [intros u v Hu Hv; apply (Csubfield_add K u v HK Hu Hv)
          | intros u v Hu Hv; apply (Csubfield_mul K u v HK Hu Hv)
          | apply (Csubfield_0 K HK) | exact HKx | exact HKy]. }
      destruct (CCevalMap_reduction K sigma Hemb HK j dtcf r w Hj1 Hlen HKdt Hrel Hw g HKg)
        as [HKrem [Hremlen [Hreal Hcplx]]].
      set (rem := snd (cpdiv_lf (length (rev g)) (rev g) (rev dtcf))) in *.
      rewrite (Hchar (x * y)%C (rev rem ++ repeat C0 (j - length rem))).
      * rewrite CCevalMap_app.
        rewrite (CCevalMap_zeros sigma Hs0).
        rewrite (Hchar x csx Hlx HKx Hxr), (Hchar y csy Hly HKy Hyr).
        transitivity (CCevalMap sigma (rev rem) w); [ring |].
        rewrite <- Hcplx. unfold g.
        rewrite (CCevalMap_cpmul K sigma Hemb HK _ _ w HKx HKy).
        reflexivity.
      * rewrite length_app, length_rev, repeat_length. lia.
      * apply Forall_app_intro_c; [apply Forall_rev; exact HKrem | apply HKzeros].
      * rewrite cpeval_app, cpeval_repeatC0.
        assert (Hbr : cpeval (rev rem) r = cpeval_lf rem r)
          by (rewrite cpeval_lf_rev_c; reflexivity).
        rewrite Hbr, <- Hreal.
        unfold g. rewrite cpeval_cpmul, <- Hxr, <- Hyr. ring.
  - exact Hagree.
  - (* sigma' r = w *)
    rewrite (Hchar r (C0 :: C1 :: repeat C0 (j - 2))).
    + cbn [CCevalMap]. rewrite (CCevalMap_zeros sigma Hs0), Hs0, Hs1. ring.
    + cbn [length]. rewrite repeat_length. lia.
    + constructor; [apply (Csubfield_0 K HK) |].
      constructor; [apply (Csubfield_1 K HK) | apply HKzeros].
    + cbn [cpeval]. rewrite cpeval_repeatC0. ring.
Qed.

(** CCevalMap under the identity is evaluation. *)
Lemma CCevalMap_id : forall p z, CCevalMap (fun c => c) p z = cpeval p z.
Proof.
  induction p as [|c p IH]; intro z; cbn [CCevalMap cpeval].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** CCevalMap depends only on sigma's values at the coefficients. *)
Lemma CCevalMap_ext_on : forall (sigma tau : C -> C) p z,
  Forall (fun c => sigma c = tau c) p ->
  CCevalMap sigma p z = CCevalMap tau p z.
Proof.
  intros sigma tau p z Hp. induction Hp as [|c p Hc Hp IH]; cbn [CCevalMap].
  - reflexivity.
  - rewrite Hc, IH. reflexivity.
Qed.

(** Every K-polynomial evaluation at r reduces into the degree-j span: the closure workhorse for the adjunction. *)
Lemma CPolyF_reduce : forall (K : C -> Prop) (r : C) (j : nat) (dtcf : list C),
  is_Csubfield K -> (1 <= j)%nat ->
  length dtcf = j -> Forall K dtcf ->
  (cpeval dtcf r + Cpow r j)%C = C0 ->
  forall g : list C, Forall K g -> CPolyF K j r (cpeval g r).
Proof.
  intros K r j dtcf HK Hj Hlen HKdt Hrel g HKg.
  assert (Hwid : (CCevalMap (fun c => c) dtcf r + Cpow r j)%C = C0)
    by (rewrite CCevalMap_id; exact Hrel).
  destruct (CCevalMap_reduction K (fun c => c) (CCembeds_id K) HK j dtcf r r
              Hj Hlen HKdt Hrel Hwid g HKg) as [HKrem [Hremlen [Hreal _]]].
  set (rem := snd (cpdiv_lf (length (rev g)) (rev g) (rev dtcf))) in *.
  exists (rev rem ++ repeat C0 (j - length rem)).
  split; [| split].
  - rewrite length_app, length_rev, repeat_length. lia.
  - apply Forall_app_intro_c; [apply Forall_rev; exact HKrem |].
    apply Forall_forall. intros z Hz.
    apply repeat_spec in Hz. subst z. apply (Csubfield_0 K HK).
  - rewrite cpeval_app, cpeval_repeatC0.
    assert (Hbr : cpeval (rev rem) r = cpeval_lf rem r)
      by (rewrite cpeval_lf_rev_c; reflexivity).
    rewrite Hbr, <- Hreal. ring.
Qed.

Lemma CPolyF_contains : forall (K : C -> Prop) (r : C) (j : nat) (dtcf : list C),
  is_Csubfield K -> (1 <= j)%nat ->
  length dtcf = j -> Forall K dtcf ->
  (cpeval dtcf r + Cpow r j)%C = C0 ->
  forall x, K x -> CPolyF K j r x.
Proof.
  intros K r j dtcf HK Hj Hlen HKdt Hrel x Hx.
  replace x with (cpeval (x :: nil) r) by (cbn [cpeval]; ring).
  apply (CPolyF_reduce K r j dtcf HK Hj Hlen HKdt Hrel).
  constructor; [exact Hx | constructor].
Qed.

Lemma CPolyF_r_mem : forall (K : C -> Prop) (r : C) (j : nat) (dtcf : list C),
  is_Csubfield K -> (1 <= j)%nat ->
  length dtcf = j -> Forall K dtcf ->
  (cpeval dtcf r + Cpow r j)%C = C0 ->
  CPolyF K j r r.
Proof.
  intros K r j dtcf HK Hj Hlen HKdt Hrel.
  assert (He : cpeval (C0 :: C1 :: nil) r = r) by (cbn [cpeval]; ring).
  assert (H : CPolyF K j r (cpeval (C0 :: C1 :: nil) r)).
  { apply (CPolyF_reduce K r j dtcf HK Hj Hlen HKdt Hrel).
    constructor; [apply (Csubfield_0 K HK) |].
    constructor; [apply (Csubfield_1 K HK) | constructor]. }
  exact (eq_ind (cpeval (C0 :: C1 :: nil) r) (CPolyF K j r) H r He).
Qed.

Lemma CPolyF_add : forall (K : C -> Prop) (r : C) (j : nat),
  is_Csubfield K ->
  forall x y, CPolyF K j r x -> CPolyF K j r y -> CPolyF K j r (x + y)%C.
Proof.
  intros K r j HK x y [cx [Hlx [HKx Hx]]] [cy [Hly [HKy Hy]]].
  exists (cpadd cx cy).
  split; [rewrite cpadd_length; lia | split].
  - apply Forall_cpadd;
      [intros u v Hu Hv; apply (Csubfield_add K u v HK Hu Hv) | exact HKx | exact HKy].
  - rewrite cpeval_cpadd, <- Hx, <- Hy. reflexivity.
Qed.

Lemma CPolyF_sub : forall (K : C -> Prop) (r : C) (j : nat),
  is_Csubfield K ->
  forall x y, CPolyF K j r x -> CPolyF K j r y -> CPolyF K j r (x - y)%C.
Proof.
  intros K r j HK x y [cx [Hlx [HKx Hx]]] [cy [Hly [HKy Hy]]].
  exists (cpadd cx (cpscale (Copp C1) cy)).
  split; [rewrite cpadd_length, cpscale_length; lia | split].
  - apply Forall_cpadd;
      [intros u v Hu Hv; apply (Csubfield_add K u v HK Hu Hv) | exact HKx |].
    apply Forall_cpscale;
      [intros u v Hu Hv; apply (Csubfield_mul K u v HK Hu Hv)
      | apply (Csubfield_opp K C1 HK (Csubfield_1 K HK)) | exact HKy].
  - rewrite cpeval_cpadd, cpeval_cpscale, <- Hx, <- Hy. ring.
Qed.

Lemma CPolyF_mul : forall (K : C -> Prop) (r : C) (j : nat) (dtcf : list C),
  is_Csubfield K -> (1 <= j)%nat ->
  length dtcf = j -> Forall K dtcf ->
  (cpeval dtcf r + Cpow r j)%C = C0 ->
  forall x y, CPolyF K j r x -> CPolyF K j r y -> CPolyF K j r (x * y)%C.
Proof.
  intros K r j dtcf HK Hj Hlen HKdt Hrel x y [cx [Hlx [HKx Hx]]] [cy [Hly [HKy Hy]]].
  assert (Hxy : (x * y)%C = cpeval (cpmul cx cy) r)
    by (rewrite cpeval_cpmul, <- Hx, <- Hy; reflexivity).
  rewrite Hxy.
  apply (CPolyF_reduce K r j dtcf HK Hj Hlen HKdt Hrel).
  apply Forall_cpmul;
    [intros u v Hu Hv; apply (Csubfield_add K u v HK Hu Hv)
    | intros u v Hu Hv; apply (Csubfield_mul K u v HK Hu Hv)
    | apply (Csubfield_0 K HK) | exact HKx | exact HKy].
Qed.

(* the Gaussian dependence kernel -- any n+1 vectors in K^n are K-dependent by pivoting, and the adjunction inverse falls out of the dependence of powers. *)

Fixpoint cdot (cs xs : list C) : C :=
  match cs, xs with
  | c :: cs', x :: xs' => (c * x + cdot cs' xs')%C
  | _, _ => C0
  end.

Lemma cdot_nil_r : forall cs, cdot cs nil = C0.
Proof. destruct cs; reflexivity. Qed.

Lemma nth_cpadd : forall u v k,
  nth k (cpadd u v) C0 = (nth k u C0 + nth k v C0)%C.
Proof.
  induction u as [|a u IH]; intros v k.
  - cbn [cpadd]. destruct k; cbn [nth]; ring.
  - destruct v as [|b v].
    + cbn [cpadd]. destruct k; cbn [nth]; ring.
    + cbn [cpadd]. destruct k as [|k']; cbn [nth]; [ring | apply IH].
Qed.

Lemma nth_cpscale : forall a v k,
  nth k (cpscale a v) C0 = (a * nth k v C0)%C.
Proof.
  intros a v k.
  destruct (le_lt_dec (length v) k) as [Hge | Hlt].
  - rewrite !nth_overflow; [ring | lia | rewrite cpscale_length; lia].
  - unfold cpscale.
    replace C0 with (Cmul a C0) at 1 by ring.
    apply map_nth.
Qed.

(** cdot against a pointwise-affine map of the vectors. *)
Lemma cdot_map_affine : forall (cs : list C) (A : Type) (rest : list A)
    (F G : A -> C) (t : C),
  cdot cs (map (fun v => (F v + G v * t)%C) rest)
  = (cdot cs (map F rest) + cdot cs (map G rest) * t)%C.
Proof.
  induction cs as [|c cs IH]; intros A rest F G t.
  - cbn [cdot]. ring.
  - destruct rest as [|v rest].
    + cbn [map cdot]. ring.
    + cbn [map cdot]. rewrite IH. ring.
Qed.

Lemma cdot_map_ext : forall (cs : list C) (A : Type) (rest : list A) (F G : A -> C),
  (forall v, In v rest -> F v = G v) ->
  cdot cs (map F rest) = cdot cs (map G rest).
Proof.
  induction cs as [|c cs IH]; intros A rest F G H.
  - reflexivity.
  - destruct rest as [|v rest].
    + reflexivity.
    + cbn [map cdot].
      rewrite (H v) by (left; reflexivity).
      rewrite (IH A rest F G) by (intros; apply H; right; assumption).
      reflexivity.
Qed.

Lemma cdot_K : forall (K : C -> Prop) cs xs, is_Csubfield K ->
  Forall K cs -> Forall K xs -> K (cdot cs xs).
Proof.
  intros K cs. induction cs as [|c cs IH]; intros xs HK Hcs Hxs.
  - cbn [cdot]. apply (Csubfield_0 K HK).
  - destruct xs as [|x xs].
    + cbn [cdot]. apply (Csubfield_0 K HK).
    + cbn [cdot]. inversion Hcs; subst. inversion Hxs; subst.
      apply Csubfield_add; [exact HK | |].
      * apply Csubfield_mul; assumption.
      * apply IH; assumption.
Qed.

Lemma cdot_app : forall cs1 cs2 xs1 xs2, length cs1 = length xs1 ->
  cdot (cs1 ++ cs2) (xs1 ++ xs2) = (cdot cs1 xs1 + cdot cs2 xs2)%C.
Proof.
  induction cs1 as [|c cs1 IH]; intros cs2 xs1 xs2 Hlen.
  - destruct xs1; [cbn [app cdot]; ring | cbn [length] in Hlen; lia].
  - destruct xs1 as [|x xs1]; [cbn [length] in Hlen; lia |].
    cbn [app cdot]. rewrite (IH cs2 xs1 xs2) by (cbn [length] in Hlen; lia).
    ring.
Qed.

(** The coordinate of a linear combination of vectors. *)
Definition vcoord (cs : list C) (vecs : list (list C)) (k : nat) : C :=
  cdot cs (map (fun v => nth k v C0) vecs).

Lemma vcoord_K : forall (K : C -> Prop) cs vecs k, is_Csubfield K ->
  Forall K cs -> Forall (Forall K) vecs -> K (vcoord cs vecs k).
Proof.
  intros K cs vecs k HK Hcs Hvecs.
  unfold vcoord.
  apply cdot_K; [exact HK | exact Hcs |].
  apply Forall_forall. intros x Hx.
  apply in_map_iff in Hx. destruct Hx as [v [Hxv Hin]]. subst x.
  assert (Hv : Forall K v)
    by (apply (proj1 (Forall_forall (Forall K) vecs) Hvecs); exact Hin).
  destruct (le_lt_dec (length v) k) as [Hge | Hlt].
  - rewrite nth_overflow by lia. apply (Csubfield_0 K HK).
  - apply (proj1 (Forall_forall K v) Hv). apply nth_In. exact Hlt.
Qed.

Lemma cdot_zero_r : forall cs xs, Forall (fun x => x = C0) xs -> cdot cs xs = C0.
Proof.
  induction cs as [|c cs IH]; intros xs Hxs.
  - reflexivity.
  - destruct xs as [|x xs]; [reflexivity |].
    inversion Hxs; subst.
    cbn [cdot]. rewrite (IH xs) by assumption. ring.
Qed.

Lemma cdot_C0_head : forall xs, cdot (C0 :: nil) xs = C0.
Proof. destruct xs; cbn [cdot]; ring. Qed.

Lemma firstn_map_c : forall (A B : Type) (f : A -> B) (n : nat) (l : list A),
  firstn n (map f l) = map f (firstn n l).
Proof.
  intros A B f n. induction n as [|n IH]; intro l.
  - reflexivity.
  - destruct l as [|a l]; [reflexivity |].
    cbn [map firstn]. rewrite IH. reflexivity.
Qed.

Lemma nth_tl_shift : forall (v : list C) k, nth k (tl v) C0 = nth (Datatypes.S k) v C0.
Proof. intros v k. destruct v; [destruct k; reflexivity | reflexivity]. Qed.

Lemma Forall_zero_app_split : forall (u v : list C),
  Forall (fun c => c = C0) (u ++ v) <->
  Forall (fun c => c = C0) u /\ Forall (fun c => c = C0) v.
Proof. intros u v. apply Forall_app. Qed.

Lemma Forall_nth_C : forall (K : C -> Prop) (v : list C) (i : nat),
  Forall K v -> (i < length v)%nat -> K (nth i v C0).
Proof.
  intros K v i HK Hi.
  apply (proj1 (Forall_forall K v) HK).
  apply nth_In. exact Hi.
Qed.

(** THE GAUSSIAN DEPENDENCE: any n+1 vectors in K^n are K-linearly dependent. *)
Lemma vectors_dependent : forall (n : nat) (K : C -> Prop) (vecs : list (list C)),
  is_Csubfield K ->
  length vecs = Datatypes.S n ->
  Forall (fun v => length v = n) vecs ->
  Forall (Forall K) vecs ->
  exists cs, length cs = Datatypes.S n /\ Forall K cs /\
    ~ Forall (fun c => c = C0) cs /\
    forall k, vcoord cs vecs k = C0.
Proof.
  induction n as [|n' IH]; intros K vecs HK Hlen Hvlen HvK.
  - destruct vecs as [|v [|w vecs]]; cbn [length] in Hlen; try lia.
    inversion Hvlen; subst.
    apply length_zero_iff_nil in H1. subst v.
    exists (C1 :: nil).
    split; [reflexivity | split].
    { constructor; [apply (Csubfield_1 K HK) | constructor]. }
    split.
    { intro Hz. inversion Hz; subst. exact (C1_neq_C0 H1). }
    intro k. unfold vcoord. cbn [map cdot].
    destruct k; cbn [nth]; ring.
  - destruct (classic (Forall (fun v => nth 0 v C0 = C0) vecs)) as [Hall0 | Hpiv].
    + set (front := firstn (Datatypes.S n') vecs).
      set (back := skipn (Datatypes.S n') vecs).
      set (front' := map (@tl C) front).
      assert (Hlf : length front = Datatypes.S n')
        by (unfold front; rewrite firstn_length; lia).
      assert (Hlf' : length front' = Datatypes.S n')
        by (unfold front'; rewrite length_map; exact Hlf).
      assert (Hvlf : Forall (fun v => length v = n') front').
      { unfold front'. apply Forall_map_intro. intros v Hv.
        assert (Hlv : length v = Datatypes.S n').
        { apply (proj1 (Forall_forall _ vecs) Hvlen).
          apply (In_firstn_incl _ _ _ _ Hv). }
        destruct v; [cbn [length] in Hlv; lia | cbn [tl length] in *; lia]. }
      assert (HvKf : Forall (Forall K) front').
      { unfold front'. apply Forall_map_intro. intros v Hv.
        apply Forall_tl.
        apply (proj1 (Forall_forall _ vecs) HvK).
        apply (In_firstn_incl _ _ _ _ Hv). }
      destruct (IH K front' HK Hlf' Hvlf HvKf) as [cs' [Hlcs' [HKcs' [Hnz' Hzero']]]].
      exists (cs' ++ C0 :: nil).
      split; [rewrite length_app, Hlcs'; cbn [length]; lia | split].
      { apply Forall_app_intro_c; [exact HKcs' |].
        constructor; [apply (Csubfield_0 K HK) | constructor]. }
      split.
      { intro Hz. apply Forall_app in Hz. exact (Hnz' (proj1 Hz)). }
      intro k.
      assert (Hsplit : vecs = front ++ back) by (symmetry; apply firstn_skipn).
      unfold vcoord. rewrite Hsplit, map_app.
      rewrite cdot_app by (rewrite length_map; lia).
      rewrite cdot_C0_head.
      assert (Hfrontk : cdot cs' (map (fun v => nth k v C0) front) = C0).
      { destruct k as [|k'].
        - apply cdot_zero_r.
          apply Forall_map_intro. intros v Hv.
          apply (proj1 (Forall_forall _ vecs) Hall0).
          apply (In_firstn_incl _ _ _ _ Hv).
        - assert (Hmm : map (fun v => nth (Datatypes.S k') v C0) front
                        = map (fun v => nth k' v C0) front').
          { unfold front'. rewrite map_map.
            apply map_ext. intro v. rewrite nth_tl_shift. reflexivity. }
          rewrite Hmm. apply (Hzero' k'). }
      rewrite Hfrontk. ring.
    + assert (Hex : Exists (fun v => nth 0 v C0 <> C0) vecs).
      { apply neg_Forall_Exists_neg; [| exact Hpiv].
        intro v. destruct (Ceq_dec (nth 0 v C0) C0); [left; assumption | right; assumption]. }
      apply Exists_exists in Hex.
      destruct Hex as [vp [Hin Ha]].
      set (a := nth 0 vp C0) in *.
      destruct (in_split vp vecs Hin) as [A0 [B0 Hsplit]].
      set (others := A0 ++ B0).
      assert (Hlo : length others = Datatypes.S n').
      { unfold others. rewrite Hsplit in Hlen.
        rewrite length_app in Hlen |- *. cbn [length] in Hlen. lia. }
      assert (Hin_others : forall v, In v others -> In v vecs).
      { intros v Hv. rewrite Hsplit. unfold others in Hv.
        apply in_app_or in Hv.
        apply in_or_app.
        destruct Hv as [Hv | Hv]; [left; exact Hv | right; right; exact Hv]. }
      assert (Hvlp : length vp = Datatypes.S n')
        by (apply (proj1 (Forall_forall _ vecs) Hvlen); exact Hin).
      assert (HvKp : Forall K vp)
        by (apply (proj1 (Forall_forall _ vecs) HvK); exact Hin).
      assert (HKa : K a)
        by (unfold a; apply Forall_nth_C; [exact HvKp | lia]).
      assert (HKinva : K (Cinv a)) by (apply Csubfield_inv; assumption).
      set (lam := fun v : list C => Copp (Cmul (nth 0 v C0) (Cinv a))).
      assert (HKlam : forall v, In v others -> K (lam v)).
      { intros v Hv. unfold lam.
        apply Csubfield_opp; [exact HK |].
        apply Csubfield_mul; [exact HK | | exact HKinva].
        assert (Hlv : length v = Datatypes.S n')
          by (apply (proj1 (Forall_forall _ vecs) Hvlen); apply Hin_others; exact Hv).
        apply Forall_nth_C;
          [apply (proj1 (Forall_forall _ vecs) HvK); apply Hin_others; exact Hv | lia]. }
      set (elim := map (fun v => cpadd v (cpscale (lam v) vp)) others).
      set (tails := map (@tl C) elim).
      assert (Hlelim : forall v, In v others ->
                length (cpadd v (cpscale (lam v) vp)) = Datatypes.S n').
      { intros v Hv.
        rewrite cpadd_length, cpscale_length, Hvlp.
        assert (Hlv : length v = Datatypes.S n')
          by (apply (proj1 (Forall_forall _ vecs) Hvlen); apply Hin_others; exact Hv).
        lia. }
      assert (Hltails : length tails = Datatypes.S n')
        by (unfold tails, elim; rewrite !length_map; exact Hlo).
      assert (Hvltails : Forall (fun v => length v = n') tails).
      { unfold tails, elim. rewrite map_map. apply Forall_map_intro. intros v Hv.
        pose proof (Hlelim v Hv) as Hl.
        destruct (cpadd v (cpscale (lam v) vp));
          [cbn [length] in Hl; lia | cbn [tl length] in *; lia]. }
      assert (HvKtails : Forall (Forall K) tails).
      { unfold tails, elim. rewrite map_map. apply Forall_map_intro. intros v Hv.
        apply Forall_tl.
        apply Forall_cpadd;
          [intros u w Hu Hw; apply (Csubfield_add K u w HK Hu Hw)
          | apply (proj1 (Forall_forall _ vecs) HvK); apply Hin_others; exact Hv |].
        apply Forall_cpscale;
          [intros u w Hu Hw; apply (Csubfield_mul K u w HK Hu Hw)
          | apply HKlam; exact Hv | exact HvKp]. }
      destruct (IH K tails HK Hltails Hvltails HvKtails)
        as [cs' [Hlcs' [HKcs' [Hnz' Hzero']]]].
      assert (Hheads : forall v, In v others ->
                nth 0 (cpadd v (cpscale (lam v) vp)) C0 = C0).
      { intros v Hv. rewrite nth_cpadd, nth_cpscale. unfold lam. fold a.
        field. exact Ha. }
      assert (Helim0 : forall k, cdot cs' (map (fun v => nth k v C0) elim) = C0).
      { intro k. destruct k as [|k'].
        - apply cdot_zero_r.
          unfold elim. rewrite map_map.
          apply Forall_map_intro. intros v Hv.
          apply Hheads. exact Hv.
        - assert (Hmm : map (fun v => nth (Datatypes.S k') v C0) elim
                        = map (fun v => nth k' v C0) tails).
          { unfold tails. rewrite map_map.
            apply map_ext. intro v. rewrite nth_tl_shift. reflexivity. }
          rewrite Hmm. apply (Hzero' k'). }
      assert (Hexpand : forall k,
        cdot cs' (map (fun v => nth k v C0) elim)
        = (cdot cs' (map (fun v => nth k v C0) others)
           + cdot cs' (map lam others) * nth k vp C0)%C).
      { intro k. unfold elim. rewrite map_map.
        rewrite (cdot_map_ext cs' _ others
                  (fun v => nth k (cpadd v (cpscale (lam v) vp)) C0)
                  (fun v => (nth k v C0 + lam v * nth k vp C0)%C))
          by (intros v _; rewrite nth_cpadd, nth_cpscale; reflexivity).
        apply (cdot_map_affine cs' _ others (fun v => nth k v C0) lam (nth k vp C0)). }
      set (Lam := cdot cs' (map lam others)).
      assert (HKLam : K Lam).
      { unfold Lam. apply cdot_K; [exact HK | exact HKcs' |].
        apply Forall_map_intro. intros v Hv. apply HKlam. exact Hv. }
      assert (Hothers : forall k,
        cdot cs' (map (fun v => nth k v C0) others) = (Copp (Lam * nth k vp C0))%C).
      { intro k.
        pose proof (Helim0 k) as H0. rewrite (Hexpand k) in H0.
        fold Lam in H0.
        transitivity ((cdot cs' (map (fun v => nth k v C0) others)
                       + Lam * nth k vp C0) - Lam * nth k vp C0)%C; [ring |].
        rewrite H0. ring. }
      set (csA := firstn (length A0) cs').
      set (csB := skipn (length A0) cs').
      assert (HlA : (length A0 <= Datatypes.S n')%nat).
      { unfold others in Hlo. rewrite length_app in Hlo. lia. }
      assert (HlcsA : length csA = length A0)
        by (unfold csA; rewrite firstn_length; lia).
      assert (Hreassemble : csA ++ csB = cs')
        by (unfold csA, csB; apply firstn_skipn).
      exists (csA ++ Lam :: csB).
      split.
      { rewrite length_app. cbn [length].
        unfold csB. rewrite skipn_length.
        rewrite HlcsA, Hlcs'. lia. }
      split.
      { apply Forall_app_intro_c;
          [unfold csA; apply Forall_firstn; exact HKcs' |].
        constructor; [exact HKLam |].
        unfold csB. apply Forall_skipn. exact HKcs'. }
      split.
      { intro Hz. apply Forall_app in Hz.
        destruct Hz as [HzA HzLB].
        apply Hnz'. rewrite <- Hreassemble.
        apply Forall_app_intro_c; [exact HzA | exact (Forall_inv_tail HzLB)]. }
      intro k.
      unfold vcoord.
      rewrite Hsplit, map_app. cbn [map].
      rewrite cdot_app by (rewrite length_map; exact HlcsA).
      cbn [cdot].
      assert (Hoth : cdot cs' (map (fun v => nth k v C0) others)
                     = (cdot csA (map (fun v => nth k v C0) A0)
                        + cdot csB (map (fun v => nth k v C0) B0))%C).
      { rewrite <- Hreassemble.
        unfold others. rewrite map_app.
        apply cdot_app. rewrite length_map. exact HlcsA. }
      pose proof (Hothers k) as Hok. rewrite Hoth in Hok.
      transitivity ((cdot csA (map (fun v => nth k v C0) A0)
                     + cdot csB (map (fun v => nth k v C0) B0))
                    + Lam * nth k vp C0)%C; [ring |].
      rewrite Hok. ring.
Qed.

Lemma list_eta_nth_c : forall (cs : list C),
  cs = map (fun i => nth i cs C0) (seq 0 (length cs)).
Proof.
  induction cs as [|c cs' IH].
  - reflexivity.
  - cbn [length seq map nth].
    f_equal. rewrite <- seq_shift, map_map. cbn [nth].
    exact IH.
Qed.

Lemma cpeval_map_plus : forall (A : Type) (l : list A) (f g : A -> C) z,
  cpeval (map (fun a => (f a + g a)%C) l) z
  = (cpeval (map f l) z + cpeval (map g l) z)%C.
Proof.
  intros A l f g z. induction l as [|a l IH]; cbn [map cpeval].
  - ring.
  - rewrite IH. ring.
Qed.

Lemma cpeval_map_scale : forall (A : Type) (l : list A) (c : C) (f : A -> C) z,
  cpeval (map (fun a => (c * f a)%C) l) z = (c * cpeval (map f l) z)%C.
Proof.
  intros A l c f z. induction l as [|a l IH]; cbn [map cpeval].
  - ring.
  - rewrite IH. ring.
Qed.

Lemma cpeval_map_zero : forall (A : Type) (l : list A) z,
  cpeval (map (fun _ => C0) l) z = C0.
Proof.
  intros A l z. induction l as [|a l IH]; cbn [map cpeval]; [ring | rewrite IH; ring].
Qed.

(** The evaluation of a coordinate-wise combination is the combination of the evaluations. *)
Lemma cdot_cpeval_bridge : forall (cs : list C) (vecs : list (list C)) (n : nat) (r : C),
  Forall (fun v => length v = n) vecs ->
  cdot cs (map (fun v => cpeval v r) vecs)
  = cpeval (map (fun k => vcoord cs vecs k) (seq 0 n)) r.
Proof.
  induction cs as [|c cs IH]; intros vecs n r Hvl.
  - cbn [cdot].
    assert (Hz : map (fun k => vcoord nil vecs k) (seq 0 n)
                 = map (fun _ => C0) (seq 0 n)).
    { apply map_ext. intro k. unfold vcoord.
      destruct vecs; reflexivity. }
    rewrite Hz, cpeval_map_zero. reflexivity.
  - destruct vecs as [|v vecs'].
    + cbn [map cdot].
      assert (Hz : map (fun k => vcoord (c :: cs) nil k) (seq 0 n)
                   = map (fun _ => C0) (seq 0 n))
        by (apply map_ext; intro k; reflexivity).
      rewrite Hz, cpeval_map_zero. reflexivity.
    + cbn [map cdot].
      inversion Hvl; subst.
      assert (Hexp : map (fun k => vcoord (c :: cs) (v :: vecs') k) (seq 0 (length v))
                     = map (fun k => (c * nth k v C0 + vcoord cs vecs' k)%C)
                         (seq 0 (length v)))
        by (apply map_ext; intro k; reflexivity).
      rewrite Hexp.
      rewrite cpeval_map_plus, cpeval_map_scale.
      rewrite (IH vecs' (length v) r H2).
      f_equal. f_equal.
      rewrite <- (list_eta_nth_c v) at 1. reflexivity.
Qed.

(** Powers of a CPolyF element stay in the span. *)
Lemma CPolyF_pow : forall (K : C -> Prop) (r : C) (j : nat) (dtcf : list C),
  is_Csubfield K -> (1 <= j)%nat ->
  length dtcf = j -> Forall K dtcf ->
  (cpeval dtcf r + Cpow r j)%C = C0 ->
  forall u, CPolyF K j r u -> forall i, CPolyF K j r (Cpow u i).
Proof.
  intros K r j dtcf HK Hj Hlen HKdt Hrel u Hu i.
  induction i as [|i IH].
  - cbn [Cpow]. apply (CPolyF_contains K r j dtcf HK Hj Hlen HKdt Hrel).
    apply (Csubfield_1 K HK).
  - cbn [Cpow]. apply (CPolyF_mul K r j dtcf HK Hj Hlen HKdt Hrel); assumption.
Qed.

(** The representation list of the powers of u, materialized. *)
Lemma pow_reps_exist : forall (K : C -> Prop) (r : C) (j : nat) (dtcf : list C),
  is_Csubfield K -> (1 <= j)%nat ->
  length dtcf = j -> Forall K dtcf ->
  (cpeval dtcf r + Cpow r j)%C = C0 ->
  forall u, CPolyF K j r u ->
  forall n, exists vecs : list (list C),
    length vecs = n /\
    Forall (fun v => length v = j) vecs /\
    Forall (Forall K) vecs /\
    (forall i, (i < n)%nat -> cpeval (nth i vecs nil) r = Cpow u i).
Proof.
  intros K r j dtcf HK Hj Hlen HKdt Hrel u Hu n.
  induction n as [|n IH].
  - exists nil. repeat split; try constructor. intros i Hi. lia.
  - destruct IH as [vecs [Hlv [Hvl [HvK Hnth]]]].
    destruct (CPolyF_pow K r j dtcf HK Hj Hlen HKdt Hrel u Hu n)
      as [rep [Hlr [HKr Hrep]]].
    exists (vecs ++ rep :: nil).
    split; [rewrite length_app, Hlv; cbn [length]; lia |].
    split.
    { apply Forall_app. split; [exact Hvl |].
      constructor; [exact Hlr | constructor]. }
    split.
    { apply Forall_app. split; [exact HvK |].
      constructor; [exact HKr | constructor]. }
    intros i Hi.
    destruct (Nat.eq_dec i n) as [-> | Hne].
    + rewrite app_nth2 by lia.
      rewrite Hlv, Nat.sub_diag. cbn [nth].
      symmetry. exact Hrep.
    + rewrite app_nth1 by lia.
      apply Hnth. lia.
Qed.

(** The first nonzero position of a complex list. *)
Fixpoint first_nz (cs : list C) : nat :=
  match cs with
  | nil => O
  | c :: cs' => if Ceq_dec c C0 then Datatypes.S (first_nz cs') else O
  end.

Lemma first_nz_spec : forall cs, ~ Forall (fun c => c = C0) cs ->
  (first_nz cs < length cs)%nat /\
  hd C0 (skipn (first_nz cs) cs) <> C0 /\
  (forall i, (i < first_nz cs)%nat -> nth i cs C0 = C0).
Proof.
  induction cs as [|c cs IH]; intro Hnz.
  - exfalso. apply Hnz. constructor.
  - cbn [first_nz].
    destruct (Ceq_dec c C0) as [-> | Hne].
    + assert (Hnz' : ~ Forall (fun x => x = C0) cs)
        by (intro Hall; apply Hnz; constructor; [reflexivity | exact Hall]).
      destruct (IH Hnz') as [Hlt [Hhd Hlow]].
      split; [cbn [length]; lia |].
      split; [cbn [skipn]; exact Hhd |].
      intros i Hi. destruct i as [|i']; [reflexivity | cbn [nth]; apply Hlow; lia].
    + split; [cbn [length]; lia |].
      split; [cbn [skipn hd]; exact Hne |].
      intros i Hi. lia.
Qed.

Lemma cpeval_skipn_split : forall (t : nat) (cs : list C) (u : C),
  (forall i, (i < t)%nat -> nth i cs C0 = C0) ->
  (t <= length cs)%nat ->
  cpeval cs u = (Cpow u t * cpeval (skipn t cs) u)%C.
Proof.
  induction t as [|t IH]; intros cs u Hlow Hle.
  - cbn [skipn Cpow]. ring.
  - destruct cs as [|c cs']; [cbn [length] in Hle; lia |].
    cbn [skipn cpeval Cpow].
    pose proof (Hlow 0%nat ltac:(lia)) as H0. cbn [nth] in H0. subst c.
    rewrite (IH cs' u) by (try (intros i Hi; exact (Hlow (Datatypes.S i) ltac:(lia)));
                           cbn [length] in Hle; lia).
    ring.
Qed.

Lemma Cpow_nonzero : forall (u : C) (t : nat), u <> C0 -> Cpow u t <> C0.
Proof.
  intros u t Hu. induction t as [|t IH]; cbn [Cpow].
  - exact C1_neq_C0.
  - intro H. destruct (Cmul_integral _ _ H) as [E | E]; [exact (Hu E) | exact (IH E)].
Qed.

Lemma Cinv_unique : forall (u x : C), u <> C0 -> (u * x)%C = C1 -> Cinv u = x.
Proof.
  intros u x Hu Hx.
  transitivity ((Cinv u * (u * x))%C).
  - rewrite Hx. ring.
  - transitivity ((Cmul (Cinv u) u * x)%C); [ring |].
    rewrite (Cinv_l u Hu). ring.
Qed.

(** Evaluation of a K-coefficient list at a CPolyF element stays in the span. *)
Lemma CPolyF_cpeval_at : forall (K : C -> Prop) (r : C) (j : nat) (dtcf : list C),
  is_Csubfield K -> (1 <= j)%nat ->
  length dtcf = j -> Forall K dtcf ->
  (cpeval dtcf r + Cpow r j)%C = C0 ->
  forall (cs : list C) (u : C), Forall K cs -> CPolyF K j r u ->
  CPolyF K j r (cpeval cs u).
Proof.
  intros K r j dtcf HK Hj Hlen HKdt Hrel cs u HKcs Hu.
  induction HKcs as [|c cs' Hc HKcs' IH]; cbn [cpeval].
  - apply (CPolyF_contains K r j dtcf HK Hj Hlen HKdt Hrel).
    apply (Csubfield_0 K HK).
  - apply (CPolyF_add K r j HK).
    + apply (CPolyF_contains K r j dtcf HK Hj Hlen HKdt Hrel). exact Hc.
    + apply (CPolyF_mul K r j dtcf HK Hj Hlen HKdt Hrel); [exact Hu | exact IH].
Qed.

Lemma cdot_map_scale : forall (cs : list C) (A : Type) (l : list A)
    (t : C) (f : A -> C),
  cdot cs (map (fun a => (t * f a)%C) l) = (t * cdot cs (map f l))%C.
Proof.
  induction cs as [|c cs IH]; intros A l t f.
  - cbn [cdot]. ring.
  - destruct l as [|a l]; cbn [map cdot]; [ring | rewrite IH; ring].
Qed.

(** cdot against the power list is evaluation. *)
Lemma cdot_powlist : forall (cs : list C) (u : C) (n : nat),
  length cs = n ->
  cdot cs (map (Cpow u) (seq 0 n)) = cpeval cs u.
Proof.
  induction cs as [|c cs IH]; intros u n Hlen.
  - cbn [cdot cpeval]. destruct n; reflexivity.
  - destruct n as [|n']; [cbn [length] in Hlen; lia |].
    cbn [length] in Hlen.
    assert (HL : map (Cpow u) (seq 0 (Datatypes.S n'))
                 = C1 :: map (fun i => (u * Cpow u i)%C) (seq 0 n')).
    { cbn [seq map Cpow].
      f_equal.
      rewrite <- seq_shift, map_map.
      apply map_ext. intro i. reflexivity. }
    rewrite HL.
    cbn [cdot cpeval].
    rewrite cdot_map_scale.
    rewrite (IH u n') by lia.
    ring.
Qed.

(** THE INVERSE IN THE ADJUNCTION: from the dependence of the powers. *)
Lemma CPolyF_inv : forall (K : C -> Prop) (r : C) (j : nat) (dtcf : list C),
  is_Csubfield K -> (1 <= j)%nat ->
  length dtcf = j -> Forall K dtcf ->
  (cpeval dtcf r + Cpow r j)%C = C0 ->
  forall u, CPolyF K j r u -> u <> C0 -> CPolyF K j r (Cinv u).
Proof.
  intros K r j dtcf HK Hj Hlen HKdt Hrel u Hu Hune.
  destruct (pow_reps_exist K r j dtcf HK Hj Hlen HKdt Hrel u Hu (Datatypes.S j))
    as [vecs [Hlv [Hvl [HvK Hnth]]]].
  destruct (vectors_dependent j K vecs HK Hlv Hvl HvK)
    as [cs [Hlcs [HKcs [Hnz Hzero]]]].
  assert (Hmapev : map (fun v => cpeval v r) vecs
                   = map (Cpow u) (seq 0 (Datatypes.S j))).
  { apply (nth_ext _ _ C0 C0).
    - rewrite !length_map, length_seq, Hlv. reflexivity.
    - intros i Hi.
      rewrite length_map, Hlv in Hi.
      rewrite (nth_indep _ C0 (cpeval nil r))
        by (rewrite length_map, Hlv; exact Hi).
      rewrite (map_nth (fun v => cpeval v r) vecs nil i).
      rewrite (nth_indep _ C0 (Cpow u 0%nat))
        by (rewrite length_map, length_seq; exact Hi).
      rewrite (map_nth (Cpow u) (seq 0 (Datatypes.S j)) 0%nat i).
      rewrite seq_nth by exact Hi.
      cbn [Nat.add]. apply Hnth. exact Hi. }
  assert (Hucomb : cpeval cs u = C0).
  { rewrite <- (cdot_powlist cs u (Datatypes.S j) Hlcs).
    rewrite <- Hmapev.
    rewrite (cdot_cpeval_bridge cs vecs j r Hvl).
    assert (Hzl : map (fun k => vcoord cs vecs k) (seq 0 j)
                  = map (fun _ => C0) (seq 0 j))
      by (apply map_ext; intro k; apply Hzero).
    rewrite Hzl, cpeval_map_zero. reflexivity. }
  set (t := first_nz cs).
  destruct (first_nz_spec cs Hnz) as [Htlt [Hthd Htlow]].
  fold t in Htlt, Hthd, Htlow.
  pose proof (cpeval_skipn_split t cs u Htlow ltac:(lia)) as Hsplit.
  rewrite Hucomb in Hsplit.
  assert (Hskip0 : cpeval (skipn t cs) u = C0).
  { destruct (Ceq_dec (cpeval (skipn t cs) u) C0) as [E | NE]; [exact E | exfalso].
    apply (Cpow_nonzero u t Hune).
    destruct (Cmul_integral _ _ (eq_sym Hsplit)) as [E | E];
      [exact E | contradiction]. }
  assert (HKsk : Forall K (skipn t cs)) by (apply Forall_skipn; exact HKcs).
  destruct (skipn t cs) as [|ct tail] eqn:Esk; [cbn [hd] in Hthd; congruence |].
  cbn [hd] in Hthd.
  cbn [cpeval] in Hskip0.
  assert (HKct : K ct) by (exact (Forall_inv HKsk)).
  assert (HKtail : Forall K tail) by (exact (Forall_inv_tail HKsk)).
  assert (Hprod : (u * (Copp (Cinv ct) * cpeval tail u))%C = C1).
  { transitivity ((Copp (Cinv ct)) * (u * cpeval tail u))%C; [ring |].
    assert (Hut : (u * cpeval tail u)%C = Copp ct).
    { transitivity (((ct + u * cpeval tail u) - ct)%C); [ring |].
      rewrite Hskip0. ring. }
    rewrite Hut.
    transitivity ((Cinv ct * ct)%C); [ring |].
    apply Cinv_l. exact Hthd. }
  rewrite (Cinv_unique u _ Hune Hprod).
  apply (CPolyF_mul K r j dtcf HK Hj Hlen HKdt Hrel).
  - apply (CPolyF_contains K r j dtcf HK Hj Hlen HKdt Hrel).
    apply Csubfield_opp; [exact HK |].
    apply Csubfield_inv; assumption.
  - apply (CPolyF_cpeval_at K r j dtcf HK Hj Hlen HKdt Hrel); [exact HKtail | exact Hu].
Qed.

(** THE ADJUNCTION IS A SUBFIELD. *)
Theorem CPolyF_Csubfield : forall (K : C -> Prop) (r : C) (j : nat) (dtcf : list C),
  is_Csubfield K -> (1 <= j)%nat ->
  length dtcf = j -> Forall K dtcf ->
  (cpeval dtcf r + Cpow r j)%C = C0 ->
  is_Csubfield (CPolyF K j r).
Proof.
  intros K r j dtcf HK Hj Hlen HKdt Hrel.
  repeat split.
  - apply (CPolyF_contains K r j dtcf HK Hj Hlen HKdt Hrel).
    apply (Csubfield_0 K HK).
  - apply (CPolyF_contains K r j dtcf HK Hj Hlen HKdt Hrel).
    apply (Csubfield_1 K HK).
  - intros x y Hx Hy. apply (CPolyF_add K r j HK); assumption.
  - intros x y Hx Hy. apply (CPolyF_sub K r j HK); assumption.
  - intros x y Hx Hy. apply (CPolyF_mul K r j dtcf HK Hj Hlen HKdt Hrel); assumption.
  - intros x Hx Hne. apply (CPolyF_inv K r j dtcf HK Hj Hlen HKdt Hrel); assumption.
Qed.

(* the maximal independent prefix over a complex subfield -- any K-relation of degree at most d refines to a monic minimal relation with independent lower powers. *)

Lemma not_Cindep_witness : forall (K : C -> Prop) (z : C) (n : nat),
  ~ Cindep_pows K z n ->
  exists cs, length cs = n /\ Forall K cs /\ cpeval cs z = C0 /\
             ~ Forall (fun c => c = C0) cs.
Proof.
  intros K z n Hnot.
  destruct (not_all_ex_not _ _ Hnot) as [cs Hcs].
  destruct (imply_to_and _ _ Hcs) as [Hlen Hcs2].
  destruct (imply_to_and _ _ Hcs2) as [HKcs Hcs3].
  destruct (imply_to_and _ _ Hcs3) as [Hev Hnz].
  exists cs. repeat split; assumption.
Qed.

Lemma Cindep_pows_1 : forall (K : C -> Prop) (z : C), Cindep_pows K z 1.
Proof.
  intros K z cs Hlen HKcs Hev.
  destruct cs as [|c [|? ?]]; [discriminate | | discriminate].
  cbn [cpeval] in Hev.
  constructor; [| constructor].
  transitivity ((c + z * C0)%C); [ring | exact Hev].
Qed.

Lemma cpowers_max_prefix : forall (K : C -> Prop) (z : C) (d : nat),
  is_Csubfield K -> (1 <= d)%nat ->
  exists j, (1 <= j <= d)%nat /\ Cindep_pows K z j /\
    (j = d \/ exists dt : list C, length dt = j /\ Forall K dt /\
       (cpeval dt z + Cpow z j)%C = C0).
Proof.
  intros K z d HK Hd. induction d as [|d' IHd]; [lia |].
  destruct (Nat.eq_dec d' 0) as [-> | Hd'].
  - exists 1%nat. split; [lia | split; [apply Cindep_pows_1 | left; reflexivity]].
  - assert (Hd'1 : (1 <= d')%nat) by lia.
    destruct (IHd Hd'1) as [j [Hjle [Hjind Hjcase]]].
    destruct Hjcase as [-> | Hrel].
    + destruct (classic (Cindep_pows K z (Datatypes.S d'))) as [Hind | Hdep].
      * exists (Datatypes.S d').
        split; [lia | split; [exact Hind | left; reflexivity]].
      * destruct (not_Cindep_witness K z (Datatypes.S d') Hdep)
          as [ks [Hklen [HKks [Hkev Hknz]]]].
        destruct (exists_last (l := ks)
                    ltac:(intro E; rewrite E in Hklen; cbn in Hklen; lia))
          as [ks' [kj Hks]].
        subst ks.
        rewrite length_app in Hklen. cbn [length] in Hklen.
        assert (Hks'len : length ks' = d') by lia.
        rewrite cpeval_app, Hks'len in Hkev.
        cbn [cpeval] in Hkev.
        apply Forall_app in HKks. destruct HKks as [HKks' HKkj].
        pose proof (Forall_inv HKkj) as Kkj.
        destruct (Ceq_dec kj C0) as [-> | Hkjne].
        { exfalso.
          assert (Hz' : cpeval ks' z = C0).
          { transitivity ((cpeval ks' z + Cpow z d' * (C0 + z * C0))
                          - Cpow z d' * (C0 + z * C0))%C; [ring |].
            rewrite Hkev. ring. }
          assert (Hzz : Forall (fun c => c = C0) ks')
            by (apply Hjind; [exact Hks'len | exact HKks' | exact Hz']).
          apply Hknz. apply Forall_app.
          split; [exact Hzz | constructor; [reflexivity | constructor]]. }
        exists d'. split; [lia | split; [exact Hjind | right]].
        exists (cpscale (Cinv kj) ks').
        split; [rewrite cpscale_length; exact Hks'len | split].
        { apply Forall_cpscale;
            [intros u v Hu Hv; apply (Csubfield_mul K u v HK Hu Hv)
            | apply (Csubfield_inv K kj HK Kkj Hkjne) | exact HKks']. }
        { rewrite cpeval_cpscale.
          apply (Cmul_eq_reg_l kj); [exact Hkjne |].
          transitivity ((cpeval ks' z + Cpow z d' * (kj + z * C0))%C).
          - transitivity ((kj * Cinv kj) * cpeval ks' z + kj * Cpow z d')%C; [ring |].
            assert (Hii : (kj * Cinv kj)%C = C1).
            { transitivity ((Cinv kj * kj)%C); [ring |]. apply Cinv_l. exact Hkjne. }
            rewrite Hii. ring.
          - rewrite Hkev. ring. }
    + exists j. split; [lia | split; [exact Hjind | right; exact Hrel]].
Qed.

(* root bookkeeping -- the minimal relation divides vanishing K-polynomials, and its sigma-image has exactly degree-many roots among the split base roots. *)

(** CCevalMap through a map is plain evaluation of the image list. *)
Lemma CCevalMap_cpeval_map : forall (sigma : C -> C) (p : list C) (z : C),
  CCevalMap sigma p z = cpeval (map sigma p) z.
Proof.
  intros sigma p z. induction p as [|c p IH]; cbn [CCevalMap map cpeval].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** THE MINIMAL RELATION DIVIDES, over C: any K-list vanishing at the root is the product of the monic minimal relation and a K-quotient. *)
Lemma cminpoly_divides : forall (K : C -> Prop) (r : C) (j : nat) (dtcf : list C),
  is_Csubfield K -> (1 <= j)%nat ->
  length dtcf = j -> Forall K dtcf ->
  (cpeval dtcf r + Cpow r j)%C = C0 ->
  Cindep_pows K r j ->
  forall g : list C, Forall K g -> cpeval g r = C0 ->
  Forall K (fst (cpdiv_lf (length (rev g)) (rev g) (rev dtcf))) /\
  (forall z, cpeval g z
     = (cpeval_lf (fst (cpdiv_lf (length (rev g)) (rev g) (rev dtcf))) z
        * (Cpow z j + cpeval dtcf z))%C).
Proof.
  intros K r j dtcf HK Hj Hlen HKdt Hrel Hindep g HKg Hgr.
  rewrite (cpeval_k dtcf r), Cpow_k in Hrel.
  rewrite cpeval_k in Hgr.
  assert (Hindep' : kindep_pows C C0 Cadd Cmul K r j).
  { intros cs Hl HF Hev.
    apply (Hindep cs Hl HF).
    rewrite cpeval_k. exact Hev. }
  destruct (kminpoly_divides _ _ _ _ _ _ _ _ _ C_field K r j dtcf
              HK Hj Hlen HKdt Hrel Hindep' g HKg Hgr) as [H1 H2].
  rewrite <- cpdiv_lf_k in H1.
  split; [exact H1 |].
  intro z.
  rewrite (cpeval_k g z), cpeval_lf_k, cpdiv_lf_k, Cpow_k, (cpeval_k dtcf z).
  exact (H2 z).
Qed.

(** AT MOST DEGREE-MANY DISTINCT ROOTS: a nonzero leading-first polynomial vanishes on at most length - 1 distinct points. *)
Lemma cp_max_roots : forall (p : list C) (zs : list C),
  NoDup zs ->
  (forall z, In z zs -> cpeval_lf p z = C0) ->
  ~ (forall w, cpeval_lf p w = C0) ->
  (length zs <= length p - 1)%nat.
Proof.
  intros p zs. revert p. induction zs as [|z zs IH]; intros p Hnd Hroots Hnz.
  - cbn [length]. lia.
  - inversion Hnd; subst.
    assert (Hz : cpeval_lf p z = C0) by (apply Hroots; left; reflexivity).
    pose proof (cp_root_factor p z Hz) as Hfac.
    set (q := fst (cpdiv_lf (length p) p (Copp z :: nil))) in *.
    assert (Hqroots : forall z', In z' zs -> cpeval_lf q z' = C0).
    { intros z' Hz'.
      pose proof (Hfac z') as Hf.
      pose proof (Hroots z' (or_intror Hz')) as Hz'0.
      rewrite Hz'0 in Hf.
      assert (Hne : (z' - z)%C <> C0).
      { intro He.
        assert (Heq : z' = z).
        { transitivity ((z' - z) + z)%C; [ring |]. rewrite He. ring. }
        subst z'. contradiction. }
      destruct (Ceq_dec (cpeval_lf q z') C0) as [E | NE]; [exact E | exfalso].
      destruct (Cmul_integral _ _ (eq_sym Hf)) as [E | E]; [exact (NE E) | exact (Hne E)]. }
    assert (Hqnz : ~ (forall w, cpeval_lf q w = C0)).
    { intro Hall. apply Hnz. intro w.
      rewrite (Hfac w), (Hall w). ring. }
    assert (Hqlen : length q = (length p - 1)%nat).
    { unfold q. rewrite (cpdiv_lf_qlen _ _ _ (Nat.le_refl _)).
      cbn [length]. lia. }
    pose proof (IH q H2 Hqroots Hqnz) as Hle.
    rewrite Hqlen in Hle.
    assert (Hp2 : (2 <= length p)%nat).
    { destruct p as [|a p']; [exfalso; apply Hnz; intro w; reflexivity |].
      destruct p' as [|b p'']; [| cbn [length]; lia].
      exfalso. apply Hnz. intro w.
      cbn [cpeval_lf length Cpow] in Hz |- *.
      exact Hz. }
    cbn [length]. lia.
Qed.

(** The split product of monic linear factors over a root list. *)
Fixpoint prod_linear (rho : list C) (z : C) : C :=
  match rho with
  | nil => C1
  | r :: rho' => ((z - r) * prod_linear rho' z)%C
  end.

Lemma prod_linear_root : forall rho r, In r rho -> forall z, z = r ->
  prod_linear rho z = C0.
Proof.
  induction rho as [|a rho IH]; intros r Hin z Hz.
  - contradiction.
  - cbn [prod_linear].
    destruct Hin as [-> | Hin].
    + subst z. replace ((r - r)%C) with C0 by ring. ring.
    + rewrite (IH r Hin z Hz). ring.
Qed.

Lemma prod_linear_zero_in : forall rho z, prod_linear rho z = C0 -> In z rho.
Proof.
  induction rho as [|a rho IH]; intros z Hz.
  - cbn [prod_linear] in Hz. exact (False_ind _ (C1_neq_C0 Hz)).
  - cbn [prod_linear] in Hz.
    destruct (Cmul_integral _ _ Hz) as [E | E].
    + left. symmetry.
      transitivity (((z - a) + a)%C); [ring |].
      rewrite E. ring.
    + right. apply IH. exact E.
Qed.

(** Some evaluation point avoids any list shorter than the point pool. *)
Lemma exists_point_outside : forall (rho : list C),
  exists z : C, ~ In z rho.
Proof.
  intro rho.
  set (pts := map (fun k => RtoC (INR k)) (seq 0 (Datatypes.S (length rho)))).
  assert (Hndpts : NoDup pts).
  { unfold pts. apply FinFun.Injective_map_NoDup.
    - intros a b Hab. apply RtoC_INR_inj in Hab. exact Hab.
    - apply seq_NoDup. }
  assert (Hlpts : length pts = Datatypes.S (length rho))
    by (unfold pts; rewrite length_map, length_seq; reflexivity).
  destruct (classic (exists z, In z pts /\ ~ In z rho)) as [[z [_ Hz]] | Hall].
  - exists z. exact Hz.
  - exfalso.
    assert (Hincl : incl pts rho).
    { intros z Hz.
      destruct (classic (In z rho)) as [H | H]; [exact H |].
      exfalso. apply Hall. exists z. split; assumption. }
    pose proof (NoDup_incl_length Hndpts Hincl) as Hle.
    rewrite Hlpts in Hle. lia.
Qed.

(** THE STEP ROOT COUNT: the sigma-image of the minimal relation has exactly its degree many roots among the split base roots. *)
Lemma image_relation_root_count :
  forall (K : C -> Prop) (sigma : C -> C) (rho : list C) (Fcf : list C)
         (lead r : C) (j : nat) (dt : list C),
  is_Csubfield K -> CCembeds K sigma ->
  NoDup rho -> lead <> C0 ->
  (forall z, cpeval Fcf z = (lead * prod_linear rho z)%C) ->
  Forall K Fcf -> length Fcf = Datatypes.S (length rho) ->
  Forall (fun c => sigma c = c) Fcf ->
  In r rho ->
  (1 <= j)%nat -> (j <= length rho)%nat ->
  length dt = j -> Forall K dt ->
  (cpeval dt r + Cpow r j)%C = C0 -> Cindep_pows K r j ->
  length (filter (fun w => if Ceq_dec ((CCevalMap sigma dt w + Cpow w j)%C) C0
                           then true else false) rho) = j.
Proof.
  intros K sigma rho Fcf lead r j dt HK Hemb Hnd Hlead Hsplit HKF HlF Hfix
         Hin Hj Hjn Hldt HKdt Hrel Hindep.
  pose proof Hemb as [Hs0 [Hs1 [Hsadd Hsmul]]].
  assert (HFr : cpeval Fcf r = C0).
  { rewrite Hsplit, (prod_linear_root rho r Hin r eq_refl). ring. }
  destruct (cminpoly_divides K r j dt HK Hj Hldt HKdt Hrel Hindep Fcf HKF HFr)
    as [HKQ Hdiv].
  set (Q := fst (cpdiv_lf (length (rev Fcf)) (rev Fcf) (rev dt))) in *.
  assert (HlQ : length Q = (length rho + 1 - j)%nat).
  { unfold Q. rewrite (cpdiv_lf_qlen _ _ _ (Nat.le_refl _)).
    rewrite !length_rev, HlF, Hldt. lia. }
  set (Msig := fun w => (CCevalMap sigma dt w + Cpow w j)%C).
  set (MsigL := C1 :: rev (map sigma dt)).
  assert (HMsigL_len : length MsigL = Datatypes.S j)
    by (unfold MsigL; cbn [length]; rewrite length_rev, length_map, Hldt; lia).
  assert (HMsigL_ev : forall w, cpeval_lf MsigL w = Msig w).
  { intro w. unfold MsigL, Msig. cbn [cpeval_lf].
    rewrite length_rev, length_map, Hldt.
    rewrite cpeval_lf_rev_c, rev_involutive.
    rewrite <- CCevalMap_cpeval_map. ring. }
  set (QsigL := map sigma Q).
  assert (HQsigL_len : length QsigL = (length rho + 1 - j)%nat)
    by (unfold QsigL; rewrite length_map; exact HlQ).
  assert (HQsigL_ev : forall w, cpeval_lf QsigL w = CCevalMap sigma (rev Q) w).
  { intro w. unfold QsigL.
    rewrite cpeval_lf_rev_c, <- map_rev, <- CCevalMap_cpeval_map.
    reflexivity. }
  assert (Hfactored : forall w, cpeval Fcf w = (cpeval_lf QsigL w * Msig w)%C).
  { intro w.
    assert (HFcoeff : Fcf = cpmul (rev Q) (dt ++ C1 :: nil)).
    { apply cpeval_ext_coeffs.
      - rewrite cpmul_length;
          [| rewrite length_rev, HlQ; lia
           | rewrite length_app, Hldt; cbn [length]; lia].
        rewrite length_rev, HlQ, length_app, Hldt. cbn [length]. lia.
      - intro z. rewrite cpeval_cpmul.
        rewrite (Hdiv z).
        assert (HQz : cpeval (rev Q) z = cpeval_lf Q z)
          by (rewrite cpeval_lf_rev_c; reflexivity).
        assert (HMz : cpeval (dt ++ C1 :: nil) z = (Cpow z j + cpeval dt z)%C).
        { rewrite cpeval_app, Hldt. cbn [cpeval]. ring. }
        rewrite HQz, HMz. ring. }
    assert (HFsig : CCevalMap sigma Fcf w = cpeval Fcf w).
    { rewrite (CCevalMap_ext_on sigma (fun c => c) Fcf w Hfix).
      apply CCevalMap_id. }
    rewrite <- HFsig.
    rewrite HFcoeff at 1.
    rewrite (CCevalMap_cpmul K sigma Hemb HK);
      [| apply Forall_rev; exact HKQ
       | apply Forall_app_intro_c;
           [exact HKdt | constructor; [apply (Csubfield_1 K HK) | constructor]]].
    rewrite HQsigL_ev.
    assert (HMw : CCevalMap sigma (dt ++ C1 :: nil) w = Msig w).
    { rewrite CCevalMap_app, Hldt. cbn [CCevalMap].
      rewrite Hs1. unfold Msig. ring. }
    rewrite HMw. reflexivity. }
  set (ftest := fun w => if Ceq_dec (Msig w) C0 then true else false).
  set (gtest := fun w => if Ceq_dec (cpeval_lf QsigL w) C0 then true else false).
  assert (HFnz : ~ (forall w, cpeval Fcf w = C0)).
  { intro Hall.
    destruct (exists_point_outside rho) as [z Hz].
    apply Hz. apply prod_linear_zero_in.
    pose proof (Hall z) as Hallz. rewrite Hsplit in Hallz.
    destruct (Cmul_integral _ _ Hallz) as [E | E]; [contradiction | exact E]. }
  assert (HMnz : ~ (forall w, cpeval_lf MsigL w = C0)).
  { apply cmonic_lf_nonzero; [reflexivity | rewrite HMsigL_len; lia]. }
  assert (HQnz : ~ (forall w, cpeval_lf QsigL w = C0)).
  { intro Hall. apply HFnz. intro w.
    rewrite (Hfactored w), (Hall w). ring. }
  assert (Hcover : forall w, In w rho -> ftest w = true \/ gtest w = true).
  { intros w Hw.
    assert (HFw : cpeval Fcf w = C0).
    { rewrite Hsplit, (prod_linear_root rho w Hw w eq_refl). ring. }
    rewrite (Hfactored w) in HFw.
    unfold ftest, gtest.
    destruct (Cmul_integral _ _ HFw) as [E | E].
    - right. destruct (Ceq_dec (cpeval_lf QsigL w) C0); [reflexivity | contradiction].
    - left. destruct (Ceq_dec (Msig w) C0); [reflexivity | contradiction]. }
  assert (Hfle : (length (filter ftest rho) <= j)%nat).
  { assert (Hroots : forall z, In z (filter ftest rho) -> cpeval_lf MsigL z = C0).
    { intros z Hz. apply filter_In in Hz. destruct Hz as [_ Hz].
      unfold ftest in Hz.
      destruct (Ceq_dec (Msig z) C0) as [E | E]; [| discriminate].
      rewrite HMsigL_ev. exact E. }
    pose proof (cp_max_roots MsigL (filter ftest rho)
                  (NoDup_filter ftest Hnd) Hroots HMnz) as Hb.
    rewrite HMsigL_len in Hb. lia. }
  assert (Hgle : (length (filter gtest rho) <= length rho - j)%nat).
  { assert (Hroots : forall z, In z (filter gtest rho) -> cpeval_lf QsigL z = C0).
    { intros z Hz. apply filter_In in Hz. destruct Hz as [_ Hz].
      unfold gtest in Hz.
      destruct (Ceq_dec (cpeval_lf QsigL z) C0) as [E | E]; [exact E | discriminate]. }
    pose proof (cp_max_roots QsigL (filter gtest rho)
                  (NoDup_filter gtest Hnd) Hroots HQnz) as Hb.
    rewrite HQsigL_len in Hb. lia. }
  pose proof (filter_cover_length C ftest gtest rho Hcover) as Hcov.
  unfold ftest, gtest, Msig in *. lia.
Qed.

(* the extension list at one adjunction step -- one embedding of K yields exactly degree-many embeddings of K(r), pairwise distinct at r. *)

Lemma CPolyF_1_iff : forall (K : C -> Prop) (r : C) (x : C),
  is_Csubfield K -> (CPolyF K 1 r x <-> K x).
Proof.
  intros K r x HK. split.
  - intros [cs [Hl [HKcs Hx]]].
    destruct cs as [|c [|? ?]]; [discriminate | | discriminate].
    inversion HKcs; subst.
    cbn [cpeval].
    replace ((c + r * C0)%C) with c by ring.
    assumption.
  - intro Hx. exists (x :: nil).
    split; [reflexivity | split].
    + constructor; [exact Hx | constructor].
    + cbn [cpeval]. ring.
Qed.

Lemma CCembeds_ext_pred : forall (K1 K2 : C -> Prop) (sigma : C -> C),
  (forall x, K1 x <-> K2 x) -> CCembeds K1 sigma -> CCembeds K2 sigma.
Proof.
  intros K1 K2 sigma Hiff [H0 [H1 [Hadd Hmul]]].
  split; [exact H0 | split; [exact H1 | split]].
  - intros x y Hx Hy. apply Hadd; apply Hiff; assumption.
  - intros x y Hx Hy. apply Hmul; apply Hiff; assumption.
Qed.

Lemma CCembeds_opp : forall (K : C -> Prop) (sigma : C -> C) (x : C),
  is_Csubfield K -> CCembeds K sigma -> K x -> sigma (Copp x) = Copp (sigma x).
Proof.
  intros K sigma x HK [H0 [H1 [Hadd Hmul]]] Hx.
  assert (Hox : K (Copp x)) by (apply Csubfield_opp; assumption).
  assert (Hsum : sigma (x + Copp x)%C = (sigma x + sigma (Copp x))%C)
    by (apply Hadd; assumption).
  replace ((x + Copp x)%C) with C0 in Hsum by ring.
  rewrite H0 in Hsum.
  transitivity ((sigma x + sigma (Copp x)) - sigma x)%C.
  - ring.
  - rewrite <- Hsum. ring.
Qed.

(** The degree-one extension: the root is already in the field and its image is forced. *)
Lemma CCembeds_extend_one :
  forall (K : C -> Prop) (r : C) (dt : list C) (sigma : C -> C) (w : C),
  is_Csubfield K ->
  length dt = 1%nat -> Forall K dt ->
  (cpeval dt r + Cpow r 1)%C = C0 ->
  CCembeds K sigma ->
  (CCevalMap sigma dt w + Cpow w 1)%C = C0 ->
  CCembeds (CPolyF K 1 r) sigma /\ sigma r = w.
Proof.
  intros K r dt sigma w HK Hlen HKdt Hrel Hemb Hw.
  destruct dt as [|c [|? ?]]; [discriminate | | discriminate].
  inversion HKdt; subst.
  cbn [cpeval Cpow] in Hrel.
  cbn [CCevalMap Cpow] in Hw.
  assert (Hr : r = Copp c).
  { transitivity (((c + r * C0) + r * C1) - c)%C; [ring |].
    rewrite Hrel. ring. }
  assert (Hwv : w = Copp (sigma c)).
  { transitivity (((sigma c + w * C0) + w * C1) - sigma c)%C; [ring |].
    rewrite Hw. ring. }
  split.
  - apply (CCembeds_ext_pred K); [| exact Hemb].
    intro x. split.
    + intro Hx. apply (proj2 (CPolyF_1_iff K r x HK)). exact Hx.
    + intro Hx. apply (proj1 (CPolyF_1_iff K r x HK)). exact Hx.
  - rewrite Hr, Hwv.
    apply (CCembeds_opp K sigma c HK Hemb H1).
Qed.

(** The value of any embedding of the adjunction on a span element. *)
Lemma CCembeds_value_on_span :
  forall (K : C -> Prop) (r : C) (j : nat) (dtcf : list C) (tau : C -> C),
  is_Csubfield K -> (1 <= j)%nat ->
  length dtcf = j -> Forall K dtcf ->
  (cpeval dtcf r + Cpow r j)%C = C0 ->
  CCembeds (CPolyF K j r) tau ->
  forall cs, Forall K cs ->
  tau (cpeval cs r) = CCevalMap tau cs (tau r).
Proof.
  intros K r j dtcf tau HK Hj Hlen HKdt Hrel Htau cs HKcs.
  pose proof Htau as [Ht0 [Ht1 [Htadd Htmul]]].
  induction HKcs as [|c cs' Hc HKcs' IH]; cbn [cpeval CCevalMap].
  - exact Ht0.
  - assert (Hcm : CPolyF K j r c)
      by (apply (CPolyF_contains K r j dtcf HK Hj Hlen HKdt Hrel); exact Hc).
    assert (Hrm : CPolyF K j r r)
      by (apply (CPolyF_r_mem K r j dtcf HK Hj Hlen HKdt Hrel)).
    assert (Hcsm : CPolyF K j r (cpeval cs' r))
      by (apply (CPolyF_cpeval_at K r j dtcf HK Hj Hlen HKdt Hrel); assumption).
    rewrite (Htadd c (r * cpeval cs' r)%C Hcm
               (CPolyF_mul K r j dtcf HK Hj Hlen HKdt Hrel r (cpeval cs' r) Hrm Hcsm)).
    rewrite (Htmul r (cpeval cs' r) Hrm Hcsm).
    rewrite IH. reflexivity.
Qed.

Lemma CCembeds_pow_val :
  forall (K : C -> Prop) (r : C) (j : nat) (dtcf : list C) (tau : C -> C),
  is_Csubfield K -> (1 <= j)%nat ->
  length dtcf = j -> Forall K dtcf ->
  (cpeval dtcf r + Cpow r j)%C = C0 ->
  CCembeds (CPolyF K j r) tau ->
  forall n, tau (Cpow r n) = Cpow (tau r) n.
Proof.
  intros K r j dtcf tau HK Hj Hlen HKdt Hrel Htau n.
  pose proof Htau as [Ht0 [Ht1 [Htadd Htmul]]].
  induction n as [|n IH]; cbn [Cpow].
  - exact Ht1.
  - assert (Hrm : CPolyF K j r r)
      by (apply (CPolyF_r_mem K r j dtcf HK Hj Hlen HKdt Hrel)).
    assert (Hpm : CPolyF K j r (Cpow r n))
      by (apply (CPolyF_pow K r j dtcf HK Hj Hlen HKdt Hrel r Hrm)).
    rewrite (Htmul r (Cpow r n) Hrm Hpm), IH. reflexivity.
Qed.

(** Any embedding of the adjunction sends the root to a root of the image relation of its restriction. *)
Lemma extension_root_lands :
  forall (K : C -> Prop) (r : C) (j : nat) (dtcf : list C)
         (sigma tau : C -> C),
  is_Csubfield K -> (1 <= j)%nat ->
  length dtcf = j -> Forall K dtcf ->
  (cpeval dtcf r + Cpow r j)%C = C0 ->
  CCembeds (CPolyF K j r) tau ->
  (forall x, K x -> tau x = sigma x) ->
  (CCevalMap sigma dtcf (tau r) + Cpow (tau r) j)%C = C0.
Proof.
  intros K r j dtcf sigma tau HK Hj Hlen HKdt Hrel Htau Hagree.
  pose proof Htau as [Ht0 [Ht1 [Htadd Htmul]]].
  assert (Hrelm : CPolyF K j r (cpeval dtcf r))
    by (apply (CPolyF_cpeval_at K r j dtcf HK Hj Hlen HKdt Hrel);
        [exact HKdt | apply (CPolyF_r_mem K r j dtcf HK Hj Hlen HKdt Hrel)]).
  assert (Hpowm : CPolyF K j r (Cpow r j))
    by (apply (CPolyF_pow K r j dtcf HK Hj Hlen HKdt Hrel r
                (CPolyF_r_mem K r j dtcf HK Hj Hlen HKdt Hrel))).
  assert (Htz : tau ((cpeval dtcf r + Cpow r j)%C) = C0)
    by (rewrite Hrel; exact Ht0).
  rewrite (Htadd _ _ Hrelm Hpowm) in Htz.
  rewrite (CCembeds_value_on_span K r j dtcf tau HK Hj Hlen HKdt Hrel Htau dtcf HKdt)
    in Htz.
  rewrite (CCembeds_pow_val K r j dtcf tau HK Hj Hlen HKdt Hrel Htau j) in Htz.
  rewrite <- Htz.
  f_equal.
  apply CCevalMap_ext_on.
  apply Forall_forall. intros c Hc.
  symmetry. apply Hagree.
  exact (proj1 (Forall_forall K dtcf) HKdt c Hc).
Qed.

(** Two embeddings of the adjunction agreeing on K and at the root agree on the whole adjunction. *)
Lemma extensions_agree :
  forall (K : C -> Prop) (r : C) (j : nat) (dtcf : list C)
         (tau tau' : C -> C),
  is_Csubfield K -> (1 <= j)%nat ->
  length dtcf = j -> Forall K dtcf ->
  (cpeval dtcf r + Cpow r j)%C = C0 ->
  CCembeds (CPolyF K j r) tau -> CCembeds (CPolyF K j r) tau' ->
  (forall x, K x -> tau x = tau' x) ->
  tau r = tau' r ->
  forall x, CPolyF K j r x -> tau x = tau' x.
Proof.
  intros K r j dtcf tau tau' HK Hj Hlen HKdt Hrel Htau Htau' Hagree Hr x Hx.
  destruct Hx as [cs [Hlcs [HKcs Hxe]]].
  rewrite Hxe.
  rewrite (CCembeds_value_on_span K r j dtcf tau HK Hj Hlen HKdt Hrel Htau cs HKcs).
  rewrite (CCembeds_value_on_span K r j dtcf tau' HK Hj Hlen HKdt Hrel Htau' cs HKcs).
  rewrite Hr.
  apply CCevalMap_ext_on.
  apply Forall_forall. intros c Hc.
  apply Hagree.
  exact (proj1 (Forall_forall K cs) HKcs c Hc).
Qed.

Lemma CCembeds_mono : forall (K K' : C -> Prop) (tau : C -> C),
  (forall x, K x -> K' x) -> CCembeds K' tau -> CCembeds K tau.
Proof.
  intros K K' tau Hincl [H0 [H1 [Hadd Hmul]]].
  split; [exact H0 | split; [exact H1 | split]].
  - intros x y Hx Hy. apply Hadd; apply Hincl; assumption.
  - intros x y Hx Hy. apply Hmul; apply Hincl; assumption.
Qed.

(** Roots of the image relation lie among the roots of the split polynomial. *)
Lemma image_root_in_rho :
  forall (K : C -> Prop) (sigma : C -> C) (rho : list C) (Fcf : list C)
         (lead r : C) (j : nat) (dt : list C),
  is_Csubfield K -> CCembeds K sigma ->
  lead <> C0 ->
  (forall z, cpeval Fcf z = (lead * prod_linear rho z)%C) ->
  Forall K Fcf -> length Fcf = Datatypes.S (length rho) ->
  Forall (fun c => sigma c = c) Fcf ->
  In r rho ->
  (1 <= j)%nat -> (j <= length rho)%nat ->
  length dt = j -> Forall K dt ->
  (cpeval dt r + Cpow r j)%C = C0 -> Cindep_pows K r j ->
  forall w, (CCevalMap sigma dt w + Cpow w j)%C = C0 -> In w rho.
Proof.
  intros K sigma rho Fcf lead r j dt HK Hemb Hlead Hsplit HKF HlF Hfix Hin
         Hj Hjn Hldt HKdt Hrel Hindep w Hw.
  pose proof Hemb as [Hs0 [Hs1 [Hsadd Hsmul]]].
  assert (HFr : cpeval Fcf r = C0).
  { rewrite Hsplit, (prod_linear_root rho r Hin r eq_refl). ring. }
  destruct (cminpoly_divides K r j dt HK Hj Hldt HKdt Hrel Hindep Fcf HKF HFr)
    as [HKQ Hdiv].
  set (Q := fst (cpdiv_lf (length (rev Fcf)) (rev Fcf) (rev dt))) in *.
  assert (HlQ : length Q = (length rho + 1 - j)%nat).
  { unfold Q. rewrite (cpdiv_lf_qlen _ _ _ (Nat.le_refl _)).
    rewrite !length_rev, HlF, Hldt. lia. }
  assert (HFcoeff : Fcf = cpmul (rev Q) (dt ++ C1 :: nil)).
  { apply cpeval_ext_coeffs.
    - rewrite cpmul_length;
        [| rewrite length_rev, HlQ; lia
         | rewrite length_app, Hldt; cbn [length]; lia].
      rewrite length_rev, HlQ, length_app, Hldt. cbn [length]. lia.
    - intro z. rewrite cpeval_cpmul.
      rewrite (Hdiv z).
      assert (HQz : cpeval (rev Q) z = cpeval_lf Q z)
        by (rewrite cpeval_lf_rev_c; reflexivity).
      assert (HMz : cpeval (dt ++ C1 :: nil) z = (Cpow z j + cpeval dt z)%C).
      { rewrite cpeval_app, Hldt. cbn [cpeval]. ring. }
      rewrite HQz, HMz. ring. }
  assert (HFw : cpeval Fcf w = C0).
  { assert (HFsig : CCevalMap sigma Fcf w = cpeval Fcf w).
    { rewrite (CCevalMap_ext_on sigma (fun c => c) Fcf w Hfix).
      apply CCevalMap_id. }
    rewrite <- HFsig.
    rewrite HFcoeff at 1.
    rewrite (CCevalMap_cpmul K sigma Hemb HK);
      [| apply Forall_rev; exact HKQ
       | apply Forall_app_intro_c;
           [exact HKdt | constructor; [apply (Csubfield_1 K HK) | constructor]]].
    assert (HMw : CCevalMap sigma (dt ++ C1 :: nil) w
                  = (CCevalMap sigma dt w + Cpow w j)%C).
    { rewrite CCevalMap_app, Hldt. cbn [CCevalMap].
      rewrite Hs1. ring. }
    rewrite HMw, Hw. ring. }
  rewrite Hsplit in HFw.
  apply prod_linear_zero_in.
  destruct (Cmul_integral _ _ HFw) as [E | E]; [contradiction | exact E].
Qed.

(** The extension list of one embedding along one adjunction step, one extension per listed target. *)
Lemma mk_extensions :
  forall (K : C -> Prop) (r : C) (j : nat) (dt : list C) (sigma : C -> C),
  is_Csubfield K -> (1 <= j)%nat ->
  length dt = j -> Forall K dt ->
  (cpeval dt r + Cpow r j)%C = C0 -> Cindep_pows K r j ->
  CCembeds K sigma ->
  forall ws : list C,
  (forall w, In w ws -> (CCevalMap sigma dt w + Cpow w j)%C = C0) ->
  exists exts : list (C -> C),
    length exts = length ws /\
    forall i, (i < length ws)%nat ->
      CCembeds (CPolyF K j r) (nth i exts (fun z => z)) /\
      (forall x, K x -> nth i exts (fun z => z) x = sigma x) /\
      nth i exts (fun z => z) r = nth i ws C0.
Proof.
  intros K r j dt sigma HK Hj Hldt HKdt Hrel Hindep Hemb ws.
  induction ws as [|w ws IH]; intro Hroots.
  - exists nil. split; [reflexivity | intros i Hi; cbn [length] in Hi; lia].
  - destruct IH as [exts [Hlex Hex]];
      [intros w' Hw'; apply Hroots; right; exact Hw' |].
    assert (Hwroot : (CCevalMap sigma dt w + Cpow w j)%C = C0)
      by (apply Hroots; left; reflexivity).
    destruct (Nat.eq_dec j 1) as [-> | Hj2].
    + destruct (CCembeds_extend_one K r dt sigma w HK Hldt HKdt Hrel Hemb Hwroot)
        as [Hemb1 Hr1].
      exists (sigma :: exts).
      split; [cbn [length]; lia |].
      intros i Hi.
      destruct i as [|i']; cbn [nth].
      * split; [exact Hemb1 | split; [intros x _; reflexivity | exact Hr1]].
      * cbn [length] in Hi. apply Hex. lia.
    + assert (Hj2' : (2 <= j)%nat) by lia.
      destruct (CCembeds_extend_step K r j dt sigma w HK Hj2' Hldt HKdt Hrel
                  Hindep Hemb Hwroot) as [sigma' [Hemb' [Hagr' Hr']]].
      exists (sigma' :: exts).
      split; [cbn [length]; lia |].
      intros i Hi.
      destruct i as [|i']; cbn [nth].
      * split; [exact Hemb' | split; [exact Hagr' | exact Hr']].
      * cbn [length] in Hi. apply Hex. lia.
Qed.

(** nth through a flat_map with uniform block width. *)
Lemma nth_flat_map_uniform :
  forall (A B : Type) (f : A -> list B) (l : list A) (width : nat)
         (dA : A) (dB : B),
  (forall a, In a l -> length (f a) = width) ->
  forall q s, (q < length l)%nat -> (s < width)%nat ->
  nth (q * width + s) (flat_map f l) dB = nth s (f (nth q l dA)) dB.
Proof.
  intros A B f l width dA dB Hw.
  induction l as [|a l IH]; intros q s Hq Hs.
  - cbn [length] in Hq. lia.
  - cbn [flat_map].
    destruct q as [|q'].
    + cbn [nth]. rewrite Nat.mul_0_l, Nat.add_0_l.
      rewrite app_nth1; [reflexivity |].
      rewrite (Hw a (or_introl eq_refl)). exact Hs.
    + cbn [nth].
      rewrite app_nth2 by (rewrite (Hw a (or_introl eq_refl)); nia).
      rewrite (Hw a (or_introl eq_refl)).
      replace (Datatypes.S q' * width + s - width)%nat
        with (q' * width + s)%nat by nia.
      apply IH; [intros a' Ha'; apply Hw; right; exact Ha' | | exact Hs].
      cbn [length] in Hq. lia.
Qed.

Lemma flat_map_length_uniform :
  forall (A B : Type) (f : A -> list B) (l : list A) (width : nat),
  (forall a, In a l -> length (f a) = width) ->
  length (flat_map f l) = (length l * width)%nat.
Proof.
  intros A B f l width Hw.
  induction l as [|a l IH]; cbn [flat_map length].
  - reflexivity.
  - rewrite length_app, (Hw a (or_introl eq_refl)), IH;
      [reflexivity | intros a' Ha'; apply Hw; right; exact Ha'].
Qed.

(* the adjunction chain -- RootChain with its subfield, inclusion, and root lemmas, and prodl of the step degrees; the embedding enumeration lives with the arbitrary-base chain count below, and its identity instance follows it. *)

Inductive RootChain (K0 : C -> Prop) (rho : list C)
  : list C -> list nat -> (C -> Prop) -> Prop :=
| RC_nil : RootChain K0 rho nil nil K0
| RC_step : forall rs js K r j dt,
    RootChain K0 rho rs js K ->
    In r rho ->
    (1 <= j)%nat -> (j <= length rho)%nat ->
    length dt = j -> Forall K dt ->
    (cpeval dt r + Cpow r j)%C = C0 ->
    Cindep_pows K r j ->
    RootChain K0 rho (rs ++ r :: nil) (js ++ j :: nil) (CPolyF K j r).

Lemma RootChain_subfield : forall K0 rho rs js K,
  is_Csubfield K0 -> RootChain K0 rho rs js K -> is_Csubfield K.
Proof.
  intros K0 rho rs js K HK0 Hch. induction Hch.
  - exact HK0.
  - apply (CPolyF_Csubfield K r j dt); assumption.
Qed.

Lemma RootChain_incl : forall K0 rho rs js K,
  is_Csubfield K0 -> RootChain K0 rho rs js K -> forall x, K0 x -> K x.
Proof.
  intros K0 rho rs js K HK0 Hch. induction Hch; intros x Hx.
  - exact Hx.
  - apply (CPolyF_contains K r j dt); try assumption.
    + apply (RootChain_subfield K0 rho rs js K); assumption.
    + apply IHHch. exact Hx.
Qed.

Lemma RootChain_roots_in : forall K0 rho rs js K,
  is_Csubfield K0 -> RootChain K0 rho rs js K -> forall r, In r rs -> K r.
Proof.
  intros K0 rho rs js K HK0 Hch. induction Hch; intros r0 Hr0.
  - contradiction.
  - assert (HKsub : is_Csubfield K)
      by (apply (RootChain_subfield K0 rho rs js K); assumption).
    apply in_app_or in Hr0.
    destruct Hr0 as [Hr0 | [-> | []]].
    + apply (CPolyF_contains K r j dt); try assumption.
      apply IHHch. exact Hr0.
    + apply (CPolyF_r_mem K r0 j dt); assumption.
Qed.

Definition prodl (js : list nat) : nat := fold_right Nat.mul 1%nat js.

Lemma prodl_app : forall js1 js2, prodl (js1 ++ js2) = (prodl js1 * prodl js2)%nat.
Proof.
  induction js1 as [|a js1 IH]; intro js2; unfold prodl in *; cbn [app fold_right].
  - lia.
  - rewrite IH. lia.
Qed.

(* the count is intrinsic -- any well-formed distinguishable list injects into any complete list, so two enumerations have equal length. *)

Lemma embedding_list_le :
  forall (K0 K : C -> Prop) (L1 L2 : list (C -> C)),
  (forall i, (i < length L1)%nat ->
     CCembeds K (nth i L1 (fun z => z)) /\
     (forall x, K0 x -> nth i L1 (fun z => z) x = x)) ->
  (forall i i', (i < length L1)%nat -> (i' < length L1)%nat -> i <> i' ->
     exists x, K x /\
       nth i L1 (fun z => z) x <> nth i' L1 (fun z => z) x) ->
  (forall tau, CCembeds K tau -> (forall x, K0 x -> tau x = x) ->
     exists k, (k < length L2)%nat /\
       (forall x, K x -> tau x = nth k L2 (fun z => z) x)) ->
  (length L1 <= length L2)%nat.
Proof.
  intros K0 K L1 L2 Hwf Hdist Hcomp.
  assert (Hks : forall n, (n <= length L1)%nat ->
    exists ks : list nat, length ks = n /\
      forall i, (i < n)%nat ->
        (nth i ks 0%nat < length L2)%nat /\
        (forall x, K x -> nth i L1 (fun z => z) x
                          = nth (nth i ks 0%nat) L2 (fun z => z) x)).
  { intro n. induction n as [|n IHn]; intro Hn.
    - exists nil. split; [reflexivity | intros i Hi; lia].
    - destruct IHn as [ks [Hlks Hprop]]; [lia |].
      destruct (Hwf n ltac:(lia)) as [Hemb Hfix].
      destruct (Hcomp (nth n L1 (fun z => z)) Hemb Hfix) as [k [Hk Hagr]].
      exists (ks ++ k :: nil).
      split; [rewrite length_app, Hlks; cbn [length]; lia |].
      intros i Hi.
      destruct (Nat.eq_dec i n) as [-> | Hne].
      + rewrite app_nth2 by lia.
        rewrite Hlks, Nat.sub_diag. cbn [nth].
        split; [exact Hk | exact Hagr].
      + rewrite app_nth1 by lia.
        apply Hprop. lia. }
  destruct (Hks (length L1) (Nat.le_refl _)) as [ks [Hlks Hprop]].
  assert (Hnd : NoDup ks).
  { apply (proj2 (NoDup_nth ks 0%nat)).
    intros a b Ha Hb Hab.
    rewrite Hlks in Ha, Hb.
    destruct (Nat.eq_dec a b) as [E | Hne]; [exact E | exfalso].
    destruct (Hdist a b Ha Hb Hne) as [x [HxK Hxne]].
    apply Hxne.
    rewrite (proj2 (Hprop a Ha) x HxK).
    rewrite (proj2 (Hprop b Hb) x HxK).
    rewrite Hab. reflexivity. }
  assert (Hincl : incl ks (seq 0 (length L2))).
  { intros k Hk.
    destruct (In_nth ks k 0%nat Hk) as [i [Hi Hnthi]].
    rewrite Hlks in Hi.
    apply in_seq.
    split; [lia |].
    rewrite <- Hnthi.
    exact (proj1 (Hprop i Hi)). }
  pose proof (NoDup_incl_length Hnd Hincl) as Hle.
  rewrite Hlks, length_seq in Hle.
  exact Hle.
Qed.

(* embeddings are injective on the field, hence permute the root list of any fixed split polynomial with coefficients in it. *)

Lemma CCembeds_injective_on :
  forall (K : C -> Prop) (tau : C -> C),
  is_Csubfield K -> CCembeds K tau ->
  forall x y, K x -> K y -> tau x = tau y -> x = y.
Proof.
  intros K tau HK Htau x y Hx Hy Hxy.
  pose proof Htau as [Ht0 [Ht1 [Htadd Htmul]]].
  destruct (Ceq_dec x y) as [E | Hne]; [exact E | exfalso].
  set (d := (x - y)%C).
  assert (Hd : K d) by (apply Csubfield_sub; assumption).
  assert (Hdne : d <> C0).
  { intro E. apply Hne.
    transitivity ((x - y) + y)%C; [ring |].
    unfold d in E. rewrite E. ring. }
  assert (Hinv : K (Cinv d)) by (apply Csubfield_inv; assumption).
  assert (Hone : (d * Cinv d)%C = C1).
  { transitivity ((Cinv d * d)%C); [ring |]. apply Cinv_l. exact Hdne. }
  assert (Htd : tau d = C0).
  { assert (Hxmy : d = (x + Copp y)%C) by (unfold d; ring).
    rewrite Hxmy.
    rewrite (Htadd x (Copp y) Hx (Csubfield_opp K y HK Hy)).
    rewrite (CCembeds_opp K tau y HK Htau Hy).
    rewrite Hxy. ring. }
  assert (Habs : tau C1 = C0).
  { rewrite <- Hone.
    rewrite (Htmul d (Cinv d) Hd Hinv).
    rewrite Htd. ring. }
  rewrite Ht1 in Habs.
  exact (C1_neq_C0 Habs).
Qed.

(** Evaluation of a fixed-coefficient K-list commutes with the embedding at a K-point. *)
Lemma tau_cpeval_fixed :
  forall (K : C -> Prop) (tau : C -> C), is_Csubfield K -> CCembeds K tau ->
  forall (cs : list C) (r : C), Forall K cs -> Forall (fun c => tau c = c) cs ->
  K r -> tau (cpeval cs r) = cpeval cs (tau r).
Proof.
  intros K tau HK Htau cs r HKcs Hfixcs HKr.
  pose proof Htau as [Ht0 [Ht1 [Htadd Htmul]]].
  assert (HKcp_gen : forall ds, Forall K ds -> K (cpeval ds r)).
  { intros ds HKds. induction HKds as [|d ds Hd HKds IHd]; cbn [cpeval].
    - apply (Csubfield_0 K HK).
    - apply Csubfield_add; [exact HK | exact Hd |].
      apply Csubfield_mul; [exact HK | exact HKr | exact IHd]. }
  induction cs as [|c cs IHcs]; cbn [cpeval].
  - exact Ht0.
  - inversion HKcs; subst. inversion Hfixcs; subst.
    rewrite (Htadd c (r * cpeval cs r)%C H1
               (Csubfield_mul K r (cpeval cs r) HK HKr (HKcp_gen cs H2))).
    rewrite (Htmul r (cpeval cs r) HKr (HKcp_gen cs H2)).
    rewrite H3, (IHcs H2 H4). reflexivity.
Qed.

(** An embedding fixing the coefficients maps the root list into itself injectively: a permutation of the roots. *)
Lemma embedding_permutes_roots :
  forall (K : C -> Prop) (tau : C -> C) (rho : list C) (Fcf : list C) (lead : C),
  is_Csubfield K -> CCembeds K tau ->
  NoDup rho -> lead <> C0 ->
  (forall z, cpeval Fcf z = (lead * prod_linear rho z)%C) ->
  Forall K Fcf ->
  Forall (fun c => tau c = c) Fcf ->
  (forall z, In z rho -> K z) ->
  Permutation rho (map tau rho).
Proof.
  intros K tau rho Fcf lead HK Htau Hnd Hlead Hsplit HKF Hfix Hroots.
  symmetry.
  apply NoDup_Permutation_bis.
  - apply NoDup_map_inj_on; [| exact Hnd].
    intros x y Hx Hy Hxy.
    apply (CCembeds_injective_on K tau HK Htau x y (Hroots x Hx) (Hroots y Hy) Hxy).
  - rewrite length_map. lia.
  - intros w Hw.
    apply in_map_iff in Hw.
    destruct Hw as [r [Hwr Hr]]. subst w.
    assert (HFr : cpeval Fcf r = C0).
    { rewrite Hsplit, (prod_linear_root rho r Hr r eq_refl). ring. }
    assert (HFtr : cpeval Fcf (tau r) = C0).
    { rewrite <- (tau_cpeval_fixed K tau HK Htau Fcf r HKF Hfix (Hroots r Hr)).
      rewrite HFr. exact (proj1 Htau). }
    rewrite Hsplit in HFtr.
    apply prod_linear_zero_in.
    destruct (Cmul_integral _ _ HFtr) as [E | E]; [contradiction | exact E].
Qed.

(* the rational base CQ inside C -- every embedding is the identity on it, and the real-rational field transports through RtoC. *)

Definition CQ (z : C) : Prop := exists x : R, is_rational x /\ z = RtoC x.

Lemma RtoC_sub_c : forall a b, RtoC (a - b) = (RtoC a - RtoC b)%C.
Proof.
  intros a b. unfold RtoC, Csub, Cadd, Copp. cbn. f_equal; ring.
Qed.

Lemma RtoC_inv_c : forall a, a <> 0 -> RtoC (/ a) = Cinv (RtoC a).
Proof.
  intros a Ha.
  apply (Cmul_eq_reg_l (RtoC a)); [apply RtoC_neq_0; exact Ha |].
  rewrite <- RtoC_mul.
  rewrite Rinv_r by exact Ha.
  symmetry.
  transitivity ((Cinv (RtoC a) * RtoC a)%C); [ring |].
  apply Cinv_l. apply RtoC_neq_0. exact Ha.
Qed.

Lemma CQ_subfield : is_Csubfield CQ.
Proof.
  assert (Hrat := is_rational_subfield).
  repeat split.
  - exists 0. split; [apply (subfield_0 is_rational Hrat) | reflexivity].
  - exists 1. split; [apply (subfield_1 is_rational Hrat) | reflexivity].
  - intros x y [a [Ha Hxa]] [b [Hb Hyb]].
    exists (a + b).
    split; [apply (subfield_add is_rational a b Hrat Ha Hb) |].
    rewrite Hxa, Hyb. symmetry. apply RtoC_add.
  - intros x y [a [Ha Hxa]] [b [Hb Hyb]].
    exists (a - b).
    split; [apply (subfield_sub is_rational a b Hrat Ha Hb) |].
    rewrite Hxa, Hyb. symmetry. apply RtoC_sub_c.
  - intros x y [a [Ha Hxa]] [b [Hb Hyb]].
    exists (a * b).
    split; [apply (subfield_mul is_rational a b Hrat Ha Hb) |].
    rewrite Hxa, Hyb. symmetry. apply RtoC_mul.
  - intros x [a [Ha Hxa]] Hne.
    assert (Hane : a <> 0).
    { intro E. apply Hne. rewrite Hxa, E. reflexivity. }
    exists (/ a).
    split; [apply (subfield_inv is_rational a Hrat Ha Hane) |].
    rewrite Hxa. symmetry. apply RtoC_inv_c. exact Hane.
Qed.

(** Integers are rational; integer complex lists live in CQ. *)
Lemma IZR_is_rational : forall n : Z, is_rational (IZR n).
Proof.
  intro n. exists n, 1%Z. split; [lia |]. field.
Qed.

Lemma CQ_IZR : forall n : Z, CQ (RtoC (IZR n)).
Proof.
  intro n. exists (IZR n). split; [apply IZR_is_rational | reflexivity].
Qed.

(** Every embedding of a field containing CQ is the identity on CQ: naturals, then integers, then quotients. *)
Lemma CCembeds_fixes_CQ :
  forall (K : C -> Prop) (tau : C -> C),
  is_Csubfield K -> CCembeds K tau ->
  (forall z, CQ z -> K z) ->
  forall z, CQ z -> tau z = z.
Proof.
  intros K tau HK Htau Hincl z HzQ.
  pose proof Htau as [Ht0 [Ht1 [Htadd Htmul]]].
  assert (HKQ : forall w, CQ w -> K w) by exact Hincl.
  assert (Hnat : forall n : nat, tau (RtoC (INR n)) = RtoC (INR n)).
  { induction n as [|n IHn].
    - cbn [INR]. exact Ht0.
    - assert (HScast : RtoC (INR (Datatypes.S n)) = (RtoC (INR n) + C1)%C).
      { rewrite S_INR, RtoC_add. reflexivity. }
      rewrite HScast.
      assert (HQn : CQ (RtoC (INR n))).
      { exists (INR n). split; [| reflexivity].
        rewrite INR_IZR_INZ. apply IZR_is_rational. }
      assert (HQ1 : CQ C1) by (apply (Csubfield_1 CQ CQ_subfield)).
      rewrite (Htadd _ _ (HKQ _ HQn) (HKQ _ HQ1)).
      rewrite IHn, Ht1. reflexivity. }
  assert (Hint : forall n : Z, tau (RtoC (IZR n)) = RtoC (IZR n)).
  { intro n.
    destruct (Z_le_dec 0 n) as [Hpos | Hneg].
    - replace (IZR n) with (INR (Z.to_nat n))
        by (rewrite INR_IZR_INZ, Z2Nat.id by lia; reflexivity).
      apply Hnat.
    - set (m := (- n)%Z).
      assert (Hm : (0 <= m)%Z) by lia.
      assert (Hcast : RtoC (IZR n) = Copp (RtoC (IZR m))).
      { unfold m. rewrite opp_IZR.
        unfold RtoC, Copp. cbn. f_equal; ring. }
      rewrite Hcast.
      assert (HQm : CQ (RtoC (IZR m)))
        by (apply CQ_IZR).
      rewrite (CCembeds_opp K tau (RtoC (IZR m)) HK Htau (HKQ _ HQm)).
      replace (IZR m) with (INR (Z.to_nat m))
        by (rewrite INR_IZR_INZ, Z2Nat.id by lia; reflexivity).
      rewrite Hnat. reflexivity. }
  destruct HzQ as [x [[p [q [Hq Hx]]] Hzx]].
  assert (Hqne : IZR q <> 0)
    by (apply IZR_neq; lia).
  assert (Hzfrac : z = (RtoC (IZR p) * Cinv (RtoC (IZR q)))%C).
  { rewrite Hzx, Hx. unfold Rdiv.
    rewrite RtoC_mul, RtoC_inv_c by exact Hqne.
    reflexivity. }
  assert (HQp : CQ (RtoC (IZR p))) by apply CQ_IZR.
  assert (HQq : CQ (RtoC (IZR q))) by apply CQ_IZR.
  assert (Hqcne : RtoC (IZR q) <> C0)
    by (apply RtoC_neq_0; exact Hqne).
  assert (HQiq : CQ (Cinv (RtoC (IZR q))))
    by (apply (Csubfield_inv CQ _ CQ_subfield HQq Hqcne)).
  rewrite Hzfrac.
  rewrite (Htmul _ _ (HKQ _ HQp) (HKQ _ HQiq)).
  rewrite Hint.
  assert (Htinv : tau (Cinv (RtoC (IZR q))) = Cinv (RtoC (IZR q))).
  { assert (Hprod : (RtoC (IZR q) * Cinv (RtoC (IZR q)))%C = C1).
    { transitivity ((Cinv (RtoC (IZR q)) * RtoC (IZR q))%C); [ring |].
      apply Cinv_l. exact Hqcne. }
    assert (Htprod : tau ((RtoC (IZR q) * Cinv (RtoC (IZR q)))%C) = C1)
      by (rewrite Hprod; exact Ht1).
    rewrite (Htmul _ _ (HKQ _ HQq) (HKQ _ HQiq)) in Htprod.
    rewrite Hint in Htprod.
    apply (Cmul_eq_reg_l (RtoC (IZR q))); [exact Hqcne |].
    rewrite Htprod. symmetry.
    transitivity ((Cinv (RtoC (IZR q)) * RtoC (IZR q))%C); [ring |].
    apply Cinv_l. exact Hqcne. }
  rewrite Htinv. reflexivity.
Qed.

(* the chain count over an arbitrary base embedding nu -- every nu has exactly prodl js extensions, the equal-fiber principle replacing the Galois correspondence. *)

Theorem RootChain_embeddings_over :
  forall (K0 : C -> Prop) (rho : list C) (Fcf : list C) (lead : C)
         (nu : C -> C),
  is_Csubfield K0 -> NoDup rho -> lead <> C0 ->
  (forall z, cpeval Fcf z = (lead * prod_linear rho z)%C) ->
  Forall K0 Fcf -> length Fcf = Datatypes.S (length rho) ->
  CCembeds K0 nu ->
  Forall (fun c => nu c = c) Fcf ->
  forall rs js K, RootChain K0 rho rs js K ->
  exists sigmas : list (C -> C),
    length sigmas = prodl js /\
    (forall i, (i < prodl js)%nat ->
       CCembeds K (nth i sigmas (fun z => z)) /\
       (forall x, K0 x -> nth i sigmas (fun z => z) x = nu x)) /\
    (forall tau, CCembeds K tau -> (forall x, K0 x -> tau x = nu x) ->
       exists i, (i < prodl js)%nat /\
         (forall x, K x -> tau x = nth i sigmas (fun z => z) x)) /\
    (forall i i', (i < prodl js)%nat -> (i' < prodl js)%nat -> i <> i' ->
       exists x, K x /\
         nth i sigmas (fun z => z) x <> nth i' sigmas (fun z => z) x).
Proof.
  intros K0 rho Fcf lead nu HK0 Hnd Hlead Hsplit HKF0 HlF Hnu HnuF rs js K Hch.
  induction Hch as [| rs js K r j dt Hch IH Hin Hj1 Hjn Hldt HKdt Hrel Hindep].
  - exists (nu :: nil).
    split; [reflexivity | split; [| split]].
    + intros i Hi.
      assert (Hi0 : i = 0%nat) by (cbn [prodl fold_right] in Hi; lia).
      subst i. cbn [nth].
      split; [exact Hnu | intros x _; reflexivity].
    + intros tau Htau Hfix.
      exists 0%nat.
      split; [cbn [prodl fold_right]; lia |].
      intros x Hx. cbn [nth]. apply Hfix. exact Hx.
    + intros i i' Hi Hi' Hne.
      cbn [prodl fold_right] in Hi, Hi'. lia.
  - destruct IH as [sigmas [Hlen [Hwf [Hcomp Hdist]]]].
    assert (HKsub : is_Csubfield K)
      by (apply (RootChain_subfield K0 rho rs js K HK0 Hch)).
    assert (HKF : Forall K Fcf).
    { apply Forall_forall. intros c Hc.
      apply (RootChain_incl K0 rho rs js K HK0 Hch).
      exact (proj1 (Forall_forall K0 Fcf) HKF0 c Hc). }
    set (N := prodl js) in *.
    set (tgt := fun (sg : C -> C) =>
      filter (fun w => if Ceq_dec ((CCevalMap sg dt w + Cpow w j)%C) C0
                       then true else false) rho).
    assert (Hfixcf : forall i, (i < N)%nat ->
              Forall (fun c => nth i sigmas (fun z => z) c = c) Fcf).
    { intros i Hi. apply Forall_forall. intros c Hc.
      assert (HcK0 : K0 c) by (exact (proj1 (Forall_forall K0 Fcf) HKF0 c Hc)).
      rewrite (proj2 (Hwf i Hi) c HcK0).
      exact (proj1 (Forall_forall _ Fcf) HnuF c Hc). }
    assert (Htlen : forall i, (i < N)%nat ->
              length (tgt (nth i sigmas (fun z => z))) = j).
    { intros i Hi. unfold tgt.
      apply (image_relation_root_count K (nth i sigmas (fun z => z)) rho Fcf lead r j dt
               HKsub (proj1 (Hwf i Hi)) Hnd Hlead Hsplit HKF HlF
               (Hfixcf i Hi) Hin Hj1 Hjn Hldt HKdt Hrel Hindep). }
    assert (Hbuild : forall (sl : list (C -> C)),
      (forall sg, In sg sl -> CCembeds K sg /\ (forall x, K0 x -> sg x = nu x) /\
                  length (tgt sg) = j) ->
      exists sigs' : list (C -> C),
        length sigs' = (length sl * j)%nat /\
        forall q s, (q < length sl)%nat -> (s < j)%nat ->
          CCembeds (CPolyF K j r) (nth (q * j + s) sigs' (fun z => z)) /\
          (forall x, K x -> nth (q * j + s) sigs' (fun z => z) x
                            = nth q sl (fun z => z) x) /\
          nth (q * j + s) sigs' (fun z => z) r
            = nth s (tgt (nth q sl (fun z => z))) C0).
    { intro sl. induction sl as [|sg sl IHsl]; intro Hsl.
      - exists nil. split; [reflexivity | intros q s Hq Hs; cbn [length] in Hq; lia].
      - destruct IHsl as [rest [Hlrest Hrest]];
          [intros sg' Hsg'; apply Hsl; right; exact Hsg' |].
        destruct (Hsl sg (or_introl eq_refl)) as [Hsgemb [Hsgfix Hsgtlen]].
        assert (Hroots : forall w, In w (tgt sg) ->
                  (CCevalMap sg dt w + Cpow w j)%C = C0).
        { intros w Hw. unfold tgt in Hw. apply filter_In in Hw.
          destruct Hw as [_ Hw].
          destruct (Ceq_dec ((CCevalMap sg dt w + Cpow w j)%C) C0) as [E | E];
            [exact E | discriminate]. }
        destruct (mk_extensions K r j dt sg HKsub Hj1 Hldt HKdt Hrel Hindep
                    Hsgemb (tgt sg) Hroots) as [exts [Hlex Hex]].
        exists (exts ++ rest).
        split.
        { rewrite length_app, Hlex, Hlrest, Hsgtlen. cbn [length]. nia. }
        intros q s Hq Hs.
        destruct q as [|q'].
        + rewrite Nat.mul_0_l, Nat.add_0_l.
          rewrite app_nth1 by (rewrite Hlex, Hsgtlen; exact Hs).
          cbn [nth].
          apply Hex. rewrite Hsgtlen. exact Hs.
        + rewrite app_nth2 by (rewrite Hlex, Hsgtlen; nia).
          rewrite Hlex, Hsgtlen.
          replace (Datatypes.S q' * j + s - j)%nat with (q' * j + s)%nat by nia.
          cbn [nth].
          apply Hrest; [cbn [length] in Hq; lia | exact Hs].
    }
    assert (Hslprops : forall sg, In sg sigmas ->
              CCembeds K sg /\ (forall x, K0 x -> sg x = nu x) /\
              length (tgt sg) = j).
    { intros sg Hsg.
      destruct (In_nth sigmas sg (fun z => z) Hsg) as [i [Hi Hnthi]].
      rewrite Hlen in Hi.
      rewrite <- Hnthi.
      split; [exact (proj1 (Hwf i Hi)) |].
      split; [exact (proj2 (Hwf i Hi)) | exact (Htlen i Hi)]. }
    destruct (Hbuild sigmas Hslprops) as [sigs' [Hlsigs' Hblock]].
    rewrite Hlen in Hlsigs', Hblock.
    assert (HNj : prodl (js ++ j :: nil) = (N * j)%nat).
    { rewrite prodl_app. unfold prodl at 2. cbn [fold_right]. unfold N. lia. }
    exists sigs'.
    assert (Hj0 : j <> 0%nat) by lia.
    split; [rewrite Hlsigs', HNj; reflexivity | split; [| split]].
    + intros i Hi. rewrite HNj in Hi.
      assert (Hq : (i / j < N)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
      assert (Hs : (i mod j < j)%nat) by (apply Nat.mod_upper_bound; exact Hj0).
      assert (Hieq : i = (i / j * j + i mod j)%nat)
        by (rewrite Nat.mul_comm; apply Nat.div_mod_eq).
      rewrite Hieq.
      destruct (Hblock (i / j)%nat (i mod j)%nat Hq Hs) as [Hb1 [Hb2 Hb3]].
      split; [exact Hb1 |].
      intros x Hx.
      rewrite (Hb2 x (RootChain_incl K0 rho rs js K HK0 Hch x Hx)).
      exact (proj2 (Hwf (i / j)%nat Hq) x Hx).
    + intros tau Htau Hfix.
      assert (Htau_K : CCembeds K tau).
      { apply (CCembeds_mono K (CPolyF K j r));
          [intros x Hx; apply (CPolyF_contains K r j dt HKsub Hj1 Hldt HKdt Hrel x Hx)
          | exact Htau]. }
      destruct (Hcomp tau Htau_K Hfix) as [q [Hq Hagq]].
      set (sq := nth q sigmas (fun z => z)) in *.
      assert (Htr_root : (CCevalMap sq dt (tau r) + Cpow (tau r) j)%C = C0).
      { apply (extension_root_lands K r j dt sq tau HKsub Hj1 Hldt HKdt Hrel Htau).
        intros x Hx. apply Hagq. exact Hx. }
      assert (Htr_rho : In (tau r) rho).
      { apply (image_root_in_rho K sq rho Fcf lead r j dt HKsub
                 (proj1 (Hwf q Hq)) Hlead Hsplit HKF HlF (Hfixcf q Hq)
                 Hin Hj1 Hjn Hldt HKdt Hrel Hindep (tau r) Htr_root). }
      assert (Htr_tgt : In (tau r) (tgt sq)).
      { unfold tgt. apply filter_In.
        split; [exact Htr_rho |].
        destruct (Ceq_dec ((CCevalMap sq dt (tau r) + Cpow (tau r) j)%C) C0) as [E | E];
          [reflexivity | contradiction]. }
      destruct (In_nth (tgt sq) (tau r) C0 Htr_tgt) as [s [Hs Hnths]].
      unfold sq in Hs. rewrite (Htlen q Hq) in Hs.
      exists (q * j + s)%nat.
      split; [rewrite HNj; nia |].
      destruct (Hblock q s Hq Hs) as [Hb1 [Hb2 Hb3]].
      intros x Hx.
      apply (extensions_agree K r j dt tau
               (nth (q * j + s)%nat sigs' (fun z => z))
               HKsub Hj1 Hldt HKdt Hrel Htau Hb1); [| | exact Hx].
      * intros y Hy. rewrite (Hb2 y Hy). apply Hagq. exact Hy.
      * rewrite Hb3. fold sq. rewrite Hnths. reflexivity.
    + intros i i' Hi Hi' Hne.
      rewrite HNj in Hi, Hi'.
      assert (Hq : (i / j < N)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
      assert (Hs : (i mod j < j)%nat) by (apply Nat.mod_upper_bound; exact Hj0).
      assert (Hq' : (i' / j < N)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
      assert (Hs' : (i' mod j < j)%nat) by (apply Nat.mod_upper_bound; exact Hj0).
      assert (Hieq : i = (i / j * j + i mod j)%nat)
        by (rewrite Nat.mul_comm; apply Nat.div_mod_eq).
      assert (Hieq' : i' = (i' / j * j + i' mod j)%nat)
        by (rewrite Nat.mul_comm; apply Nat.div_mod_eq).
      destruct (Hblock (i / j)%nat (i mod j)%nat Hq Hs) as [Ha1 [Ha2 Ha3]].
      destruct (Hblock (i' / j)%nat (i' mod j)%nat Hq' Hs') as [Hb1 [Hb2 Hb3]].
      destruct (Nat.eq_dec (i / j) (i' / j)) as [Eq | Neq].
      * assert (Hsne : i mod j <> i' mod j) by (intro E; apply Hne; lia).
        exists r.
        split; [apply (CPolyF_r_mem K r j dt HKsub Hj1 Hldt HKdt Hrel) |].
        rewrite Hieq, Hieq', Ha3, Hb3, Eq.
        set (sq := nth (i' / j)%nat sigmas (fun z => z)) in *.
        assert (Hndt : NoDup (tgt sq)) by (unfold tgt; apply NoDup_filter; exact Hnd).
        intro E.
        apply Hsne.
        apply (proj1 (NoDup_nth (tgt sq) C0) Hndt);
          [unfold sq; rewrite (Htlen (i' / j)%nat Hq'); exact Hs
          | unfold sq; rewrite (Htlen (i' / j)%nat Hq'); exact Hs'
          | exact E].
      * destruct (Hdist (i / j)%nat (i' / j)%nat Hq Hq' Neq) as [x [HxK Hxne]].
        exists x.
        split; [apply (CPolyF_contains K r j dt HKsub Hj1 Hldt HKdt Hrel x HxK) |].
        rewrite Hieq, Hieq'.
        rewrite (Ha2 x HxK), (Hb2 x HxK).
        exact Hxne.
Qed.

(** THE CHAIN EMBEDDING COUNT: the identity-embedding instance of the enumeration over nu. *)
Theorem RootChain_embeddings :
  forall (K0 : C -> Prop) (rho : list C) (Fcf : list C) (lead : C),
  is_Csubfield K0 -> NoDup rho -> lead <> C0 ->
  (forall z, cpeval Fcf z = (lead * prod_linear rho z)%C) ->
  Forall K0 Fcf -> length Fcf = Datatypes.S (length rho) ->
  forall rs js K, RootChain K0 rho rs js K ->
  exists sigmas : list (C -> C),
    length sigmas = prodl js /\
    (forall i, (i < prodl js)%nat ->
       CCembeds K (nth i sigmas (fun z => z)) /\
       (forall x, K0 x -> nth i sigmas (fun z => z) x = x)) /\
    (forall tau, CCembeds K tau -> (forall x, K0 x -> tau x = x) ->
       exists i, (i < prodl js)%nat /\
         (forall x, K x -> tau x = nth i sigmas (fun z => z) x)) /\
    (forall i i', (i < prodl js)%nat -> (i' < prodl js)%nat -> i <> i' ->
       exists x, K x /\
         nth i sigmas (fun z => z) x <> nth i' sigmas (fun z => z) x).
Proof.
  intros K0 rho Fcf lead HK0 Hnd Hlead Hsplit HKF0 HlF rs js K Hch.
  apply (RootChain_embeddings_over K0 rho Fcf lead (fun z => z) HK0 Hnd Hlead
           Hsplit HKF0 HlF (CCembeds_id K0)
           ltac:(apply Forall_forall; intros c _; reflexivity)
           rs js K Hch).
Qed.

(* complexification of a real subfield through RtoC, with tower inclusion and step relations transported. *)

Definition CB (F : R -> Prop) (z : C) : Prop := exists x : R, F x /\ z = RtoC x.

Lemma CB_subfield : forall F : R -> Prop, is_subfield F -> is_Csubfield (CB F).
Proof.
  intros F HF.
  repeat split.
  - exists 0. split; [apply (subfield_0 F HF) | reflexivity].
  - exists 1. split; [apply (subfield_1 F HF) | reflexivity].
  - intros x y [a [Ha Hxa]] [b [Hb Hyb]].
    exists (a + b).
    split; [apply (subfield_add F a b HF Ha Hb) |].
    rewrite Hxa, Hyb. symmetry. apply RtoC_add.
  - intros x y [a [Ha Hxa]] [b [Hb Hyb]].
    exists (a - b).
    split; [apply (subfield_sub F a b HF Ha Hb) |].
    rewrite Hxa, Hyb. symmetry. apply RtoC_sub_c.
  - intros x y [a [Ha Hxa]] [b [Hb Hyb]].
    exists (a * b).
    split; [apply (subfield_mul F a b HF Ha Hb) |].
    rewrite Hxa, Hyb. symmetry. apply RtoC_mul.
  - intros x [a [Ha Hxa]] Hne.
    assert (Hane : a <> 0).
    { intro E. apply Hne. rewrite Hxa, E. reflexivity. }
    exists (/ a).
    split; [apply (subfield_inv F a HF Ha Hane) |].
    rewrite Hxa. symmetry. apply RtoC_inv_c. exact Hane.
Qed.

Lemma CB_mono : forall (F G : R -> Prop),
  (forall x, F x -> G x) -> forall z, CB F z -> CB G z.
Proof.
  intros F G Hincl z [x [Hx Hzx]].
  exists x. split; [apply Hincl; exact Hx | exact Hzx].
Qed.

Lemma CQ_in_CB : forall (F : R -> Prop),
  (forall x, is_rational x -> F x) -> forall z, CQ z -> CB F z.
Proof.
  intros F Hincl z [x [Hx Hzx]].
  exists x. split; [apply Hincl; exact Hx | exact Hzx].
Qed.

(** A real monic relation transports to a CB-relation on the complex lift. *)
Lemma real_relation_to_CB :
  forall (F : R -> Prop) (beta : R) (d : nat) (c : nat -> R),
  (forall i, (i < d)%nat -> F (c i)) ->
  fsum d (fun i => c i * beta ^ i) + beta ^ d = 0 ->
  let dt := map (fun i => RtoC (c i)) (seq 0 d) in
  length dt = d /\ Forall (CB F) dt /\
  (cpeval dt (RtoC beta) + Cpow (RtoC beta) d)%C = C0.
Proof.
  intros F beta d c Hc Hrel dt.
  assert (Hlen : length dt = d)
    by (unfold dt; rewrite length_map, length_seq; reflexivity).
  split; [exact Hlen | split].
  - unfold dt. apply Forall_map_intro. intros i Hi.
    apply in_seq in Hi.
    exists (c i). split; [apply Hc; lia | reflexivity].
  - assert (Hbridge : forall (l : list R) (z : C), cpeval (map RtoC l) z = CevalR l z).
    { intros l z. induction l as [|a l IHl]; cbn [map cpeval CevalR].
      - reflexivity.
      - rewrite IHl. reflexivity. }
    assert (Hev : cpeval dt (RtoC beta) = RtoC (fsum d (fun i => c i * beta ^ i))).
    { unfold dt.
      assert (Hmm : map (fun i => RtoC (c i)) (seq 0 d)
                    = map RtoC (map c (seq 0 d)))
        by (rewrite map_map; reflexivity).
      rewrite Hmm, Hbridge, CevalR_RtoC, pevalR_map_seq.
      reflexivity. }
    rewrite Hev, Cpow_RtoC, <- RtoC_add, Hrel.
    reflexivity.
Qed.

(* chain containment in a larger field, and the intrinsic count transported across pointwise-equal fields. *)

Lemma RootChain_contained :
  forall (K0 : C -> Prop) (rho : list C) (rs : list C) (js : list nat)
         (K M : C -> Prop),
  is_Csubfield K0 -> RootChain K0 rho rs js K ->
  is_Csubfield M ->
  (forall x, K0 x -> M x) ->
  (forall r, In r rs -> M r) ->
  forall x, K x -> M x.
Proof.
  intros K0 rho rs js K M HK0 Hch HM Hbase Hroots.
  induction Hch as [| rs js K r j dt Hch IH Hin Hj1 Hjn Hldt HKdt Hrel Hindep];
    intros x Hx.
  - apply Hbase. exact Hx.
  - assert (IH' : forall y, K y -> M y).
    { apply IH. intros r0 Hr0. apply Hroots. apply in_or_app. left. exact Hr0. }
    destruct Hx as [cs [Hlcs [HKcs Hxe]]].
    assert (HMr : M r).
    { apply Hroots. apply in_or_app. right. left. reflexivity. }
    assert (HMcs : Forall M cs).
    { apply Forall_forall. intros z Hz.
      apply IH'. exact (proj1 (Forall_forall K cs) HKcs z Hz). }
    rewrite Hxe.
    clear Hxe Hlcs HKcs.
    induction HMcs as [|a cs' Ha HMcs' IHcs]; cbn [cpeval].
    + apply (Csubfield_0 M HM).
    + apply Csubfield_add; [exact HM | exact Ha |].
      apply Csubfield_mul; [exact HM | exact HMr | exact IHcs].
Qed.

(** The intrinsic embedding count transports across pointwise-equal fields and bases. *)
Lemma embedding_count_transport :
  forall (K0 K0' K K' : C -> Prop) (L1 L2 : list (C -> C)),
  (forall x, K0 x <-> K0' x) -> (forall x, K x <-> K' x) ->
  (forall i, (i < length L1)%nat ->
     CCembeds K (nth i L1 (fun z => z)) /\
     (forall x, K0 x -> nth i L1 (fun z => z) x = x)) ->
  (forall i i', (i < length L1)%nat -> (i' < length L1)%nat -> i <> i' ->
     exists x, K x /\
       nth i L1 (fun z => z) x <> nth i' L1 (fun z => z) x) ->
  (forall tau, CCembeds K' tau -> (forall x, K0' x -> tau x = x) ->
     exists k, (k < length L2)%nat /\
       (forall x, K' x -> tau x = nth k L2 (fun z => z) x)) ->
  (length L1 <= length L2)%nat.
Proof.
  intros K0 K0' K K' L1 L2 Hbiff Hkiff Hwf Hdist Hcomp.
  apply (embedding_list_le K0 K L1 L2 Hwf Hdist).
  intros tau Htau Hfix.
  assert (Htau' : CCembeds K' tau)
    by (apply (CCembeds_ext_pred K K' tau Hkiff); exact Htau).
  assert (Hfix' : forall x, K0' x -> tau x = x)
    by (intros x Hx; apply Hfix; apply Hbiff; exact Hx).
  destruct (Hcomp tau Htau' Hfix') as [k [Hk Hagr]].
  exists k.
  split; [exact Hk |].
  intros x Hx. apply Hagr. apply Hkiff. exact Hx.
Qed.

(* monic positive-degree divisors of split polynomials vanish at a split point, by cancel-and-peel. *)

Lemma cancel_linear_factor :
  forall (p q : list C) (w : C),
  (forall z, (cpeval_lf p z * (z - w))%C = (cpeval_lf q z * (z - w))%C) ->
  forall z, cpeval_lf p z = cpeval_lf q z.
Proof.
  intros p q w Hid z.
  set (e := cpadd (rev p) (cpscale (Copp C1) (rev q))).
  assert (Hediff : forall y, cpeval e y = (cpeval_lf p y - cpeval_lf q y)%C).
  { intro y. unfold e.
    rewrite cpeval_cpadd, cpeval_cpscale, <- !cpeval_lf_rev_c. ring. }
  assert (Hevanish : forall y, y <> w -> cpeval e y = C0).
  { intros y Hy.
    pose proof (Hid y) as Hidy.
    assert (Hne : (y - w)%C <> C0).
    { intro E. apply Hy.
      transitivity ((y - w) + w)%C; [ring |]. rewrite E. ring. }
    rewrite Hediff.
    assert (Hd : ((cpeval_lf p y - cpeval_lf q y) * (y - w))%C = C0).
    { transitivity ((cpeval_lf p y * (y - w)) - (cpeval_lf q y * (y - w)))%C;
        [ring |].
      rewrite Hidy. ring. }
    destruct (Cmul_integral _ _ Hd) as [E | E]; [exact E | contradiction]. }
  assert (Hzero : Forall (fun c => c = C0) (rev e)).
  { destruct (classic (exists m : nat, w = RtoC (INR m))) as [[m Hm] | Hno].
    - apply (cp_vanish_zero_gen (length (rev e)) (rev e) (Datatypes.S m) eq_refl).
      intro k.
      rewrite cpeval_lf_rev_c, rev_involutive.
      apply Hevanish.
      intro E. rewrite Hm in E.
      apply RtoC_INR_inj in E. lia.
    - apply (cp_vanish_zero_gen (length (rev e)) (rev e) 0%nat eq_refl).
      intro k.
      rewrite cpeval_lf_rev_c, rev_involutive.
      apply Hevanish.
      intro E. apply Hno. exists (k + 0)%nat. symmetry. exact E. }
  assert (He0 : cpeval e z = C0).
  { rewrite <- (rev_involutive e).
    rewrite <- cpeval_lf_rev_c.
    apply Forall_zero_cpeval. exact Hzero. }
  rewrite Hediff in He0.
  transitivity ((cpeval_lf p z - cpeval_lf q z) + cpeval_lf q z)%C; [| rewrite He0]; ring.
Qed.

(** The top convolution coefficient over C. *)
Lemma cpmul_top : forall (p q : list C) (m n : nat),
  length p = Datatypes.S m -> length q = Datatypes.S n ->
  nth (m + n) (cpmul p q) C0 = (nth m p C0 * nth n q C0)%C.
Proof.
  induction p as [|a p IH]; intros q m n Hlp Hlq.
  - cbn [length] in Hlp. lia.
  - cbn [length] in Hlp.
    rewrite cpmul_cons, nth_cpadd, nth_cpscale.
    destruct m as [|m'].
    + cbn [Nat.add nth].
      assert (Hp0 : p = nil) by (apply length_zero_iff_nil; lia).
      subst p.
      cbn [cpmul].
      destruct n as [|n']; cbn [nth].
      * ring.
      * replace (match n' with O | _ => C0 end) with C0
          by (destruct n'; reflexivity).
        ring.
    + cbn [nth].
      assert (Hover : nth (Datatypes.S m' + n) q C0 = C0)
        by (apply nth_overflow; lia).
      rewrite Hover.
      replace (Datatypes.S m' + n)%nat with (Datatypes.S (m' + n))%nat by lia.
      cbn [nth].
      rewrite (IH q m' n ltac:(lia) Hlq).
      ring.
Qed.

(** A monic list of positive degree cannot divide the constant one. *)
Lemma monic_no_unit_divisor : forall (A B : list C),
  hd C0 A = C1 -> (2 <= length A)%nat ->
  (forall z, (cpeval_lf A z * cpeval_lf B z)%C = C1) ->
  False.
Proof.
  intros A B HmonA HlenA Hunit.
  assert (Hunit' : forall z, (cpeval_lf A z * cpeval_lf (clnorm B) z)%C = C1)
    by (intro z; rewrite clnorm_eval; apply Hunit).
  destruct (clnorm_head B) as [Hnil | Hhd].
  - pose proof (Hunit' C0) as H0.
    rewrite Hnil in H0.
    cbn [cpeval_lf] in H0.
    apply C1_neq_C0.
    rewrite <- H0. ring.
  - destruct (clnorm B) as [|b N'] eqn:EN; [cbn [hd] in Hhd; congruence |].
    cbn [hd] in Hhd.
    set (Acf := rev A). set (Bcf := rev (b :: N')).
    assert (HlAcf : length Acf = length A) by (unfold Acf; apply length_rev).
    assert (HlBcf : length Bcf = Datatypes.S (length N'))
      by (unfold Bcf; rewrite length_rev; reflexivity).
    assert (Hprod : forall z, (cpeval Acf z * cpeval Bcf z)%C = C1).
    { intro z. unfold Acf, Bcf.
      rewrite <- !cpeval_lf_rev_c.
      apply Hunit'. }
    assert (Hlm : length Acf = Datatypes.S (length A - 1))
      by (rewrite HlAcf; lia).
    assert (Hcoeff : cpmul Acf Bcf
                     = C1 :: repeat C0 (length (cpmul Acf Bcf) - 1)).
    { apply cpeval_ext_coeffs.
      - cbn [length]. rewrite repeat_length.
        rewrite cpmul_length; [lia | rewrite Hlm; lia | rewrite HlBcf; lia].
      - intro z.
        rewrite cpeval_cpmul, Hprod.
        cbn [cpeval].
        rewrite cpeval_repeatC0. ring. }
    assert (Htop : nth ((length A - 1) + length N') (cpmul Acf Bcf) C0
                   = (nth (length A - 1) Acf C0 * nth (length N') Bcf C0)%C).
    { apply cpmul_top; [exact Hlm | exact HlBcf]. }
    assert (HAtop : nth (length A - 1) Acf C0 = C1).
    { unfold Acf.
      destruct A as [|a A']; [cbn [length] in HlenA; lia |].
      cbn [hd] in HmonA. subst a.
      cbn [rev length].
      rewrite app_nth2 by (rewrite length_rev; cbn [length]; lia).
      rewrite length_rev.
      replace (Datatypes.S (length A') - 1 - length A')%nat with 0%nat by lia.
      reflexivity. }
    assert (HBtop : nth (length N') Bcf C0 = b).
    { unfold Bcf. cbn [rev].
      rewrite app_nth2 by (rewrite length_rev; lia).
      rewrite length_rev, Nat.sub_diag.
      reflexivity. }
    rewrite HAtop, HBtop in Htop.
    assert (Hzero : nth ((length A - 1) + length N') (cpmul Acf Bcf) C0 = C0).
    { rewrite Hcoeff.
      destruct ((length A - 1) + length N')%nat as [|k] eqn:Ek; [lia |].
      cbn [nth].
      destruct (le_lt_dec (length (cpmul Acf Bcf) - 1) k) as [Hge | Hlt].
      - apply nth_overflow. rewrite repeat_length. exact Hge.
      - apply nth_repeat. }
    rewrite Hzero in Htop.
    apply Hhd.
    transitivity ((C1 * b)%C); [ring |].
    rewrite <- Htop. reflexivity.
Qed.

(** The linear-product list realizing prod_linear as an evaluation. *)
Fixpoint plin_list (ws : list C) : list C :=
  match ws with
  | nil => C1 :: nil
  | w :: ws' => cpmul_lf (C1 :: Copp w :: nil) (plin_list ws')
  end.

Lemma plin_list_eval : forall ws z, cpeval_lf (plin_list ws) z = prod_linear ws z.
Proof.
  induction ws as [|w ws IH]; intro z; cbn [plin_list prod_linear].
  - cbn [cpeval_lf length Cpow]. ring.
  - rewrite cpmul_lf_eval, IH.
    cbn [cpeval_lf length Cpow]. ring.
Qed.

(** THE SPLIT-DIVISOR ROOT: a monic positive-degree divisor of a product of linear factors vanishes at one of the factor points. *)
Lemma split_divisor_has_root :
  forall (ws : list C) (A B : list C),
  hd C0 A = C1 -> (2 <= length A)%nat ->
  (forall z, prod_linear ws z = (cpeval_lf A z * cpeval_lf B z)%C) ->
  exists w, In w ws /\ cpeval_lf A w = C0.
Proof.
  induction ws as [|w ws IH]; intros A B HmonA HlenA Hsplit.
  - exfalso.
    apply (monic_no_unit_divisor A B HmonA HlenA).
    intro z. rewrite <- (Hsplit z). reflexivity.
  - destruct (Ceq_dec (cpeval_lf A w) C0) as [HAw | HAw].
    + exists w. split; [left; reflexivity | exact HAw].
    + assert (HBw : cpeval_lf B w = C0).
      { pose proof (Hsplit w) as Hw.
        cbn [prod_linear] in Hw.
        replace ((w - w)%C) with C0 in Hw by ring.
        assert (Hz : (cpeval_lf A w * cpeval_lf B w)%C = C0)
          by (rewrite <- Hw; ring).
        destruct (Cmul_integral _ _ Hz) as [E | E]; [contradiction | exact E]. }
      set (Bq := fst (cpdiv_lf (length B) B (Copp w :: nil))).
      assert (HBfac : forall z, cpeval_lf B z = (cpeval_lf Bq z * (z - w))%C)
        by (intro z; apply (cp_root_factor B w HBw z)).
      assert (Hcancel : forall z, prod_linear ws z
                        = (cpeval_lf A z * cpeval_lf Bq z)%C).
      { intro z.
        assert (Hid : forall y,
          (cpeval_lf (plin_list ws) y * (y - w))%C
          = (cpeval_lf (cpmul_lf A Bq) y * (y - w))%C).
        { intro y.
          rewrite plin_list_eval, cpmul_lf_eval.
          pose proof (Hsplit y) as Hy.
          cbn [prod_linear] in Hy.
          rewrite (HBfac y) in Hy.
          transitivity ((y - w) * prod_linear ws y)%C; [ring |].
          rewrite Hy. ring. }
        pose proof (cancel_linear_factor (plin_list ws) (cpmul_lf A Bq) w Hid z) as Hc.
        rewrite plin_list_eval, cpmul_lf_eval in Hc.
        exact Hc. }
      destruct (IH A Bq HmonA HlenA Hcancel) as [w' [Hw' HAw']].
      exists w'. split; [right; exact Hw' | exact HAw'].
Qed.

(* real monic step polynomials of degree 2, 3, 5 split over C into prod_linear form, by the quadratic, Cardano, and odd-root splitting formulas. *)

Lemma Cpow_2_expand : forall z, Cpow z 2 = (z * z)%C.
Proof. intro z. cbn [Cpow]. ring. Qed.

Lemma Cpow_3_expand : forall z, Cpow z 3 = (z * z * z)%C.
Proof. intro z. cbn [Cpow]. ring. Qed.

Lemma Cpow_5_expand : forall z, Cpow z 5 = (z * z * (z * z) * z)%C.
Proof. intro z. cbn [Cpow]. ring. Qed.

(** Degree-2 split. *)
Lemma monic_step_splits_2 : forall b c : C,
  exists ws : list C, length ws = 2%nat /\
  forall z, (cpeval (c :: b :: nil) z + Cpow z 2)%C = prod_linear ws z.
Proof.
  intros b c.
  destruct (Cquadratic_split b c) as [z1 [z2 Hq]].
  exists (z1 :: z2 :: nil).
  split; [reflexivity |].
  intro z.
  cbn [cpeval prod_linear].
  rewrite Cpow_2_expand.
  transitivity ((z * z + b * z + c)%C); [ring |].
  rewrite (Hq z). ring.
Qed.

(** Degree-3 split. *)
Lemma monic_step_splits_3 : forall b c d : C,
  exists ws : list C, length ws = 3%nat /\
  forall z, (cpeval (d :: c :: b :: nil) z + Cpow z 3)%C = prod_linear ws z.
Proof.
  intros b c d.
  destruct (Ccubic_split b c d) as [z1 [z2 [z3 Hq]]].
  exists (z1 :: z2 :: z3 :: nil).
  split; [reflexivity |].
  intro z.
  cbn [cpeval prod_linear].
  rewrite Cpow_3_expand.
  transitivity ((z * z * z + b * (z * z) + c * z + d)%C); [ring |].
  rewrite (Hq z). ring.
Qed.

(** Degree-5 split, real coefficients. *)
Lemma monic_step_splits_5 : forall a4 a3 a2 a1 a0 : R,
  exists ws : list C, length ws = 5%nat /\
  forall z, (cpeval (map RtoC (a0 :: a1 :: a2 :: a3 :: a4 :: nil)) z + Cpow z 5)%C
            = prod_linear ws z.
Proof.
  intros a4 a3 a2 a1 a0.
  destruct (Rquintic_split_C a4 a3 a2 a1 a0) as [rho [w1 [w2 [w3 [w4 Hq]]]]].
  exists (RtoC rho :: w1 :: w2 :: w3 :: w4 :: nil).
  split; [reflexivity |].
  intro z.
  cbn [map cpeval prod_linear].
  rewrite Cpow_5_expand.
  transitivity ((z * z * (z * z) * z + RtoC a4 * (z * z * (z * z))
                 + RtoC a3 * (z * z * z) + RtoC a2 * (z * z)
                 + RtoC a1 * z + RtoC a0)%C); [ring |].
  rewrite (Hq z). ring.
Qed.

(** THE STEP SPLIT: every monic real relation of degree 2, 3, or 5 splits into linear factors over C. *)
Lemma monic_real_step_splits : forall (d : nat) (rt : list R),
  (d = 2 \/ d = 3 \/ d = 5)%nat -> length rt = d ->
  exists ws : list C, length ws = d /\
  forall z, (cpeval (map RtoC rt) z + Cpow z d)%C = prod_linear ws z.
Proof.
  intros d rt Hd Hlen.
  destruct Hd as [-> | [-> | ->]].
  - destruct rt as [|c0 [|c1 [|? ?]]]; try (cbn [length] in Hlen; lia).
    destruct (monic_step_splits_2 (RtoC c1) (RtoC c0)) as [ws [Hlw Hws]].
    exists ws. split; [exact Hlw |].
    intro z. cbn [map]. apply Hws.
  - destruct rt as [|c0 [|c1 [|c2 [|? ?]]]]; try (cbn [length] in Hlen; lia).
    destruct (monic_step_splits_3 (RtoC c2) (RtoC c1) (RtoC c0)) as [ws [Hlw Hws]].
    exists ws. split; [exact Hlw |].
    intro z. cbn [map]. apply Hws.
  - destruct rt as [|c0 [|c1 [|c2 [|c3 [|c4 [|? ?]]]]]];
      try (cbn [length] in Hlen; lia).
    destruct (monic_step_splits_5 c4 c3 c2 c1 c0) as [ws [Hlw Hws]].
    exists ws. split; [exact Hlw |].
    intro z. apply Hws.
Qed.

(* the minimal relation of a step element divides the split step polynomial, so every embedding fixing the step coefficients extends to the adjunction. *)

Lemma CCembeds_extend_along_element :
  forall (K : C -> Prop) (beta : C) (d : nat) (dtK : list C) (sigma : C -> C),
  is_Csubfield K ->
  (1 <= d)%nat -> length dtK = d -> Forall K dtK ->
  (cpeval dtK beta + Cpow beta d)%C = C0 ->
  Cindep_pows K beta d ->
  CCembeds K sigma ->
  (exists ws : list C, (1 <= length ws)%nat /\
     forall z, (CCevalMap sigma dtK z + Cpow z d)%C = prod_linear ws z) ->
  exists sigma' : C -> C,
    CCembeds (CPolyF K d beta) sigma' /\
    (forall x, K x -> sigma' x = sigma x).
Proof.
  intros K beta d dtK sigma HK Hd Hldt HKdt Hrel Hindep Hemb [ws [Hlws Hsplit]].
  assert (Hroot : exists w, (CCevalMap sigma dtK w + Cpow w d)%C = C0).
  { set (A := C1 :: rev (map sigma dtK)).
    assert (HlA : length A = Datatypes.S d)
      by (unfold A; cbn [length]; rewrite length_rev, length_map, Hldt; lia).
    assert (HevA : forall z, cpeval_lf A z = (CCevalMap sigma dtK z + Cpow z d)%C).
    { intro z. unfold A. cbn [cpeval_lf].
      rewrite length_rev, length_map, Hldt.
      rewrite cpeval_lf_rev_c, rev_involutive, <- CCevalMap_cpeval_map.
      ring. }
    destruct (split_divisor_has_root ws A (C1 :: nil)
                ltac:(reflexivity) ltac:(rewrite HlA; lia)) as [w [Hw HAw]].
    - intro z.
      rewrite HevA.
      cbn [cpeval_lf length Cpow].
      rewrite (Hsplit z). ring.
    - exists w. rewrite <- HevA. exact HAw. }
  destruct Hroot as [w Hw].
  destruct (Nat.eq_dec d 1) as [-> | Hd2].
  - destruct (CCembeds_extend_one K beta dtK sigma w HK Hldt HKdt Hrel Hemb Hw)
      as [Hemb1 _].
    exists sigma.
    split; [exact Hemb1 | intros x _; reflexivity].
  - destruct (CCembeds_extend_step K beta d dtK sigma w HK ltac:(lia) Hldt HKdt
                Hrel Hindep Hemb Hw) as [sigma' [Hemb' [Hagr' _]]].
    exists sigma'.
    split; [exact Hemb' | exact Hagr'].
Qed.

(* THE DESCENT -- adjoining one real tower-step element divides the embedding count by at most the step degree, by classifying extensions over base-restriction classes. *)

Lemma nat_list_bounded_NoDup_length :
  forall (l : list nat) (bound : nat),
  NoDup l -> (forall k, In k l -> (k < bound)%nat) -> (length l <= bound)%nat.
Proof.
  intros l bound Hnd Hb.
  assert (Hincl : incl l (seq 0 bound)).
  { intros k Hk. apply in_seq. split; [lia | cbn [Nat.add]].
    replace (0 + bound)%nat with bound by lia.
    apply Hb. exact Hk. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hle.
  rewrite length_seq in Hle. exact Hle.
Qed.

(** The base adjunction embeds in the chain adjunction. *)
Lemma CPolyF_base_mono :
  forall (B K : C -> Prop) (beta : C) (db jb : nat) (dtK : list C),
  is_Csubfield K -> (forall x, B x -> K x) ->
  (1 <= jb)%nat -> length dtK = jb -> Forall K dtK ->
  (cpeval dtK beta + Cpow beta jb)%C = C0 ->
  forall x, CPolyF B db beta x -> CPolyF K jb beta x.
Proof.
  intros B K beta db jb dtK HK Hincl Hjb HldtK HKdtK HrelK x [cs [Hlcs [HBcs Hxe]]].
  rewrite Hxe.
  apply (CPolyF_reduce K beta jb dtK HK Hjb HldtK HKdtK HrelK).
  apply Forall_forall. intros c Hc.
  apply Hincl. exact (proj1 (Forall_forall B cs) HBcs c Hc).
Qed.

(** First matching index in a list of candidate indices. *)
Fixpoint find_left (test : nat -> bool) (l : list nat) (dflt : nat) : nat :=
  match l with
  | nil => dflt
  | j :: tl => if test j then j else find_left test tl dflt
  end.

Lemma find_left_spec : forall test l dflt,
  (exists j, In j l /\ test j = true) ->
  In (find_left test l dflt) l /\ test (find_left test l dflt) = true.
Proof.
  intros test l dflt. induction l as [|j tl IH]; intros [j0 [Hin Ht]].
  - contradiction.
  - cbn [find_left].
    destruct (test j) eqn:Etj.
    + split; [left; reflexivity | exact Etj].
    + destruct Hin as [-> | Hin]; [congruence |].
      destruct (IH (ex_intro _ j0 (conj Hin Ht))) as [H1 H2].
      split; [right; exact H1 | exact H2].
Qed.

(** THE DESCENT THEOREM: adjoining an element of base-relation degree db divides the embedding count by at most db. *)
Theorem descent_step :
  forall (B K : C -> Prop) (beta : C)
         (db : nat) (dtB : list C) (jb : nat) (dtK : list C)
         (sigmas : list (C -> C)) (N N' : nat),
  is_Csubfield B -> is_Csubfield K ->
  (forall x, B x -> K x) ->
  (1 <= db)%nat -> length dtB = db -> Forall B dtB ->
  (cpeval dtB beta + Cpow beta db)%C = C0 ->
  (1 <= jb)%nat -> length dtK = jb -> Forall K dtK ->
  (cpeval dtK beta + Cpow beta jb)%C = C0 ->
  Cindep_pows K beta jb ->
  (forall sigma, CCembeds K sigma -> (forall x, B x -> sigma x = x) ->
     exists ws : list C, (1 <= length ws)%nat /\
       forall z, (CCevalMap sigma dtK z + Cpow z jb)%C = prod_linear ws z) ->
  length sigmas = N ->
  (forall i, (i < N)%nat ->
     CCembeds K (nth i sigmas (fun z => z)) /\
     (forall x, B x -> nth i sigmas (fun z => z) x = x)) ->
  (forall i i', (i < N)%nat -> (i' < N)%nat -> i <> i' ->
     exists x, K x /\
       nth i sigmas (fun z => z) x <> nth i' sigmas (fun z => z) x) ->
  (forall nu, CCembeds (CPolyF B db beta) nu ->
     (forall x, B x -> nu x = x) ->
     exists exts : list (C -> C), length exts = N' /\
       forall tau, CCembeds (CPolyF K jb beta) tau ->
         (forall x, CPolyF B db beta x -> tau x = nu x) ->
         exists k, (k < N')%nat /\
           forall x, CPolyF K jb beta x -> tau x = nth k exts (fun z => z) x) ->
  (N <= db * N')%nat.
Proof.
  intros B K beta db dtB jb dtK sigmas N N'
         HB HK Hincl Hdb HldtB HBdtB HrelB Hjb HldtK HKdtK HrelK Hindep
         Hsplitcert Hlsig Hwf Hdist Hfibers.
  set (M := CPolyF K jb beta) in *.
  assert (HMsub : is_Csubfield M)
    by (apply (CPolyF_Csubfield K beta jb dtK HK Hjb HldtK HKdtK HrelK)).
  (* choose one extension per index, materialized as a list by induction *)
  assert (Hextlist : forall n, (n <= N)%nat ->
    exists tofl : list (C -> C), length tofl = n /\
      forall i, (i < n)%nat ->
        CCembeds M (nth i tofl (fun z => z)) /\
        (forall x, K x -> nth i tofl (fun z => z) x
                          = nth i sigmas (fun z => z) x)).
  { intro n. induction n as [|n IHn]; intro Hn.
    - exists nil. split; [reflexivity | intros i Hi; lia].
    - destruct IHn as [tofl [Hltofl Htofl]]; [lia |].
      destruct (Hwf n ltac:(lia)) as [Hembn Hfixn].
      destruct (Hsplitcert (nth n sigmas (fun z => z)) Hembn Hfixn)
        as [ws [Hlws Hws]].
      destruct (CCembeds_extend_along_element K beta jb dtK
                  (nth n sigmas (fun z => z)) HK Hjb HldtK HKdtK HrelK Hindep
                  Hembn (ex_intro _ ws (conj Hlws Hws)))
        as [taun [Htaun Hagrn]].
      exists (tofl ++ taun :: nil).
      split; [rewrite length_app, Hltofl; cbn [length]; lia |].
      intros i Hi.
      destruct (Nat.eq_dec i n) as [-> | Hne].
      + rewrite app_nth2 by lia.
        rewrite Hltofl, Nat.sub_diag. cbn [nth].
        split; [exact Htaun | exact Hagrn].
      + rewrite app_nth1 by lia.
        apply Htofl. lia. }
  destruct (Hextlist N (Nat.le_refl _)) as [tofl [Hltofl Htofl]].
  set (tof := fun i => nth i tofl (fun z => z)) in *.
  assert (Htofp : forall i, (i < N)%nat ->
    CCembeds M (tof i) /\
    (forall x, K x -> tof i x = nth i sigmas (fun z => z) x))
    by (intros i Hi; exact (Htofl i Hi)).
  (* value at beta roots the B-relation *)
  assert (HbetaM : M beta)
    by (apply (CPolyF_r_mem K beta jb dtK HK Hjb HldtK HKdtK HrelK)).
  assert (HdtBK : Forall K dtB).
  { apply Forall_forall. intros c Hc.
    apply Hincl. exact (proj1 (Forall_forall B dtB) HBdtB c Hc). }
  assert (Hfixtof : forall i, (i < N)%nat -> forall x, B x -> tof i x = x).
  { intros i Hi x Hx.
    rewrite (proj2 (Htofp i Hi) x (Hincl x Hx)).
    exact (proj2 (Hwf i Hi) x Hx). }
  assert (Hbval : forall i, (i < N)%nat ->
    (cpeval dtB (tof i beta) + Cpow (tof i beta) db)%C = C0).
  { intros i Hi.
    destruct (Htofp i Hi) as [Htaui _].
    pose proof Htaui as [Ht0 [Ht1 [Htadd Htmul]]].
    assert (Hcpev : M (cpeval dtB beta)).
    { apply (CPolyF_cpeval_at K beta jb dtK HK Hjb HldtK HKdtK HrelK);
        [exact HdtBK | exact HbetaM]. }
    assert (Hpowm : M (Cpow beta db))
      by (apply (CPolyF_pow K beta jb dtK HK Hjb HldtK HKdtK HrelK beta HbetaM)).
    assert (Htz : tof i ((cpeval dtB beta + Cpow beta db)%C) = C0)
      by (rewrite HrelB; exact Ht0).
    rewrite (Htadd _ _ Hcpev Hpowm) in Htz.
    rewrite (CCembeds_value_on_span K beta jb dtK (tof i) HK Hjb HldtK HKdtK
               HrelK Htaui dtB HdtBK) in Htz.
    rewrite (CCembeds_pow_val K beta jb dtK (tof i) HK Hjb HldtK HKdtK HrelK
               Htaui db) in Htz.
    rewrite <- Htz.
    f_equal.
    rewrite <- (CCevalMap_id dtB (tof i beta)).
    apply CCevalMap_ext_on.
    apply Forall_forall. intros c Hc.
    symmetry. apply (Hfixtof i Hi).
    exact (proj1 (Forall_forall B dtB) HBdtB c Hc). }
  (* agreement on the base adjunction within a class *)
  assert (Hspanval : forall i, (i < N)%nat ->
    forall cs, Forall B cs -> tof i (cpeval cs beta) = cpeval cs (tof i beta)).
  { intros i Hi cs HBcs.
    assert (HKcs : Forall K cs).
    { apply Forall_forall. intros c Hc.
      apply Hincl. exact (proj1 (Forall_forall B cs) HBcs c Hc). }
    rewrite (CCembeds_value_on_span K beta jb dtK (tof i) HK Hjb HldtK HKdtK
               HrelK (proj1 (Htofp i Hi)) cs HKcs).
    rewrite (CCevalMap_ext_on (tof i) (fun c => c) cs).
    - apply CCevalMap_id.
    - apply Forall_forall. intros c Hc.
      apply (Hfixtof i Hi).
      exact (proj1 (Forall_forall B cs) HBcs c Hc). }
  (* the distinct class values *)
  set (vals := nodup Ceq_dec (map (fun i => tof i beta) (seq 0 N))).
  assert (Hvals_in : forall i, (i < N)%nat -> In (tof i beta) vals).
  { intros i Hi. unfold vals. apply nodup_In.
    apply in_map_iff. exists i. split; [reflexivity |].
    apply in_seq. lia. }
  assert (Hvals_from : forall v, In v vals -> exists i, (i < N)%nat /\ tof i beta = v).
  { intros v Hv. unfold vals in Hv.
    apply nodup_In in Hv.
    apply in_map_iff in Hv. destruct Hv as [i [Hvi Hi]].
    apply in_seq in Hi. exists i. split; [lia | exact Hvi]. }
  assert (Hvals_len : (length vals <= db)%nat).
  { set (BrelL := C1 :: rev dtB).
    assert (HlBrel : length BrelL = Datatypes.S db)
      by (unfold BrelL; cbn [length]; rewrite length_rev, HldtB; lia).
    assert (HevBrel : forall z, cpeval_lf BrelL z = (cpeval dtB z + Cpow z db)%C).
    { intro z. unfold BrelL. cbn [cpeval_lf].
      rewrite length_rev, HldtB.
      rewrite cpeval_lf_rev_c, rev_involutive. ring. }
    assert (Hroots : forall v, In v vals -> cpeval_lf BrelL v = C0).
    { intros v Hv.
      destruct (Hvals_from v Hv) as [i [Hi Hvi]].
      rewrite HevBrel, <- Hvi.
      apply Hbval. exact Hi. }
    pose proof (cp_max_roots BrelL vals (NoDup_nodup Ceq_dec _) Hroots
                  ltac:(apply cmonic_lf_nonzero;
                        [reflexivity | rewrite HlBrel; lia])) as Hb.
    rewrite HlBrel in Hb. lia. }
  (* class representative: first index attaining a value *)
  set (repof := fun v =>
    find_left (fun j => if Ceq_dec (tof j beta) v then true else false)
      (seq 0 N) 0%nat).
  assert (Hrep : forall v, In v vals ->
    (repof v < N)%nat /\ tof (repof v) beta = v).
  { intros v Hv.
    destruct (Hvals_from v Hv) as [i [Hi Hvi]].
    destruct (find_left_spec
                (fun j => if Ceq_dec (tof j beta) v then true else false)
                (seq 0 N) 0%nat) as [Hin Htest].
    - exists i. split; [apply in_seq; lia |].
      destruct (Ceq_dec (tof i beta) v); [reflexivity | contradiction].
    - apply in_seq in Hin.
      unfold repof.
      split; [lia |].
      destruct (Ceq_dec (tof (find_left
        (fun j => if Ceq_dec (tof j beta) v then true else false)
        (seq 0 N) 0%nat) beta) v) as [E | E]; [exact E | congruence]. }
  (* the per-class extension lists, materialized over vals *)
  assert (Hclassexts : forall vl : list C,
    (forall v, In v vl -> In v vals) ->
    exists extss : list (list (C -> C)),
      length extss = length vl /\
      forall c, (c < length vl)%nat ->
        length (nth c extss nil) = N' /\
        forall tau, CCembeds M tau ->
          (forall x, CPolyF B db beta x -> tau x = tof (repof (nth c vl C0)) x) ->
          exists k, (k < N')%nat /\
            forall x, M x -> tau x = nth k (nth c extss nil) (fun z => z) x).
  { intro vl. induction vl as [|v vl IHvl]; intro Hvl.
    - exists nil. split; [reflexivity | intros c Hc; cbn [length] in Hc; lia].
    - destruct IHvl as [extss [Hlex Hex]];
        [intros v' Hv'; apply Hvl; right; exact Hv' |].
      assert (HvV : In v vals) by (apply Hvl; left; reflexivity).
      destruct (Hrep v HvV) as [Hrlt Hrval].
      assert (Hnuemb : CCembeds (CPolyF B db beta) (tof (repof v))).
      { apply (CCembeds_mono (CPolyF B db beta) M);
          [| exact (proj1 (Htofp (repof v) Hrlt))].
        intros x Hx.
        apply (CPolyF_base_mono B K beta db jb dtK HK Hincl Hjb HldtK HKdtK HrelK).
        exact Hx. }
      assert (Hnufix : forall x, B x -> tof (repof v) x = x)
        by (intros x Hx; apply (Hfixtof (repof v) Hrlt); exact Hx).
      destruct (Hfibers (tof (repof v)) Hnuemb Hnufix) as [exts [Hlext Hcompl]].
      exists (exts :: extss).
      split; [cbn [length]; rewrite Hlex; reflexivity |].
      intros c Hc.
      destruct c as [|c'].
      + cbn [nth].
        split; [exact Hlext |].
        intros tau Htau Hagr.
        apply (Hcompl tau Htau Hagr).
      + cbn [nth].
        cbn [length] in Hc.
        apply Hex. lia. }
  destruct (Hclassexts vals (fun v Hv => Hv)) as [extss [Hlextss Hextss]].
  (* handle N' = 0 *)
  destruct N as [|N0]; [lia |].
  set (NN := Datatypes.S N0) in *.
  assert (HN'pos : (1 <= N')%nat).
  { assert (H0N : (0 < NN)%nat) by lia.
    pose proof (Hvals_in 0%nat H0N) as Hv0.
    destruct (In_nth vals (tof 0%nat beta) C0 Hv0) as [c [Hc Hnthc]].
    destruct (Hextss c Hc) as [Hlen0 Hcompl0].
    assert (Hagr0 : forall x, CPolyF B db beta x ->
              tof 0%nat x = tof (repof (nth c vals C0)) x).
    { intros x [cs [Hlcs [HBcs Hxe]]].
      rewrite Hnthc.
      destruct (Hrep (tof 0%nat beta) Hv0) as [Hrlt Hrval].
      rewrite Hxe, (Hspanval 0%nat H0N cs HBcs),
        (Hspanval (repof (tof 0%nat beta)) Hrlt cs HBcs), Hrval.
      reflexivity. }
    destruct (Hcompl0 (tof 0%nat) (proj1 (Htofp 0%nat H0N)) Hagr0)
      as [k [Hk _]].
    lia. }
  (* build the code list *)
  assert (Hcodes : forall n, (n <= NN)%nat ->
    exists codes : list nat,
      length codes = n /\
      forall m, (m < n)%nat ->
        (nth m codes 0%nat < length vals * N')%nat /\
        exists c k, nth m codes 0%nat = (c * N' + k)%nat /\
          (c < length vals)%nat /\ (k < N')%nat /\
          nth c vals C0 = tof m beta /\
          (forall x, M x -> tof m x = nth k (nth c extss nil) (fun z => z) x)).
  { intro n. induction n as [|n IHn]; intro Hn.
    - exists nil. split; [reflexivity | intros m Hm; lia].
    - destruct IHn as [codes [Hlcodes Hcodes]]; [lia |].
      assert (HnN : (n < NN)%nat) by lia.
      pose proof (Hvals_in n HnN) as Hvn.
      destruct (In_nth vals (tof n beta) C0 Hvn) as [c [Hc Hnthc]].
      destruct (Hextss c Hc) as [Hlenc Hcomplc].
      assert (Hagrn : forall x, CPolyF B db beta x ->
                tof n x = tof (repof (nth c vals C0)) x).
      { intros x [cs [Hlcs [HBcs Hxe]]].
        rewrite Hnthc.
        destruct (Hrep (tof n beta) Hvn) as [Hrlt Hrval].
        rewrite Hxe, (Hspanval n HnN cs HBcs),
          (Hspanval (repof (tof n beta)) Hrlt cs HBcs), Hrval.
        reflexivity. }
      destruct (Hcomplc (tof n) (proj1 (Htofp n HnN)) Hagrn)
        as [k [Hk Hagrk]].
      exists (codes ++ (c * N' + k)%nat :: nil).
      split; [rewrite length_app, Hlcodes; cbn [length]; lia |].
      intros m Hm.
      destruct (Nat.eq_dec m n) as [-> | Hne].
      + rewrite app_nth2 by lia.
        rewrite Hlcodes, Nat.sub_diag. cbn [nth].
        split; [nia |].
        exists c, k.
        repeat split; [exact Hc | exact Hk | exact Hnthc | exact Hagrk].
      + rewrite app_nth1 by lia.
        apply Hcodes. lia. }
  destruct (Hcodes NN (Nat.le_refl _)) as [codes [Hlcodes Hcprop]].
  (* the codes are pairwise distinct *)
  assert (Hcodes_nd : NoDup codes).
  { apply (proj2 (NoDup_nth codes 0%nat)).
    intros a b Ha Hb Hab.
    rewrite Hlcodes in Ha, Hb.
    destruct (Nat.eq_dec a b) as [E | Hne]; [exact E | exfalso].
    destruct (Hcprop a Ha) as [_ [ca [ka [Hea [Hca [Hka [Hva Hagra]]]]]]].
    destruct (Hcprop b Hb) as [_ [cb [kb [Heb [Hcb [Hkb [Hvb Hagrb]]]]]]].
    rewrite Hea, Heb in Hab.
    assert (Hcc : ca = cb).
    { assert (Hd : ((ca * N' + ka) / N' = (cb * N' + kb) / N')%nat)
        by (rewrite Hab; reflexivity).
      rewrite !Nat.div_add_l in Hd by lia.
      rewrite !Nat.div_small in Hd by lia.
      lia. }
    assert (Hkk : ka = kb) by nia.
    subst cb kb.
    assert (Hsame : forall x, M x -> tof a x = tof b x).
    { intros x Hx.
      rewrite (Hagra x Hx), (Hagrb x Hx). reflexivity. }
    destruct (Hdist a b Ha Hb Hne) as [x [HxK Hxne]].
    apply Hxne.
    assert (HxM : M x)
      by (apply (CPolyF_contains K beta jb dtK HK Hjb HldtK HKdtK HrelK x HxK)).
    rewrite <- (proj2 (Htofp a Ha) x HxK).
    rewrite <- (proj2 (Htofp b Hb) x HxK).
    apply Hsame. exact HxM. }
  (* conclude by cardinality *)
  assert (Hbound : (NN <= length vals * N')%nat).
  { rewrite <- Hlcodes.
    apply nat_list_bounded_NoDup_length; [exact Hcodes_nd |].
    intros kk Hkk.
    destruct (In_nth codes kk 0%nat Hkk) as [m [Hm Hnthm]].
    rewrite Hlcodes in Hm.
    rewrite <- Hnthm.
    exact (proj1 (Hcprop m Hm)). }
  nia.
Qed.

(* the symmetric group on n letters without enumeration -- the permutation predicate as permutation of the letter interval, composition closure, identity laws, and the positional inverse; the six-letter layer below keeps its enumerated vm instance. *)

Definition pcomp (p q : list nat) : list nat := map (fun i => nth i p 0%nat) q.

Definition pidn (n : nat) : list nat := seq 0 n.

Definition is_permb (n : nat) (p : list nat) : bool :=
  (Nat.eqb (length p) n) &&
  forallb (fun i => existsb (fun j => Nat.eqb (nth j p 0%nat) i) (seq 0 n)) (seq 0 n).

Lemma nat_list_eta : forall (p : list nat),
  p = map (fun i => nth i p 0%nat) (seq 0 (length p)).
Proof.
  induction p as [|a p IH].
  - reflexivity.
  - cbn [length seq map nth].
    f_equal. rewrite <- seq_shift, map_map. cbn [nth]. exact IH.
Qed.

(** The permutation predicate is exactly permutation of the letter interval. *)
Lemma is_permb_perm : forall n p,
  is_permb n p = true <-> Permutation (seq 0 n) p.
Proof.
  intros n p. split.
  - intro H. apply andb_prop in H. destruct H as [Hlen Hsurj].
    apply Nat.eqb_eq in Hlen.
    apply NoDup_Permutation_bis.
    + apply seq_NoDup.
    + rewrite length_seq, Hlen. lia.
    + intros i Hi. apply in_seq in Hi.
      assert (Hrow : existsb (fun j => Nat.eqb (nth j p 0%nat) i) (seq 0 n) = true).
      { apply (proj1 (forallb_forall _ (seq 0 n)) Hsurj). apply in_seq. lia. }
      apply existsb_exists in Hrow.
      destruct Hrow as [j [Hj Hnth]].
      apply in_seq in Hj. apply Nat.eqb_eq in Hnth.
      rewrite <- Hnth. apply nth_In. lia.
  - intro H. apply andb_true_intro. split.
    + apply Nat.eqb_eq.
      rewrite <- (Permutation_length H), length_seq. reflexivity.
    + apply forallb_forall. intros i Hi.
      apply existsb_exists.
      assert (Hin : In i p) by (apply (Permutation_in _ H); exact Hi).
      destruct (In_nth p i 0%nat Hin) as [j [Hj Hnth]].
      exists j. split.
      * apply in_seq. rewrite <- (Permutation_length H), length_seq in Hj. lia.
      * apply Nat.eqb_eq. exact Hnth.
Qed.

Lemma is_permb_len : forall n p, is_permb n p = true -> length p = n.
Proof.
  intros n p H.
  rewrite <- (Permutation_length (proj1 (is_permb_perm n p) H)), length_seq.
  reflexivity.
Qed.

Lemma is_permb_NoDup : forall n p, is_permb n p = true -> NoDup p.
Proof.
  intros n p H.
  apply (Permutation_NoDup (proj1 (is_permb_perm n p) H)).
  apply seq_NoDup.
Qed.

Lemma is_permb_in : forall n p, is_permb n p = true -> forall a, In a p -> (a < n)%nat.
Proof.
  intros n p H a Ha.
  assert (Hin : In a (seq 0 n))
    by (apply (Permutation_in _ (Permutation_sym (proj1 (is_permb_perm n p) H))); exact Ha).
  apply in_seq in Hin. lia.
Qed.

Lemma is_permb_entry_lt : forall n p, is_permb n p = true ->
  forall j, (j < n)%nat -> (nth j p 0%nat < n)%nat.
Proof.
  intros n p H j Hj.
  apply (is_permb_in n p H).
  apply nth_In. rewrite (is_permb_len n p H). exact Hj.
Qed.

Lemma is_permb_inj : forall n p, is_permb n p = true ->
  forall i j, (i < n)%nat -> (j < n)%nat -> nth i p 0%nat = nth j p 0%nat -> i = j.
Proof.
  intros n p H i j Hi Hj He.
  apply (proj1 (NoDup_nth p 0%nat) (is_permb_NoDup n p H));
    rewrite ?(is_permb_len n p H); assumption.
Qed.

Lemma is_permb_preim : forall n p i, is_permb n p = true -> (i < n)%nat ->
  exists j, (j < n)%nat /\ nth j p 0%nat = i.
Proof.
  intros n p i H Hi.
  assert (Hin : In i p).
  { apply (Permutation_in _ (proj1 (is_permb_perm n p) H)). apply in_seq. lia. }
  destruct (In_nth p i 0%nat Hin) as [j [Hj Hnth]].
  exists j. split; [rewrite <- (is_permb_len n p H); exact Hj | exact Hnth].
Qed.

Lemma pidn_permb : forall n, is_permb n (pidn n) = true.
Proof. intro n. apply is_permb_perm. apply Permutation_refl. Qed.

(** Composition of permutations is a permutation. *)
Lemma pcomp_permb : forall n p q, is_permb n p = true -> is_permb n q = true ->
  is_permb n (pcomp p q) = true.
Proof.
  intros n p q Hp Hq.
  apply is_permb_perm.
  assert (Ep : p = map (fun i => nth i p 0%nat) (seq 0 n)).
  { rewrite <- (is_permb_len n p Hp) at 1. apply nat_list_eta. }
  unfold pcomp.
  apply Permutation_trans with (map (fun i => nth i p 0%nat) (seq 0 n)).
  - rewrite <- Ep. apply is_permb_perm. exact Hp.
  - apply Permutation_map. apply is_permb_perm. exact Hq.
Qed.

Lemma pcomp_len : forall p q, length (pcomp p q) = length q.
Proof. intros. unfold pcomp. apply length_map. Qed.

Lemma pcomp_nth : forall p q i, (i < length q)%nat ->
  nth i (pcomp p q) 0%nat = nth (nth i q 0%nat) p 0%nat.
Proof.
  intros p q i Hi. unfold pcomp.
  rewrite (nth_indep _ 0%nat (nth 0%nat p 0%nat))
    by (rewrite length_map; exact Hi).
  apply (map_nth (fun k => nth k p 0%nat) q 0%nat i).
Qed.

Lemma pcompn_assoc : forall n p q r,
  is_permb n p = true -> is_permb n q = true -> is_permb n r = true ->
  pcomp (pcomp p q) r = pcomp p (pcomp q r).
Proof.
  intros n p q r Hp Hq Hr.
  apply (nth_ext _ _ 0%nat 0%nat).
  - rewrite !pcomp_len. reflexivity.
  - intros i Hi.
    rewrite pcomp_len, (is_permb_len n r Hr) in Hi.
    rewrite (pcomp_nth (pcomp p q) r i)
      by (rewrite (is_permb_len n r Hr); exact Hi).
    rewrite (pcomp_nth p (pcomp q r) i)
      by (rewrite pcomp_len, (is_permb_len n r Hr); exact Hi).
    rewrite (pcomp_nth q r i)
      by (rewrite (is_permb_len n r Hr); exact Hi).
    rewrite (pcomp_nth p q (nth i r 0%nat))
      by (rewrite (is_permb_len n q Hq);
          apply (is_permb_entry_lt n r Hr); exact Hi).
    reflexivity.
Qed.

Lemma pcompn_id_right : forall n p, is_permb n p = true -> pcomp p (pidn n) = p.
Proof.
  intros n p Hp. unfold pcomp, pidn.
  rewrite <- (is_permb_len n p Hp).
  symmetry. apply nat_list_eta.
Qed.

Lemma pcompn_id_left : forall n p, is_permb n p = true -> pcomp (pidn n) p = p.
Proof.
  intros n p Hp.
  apply (nth_ext _ _ 0%nat 0%nat).
  - apply pcomp_len.
  - intros i Hi. rewrite pcomp_len in Hi.
    rewrite (pcomp_nth (pidn n) p i) by exact Hi.
    unfold pidn.
    rewrite seq_nth
      by (apply (is_permb_entry_lt n p Hp);
          rewrite <- (is_permb_len n p Hp); exact Hi).
    reflexivity.
Qed.

(** The positional inverse. *)
Definition pinvn (n : nat) (p : list nat) : list nat :=
  map (fun i => find_left (fun j => Nat.eqb (nth j p 0%nat) i) (seq 0 n) 0%nat)
    (seq 0 n).

Lemma pinvn_len : forall n p, length (pinvn n p) = n.
Proof. intros. unfold pinvn. rewrite length_map, length_seq. reflexivity. Qed.

Lemma pinvn_entry : forall n p i, is_permb n p = true -> (i < n)%nat ->
  (nth i (pinvn n p) 0%nat < n)%nat /\
  nth (nth i (pinvn n p) 0%nat) p 0%nat = i.
Proof.
  intros n p i Hp Hi.
  assert (Hex : exists j, In j (seq 0 n) /\ Nat.eqb (nth j p 0%nat) i = true).
  { destruct (is_permb_preim n p i Hp Hi) as [j [Hj Hnth]].
    exists j. split; [apply in_seq; lia | apply Nat.eqb_eq; exact Hnth]. }
  pose proof (find_left_spec (fun j => Nat.eqb (nth j p 0%nat) i) (seq 0 n) 0%nat Hex)
    as [Hin Htest].
  apply in_seq in Hin. apply Nat.eqb_eq in Htest.
  unfold pinvn.
  rewrite (nth_indep _ 0%nat
             (find_left (fun j => Nat.eqb (nth j p 0%nat) 0%nat) (seq 0 n) 0%nat))
    by (rewrite length_map, length_seq; exact Hi).
  rewrite (map_nth
             (fun v => find_left (fun j => Nat.eqb (nth j p 0%nat) v) (seq 0 n) 0%nat)
             (seq 0 n) 0%nat i).
  rewrite seq_nth by exact Hi.
  cbn [Nat.add].
  split; [lia | exact Htest].
Qed.

Lemma pinvn_nth_of : forall n p k, is_permb n p = true -> (k < n)%nat ->
  nth (nth k p 0%nat) (pinvn n p) 0%nat = k.
Proof.
  intros n p k Hp Hk.
  assert (Hpk : (nth k p 0%nat < n)%nat) by (apply (is_permb_entry_lt n p Hp); exact Hk).
  destruct (pinvn_entry n p (nth k p 0%nat) Hp Hpk) as [Hlt Hval].
  apply (is_permb_inj n p Hp); [exact Hlt | exact Hk | exact Hval].
Qed.

Lemma pinvn_permb : forall n p, is_permb n p = true -> is_permb n (pinvn n p) = true.
Proof.
  intros n p Hp.
  apply andb_true_intro. split.
  - apply Nat.eqb_eq. apply pinvn_len.
  - apply forallb_forall. intros k Hk. apply in_seq in Hk.
    apply existsb_exists.
    exists (nth k p 0%nat). split.
    + apply in_seq.
      pose proof (is_permb_entry_lt n p Hp k ltac:(lia)). lia.
    + apply Nat.eqb_eq. apply pinvn_nth_of; [exact Hp | lia].
Qed.

Lemma pinvn_right : forall n p, is_permb n p = true -> pcomp p (pinvn n p) = pidn n.
Proof.
  intros n p Hp.
  apply (nth_ext _ _ 0%nat 0%nat).
  - rewrite pcomp_len, pinvn_len. unfold pidn. rewrite length_seq. reflexivity.
  - intros i Hi. rewrite pcomp_len, pinvn_len in Hi.
    rewrite (pcomp_nth p (pinvn n p) i) by (rewrite pinvn_len; exact Hi).
    destruct (pinvn_entry n p i Hp Hi) as [_ Hval].
    rewrite Hval. unfold pidn. rewrite seq_nth by exact Hi. reflexivity.
Qed.

Lemma pinvn_left : forall n p, is_permb n p = true -> pcomp (pinvn n p) p = pidn n.
Proof.
  intros n p Hp.
  apply (nth_ext _ _ 0%nat 0%nat).
  - rewrite pcomp_len, (is_permb_len n p Hp). unfold pidn.
    rewrite length_seq. reflexivity.
  - intros i Hi. rewrite pcomp_len, (is_permb_len n p Hp) in Hi.
    rewrite (pcomp_nth (pinvn n p) p i)
      by (rewrite (is_permb_len n p Hp); exact Hi).
    rewrite (pinvn_nth_of n p i Hp Hi).
    unfold pidn. rewrite seq_nth by exact Hi. reflexivity.
Qed.

(* parity on n letters -- the inversion count, the adjacent transposition and its unit inversion step. *)

Definition invrow (p : list nat) (i len : nat) : nat :=
  length (filter (fun j => Nat.ltb (nth j p 0%nat) (nth i p 0%nat)) (seq (S i) len)).

Definition inversions_n (n : nat) (p : list nat) : nat :=
  fold_right Nat.add 0%nat (map (fun i => invrow p i (n - S i)) (seq 0 n)).

Definition adjT (n k : nat) : list nat :=
  map (fun i => if Nat.eqb i k then S k
                else if Nat.eqb i (S k) then k else i) (seq 0 n).

Lemma adjT_len : forall n k, length (adjT n k) = n.
Proof. intros. unfold adjT. rewrite length_map, length_seq. reflexivity. Qed.

Lemma adjT_nth : forall n k i, (i < n)%nat ->
  nth i (adjT n k) 0%nat
  = (if Nat.eqb i k then S k else if Nat.eqb i (S k) then k else i).
Proof.
  intros n k i Hi. unfold adjT.
  rewrite (nth_indep _ 0%nat
             (if Nat.eqb 0 k then S k else if Nat.eqb 0 (S k) then k else 0)%nat)
    by (rewrite length_map, length_seq; exact Hi).
  rewrite (map_nth (fun v => if Nat.eqb v k then S k
                             else if Nat.eqb v (S k) then k else v) (seq 0 n) 0%nat i).
  rewrite seq_nth by exact Hi.
  reflexivity.
Qed.

Lemma adjT_permb : forall n k, (S k < n)%nat -> is_permb n (adjT n k) = true.
Proof.
  intros n k Hk.
  apply is_permb_perm.
  apply NoDup_Permutation_bis.
  - apply seq_NoDup.
  - rewrite adjT_len, length_seq. lia.
  - intros i Hi. apply in_seq in Hi.
    set (sw := fun v => if Nat.eqb v k then S k
                        else if Nat.eqb v (S k) then k else v).
    assert (Hsw : forall v, (v < n)%nat -> nth (sw v) (adjT n k) 0%nat = v).
    { intros v Hv.
      assert (Hswlt : (sw v < n)%nat).
      { unfold sw. destruct (Nat.eqb_spec v k) as [->|];
          [lia | destruct (Nat.eqb_spec v (S k)) as [->|]; lia]. }
      rewrite adjT_nth by exact Hswlt.
      unfold sw.
      destruct (Nat.eqb_spec v k) as [->|Hvk].
      - destruct (Nat.eqb_spec (S k) k) as [E|_]; [lia |].
        destruct (Nat.eqb_spec (S k) (S k)) as [_|E]; [reflexivity | lia].
      - destruct (Nat.eqb_spec v (S k)) as [->|Hvsk].
        + destruct (Nat.eqb_spec k k) as [_|E]; [reflexivity | lia].
        + destruct (Nat.eqb_spec v k) as [E|_]; [lia |].
          destruct (Nat.eqb_spec v (S k)) as [E|_]; [lia | reflexivity]. }
    rewrite <- (Hsw i ltac:(lia)).
    apply nth_In. rewrite adjT_len.
    unfold sw. destruct (Nat.eqb_spec i k) as [->|];
      [lia | destruct (Nat.eqb_spec i (S k)) as [->|]; lia].
Qed.

Lemma pcomp_adjT_nth : forall n p k i, (S k < n)%nat -> (i < n)%nat ->
  length p = n ->
  nth i (pcomp p (adjT n k)) 0%nat
  = nth (if Nat.eqb i k then S k else if Nat.eqb i (S k) then k else i) p 0%nat.
Proof.
  intros n p k i Hk Hi Hlen.
  rewrite (pcomp_nth p (adjT n k) i) by (rewrite adjT_len; exact Hi).
  rewrite adjT_nth by exact Hi.
  reflexivity.
Qed.

Lemma sum_app : forall l1 l2,
  fold_right Nat.add 0%nat (l1 ++ l2)
  = (fold_right Nat.add 0%nat l1 + fold_right Nat.add 0%nat l2)%nat.
Proof.
  induction l1 as [|a l1 IH]; intro l2; cbn [app fold_right].
  - reflexivity.
  - rewrite IH. lia.
Qed.

Lemma filter_row_ext : forall (p p' : list nat) (c c' a len : nat),
  c' = c ->
  (forall j, In j (seq a len) -> nth j p' 0%nat = nth j p 0%nat) ->
  length (filter (fun j => Nat.ltb (nth j p' 0%nat) c') (seq a len))
  = length (filter (fun j => Nat.ltb (nth j p 0%nat) c) (seq a len)).
Proof.
  intros p p' c c' a len Hc Hj.
  subst c'. f_equal.
  apply filter_ext_in.
  intros j Hjin. rewrite (Hj j Hjin). reflexivity.
Qed.

Lemma filter_cons_len : forall (t : nat -> bool) (a : nat) (l : list nat),
  length (filter t (a :: l)) = ((if t a then 1 else 0) + length (filter t l))%nat.
Proof. intros. cbn [filter]. destruct (t a); cbn [length]; lia. Qed.

(** THE UNIT STEP: composing with an adjacent transposition moves the inversion count by exactly the flip of the adjacent pair. *)
Lemma inversions_pcomp_adjT : forall n p k,
  is_permb n p = true -> (S k < n)%nat ->
  (inversions_n n (pcomp p (adjT n k))
   + (if Nat.ltb (nth (S k) p 0%nat) (nth k p 0%nat) then 1 else 0)
   = inversions_n n p
   + (if Nat.ltb (nth k p 0%nat) (nth (S k) p 0%nat) then 1 else 0))%nat.
Proof.
  intros n p k Hp Hk.
  set (p' := pcomp p (adjT n k)) in *.
  assert (Hplen : length p = n) by (apply (is_permb_len n p Hp)).
  assert (Hp'k : nth k p' 0%nat = nth (S k) p 0%nat).
  { unfold p'. rewrite (pcomp_adjT_nth n p k k Hk ltac:(lia) Hplen).
    rewrite Nat.eqb_refl. reflexivity. }
  assert (Hp'sk : nth (S k) p' 0%nat = nth k p 0%nat).
  { unfold p'. rewrite (pcomp_adjT_nth n p k (S k) Hk Hk Hplen).
    destruct (Nat.eqb_spec (S k) k) as [E|_]; [lia |].
    rewrite Nat.eqb_refl. reflexivity. }
  assert (Hp'o : forall j, (j < n)%nat -> j <> k -> j <> S k ->
            nth j p' 0%nat = nth j p 0%nat).
  { intros j Hj Hjk Hjsk.
    unfold p'. rewrite (pcomp_adjT_nth n p k j Hk Hj Hplen).
    destruct (Nat.eqb_spec j k) as [E|_]; [lia |].
    destruct (Nat.eqb_spec j (S k)) as [E|_]; [lia |].
    reflexivity. }
  set (m := (n - S (S k))%nat).
  assert (Hn : n = (k + S (S m))%nat) by lia.
  unfold inversions_n.
  rewrite Hn.
  rewrite seq_app.
  cbn [Nat.add].
  cbn [seq].
  rewrite !map_app.
  cbn [map].
  rewrite !sum_app.
  cbn [fold_right].
  replace ((k + S (S m)) - S k)%nat with (S m) by lia.
  replace ((k + S (S m)) - S (S k))%nat with m by lia.
  assert (HA : map (fun i => invrow p' i ((k + S (S m)) - S i)%nat) (seq 0 k)
             = map (fun i => invrow p i ((k + S (S m)) - S i)%nat) (seq 0 k)).
  { apply map_ext_in. intros i Hi. apply in_seq in Hi.
    replace ((k + S (S m)) - S i)%nat with ((k - S i) + S (S m))%nat by lia.
    unfold invrow.
    rewrite seq_app.
    replace (S i + (k - S i))%nat with k by lia.
    cbn [seq].
    rewrite !filter_app, !length_app.
    rewrite !filter_cons_len.
    assert (Hci : nth i p' 0%nat = nth i p 0%nat)
      by (apply Hp'o; lia).
    rewrite (filter_row_ext p p' (nth i p 0%nat) (nth i p' 0%nat) (S i) (k - S i)
               Hci
               ltac:(intros j Hj; apply in_seq in Hj; apply Hp'o; lia)).
    rewrite (filter_row_ext p p' (nth i p 0%nat) (nth i p' 0%nat) (S (S k)) m
               Hci
               ltac:(intros j Hj; apply in_seq in Hj; apply Hp'o; lia)).
    rewrite Hp'k, Hp'sk, Hci.
    lia. }
  assert (HB : invrow p' k (S m)
             = ((if Nat.ltb (nth k p 0%nat) (nth (S k) p 0%nat) then 1 else 0)
                + invrow p (S k) m)%nat).
  { unfold invrow.
    cbn [seq].
    rewrite filter_cons_len.
    rewrite (filter_row_ext p p' (nth (S k) p 0%nat) (nth k p' 0%nat) (S (S k)) m
               Hp'k
               ltac:(intros j Hj; apply in_seq in Hj; apply Hp'o; lia)).
    rewrite Hp'k, Hp'sk.
    reflexivity. }
  assert (HC : invrow p k (S m)
             = ((if Nat.ltb (nth (S k) p 0%nat) (nth k p 0%nat) then 1 else 0)
                + invrow p' (S k) m)%nat).
  { unfold invrow.
    cbn [seq].
    rewrite filter_cons_len.
    rewrite (filter_row_ext p' p (nth (S k) p' 0%nat) (nth k p 0%nat) (S (S k)) m
               ltac:(rewrite Hp'sk; reflexivity)
               ltac:(intros j Hj; apply in_seq in Hj; symmetry; apply Hp'o; lia)).
    reflexivity. }
  assert (HD : map (fun i => invrow p' i ((k + S (S m)) - S i)%nat) (seq (S (S k)) m)
             = map (fun i => invrow p i ((k + S (S m)) - S i)%nat) (seq (S (S k)) m)).
  { apply map_ext_in. intros i Hi. apply in_seq in Hi.
    unfold invrow.
    apply (filter_row_ext p p' (nth i p 0%nat) (nth i p' 0%nat) (S i)
             ((k + S (S m)) - S i)%nat).
    - apply Hp'o; lia.
    - intros j Hj. apply in_seq in Hj. apply Hp'o; lia. }
  rewrite HA, HB, HC, HD.
  lia.
Qed.

Definition even_permn (n : nat) (p : list nat) : bool :=
  Nat.even (inversions_n n p).

Lemma even_permn_adjT_flip : forall n p k,
  is_permb n p = true -> (S k < n)%nat ->
  even_permn n (pcomp p (adjT n k)) = negb (even_permn n p).
Proof.
  intros n p k Hp Hk.
  pose proof (inversions_pcomp_adjT n p k Hp Hk) as HE.
  assert (Hne : nth k p 0%nat <> nth (S k) p 0%nat).
  { intro E.
    pose proof (is_permb_inj n p Hp k (S k) ltac:(lia) ltac:(lia) E). lia. }
  unfold even_permn.
  destruct (Nat.ltb (nth k p 0%nat) (nth (S k) p 0%nat)) eqn:E1;
    destruct (Nat.ltb (nth (S k) p 0%nat) (nth k p 0%nat)) eqn:E2.
  - apply Nat.ltb_lt in E1. apply Nat.ltb_lt in E2. lia.
  - assert (E : inversions_n n (pcomp p (adjT n k)) = S (inversions_n n p)) by lia.
    rewrite E, Nat.even_succ, <- Nat.negb_even. reflexivity.
  - assert (E : S (inversions_n n (pcomp p (adjT n k))) = inversions_n n p) by lia.
    rewrite <- E, Nat.even_succ, <- Nat.negb_even.
    rewrite Bool.negb_involutive. reflexivity.
  - apply Nat.ltb_ge in E1. apply Nat.ltb_ge in E2. lia.
Qed.

(* decomposition by bubble sort and multiplicativity of parity under composition. *)

Fixpoint compadj (n : nat) (ks : list nat) : list nat :=
  match ks with
  | nil => pidn n
  | k :: tl => pcomp (compadj n tl) (adjT n k)
  end.

Lemma compadj_permb : forall n ks, Forall (fun k => (S k < n)%nat) ks ->
  is_permb n (compadj n ks) = true.
Proof.
  intros n ks H. induction H as [|k ks Hk Hks IH]; cbn [compadj].
  - apply pidn_permb.
  - apply pcomp_permb; [exact IH | apply adjT_permb; exact Hk].
Qed.

Lemma filter_all_false_len : forall (t : nat -> bool) (l : list nat),
  (forall a, In a l -> t a = false) -> length (filter t l) = 0%nat.
Proof.
  intros t l H. induction l as [|a l IH]; cbn [filter].
  - reflexivity.
  - rewrite (H a (or_introl eq_refl)).
    apply IH. intros b Hb. apply H. right. exact Hb.
Qed.

Lemma filter_len_zero_all : forall (t : nat -> bool) (l : list nat),
  length (filter t l) = 0%nat -> forall a, In a l -> t a = false.
Proof.
  intros t l. induction l as [|a l IH]; intros H b Hb; [contradiction |].
  cbn [filter] in H.
  destruct (t a) eqn:Eta; [cbn [length] in H; lia |].
  destruct Hb as [-> | Hb]; [exact Eta | apply IH; assumption].
Qed.

Lemma sum_zeros : forall (l : list nat),
  fold_right Nat.add 0%nat (map (fun _ => 0%nat) l) = 0%nat.
Proof. induction l as [|a l IH]; cbn [map fold_right]; lia. Qed.

Lemma sum_zero_all : forall (l : list nat),
  fold_right Nat.add 0%nat l = 0%nat -> forall x, In x l -> x = 0%nat.
Proof.
  induction l as [|a l IH]; intros H x Hx; [contradiction |].
  cbn [fold_right] in H.
  destruct Hx as [-> | Hx]; [lia | apply IH; [lia | exact Hx]].
Qed.

Lemma inversions_pidn : forall n, inversions_n n (pidn n) = 0%nat.
Proof.
  intro n. unfold inversions_n.
  assert (HZ : map (fun i => invrow (pidn n) i (n - S i)%nat) (seq 0 n)
             = map (fun _ => 0%nat) (seq 0 n)).
  { apply map_ext_in. intros i Hi. apply in_seq in Hi.
    unfold invrow.
    apply filter_all_false_len.
    intros j Hj. apply in_seq in Hj.
    unfold pidn. rewrite !seq_nth by lia.
    apply Nat.ltb_ge. lia. }
  rewrite HZ. apply sum_zeros.
Qed.

Lemma even_permn_pidn : forall n, even_permn n (pidn n) = true.
Proof. intro n. unfold even_permn. rewrite inversions_pidn. reflexivity. Qed.

(** Zero inversions forces the identity. *)
Lemma inversions_zero_pidn : forall n p, is_permb n p = true ->
  inversions_n n p = 0%nat -> p = pidn n.
Proof.
  intros n p Hp H0.
  assert (Hplen : length p = n) by (apply (is_permb_len n p Hp)).
  assert (Hasc : forall k, (S k < n)%nat ->
            (nth k p 0%nat < nth (S k) p 0%nat)%nat).
  { intros k Hk.
    assert (Hrow : invrow p k (n - S k)%nat = 0%nat).
    { apply (sum_zero_all _ H0).
      apply in_map_iff. exists k. split; [reflexivity | apply in_seq; lia]. }
    unfold invrow in Hrow.
    pose proof (filter_len_zero_all _ _ Hrow (S k) ltac:(apply in_seq; lia)) as Hb.
    apply Nat.ltb_ge in Hb.
    assert (Hne : nth k p 0%nat <> nth (S k) p 0%nat).
    { intro E.
      pose proof (is_permb_inj n p Hp k (S k) ltac:(lia) ltac:(lia) E). lia. }
    lia. }
  assert (Hup : forall i, (i < n)%nat -> (i <= nth i p 0%nat)%nat).
  { induction i as [|i IH]; intro Hi; [lia |].
    pose proof (IH ltac:(lia)) as Hle.
    pose proof (Hasc i Hi). lia. }
  assert (Hdown : forall i, (i < n)%nat -> (nth i p 0%nat <= i)%nat).
  { intros i Hi.
    destruct (le_lt_dec (nth i p 0%nat) i) as [Hle | Hgt]; [exact Hle |].
    exfalso.
    assert (Hgen : forall d, (i + d < n)%nat ->
              (i + 1 + d <= nth (i + d)%nat p 0%nat)%nat).
    { induction d as [|d IH]; intro Hd.
      - rewrite !Nat.add_0_r. lia.
      - pose proof (IH ltac:(lia)) as Hle.
        replace (i + S d)%nat with (S (i + d)) by lia.
        pose proof (Hasc (i + d)%nat ltac:(lia)). lia. }
    pose proof (Hgen (n - 1 - i)%nat ltac:(lia)) as Hbig.
    pose proof (is_permb_entry_lt n p Hp (i + (n - 1 - i))%nat ltac:(lia)). lia. }
  apply (nth_ext _ _ 0%nat 0%nat).
  - rewrite Hplen. unfold pidn. rewrite length_seq. reflexivity.
  - intros i Hi. rewrite Hplen in Hi.
    unfold pidn. rewrite seq_nth by exact Hi.
    pose proof (Hup i Hi). pose proof (Hdown i Hi). lia.
Qed.

Lemma adjT_invol : forall n k, (S k < n)%nat ->
  pcomp (adjT n k) (adjT n k) = pidn n.
Proof.
  intros n k Hk.
  pose proof (adjT_permb n k Hk) as HT.
  apply (nth_ext _ _ 0%nat 0%nat).
  - rewrite pcomp_len, adjT_len. unfold pidn. rewrite length_seq. reflexivity.
  - intros i Hi. rewrite pcomp_len, adjT_len in Hi.
    rewrite (pcomp_nth (adjT n k) (adjT n k) i) by (rewrite adjT_len; exact Hi).
    rewrite (adjT_nth n k i Hi).
    unfold pidn. rewrite seq_nth by exact Hi.
    destruct (Nat.eqb_spec i k) as [->|Hik].
    + rewrite adjT_nth by lia.
      destruct (Nat.eqb_spec (S k) k) as [E|_]; [lia |].
      rewrite Nat.eqb_refl. reflexivity.
    + destruct (Nat.eqb_spec i (S k)) as [->|Hisk].
      * rewrite adjT_nth by lia.
        rewrite Nat.eqb_refl. reflexivity.
      * rewrite adjT_nth by exact Hi.
        destruct (Nat.eqb_spec i k) as [E|_]; [lia |].
        destruct (Nat.eqb_spec i (S k)) as [E|_]; [lia |].
        reflexivity.
Qed.

(** Bubble-sort decomposition into adjacent transpositions, with the parity of the word length. *)
Lemma permb_decomp : forall n p, is_permb n p = true ->
  exists ks, Forall (fun k => (S k < n)%nat) ks /\
             p = compadj n ks /\
             Nat.even (length ks) = even_permn n p.
Proof.
  intros n p Hp.
  remember (inversions_n n p) as v eqn:Hv.
  revert p Hp Hv.
  induction v as [v IH] using (well_founded_induction lt_wf).
  intros p Hp Hv.
  destruct (existsb (fun k => Nat.ltb (nth (S k) p 0%nat) (nth k p 0%nat))
              (seq 0 (n - 1))) eqn:Ed.
  - apply existsb_exists in Ed.
    destruct Ed as [k [Hkin Hklt]].
    apply in_seq in Hkin. apply Nat.ltb_lt in Hklt.
    assert (Hk : (S k < n)%nat) by lia.
    set (p2 := pcomp p (adjT n k)).
    assert (Hp2 : is_permb n p2 = true)
      by (apply pcomp_permb; [exact Hp | apply adjT_permb; exact Hk]).
    pose proof (inversions_pcomp_adjT n p k Hp Hk) as HE.
    destruct (Nat.ltb (nth k p 0%nat) (nth (S k) p 0%nat)) eqn:E1;
      [apply Nat.ltb_lt in E1; lia |].
    destruct (Nat.ltb (nth (S k) p 0%nat) (nth k p 0%nat)) eqn:E2;
      [| apply Nat.ltb_ge in E2; lia].
    assert (Hdec : (inversions_n n p2 < v)%nat) by (unfold p2; lia).
    destruct (IH (inversions_n n p2) ltac:(lia) p2 Hp2 eq_refl)
      as [ks [Hks [Hcomp Hpar]]].
    exists (k :: ks).
    split; [constructor; [exact Hk | exact Hks] |].
    split.
    + cbn [compadj]. rewrite <- Hcomp.
      unfold p2.
      rewrite (pcompn_assoc n p (adjT n k) (adjT n k) Hp
                 (adjT_permb n k Hk) (adjT_permb n k Hk)).
      rewrite (adjT_invol n k Hk).
      symmetry. apply (pcompn_id_right n p Hp).
    + cbn [length].
      rewrite Nat.even_succ, <- Nat.negb_even, Hpar.
      assert (Hflip : even_permn n p2 = negb (even_permn n p))
        by (apply even_permn_adjT_flip; assumption).
      rewrite Hflip. apply Bool.negb_involutive.
  - exists nil.
    split; [constructor |].
    assert (Hzero : inversions_n n p = 0%nat).
    { assert (Hasc : forall k, (S k < n)%nat ->
                (nth k p 0%nat < nth (S k) p 0%nat)%nat).
      { intros k Hk.
        assert (Hfalse : Nat.ltb (nth (S k) p 0%nat) (nth k p 0%nat) = false).
        { destruct (Nat.ltb (nth (S k) p 0%nat) (nth k p 0%nat)) eqn:Eb;
            [| reflexivity].
          exfalso.
          assert (Ec : existsb (fun k0 => Nat.ltb (nth (S k0) p 0%nat)
                                            (nth k0 p 0%nat)) (seq 0 (n - 1)) = true).
          { apply existsb_exists. exists k.
            split; [apply in_seq; lia | exact Eb]. }
          rewrite Ec in Ed. discriminate. }
        apply Nat.ltb_ge in Hfalse.
        assert (Hne : nth k p 0%nat <> nth (S k) p 0%nat).
        { intro E.
          pose proof (is_permb_inj n p Hp k (S k) ltac:(lia) ltac:(lia) E). lia. }
        lia. }
      unfold inversions_n.
      assert (HZ : map (fun i => invrow p i (n - S i)%nat) (seq 0 n)
                 = map (fun _ => 0%nat) (seq 0 n)).
      { apply map_ext_in. intros i Hi. apply in_seq in Hi.
        unfold invrow.
        apply filter_all_false_len.
        intros j Hj. apply in_seq in Hj.
        assert (Hmono : forall d i0, (i0 + S d < n)%nat ->
                  (nth i0 p 0%nat < nth (i0 + S d)%nat p 0%nat)%nat).
        { induction d as [|d IHd]; intros i0 Hd.
          - replace (i0 + 1)%nat with (S i0) by lia. apply Hasc. lia.
          - pose proof (IHd i0 ltac:(lia)).
            replace (i0 + S (S d))%nat with (S (i0 + S d)) by lia.
            pose proof (Hasc (i0 + S d)%nat ltac:(lia)). lia. }
        apply Nat.ltb_ge.
        pose proof (Hmono (j - S i)%nat i ltac:(lia)) as Hm.
        replace (i + S (j - S i))%nat with j in Hm by lia.
        lia. }
      rewrite HZ. apply sum_zeros. }
    split.
    + cbn [compadj]. apply (inversions_zero_pidn n p Hp Hzero).
    + cbn [length Nat.even].
      unfold even_permn. rewrite Hzero. reflexivity.
Qed.

(** MULTIPLICATIVITY OF PARITY. *)
Lemma even_permn_pcomp : forall n p q,
  is_permb n p = true -> is_permb n q = true ->
  even_permn n (pcomp p q) = Bool.eqb (even_permn n p) (even_permn n q).
Proof.
  intros n p q Hp Hq.
  destruct (permb_decomp n q Hq) as [ks [Hks [Hq' Hpar]]].
  assert (Hgen : forall ks0, Forall (fun k => (S k < n)%nat) ks0 ->
    forall p0, is_permb n p0 = true ->
    even_permn n (pcomp p0 (compadj n ks0))
    = Bool.eqb (even_permn n p0) (Nat.even (length ks0))).
  { induction ks0 as [|k ks0 IHks]; intros Hf p0 Hp0.
    - cbn [compadj length Nat.even].
      rewrite (pcompn_id_right n p0 Hp0).
      destruct (even_permn n p0); reflexivity.
    - cbn [compadj length].
      inversion Hf as [|? ? Hk Hks0]; subst.
      rewrite <- (pcompn_assoc n p0 (compadj n ks0) (adjT n k) Hp0
                    (compadj_permb n ks0 Hks0) (adjT_permb n k Hk)).
      rewrite (even_permn_adjT_flip n (pcomp p0 (compadj n ks0)) k
                 (pcomp_permb n p0 (compadj n ks0) Hp0 (compadj_permb n ks0 Hks0))
                 Hk).
      rewrite (IHks Hks0 p0 Hp0).
      rewrite Nat.even_succ, <- Nat.negb_even.
      destruct (even_permn n p0); destruct (Nat.even (length ks0)); reflexivity. }
  rewrite Hq'.
  rewrite (Hgen ks Hks p Hp).
  rewrite Hpar, Hq'.
  reflexivity.
Qed.

Lemma even_permn_pinvn : forall n p, is_permb n p = true ->
  even_permn n (pinvn n p) = even_permn n p.
Proof.
  intros n p Hp.
  pose proof (even_permn_pcomp n p (pinvn n p) Hp (pinvn_permb n p Hp)) as HE.
  rewrite (pinvn_right n p Hp), even_permn_pidn in HE.
  destruct (even_permn n p); destruct (even_permn n (pinvn n p));
    cbn [Bool.eqb] in HE; congruence.
Qed.

(* ambient-free groups of n-letter permutations, with inverses from cycling powers. *)

Record pgroupn (n : nat) (G : list (list nat)) : Prop := mkPgroupn {
  pgn_perm : forall p, In p G -> is_permb n p = true;
  pgn_nd : NoDup G;
  pgn_id : In (pidn n) G;
  pgn_comp : forall p q, In p G -> In q G -> In (pcomp p q) G
}.

Fixpoint ppown (n : nat) (p : list nat) (k : nat) : list nat :=
  match k with
  | O => pidn n
  | S k' => pcomp p (ppown n p k')
  end.

Lemma ppown_permb : forall n p k, is_permb n p = true ->
  is_permb n (ppown n p k) = true.
Proof.
  intros n p k Hp. induction k as [|k IH]; cbn [ppown].
  - apply pidn_permb.
  - apply pcomp_permb; assumption.
Qed.

Lemma ppown_in : forall n G p k, pgroupn n G -> In p G ->
  In (ppown n p (S k)) G.
Proof.
  intros n G p k HG Hp. induction k as [|k IH]; cbn [ppown].
  - rewrite (pcompn_id_right n p (pgn_perm n G HG p Hp)). exact Hp.
  - apply (pgn_comp n G HG); [exact Hp | exact IH].
Qed.

Lemma ppown_add : forall n p a b, is_permb n p = true ->
  ppown n p (a + b) = pcomp (ppown n p a) (ppown n p b).
Proof.
  intros n p a b Hp. induction a as [|a IH]; cbn [ppown Nat.add].
  - symmetry. apply (pcompn_id_left n (ppown n p b)).
    apply ppown_permb. exact Hp.
  - rewrite IH.
    symmetry.
    apply (pcompn_assoc n p (ppown n p a) (ppown n p b) Hp);
      apply ppown_permb; exact Hp.
Qed.

(** Left cancellation for permutation composition. *)
Lemma pcompn_cancel_l : forall n p x y, is_permb n p = true ->
  is_permb n x = true -> is_permb n y = true ->
  pcomp p x = pcomp p y -> x = y.
Proof.
  intros n p x y Hp Hx Hy He.
  assert (E2 : pcomp (pinvn n p) (pcomp p x) = pcomp (pinvn n p) (pcomp p y))
    by (rewrite He; reflexivity).
  rewrite <- (pcompn_assoc n (pinvn n p) p x (pinvn_permb n p Hp) Hp Hx) in E2.
  rewrite <- (pcompn_assoc n (pinvn n p) p y (pinvn_permb n p Hp) Hp Hy) in E2.
  rewrite (pinvn_left n p Hp) in E2.
  rewrite (pcompn_id_left n x Hx), (pcompn_id_left n y Hy) in E2.
  exact E2.
Qed.

(** A duplicate among a list longer than a bounding superset. *)
Lemma long_list_collision : forall (dflt : list nat)
    (l : list (list nat)) (bound : list (list nat)),
  incl l bound -> (length bound < length l)%nat ->
  exists i j, (i < j)%nat /\ (j < length l)%nat /\
    nth i l dflt = nth j l dflt.
Proof.
  intros dflt l bound Hincl Hlt.
  destruct (classic (exists i j, (i < j)%nat /\ (j < length l)%nat /\
                     nth i l dflt = nth j l dflt)) as [Hyes | Hno]; [exact Hyes |].
  exfalso.
  assert (Hnd : NoDup l).
  { apply (proj2 (NoDup_nth l dflt)).
    intros i j Hi Hj He.
    destruct (Nat.lt_trichotomy i j) as [Hij | [Hij | Hij]].
    - exfalso. apply Hno. exists i, j. repeat split; assumption.
    - exact Hij.
    - exfalso. apply Hno. exists j, i.
      repeat split; [exact Hij | exact Hi | symmetry; exact He]. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hle.
  lia.
Qed.

(** A pigeonhole collision among the first length G + 1 powers puts the inverse inside the group. *)
Lemma pgroupn_inv_in : forall n G p, pgroupn n G -> In p G ->
  In (pinvn n p) G.
Proof.
  intros n G p HG Hp.
  assert (Hpp : is_permb n p = true) by (apply (pgn_perm n G HG p Hp)).
  set (pows := map (fun k => ppown n p (S k)) (seq 0 (S (length G)))).
  assert (Hlp : length pows = S (length G))
    by (unfold pows; rewrite length_map, length_seq; reflexivity).
  assert (Hincl : incl pows G).
  { intros q Hq. unfold pows in Hq.
    apply in_map_iff in Hq. destruct Hq as [k [Hqk _]].
    rewrite <- Hqk. apply (ppown_in n G p k HG Hp). }
  destruct (long_list_collision (pidn n) pows G Hincl ltac:(rewrite Hlp; lia))
    as [i [j [Hij [Hjl He]]]].
  assert (Hnth : forall m, (m < S (length G))%nat ->
            nth m pows (pidn n) = ppown n p (S m)).
  { intros m Hm. unfold pows.
    rewrite (nth_indep _ (pidn n) (ppown n p (S 0%nat)))
      by (rewrite length_map, length_seq; exact Hm).
    rewrite (map_nth (fun k => ppown n p (S k)) (seq 0 (S (length G))) 0%nat m).
    rewrite seq_nth by exact Hm.
    reflexivity. }
  rewrite Hlp in Hjl.
  rewrite (Hnth i ltac:(lia)), (Hnth j ltac:(lia)) in He.
  set (d := (j - i)%nat).
  assert (Hd1 : (1 <= d)%nat) by (unfold d; lia).
  assert (Hcyc : ppown n p d = pidn n).
  { assert (Hsplit : (S j = S i + d)%nat) by (unfold d; lia).
    rewrite Hsplit, (ppown_add n p (S i) d Hpp) in He.
    apply (pcompn_cancel_l n (ppown n p (S i)));
      [apply ppown_permb; exact Hpp
       | apply ppown_permb; exact Hpp
       | apply pidn_permb |].
    rewrite (pcompn_id_right n (ppown n p (S i)))
      by (apply ppown_permb; exact Hpp).
    symmetry. exact He. }
  assert (Hstep : pcomp p (ppown n p (d - 1)) = pidn n).
  { replace (pcomp p (ppown n p (d - 1))) with (ppown n p (S (d - 1)))
      by reflexivity.
    replace (S (d - 1))%nat with d by lia.
    exact Hcyc. }
  assert (Hinv_eq : pinvn n p = ppown n p (d - 1)).
  { apply (pcompn_cancel_l n p);
      [exact Hpp
       | apply pinvn_permb; exact Hpp
       | apply ppown_permb; exact Hpp |].
    rewrite (pinvn_right n p Hpp).
    symmetry. exact Hstep. }
  rewrite Hinv_eq.
  destruct (Nat.eq_dec d 1%nat) as [-> | Hd2].
  - replace (1 - 1)%nat with 0%nat by lia. cbn [ppown].
    apply (pgn_id n G HG).
  - assert (Hd' : exists d', (d - 1)%nat = S d') by (exists (d - 2)%nat; lia).
    destruct Hd' as [d' Hd'].
    rewrite Hd'. apply (ppown_in n G p d' HG Hp).
Qed.


(* the concrete symmetric group on six letters -- image lists over 0..5, composition, parity by inversion count, the full enumeration, all vm-checkable. *)

Definition pid6 : list nat := seq 0 6.

Definition is_perm6 (p : list nat) : bool :=
  (Nat.eqb (length p) 6) &&
  forallb (fun i => existsb (fun j => Nat.eqb (nth j p 0%nat) i) (seq 0 6)) (seq 0 6).

Fixpoint insert_everywhere (x : nat) (l : list nat) : list (list nat) :=
  (x :: l) :: match l with
              | nil => nil
              | y :: tl => map (cons y) (insert_everywhere x tl)
              end.

Fixpoint perms_of (l : list nat) : list (list nat) :=
  match l with
  | nil => nil :: nil
  | x :: tl => flat_map (insert_everywhere x) (perms_of tl)
  end.

Definition S6list : list (list nat) := perms_of (seq 0 6).

Lemma S6list_length : length S6list = 720%nat.
Proof. vm_compute. reflexivity. Qed.

(** Parity by inversion count. *)
Definition inversions (p : list nat) : nat :=
  fold_right Nat.add 0%nat
    (map (fun i =>
      length (filter (fun j => Nat.ltb (nth j p 0%nat) (nth i p 0%nat))
                (seq (Datatypes.S i) (5 - i))))
      (seq 0 6)).

Definition even_perm (p : list nat) : bool := Nat.even (inversions p).

Definition A6list : list (list nat) := filter even_perm S6list.

Lemma A6list_length : length A6list = 360%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma S6list_all_perms : forallb is_perm6 S6list = true.
Proof. vm_compute. reflexivity. Qed.

(** Membership as a boolean, via list equality on nat lists. *)
Fixpoint eqb_listnat (a b : list nat) : bool :=
  match a, b with
  | nil, nil => true
  | x :: a', y :: b' => Nat.eqb x y && eqb_listnat a' b'
  | _, _ => false
  end.

Lemma eqb_listnat_spec : forall a b, eqb_listnat a b = true <-> a = b.
Proof.
  induction a as [|x a IH]; intros b; destruct b as [|y b]; cbn [eqb_listnat].
  - split; [intros _; reflexivity | intros _; reflexivity].
  - split; [discriminate | discriminate].
  - split; [discriminate | discriminate].
  - split.
    + intro H. apply andb_prop in H. destruct H as [H1 H2].
      apply Nat.eqb_eq in H1. apply IH in H2. subst. reflexivity.
    + intro H. injection H as -> ->.
      apply andb_true_intro.
      split; [apply Nat.eqb_refl | apply IH; reflexivity].
Qed.

Definition memb (p : list nat) (l : list (list nat)) : bool :=
  existsb (eqb_listnat p) l.

Lemma memb_spec : forall p l, memb p l = true <-> In p l.
Proof.
  intros p l. unfold memb. rewrite existsb_exists.
  split.
  - intros [q [Hq He]]. apply eqb_listnat_spec in He. subst. exact Hq.
  - intro H. exists p. split; [exact H | apply eqb_listnat_spec; reflexivity].
Qed.

(** The boolean NoDup checker, for vm-certified distinctness of permutation lists. *)
Fixpoint distinctb (l : list (list nat)) : bool :=
  match l with
  | nil => true
  | x :: tl => negb (memb x tl) && distinctb tl
  end.

Lemma distinctb_NoDup : forall l, distinctb l = true -> NoDup l.
Proof.
  induction l as [|x tl IH]; intro Hb; cbn [distinctb] in Hb.
  - constructor.
  - apply andb_prop in Hb. destruct Hb as [H1 H2].
    constructor.
    + intro Hc. rewrite negb_true_iff in H1.
      apply memb_spec in Hc. rewrite Hc in H1. discriminate.
    + apply IH. exact H2.
Qed.

(** Completeness of the enumeration: every arrangement is produced, so composition closure follows from surjectivity without a quadratic vm sweep. *)
Lemma insert_everywhere_hits : forall (x : nat) (m1 m2 : list nat),
  In (m1 ++ x :: m2) (insert_everywhere x (m1 ++ m2)).
Proof.
  intros x m1. induction m1 as [|y m1 IH]; intro m2.
  - rewrite !app_nil_l.
    destruct m2 as [|z tl]; cbn [insert_everywhere]; apply in_eq.
  - rewrite <- !app_comm_cons. cbn [insert_everywhere].
    apply in_cons.
    apply in_map. apply IH.
Qed.

Lemma perms_of_complete : forall (l m : list nat),
  Permutation l m -> In m (perms_of l).
Proof.
  induction l as [|x l IH]; intros m Hp.
  - apply Permutation_nil in Hp. subst. left. reflexivity.
  - assert (Hp' : Permutation m (x :: l)) by (symmetry; exact Hp).
    destruct (Permutation_vs_cons_inv Hp') as [m1 [m2 Hm]].
    subst m.
    apply Permutation_cons_app_inv in Hp.
    cbn [perms_of].
    apply in_flat_map.
    exists (m1 ++ m2).
    split; [apply IH; exact Hp | apply insert_everywhere_hits].
Qed.

Lemma is_permn_in_perms_of : forall (n : nat) (p : list nat),
  length p = n ->
  (forall i, (i < n)%nat -> exists j, (j < n)%nat /\ nth j p 0%nat = i) ->
  In p (perms_of (seq 0 n)).
Proof.
  intros n p Hlen Hsurj.
  apply perms_of_complete.
  apply NoDup_Permutation_bis.
  - apply seq_NoDup.
  - rewrite length_seq, Hlen. lia.
  - intros i Hi.
    apply in_seq in Hi.
    destruct (Hsurj i ltac:(lia)) as [j [Hj Hnth]].
    rewrite <- Hnth.
    apply nth_In. lia.
Qed.

Lemma is_perm6_in_S6list : forall p,
  length p = 6%nat ->
  (forall i, (i < 6)%nat -> exists j, (j < 6)%nat /\ nth j p 0%nat = i) ->
  In p S6list.
Proof.
  exact (is_permn_in_perms_of 6).
Qed.

(** Inverse of a concrete permutation: position of each letter. *)
Definition pinv (p : list nat) : list nat :=
  map (fun i => find_left (fun j => Nat.eqb (nth j p 0%nat) i) (seq 0 6) 0%nat)
    (seq 0 6).

(** Pointwise facts over the enumeration, harvested through forallb. *)
Lemma S6_fact_pointwise :
  forall (test : list nat -> bool),
  forallb test S6list = true ->
  forall p, In p S6list -> test p = true.
Proof.
  intros test Hall p Hp.
  exact (proj1 (forallb_forall test S6list) Hall p Hp).
Qed.

Lemma S6_inv_right :
  forall p, In p S6list -> pcomp p (pinv p) = pid6.
Proof.
  intros p Hp.
  apply eqb_listnat_spec.
  apply (S6_fact_pointwise (fun q => eqb_listnat (pcomp q (pinv q)) pid6));
    [vm_compute; reflexivity | exact Hp].
Qed.

Lemma S6_inv_left :
  forall p, In p S6list -> pcomp (pinv p) p = pid6.
Proof.
  intros p Hp.
  apply eqb_listnat_spec.
  apply (S6_fact_pointwise (fun q => eqb_listnat (pcomp (pinv q) q) pid6));
    [vm_compute; reflexivity | exact Hp].
Qed.

Lemma S6_inv_in :
  forall p, In p S6list -> In (pinv p) S6list.
Proof.
  intros p Hp.
  apply memb_spec.
  apply (S6_fact_pointwise (fun q => memb (pinv q) S6list));
    [vm_compute; reflexivity | exact Hp].
Qed.

Lemma S6_id_in : In pid6 S6list.
Proof. apply memb_spec. vm_compute. reflexivity. Qed.

Lemma S6_surj :
  forall p, In p S6list ->
  forall i, (i < 6)%nat -> exists j, (j < 6)%nat /\ nth j p 0%nat = i.
Proof.
  intros p Hp i Hi.
  pose proof (S6_fact_pointwise is_perm6 S6list_all_perms p Hp) as Hperm.
  unfold is_perm6 in Hperm.
  apply andb_prop in Hperm. destruct Hperm as [_ Hsurj].
  assert (Hrow : existsb (fun j => Nat.eqb (nth j p 0%nat) i) (seq 0 6) = true).
  { apply (proj1 (forallb_forall _ (seq 0 6)) Hsurj).
    apply in_seq. lia. }
  apply existsb_exists in Hrow.
  destruct Hrow as [j [Hj He]].
  apply in_seq in Hj.
  apply Nat.eqb_eq in He.
  exists j. split; [lia | exact He].
Qed.


Lemma S6_id_left :
  forall p, In p S6list -> pcomp pid6 p = p.
Proof.
  intros p Hp.
  apply eqb_listnat_spec.
  apply (S6_fact_pointwise (fun q => eqb_listnat (pcomp pid6 q) q));
    [vm_compute; reflexivity | exact Hp].
Qed.

Lemma S6_id_right :
  forall p, In p S6list -> pcomp p pid6 = p.
Proof.
  intros p Hp.
  apply eqb_listnat_spec.
  apply (S6_fact_pointwise (fun q => eqb_listnat (pcomp q pid6) q));
    [vm_compute; reflexivity | exact Hp].
Qed.

Lemma S6_length6 :
  forall p, In p S6list -> length p = 6%nat.
Proof.
  intros p Hp.
  apply Nat.eqb_eq.
  apply (S6_fact_pointwise (fun q => Nat.eqb (length q) 6));
    [vm_compute; reflexivity | exact Hp].
Qed.

Lemma S6_entries_lt :
  forall p, In p S6list -> forall i, (i < 6)%nat -> (nth i p 0%nat < 6)%nat.
Proof.
  intros p Hp i Hi.
  assert (Hall : forallb
    (fun q => forallb (fun i0 => Nat.ltb (nth i0 q 0%nat) 6) (seq 0 6)) S6list = true)
    by (vm_compute; reflexivity).
  pose proof (S6_fact_pointwise _ Hall p Hp) as Hrow.
  apply Nat.ltb_lt.
  apply (proj1 (forallb_forall _ (seq 0 6)) Hrow).
  apply in_seq. lia.
Qed.

(** Composition closure, abstractly: the composite is surjective. *)
Lemma S6_comp_in :
  forall p q, In p S6list -> In q S6list -> In (pcomp p q) S6list.
Proof.
  intros p q Hp Hq.
  apply is_perm6_in_S6list.
  - unfold pcomp. rewrite length_map. apply (S6_length6 q Hq).
  - intros i Hi.
    destruct (S6_surj p Hp i Hi) as [j [Hj Hpj]].
    destruct (S6_surj q Hq j Hj) as [k [Hk Hqk]].
    exists k. split; [exact Hk |].
    unfold pcomp.
    rewrite (nth_indep (map (fun a => nth a p 0%nat) q) 0%nat (nth 0 p 0%nat))
      by (rewrite length_map, (S6_length6 q Hq); exact Hk).
    rewrite (map_nth (fun a => nth a p 0%nat) q 0%nat k).
    rewrite Hqk. exact Hpj.
Qed.

(** Associativity of composition, abstractly, from entry bounds. *)
Lemma pcomp_assoc :
  forall p q r, In p S6list -> In q S6list -> In r S6list ->
  pcomp (pcomp p q) r = pcomp p (pcomp q r).
Proof.
  intros p q r Hp Hq Hr.
  unfold pcomp.
  rewrite map_map.
  apply map_ext_in.
  intros i Hi.
  assert (Hlt : (i < 6)%nat).
  { destruct (In_nth r i 0%nat Hi) as [k [Hk Hnth]].
    rewrite (S6_length6 r Hr) in Hk.
    rewrite <- Hnth.
    apply (S6_entries_lt r Hr k Hk). }
  rewrite (nth_indep (map (fun j => nth j p 0%nat) q) 0%nat (nth 0 p 0%nat))
    by (rewrite length_map, (S6_length6 q Hq); exact Hlt).
  rewrite (map_nth (fun j => nth j p 0%nat) q 0%nat i).
  reflexivity.
Qed.

(* generation by closure computation -- fueled left-products stay inside any composition-closed superset; vm facts certify that transpositions generate S6 and two squares generate A6. *)

Definition transp (i j : nat) : list nat :=
  map (fun k => if Nat.eqb k i then j else if Nat.eqb k j then i else k) (seq 0 6).

Definition tlist : list (list nat) :=
  flat_map (fun i => map (transp i) (seq (Datatypes.S i) (5 - i))) (seq 0 6).

Lemma tlist_length : length tlist = 15%nat.
Proof. vm_compute. reflexivity. Qed.

(** A depth-6 six-way trie gating duplicate insertion during closure. *)
Inductive trie6 : Type :=
| TLf : bool -> trie6
| TNd : trie6 -> trie6 -> trie6 -> trie6 -> trie6 -> trie6 -> trie6.

Fixpoint trie_mem (p : list nat) (t : trie6) : bool :=
  match t with
  | TLf b => match p with nil => b | _ => false end
  | TNd c0 c1 c2 c3 c4 c5 =>
      match p with
      | nil => false
      | i :: p' =>
          trie_mem p' (match i with
                       | 0%nat => c0 | 1%nat => c1 | 2%nat => c2
                       | 3%nat => c3 | 4%nat => c4 | _ => c5 end)
      end
  end.

Fixpoint trie_empty (d : nat) : trie6 :=
  match d with
  | O => TLf false
  | Datatypes.S d' =>
      let e := trie_empty d' in TNd e e e e e e
  end.

Fixpoint trie_add (p : list nat) (t : trie6) : trie6 :=
  match t with
  | TLf _ => match p with nil => TLf true | _ => t end
  | TNd c0 c1 c2 c3 c4 c5 =>
      match p with
      | nil => t
      | i :: p' =>
          match i with
          | 0%nat => TNd (trie_add p' c0) c1 c2 c3 c4 c5
          | 1%nat => TNd c0 (trie_add p' c1) c2 c3 c4 c5
          | 2%nat => TNd c0 c1 (trie_add p' c2) c3 c4 c5
          | 3%nat => TNd c0 c1 c2 (trie_add p' c3) c4 c5
          | 4%nat => TNd c0 c1 c2 c3 (trie_add p' c4) c5
          | _ => TNd c0 c1 c2 c3 c4 (trie_add p' c5)
          end
      end
  end.

Definition gcstate : Type := (list (list nat) * trie6)%type.

Definition gc_insert (pc : list nat) (st : gcstate) : gcstate :=
  if trie_mem pc (snd st) then st else (pc :: fst st, trie_add pc (snd st)).

Definition gen_round (gens : list (list nat)) (st : gcstate) : gcstate :=
  fold_left (fun st1 g =>
    fold_left (fun st2 c => gc_insert (pcomp g c) st2) (fst st) st1) gens st.

Fixpoint gen_closure (fuel : nat) (gens : list (list nat)) (st : gcstate) : gcstate :=
  match fuel with
  | O => st
  | Datatypes.S f => gen_closure f gens (gen_round gens st)
  end.

Definition gc_seed (cur : list (list nat)) : gcstate :=
  (cur, fold_left (fun t p => trie_add p t) cur (trie_empty 6)).

(** Closure members are words: they stay inside any composition-closed set containing the seed. *)
Lemma fold_insert_in :
  forall (P : list nat -> Prop) (g : list nat) (items : list (list nat))
         (st : gcstate),
  (forall c, In c items -> P (pcomp g c)) ->
  Forall P (fst st) ->
  Forall P (fst (fold_left (fun st2 c => gc_insert (pcomp g c) st2) items st)).
Proof.
  intros P g items. induction items as [|c items IH]; intros st Hitems Hst;
    cbn [fold_left].
  - exact Hst.
  - apply IH.
    + intros c' Hc'. apply Hitems. right. exact Hc'.
    + unfold gc_insert.
      destruct (trie_mem (pcomp g c) (snd st)).
      * exact Hst.
      * cbn [fst].
        constructor; [apply Hitems; left; reflexivity | exact Hst].
Qed.

Lemma gen_round_in :
  forall (P : list nat -> Prop) gens st,
  (forall g c, P g -> P c -> P (pcomp g c)) ->
  Forall P gens -> Forall P (fst st) ->
  Forall P (fst (gen_round gens st)).
Proof.
  intros P gens st Hcomp Hgens Hst.
  unfold gen_round.
  assert (Hgen : forall gs st1, Forall P gs -> Forall P (fst st1) ->
    Forall P (fst (fold_left (fun st2 g =>
      fold_left (fun st3 c => gc_insert (pcomp g c) st3) (fst st) st2) gs st1))).
  { induction gs as [|g gs IHgs]; intros st1 Hgs Hst1; cbn [fold_left].
    - exact Hst1.
    - inversion Hgs; subst.
      apply IHgs; [assumption |].
      apply fold_insert_in; [| exact Hst1].
      intros c Hc.
      apply Hcomp; [assumption |].
      exact (proj1 (Forall_forall P (fst st)) Hst c Hc). }
  apply Hgen; [exact Hgens | exact Hst].
Qed.

Lemma gen_closure_in :
  forall (P : list nat -> Prop) fuel gens st,
  (forall g c, P g -> P c -> P (pcomp g c)) ->
  Forall P gens -> Forall P (fst st) ->
  Forall P (fst (gen_closure fuel gens st)).
Proof.
  intros P fuel. induction fuel as [|f IH]; intros gens st Hcomp Hgens Hst;
    cbn [gen_closure].
  - exact Hst.
  - apply IH; [exact Hcomp | exact Hgens |].
    apply gen_round_in; assumption.
Qed.

Lemma gc_seed_fst : forall cur, fst (gc_seed cur) = cur.
Proof. reflexivity. Qed.

(** The two concrete square generators of A6. *)
Definition sq_root1 : list nat := (1 :: 2 :: 3 :: 4 :: 5 :: 0 :: nil)%nat.
Definition sq_root2 : list nat := (1 :: 2 :: 3 :: 4 :: 0 :: 5 :: nil)%nat.

(** THE GENERATION FACTS. *)
Lemma transpositions_generate_S6 :
  forallb (fun p => memb p (fst (gen_closure 7 tlist (gc_seed (pid6 :: tlist)))))
    S6list = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma squares_generate_A6 :
  forallb (fun p => memb p
    (fst (gen_closure 40 (pcomp sq_root1 sq_root1 :: pcomp sq_root2 sq_root2 :: nil)
       (gc_seed (pid6 :: pcomp sq_root1 sq_root1 :: pcomp sq_root2 sq_root2 :: nil)))))
    A6list = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma sq_roots_in_S6 : In sq_root1 S6list /\ In sq_root2 S6list.
Proof.
  split; apply memb_spec; vm_compute; reflexivity.
Qed.

Lemma squares_are_even :
  forallb (fun p => memb (pcomp p p) A6list) S6list = true.
Proof. vm_compute. reflexivity. Qed.

Lemma A6_sub_S6 : incl A6list S6list.
Proof.
  intros p Hp. unfold A6list in Hp.
  apply filter_In in Hp. exact (proj1 Hp).
Qed.

(* finite group theory on permutation lists -- pgroups and inverses from cycling powers; Lagrange is projected from the coset decomposition below. *)

Record pgroup (G : list (list nat)) : Prop := mkPgroup {
  pg_S6 : incl G S6list;
  pg_nd : NoDup G;
  pg_id : In pid6 G;
  pg_comp : forall p q, In p G -> In q G -> In (pcomp p q) G
}.

Fixpoint ppow (p : list nat) (n : nat) : list nat :=
  match n with
  | O => pid6
  | Datatypes.S k => pcomp p (ppow p k)
  end.

Lemma ppow_in_S6 : forall p n, In p S6list -> In (ppow p n) S6list.
Proof.
  intros p n Hp. induction n as [|n IH]; cbn [ppow].
  - exact S6_id_in.
  - apply S6_comp_in; assumption.
Qed.

Lemma ppow_in_G : forall G p n, pgroup G -> In p G -> In (ppow p (Datatypes.S n)) G.
Proof.
  intros G p n HG Hp. induction n as [|n IH]; cbn [ppow].
  - rewrite S6_id_right; [exact Hp | apply (pg_S6 G HG); exact Hp].
  - apply (pg_comp G HG); [exact Hp |].
    exact IH.
Qed.

Lemma pcomp_cancel_l : forall p u v,
  In p S6list -> In u S6list -> In v S6list ->
  pcomp p u = pcomp p v -> u = v.
Proof.
  intros p u v Hp Hu Hv He.
  assert (Hchain : forall w, In w S6list -> pcomp (pinv p) (pcomp p w) = w).
  { intros w Hw.
    rewrite <- pcomp_assoc;
      [| apply S6_inv_in; exact Hp | exact Hp | exact Hw].
    rewrite S6_inv_left by exact Hp.
    apply S6_id_left. exact Hw. }
  rewrite <- (Hchain u Hu), <- (Hchain v Hv), He.
  reflexivity.
Qed.

Lemma ppow_add : forall p m n, In p S6list ->
  ppow p (m + n) = pcomp (ppow p m) (ppow p n).
Proof.
  intros p m n Hp. induction m as [|m IH]; cbn [ppow Nat.add].
  - rewrite S6_id_left; [reflexivity | apply ppow_in_S6; exact Hp].
  - rewrite IH.
    rewrite pcomp_assoc;
      [reflexivity | exact Hp | apply ppow_in_S6; exact Hp | apply ppow_in_S6; exact Hp].
Qed.

(** Extracting a collision from a too-long list. *)
(** INVERSES: the powers of a group element cycle back through the identity. *)
Lemma pgroup_inv : forall G p, pgroup G -> In p G -> In (pinv p) G.
Proof.
  intros G p HG Hp.
  assert (HpS : In p S6list) by (apply (pg_S6 G HG); exact Hp).
  set (powers := map (fun k => ppow p (Datatypes.S k)) (seq 0 721)).
  assert (Hlp : length powers = 721%nat)
    by (unfold powers; rewrite length_map, length_seq; reflexivity).
  assert (Hincl : incl powers S6list).
  { intros q Hq. unfold powers in Hq.
    apply in_map_iff in Hq. destruct Hq as [k [Hqk _]].
    rewrite <- Hqk. apply ppow_in_S6. exact HpS. }
  destruct (long_list_collision pid6 powers S6list Hincl
              ltac:(rewrite Hlp, S6list_length; lia)) as [i [j [Hij [Hjl He]]]].
  assert (Hnth : forall m, (m < 721)%nat -> nth m powers pid6 = ppow p (Datatypes.S m)).
  { intros m Hm. unfold powers.
    rewrite (nth_indep _ pid6 (ppow p (Datatypes.S 0%nat)))
      by (rewrite length_map, length_seq; exact Hm).
    rewrite (map_nth (fun k => ppow p (Datatypes.S k)) (seq 0 721) 0%nat m).
    rewrite seq_nth by exact Hm.
    reflexivity. }
  rewrite Hlp in Hjl.
  rewrite (Hnth i ltac:(lia)), (Hnth j ltac:(lia)) in He.
  set (d := (j - i)%nat).
  assert (Hd1 : (1 <= d)%nat) by (unfold d; lia).
  assert (Hcyc : ppow p d = pid6).
  { assert (Hsplit : (Datatypes.S j = Datatypes.S i + d)%nat) by (unfold d; lia).
    rewrite Hsplit, (ppow_add p (Datatypes.S i) d HpS) in He.
    assert (He2 : pcomp (ppow p (Datatypes.S i)) (ppow p d)
                  = pcomp (ppow p (Datatypes.S i)) pid6).
    { rewrite S6_id_right by (apply ppow_in_S6; exact HpS).
      symmetry. exact He. }
    apply (pcomp_cancel_l (ppow p (Datatypes.S i)));
      [apply ppow_in_S6; exact HpS | apply ppow_in_S6; exact HpS
       | exact S6_id_in | exact He2]. }
  assert (Hstep : pcomp p (ppow p (d - 1)) = pid6).
  { replace (pcomp p (ppow p (d - 1))) with (ppow p (Datatypes.S (d - 1)))
      by reflexivity.
    replace (Datatypes.S (d - 1))%nat with d by lia.
    exact Hcyc. }
  assert (Hinv_eq : pinv p = ppow p (d - 1)).
  { apply (pcomp_cancel_l p (pinv p) (ppow p (d - 1)) HpS);
      [apply S6_inv_in; exact HpS | apply ppow_in_S6; exact HpS |].
    rewrite S6_inv_right by exact HpS.
    symmetry. exact Hstep. }
  rewrite Hinv_eq.
  destruct (Nat.eq_dec d 1%nat) as [-> | Hd2].
  - cbn [Nat.sub ppow]. apply (pg_id G HG).
  - replace (d - 1)%nat with (Datatypes.S (d - 2)) by lia.
    apply ppow_in_G; [exact HG | exact Hp].
Qed.

(** Left translation is injective; a coset has the size of the subgroup. *)
Lemma coset_NoDup : forall (g : list nat) (H : list (list nat)),
  In g S6list -> incl H S6list -> NoDup H ->
  NoDup (map (pcomp g) H).
Proof.
  intros g H Hg HHS Hnd.
  apply NoDup_map_inj_gen; [| exact Hnd].
  intros x y Hx Hy He.
  apply (pcomp_cancel_l g x y Hg (HHS x Hx) (HHS y Hy) He).
Qed.

(** Splitting a NoDup list by a membership test preserves counting. *)
Lemma filter_partition_length : forall (f : list nat -> bool) (l : list (list nat)),
  length l = (length (filter f l) + length (filter (fun x => negb (f x)) l))%nat.
Proof.
  intros f l. induction l as [|a l IH]; cbn [filter length].
  - reflexivity.
  - destruct (f a); cbn [negb length]; lia.
Qed.

(* parity -- the vm sign table, parity of inverses, and the dichotomy: a group between A6 and S6 is one of the two. *)

Lemma parity_pcomp_table :
  forallb (fun p => forallb (fun q =>
    Bool.eqb (even_perm (pcomp p q)) (Bool.eqb (even_perm p) (even_perm q)))
    S6list) S6list = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma parity_pinv_table :
  forallb (fun p => Bool.eqb (even_perm (pinv p)) (even_perm p)) S6list = true.
Proof. vm_compute. reflexivity. Qed.

Lemma parity_pcomp : forall p q, In p S6list -> In q S6list ->
  even_perm (pcomp p q) = Bool.eqb (even_perm p) (even_perm q).
Proof.
  intros p q Hp Hq.
  apply Bool.eqb_prop.
  pose proof (S6_fact_pointwise _ parity_pcomp_table p Hp) as Hrow.
  exact (proj1 (forallb_forall _ S6list) Hrow q Hq).
Qed.

Lemma parity_pinv : forall p, In p S6list ->
  even_perm (pinv p) = even_perm p.
Proof.
  intros p Hp.
  apply Bool.eqb_prop.
  exact (S6_fact_pointwise _ parity_pinv_table p Hp).
Qed.

Lemma A6list_iff : forall q, In q A6list <-> In q S6list /\ even_perm q = true.
Proof. intro q. unfold A6list. apply filter_In. Qed.

Lemma pid6_even : even_perm pid6 = true.
Proof. vm_compute. reflexivity. Qed.

(** THE DICHOTOMY: a group containing the alternating set is A6 or S6. *)
Lemma between_A6_S6 : forall (P : list (list nat)),
  pgroup P -> incl A6list P ->
  (incl P A6list /\ incl A6list P) \/ (incl P S6list /\ incl S6list P).
Proof.
  intros P HP HAP.
  destruct (classic (exists h, In h P /\ even_perm h = false)) as [[h [HhP Hodd]] | Hno].
  - right.
    split; [exact (pg_S6 P HP) |].
    intros q Hq.
    assert (HhS : In h S6list) by (apply (pg_S6 P HP); exact HhP).
    destruct (even_perm q) eqn:Eq.
    + apply HAP. apply A6list_iff. split; assumption.
    + assert (Hqin : q = pcomp h (pcomp (pinv h) q)).
      { rewrite <- pcomp_assoc;
          [| exact HhS | apply S6_inv_in; exact HhS | exact Hq].
        rewrite S6_inv_right by exact HhS.
        rewrite S6_id_left by exact Hq.
        reflexivity. }
      rewrite Hqin.
      apply (pg_comp P HP); [exact HhP |].
      apply HAP. apply A6list_iff.
      split.
      * apply S6_comp_in; [apply S6_inv_in; exact HhS | exact Hq].
      * rewrite parity_pcomp; [| apply S6_inv_in; exact HhS | exact Hq].
        rewrite parity_pinv by exact HhS.
        rewrite Hodd, Eq. reflexivity.
  - left.
    split; [| exact HAP].
    intros q Hq.
    apply A6list_iff.
    split; [apply (pg_S6 P HP); exact Hq |].
    destruct (even_perm q) eqn:Eq; [reflexivity |].
    exfalso. apply Hno. exists q. split; assumption.
Qed.

(** The even part of a group is a group, of size at least half. *)
Lemma even_part_group : forall (P : list (list nat)),
  pgroup P ->
  pgroup (filter even_perm P) /\
  (length P <= 2 * length (filter even_perm P))%nat /\
  incl (filter even_perm P) A6list.
Proof.
  intros P HP.
  set (Pe := filter even_perm P).
  set (Po := filter (fun x => negb (even_perm x)) P).
  assert (HPe_g : pgroup Pe).
  { constructor.
    - intros p Hp. unfold Pe in Hp. apply filter_In in Hp.
      apply (pg_S6 P HP). exact (proj1 Hp).
    - unfold Pe. apply NoDup_filter. exact (pg_nd P HP).
    - unfold Pe. apply filter_In.
      split; [exact (pg_id P HP) | exact pid6_even].
    - intros p q Hp Hq.
      unfold Pe in Hp, Hq |- *.
      apply filter_In in Hp. apply filter_In in Hq.
      destruct Hp as [HpP Hpe]. destruct Hq as [HqP Hqe].
      apply filter_In.
      split; [apply (pg_comp P HP); assumption |].
      rewrite parity_pcomp;
        [| apply (pg_S6 P HP); exact HpP | apply (pg_S6 P HP); exact HqP].
      rewrite Hpe, Hqe. reflexivity. }
  split; [exact HPe_g | split].
  - destruct (classic (exists h, In h Po)) as [[h HhPo] | Hno].
    + assert (HhP : In h P /\ even_perm h = false).
      { unfold Po in HhPo. apply filter_In in HhPo.
        destruct HhPo as [H1 H2].
        rewrite negb_true_iff in H2.
        split; assumption. }
      destruct HhP as [HhP Hodd].
      assert (HhS : In h S6list) by (apply (pg_S6 P HP); exact HhP).
      assert (Hinj : (length Po <= length Pe)%nat).
      { assert (Hmap : incl (map (pcomp (pinv h)) Po) Pe).
        { intros x Hx. apply in_map_iff in Hx.
          destruct Hx as [o [Hxo Ho]].
          unfold Po in Ho. apply filter_In in Ho.
          destruct Ho as [HoP Hoodd].
          rewrite negb_true_iff in Hoodd.
          unfold Pe. apply filter_In.
          split.
          - rewrite <- Hxo.
            apply (pg_comp P HP); [| exact HoP].
            apply pgroup_inv; [exact HP | exact HhP].
          - rewrite <- Hxo.
            rewrite parity_pcomp;
              [| apply S6_inv_in; exact HhS | apply (pg_S6 P HP); exact HoP].
            rewrite parity_pinv by exact HhS.
            rewrite Hodd, Hoodd. reflexivity. }
        assert (Hmnd : NoDup (map (pcomp (pinv h)) Po)).
        { apply NoDup_map_inj_gen; [| unfold Po; apply NoDup_filter; exact (pg_nd P HP)].
          intros x y Hx Hy He.
          apply (pcomp_cancel_l (pinv h) x y);
            [apply S6_inv_in; exact HhS
            | apply (pg_S6 P HP); unfold Po in Hx; apply filter_In in Hx; exact (proj1 Hx)
            | apply (pg_S6 P HP); unfold Po in Hy; apply filter_In in Hy; exact (proj1 Hy)
            | exact He]. }
        pose proof (NoDup_incl_length Hmnd Hmap) as Hle.
        rewrite length_map in Hle. exact Hle. }
      pose proof (filter_partition_length even_perm P) as Hpart.
      fold Pe Po in Hpart. lia.
    + assert (HPo0 : length Po = 0%nat).
      { destruct Po as [|x Po']; [reflexivity |].
        exfalso. apply Hno. exists x. left. reflexivity. }
      pose proof (filter_partition_length even_perm P) as Hpart.
      fold Pe Po in Hpart. lia.
  - intros p Hp. unfold Pe in Hp. apply filter_In in Hp.
    apply A6list_iff.
    split; [apply (pg_S6 P HP); exact (proj1 Hp) | exact (proj2 Hp)].
Qed.


Lemma A6_pgroup : pgroup A6list.
Proof.
  constructor.
  - exact A6_sub_S6.
  - unfold A6list. apply NoDup_filter.
    apply distinctb_NoDup. vm_compute. reflexivity.
  - apply A6list_iff. split; [exact S6_id_in | exact pid6_even].
  - intros p q Hp Hq.
    apply A6list_iff in Hp. apply A6list_iff in Hq.
    destruct Hp as [HpS Hpe]. destruct Hq as [HqS Hqe].
    apply A6list_iff.
    split; [apply S6_comp_in; assumption |].
    rewrite parity_pcomp by assumption.
    rewrite Hpe, Hqe. reflexivity.
Qed.

Lemma S6_pgroup : pgroup S6list.
Proof.
  constructor.
  - apply incl_refl.
  - apply distinctb_NoDup. vm_compute. reflexivity.
  - exact S6_id_in.
  - exact S6_comp_in.
Qed.

(* coset decomposition with representatives, product inverses, and utilities for the action argument. *)

Lemma pinv_pcomp : forall a b, In a S6list -> In b S6list ->
  pinv (pcomp a b) = pcomp (pinv b) (pinv a).
Proof.
  intros a b Ha Hb.
  assert (HabS : In (pcomp a b) S6list) by (apply S6_comp_in; assumption).
  apply (pcomp_cancel_l (pcomp a b) (pinv (pcomp a b)) (pcomp (pinv b) (pinv a))
           HabS (S6_inv_in _ HabS)).
  - apply S6_comp_in; apply S6_inv_in; assumption.
  - rewrite S6_inv_right by exact HabS.
    rewrite pcomp_assoc;
      [| exact Ha | exact Hb
       | apply S6_comp_in; apply S6_inv_in; assumption].
    rewrite <- (pcomp_assoc b (pinv b) (pinv a));
      [| exact Hb | apply S6_inv_in; exact Hb | apply S6_inv_in; exact Ha].
    rewrite S6_inv_right by exact Hb.
    rewrite S6_id_left by (apply S6_inv_in; exact Ha).
    rewrite S6_inv_right by exact Ha.
    reflexivity.
Qed.

Lemma nonid_element : forall (K : list (list nat)),
  NoDup K -> (2 <= length K)%nat ->
  exists g, In g K /\ g <> pid6.
Proof.
  intros K Hnd Hlen.
  destruct K as [|a [|b K']]; cbn [length] in Hlen; try lia.
  inversion Hnd; subst.
  destruct (list_eq_dec Nat.eq_dec a pid6) as [-> | Hne].
  - exists b.
    split; [right; left; reflexivity |].
    intro E. subst b. apply H1. left. reflexivity.
  - exists a. split; [left; reflexivity | exact Hne].
Qed.

(** THE COSET DECOMPOSITION: representatives with the identity first. *)
Lemma coset_decomp : forall (G H : list (list nat)),
  pgroup G -> pgroup H -> incl H G ->
  exists reps : list (list nat),
    (1 <= length reps)%nat /\
    nth 0 reps pid6 = pid6 /\
    incl reps G /\
    length G = (length reps * length H)%nat /\
    (forall x, In x G -> exists i h, (i < length reps)%nat /\
       In h H /\ x = pcomp (nth i reps pid6) h) /\
    (forall i j h h', (i < length reps)%nat -> (j < length reps)%nat ->
       In h H -> In h' H ->
       pcomp (nth i reps pid6) h = pcomp (nth j reps pid6) h' -> i = j).
Proof.
  intros G H HG HH HHG.
  assert (HH1 : (1 <= length H)%nat).
  { pose proof (pg_id H HH) as Hid.
    destruct H as [|h H']; [contradiction | cbn [length]; lia]. }
  assert (Hpeel : forall n (R : list (list nat)),
    (length R <= n)%nat ->
    NoDup R -> incl R G ->
    (forall x h, In x R -> In h H -> In (pcomp x h) R) ->
    exists reps : list (list nat),
      incl reps R /\
      length R = (length reps * length H)%nat /\
      (forall x, In x R -> exists i h, (i < length reps)%nat /\
         In h H /\ x = pcomp (nth i reps pid6) h) /\
      (forall i j h h', (i < length reps)%nat -> (j < length reps)%nat ->
         In h H -> In h' H ->
         pcomp (nth i reps pid6) h = pcomp (nth j reps pid6) h' -> i = j) /\
      (forall r0, R = r0 :: tl R -> nth 0 reps pid6 = r0 \/ reps = nil)).
  { intro n. induction n as [|n IHn]; intros R Hlen Hnd Hincl Hsat.
    - exists nil.
      destruct R; [| cbn [length] in Hlen; lia].
      repeat split.
      + intros x Hx. contradiction.
      + intros x Hx. contradiction.
      + intros i j h h' Hi. cbn [length] in Hi. lia.
      + intros r0 Hr0. right. reflexivity.
    - destruct R as [|r R'] eqn:ER; [| rewrite <- ER in * ].
      + exists nil.
        repeat split.
        * intros x Hx. contradiction.
        * intros x Hx. contradiction.
        * intros i j h h' Hi. cbn [length] in Hi. lia.
        * intros r0 Hr0. right. reflexivity.
      + assert (HrR : In r R) by (rewrite ER; left; reflexivity).
        assert (HrS : In r S6list) by (apply (pg_S6 G HG); apply Hincl; exact HrR).
        set (Cst := map (pcomp r) H).
        assert (HCnd : NoDup Cst).
        { apply coset_NoDup; [exact HrS | | exact (pg_nd H HH)].
          intros h Hh. apply (pg_S6 G HG). apply HHG. exact Hh. }
        assert (HClen : length Cst = length H)
          by (unfold Cst; apply length_map).
        assert (HCR : incl Cst R).
        { intros c Hc. unfold Cst in Hc.
          apply in_map_iff in Hc. destruct Hc as [h [Hch Hh]].
          rewrite <- Hch. apply Hsat; assumption. }
        set (R'' := filter (fun x => negb (memb x Cst)) R).
        assert (HinC_iff : forall x, memb x Cst = true <-> In x Cst)
          by (intro x; apply memb_spec).
        assert (HR''len : length R = (length H + length R'')%nat).
        { pose proof (filter_partition_length (fun x => memb x Cst) R) as Hpart.
          assert (Hfin : length (filter (fun x => memb x Cst) R) = length Cst).
          { apply NoDup_same_set_length.
            - apply NoDup_filter. exact Hnd.
            - exact HCnd.
            - intros x Hx. apply filter_In in Hx.
              destruct Hx as [_ Hx]. apply HinC_iff. exact Hx.
            - intros x Hx.
              apply filter_In.
              split; [apply HCR; exact Hx | apply HinC_iff; exact Hx]. }
          unfold R''. rewrite Hpart, Hfin, HClen. reflexivity. }
        assert (HR''nd : NoDup R'') by (unfold R''; apply NoDup_filter; exact Hnd).
        assert (HR''incl : incl R'' G).
        { intros x Hx. unfold R'' in Hx.
          apply filter_In in Hx. apply Hincl. exact (proj1 Hx). }
        assert (HR''sat : forall x h, In x R'' -> In h H -> In (pcomp x h) R'').
        { intros x h Hx Hh.
          unfold R'' in Hx. apply filter_In in Hx.
          destruct Hx as [HxR Hxnot].
          unfold R''. apply filter_In.
          split; [apply Hsat; assumption |].
          rewrite negb_true_iff in Hxnot |- *.
          destruct (memb (pcomp x h) Cst) eqn:Ememb; [| reflexivity].
          exfalso.
          apply (proj1 (HinC_iff (pcomp x h))) in Ememb.
          unfold Cst in Ememb.
          apply in_map_iff in Ememb.
          destruct Ememb as [h' [Heq Hh']].
          assert (HxS : In x S6list)
            by (apply (pg_S6 G HG); apply Hincl; exact HxR).
          assert (HhS : In h S6list)
            by (apply (pg_S6 G HG); apply HHG; exact Hh).
          assert (Hh'S : In h' S6list)
            by (apply (pg_S6 G HG); apply HHG; exact Hh').
          assert (Hxeq : x = pcomp r (pcomp h' (pinv h))).
          { assert (Hstep : pcomp (pcomp x h) (pinv h) = pcomp (pcomp r h') (pinv h))
              by (rewrite Heq; reflexivity).
            rewrite pcomp_assoc in Hstep;
              [| exact HxS | exact HhS | apply S6_inv_in; exact HhS].
            rewrite S6_inv_right in Hstep by exact HhS.
            rewrite S6_id_right in Hstep by exact HxS.
            rewrite pcomp_assoc in Hstep;
              [| exact HrS | exact Hh'S | apply S6_inv_in; exact HhS].
            exact Hstep. }
          assert (Hmem : In (pcomp h' (pinv h)) H).
          { apply (pg_comp H HH); [exact Hh' |].
            apply pgroup_inv; [exact HH | exact Hh]. }
          assert (HxC : In x Cst).
          { unfold Cst. rewrite Hxeq.
            apply in_map. exact Hmem. }
          apply (proj2 (HinC_iff x)) in HxC.
          rewrite HxC in Hxnot. discriminate. }
        destruct (IHn R'' ltac:(lia) HR''nd HR''incl HR''sat)
          as [reps' [Hr'incl [Hr'len [Hr'cov [Hr'dis _]]]]].
        exists (r :: reps').
        repeat split.
        * intros x Hx.
          destruct Hx as [<- | Hx]; [exact HrR |].
          assert (HxR'' : In x R'') by (apply Hr'incl; exact Hx).
          unfold R'' in HxR''. apply filter_In in HxR''. exact (proj1 HxR'').
        * cbn [length]. rewrite HR''len, Hr'len. lia.
        * intros x Hx.
          destruct (memb x Cst) eqn:EC.
          { apply (proj1 (HinC_iff x)) in EC.
            unfold Cst in EC. apply in_map_iff in EC.
            destruct EC as [h [Hxh Hh]].
            exists 0%nat, h.
            repeat split; [cbn [length]; lia | exact Hh |].
            cbn [nth]. symmetry. exact Hxh. }
          { assert (HxR'' : In x R'').
            { unfold R''. apply filter_In.
              split; [exact Hx | rewrite EC; reflexivity]. }
            destruct (Hr'cov x HxR'') as [i [h [Hi [Hh Hxe]]]].
            exists (Datatypes.S i), h.
            repeat split; [cbn [length]; lia | exact Hh |].
            cbn [nth]. exact Hxe. }
        * intros i j h h' Hi Hj Hh Hh' He.
          destruct i as [|i']; destruct j as [|j'].
          { reflexivity. }
          { exfalso.
            cbn [nth] in He.
            assert (Hrj : In (nth j' reps' pid6) R'').
            { apply Hr'incl. apply nth_In. cbn [length] in Hj. lia. }
            assert (Hin1 : In (pcomp (nth j' reps' pid6) h') R'')
              by (apply HR''sat; assumption).
            assert (Hin2 : In (pcomp r h) Cst)
              by (unfold Cst; apply in_map; exact Hh).
            rewrite He in Hin2.
            unfold R'' in Hin1. apply filter_In in Hin1.
            destruct Hin1 as [_ Hneg].
            rewrite negb_true_iff in Hneg.
            apply (proj2 (HinC_iff _)) in Hin2.
            rewrite Hin2 in Hneg. discriminate. }
          { exfalso.
            cbn [nth] in He.
            assert (Hri : In (nth i' reps' pid6) R'').
            { apply Hr'incl. apply nth_In. cbn [length] in Hi. lia. }
            assert (Hin1 : In (pcomp (nth i' reps' pid6) h) R'')
              by (apply HR''sat; assumption).
            assert (Hin2 : In (pcomp r h') Cst)
              by (unfold Cst; apply in_map; exact Hh').
            rewrite <- He in Hin2.
            unfold R'' in Hin1. apply filter_In in Hin1.
            destruct Hin1 as [_ Hneg].
            rewrite negb_true_iff in Hneg.
            apply (proj2 (HinC_iff _)) in Hin2.
            rewrite Hin2 in Hneg. discriminate. }
          { cbn [nth] in He.
            cbn [length] in Hi, Hj.
            f_equal.
            apply (Hr'dis i' j' h h'); [lia | lia | exact Hh | exact Hh' | exact He]. }
        * intros r0 Hr0.
          left.
          rewrite ER in Hr0.
          injection Hr0 as Hhead.
          cbn [nth]. exact Hhead. }
  set (Gid := pid6 :: filter (fun x => negb (eqb_listnat x pid6)) G).
  assert (HGid_set : forall x, In x Gid <-> In x G).
  { intro x. unfold Gid. split.
    - intros [<- | Hx]; [exact (pg_id G HG) |].
      apply filter_In in Hx. exact (proj1 Hx).
    - intro Hx.
      destruct (list_eq_dec Nat.eq_dec x pid6) as [-> | Hne];
        [left; reflexivity |].
      right. apply filter_In.
      split; [exact Hx |].
      rewrite negb_true_iff.
      destruct (eqb_listnat x pid6) eqn:E; [| reflexivity].
      apply eqb_listnat_spec in E. contradiction.
  }
  assert (HGid_nd : NoDup Gid).
  { unfold Gid. constructor.
    - intro Hc. apply filter_In in Hc.
      destruct Hc as [_ Hc].
      rewrite negb_true_iff in Hc.
      assert (E : eqb_listnat pid6 pid6 = true)
        by (apply eqb_listnat_spec; reflexivity).
      rewrite E in Hc. discriminate.
    - apply NoDup_filter. exact (pg_nd G HG). }
  assert (HGid_len : length Gid = length G).
  { apply NoDup_same_set_length;
      [exact HGid_nd | exact (pg_nd G HG)
       | intros x Hx; apply HGid_set; exact Hx
       | intros x Hx; apply HGid_set; exact Hx]. }
  destruct (Hpeel (length Gid) Gid (Nat.le_refl _) HGid_nd
              ltac:(intros x Hx; apply (HGid_set x) in Hx; exact Hx)
              ltac:(intros x h Hx Hh; apply HGid_set;
                    apply (pg_comp G HG);
                    [apply (HGid_set x); exact Hx | apply HHG; exact Hh]))
    as [reps [Hrincl [Hrlen [Hrcov [Hrdis Hrhead]]]]].
  exists reps.
  assert (Hreps1 : (1 <= length reps)%nat).
  { destruct reps as [|r0 reps']; [| cbn [length]; lia].
    exfalso.
    cbn [length] in Hrlen.
    assert (HGlen : length G = 0%nat) by lia.
    pose proof (pg_id G HG) as Hid.
    destruct G; [contradiction | cbn [length] in HGlen; lia]. }
  repeat split.
  - exact Hreps1.
  - destruct (Hrhead pid6 eq_refl) as [E | E].
    + exact E.
    + exfalso. rewrite E in Hreps1. cbn [length] in Hreps1. lia.
  - intros x Hx. apply HGid_set. apply Hrincl. exact Hx.
  - rewrite <- HGid_len. exact Hrlen.
  - intros x Hx.
    apply (Hrcov x). apply HGid_set. exact Hx.
  - intros i j h h' Hi Hj Hh Hh' He.
    apply (Hrdis i j h h'); assumption.
Qed.

(** LAGRANGE: the subgroup size divides the group size, projected from the coset decomposition. *)
Lemma lagrange : forall (G H : list (list nat)),
  pgroup G -> pgroup H -> incl H G ->
  exists k, length G = (k * length H)%nat.
Proof.
  intros G H HG HH HHG.
  destruct (coset_decomp G H HG HH HHG) as [reps [_ [_ [_ [Hlen _]]]]].
  exists (length reps).
  exact Hlen.
Qed.

(* the class equation and simplicity of A6 -- six vm conjugacy classes, and the subset sums of class sizes admit only the full group. *)

Definition conj_of (h g : list nat) : list nat := pcomp h (pcomp g (pinv h)).

Definition cls (r : list nat) : list (list nat) :=
  nodup (list_eq_dec Nat.eq_dec) (map (fun h => conj_of h r) A6list).

Definition cls1 : list (list nat) := cls (1 :: 2 :: 0 :: 3 :: 4 :: 5 :: nil)%nat.
Definition cls2 : list (list nat) := cls (1 :: 2 :: 0 :: 4 :: 5 :: 3 :: nil)%nat.
Definition cls3 : list (list nat) := cls (1 :: 0 :: 3 :: 2 :: 4 :: 5 :: nil)%nat.
Definition cls4 : list (list nat) := cls (1 :: 2 :: 3 :: 0 :: 5 :: 4 :: nil)%nat.
Definition cls5 : list (list nat) := cls (1 :: 2 :: 3 :: 4 :: 0 :: 5 :: nil)%nat.
Definition cls6 : list (list nat) := cls (2 :: 3 :: 4 :: 0 :: 1 :: 5 :: nil)%nat.

Definition all_cls : list (list (list nat)) :=
  cls1 :: cls2 :: cls3 :: cls4 :: cls5 :: cls6 :: nil.

(** Membership in a class is exactly conjugacy to any of its members. *)
Lemma cls_from_rep : forall r x, In x (cls r) ->
  exists h, In h A6list /\ x = conj_of h r.
Proof.
  intros r x Hx. unfold cls in Hx.
  apply nodup_In in Hx.
  apply in_map_iff in Hx.
  destruct Hx as [h [Hxh Hh]].
  exists h. split; [exact Hh | symmetry; exact Hxh].
Qed.

Lemma cls_to_rep : forall r h, In h A6list -> In (conj_of h r) (cls r).
Proof.
  intros r h Hh. unfold cls.
  apply nodup_In.
  apply in_map_iff.
  exists h. split; [reflexivity | exact Hh].
Qed.

(** vm facts about the six classes. *)
Lemma cls_cover :
  forallb (fun g => eqb_listnat g pid6
    || memb g cls1 || memb g cls2 || memb g cls3
    || memb g cls4 || memb g cls5 || memb g cls6) A6list = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cls_in_A6 :
  forallb (fun C => forallb (fun x => memb x A6list) C) all_cls = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cls_no_id :
  forallb (fun C => negb (memb pid6 C)) all_cls = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cls_disjoint :
  forallb (fun C => forallb (fun C' =>
    (if list_eq_dec (list_eq_dec Nat.eq_dec) C C' then true
     else forallb (fun x => negb (memb x C')) C)) all_cls) all_cls = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cls_sizes_ok :
  forallb (fun s =>
    (Nat.eqb s 0) || (Nat.eqb (Datatypes.S s) 360)
    || negb (Nat.eqb (360 mod (Datatypes.S s)) 0))
    (fold_right (fun x acc => acc ++ map (Nat.add x) acc)
       (0%nat :: nil) (map (@length (list nat)) all_cls)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Distinct classes are distinct lists. *)
Lemma all_cls_distinct : NoDup all_cls.
Proof.
  assert (Hlen : map (@length (list nat)) all_cls
                 = (40 :: 40 :: 45 :: 90 :: 72 :: 72 :: nil)%nat)
    by (vm_compute; reflexivity).
  assert (Hfirst : forallb (fun C => forallb (fun C' =>
    (if list_eq_dec (list_eq_dec Nat.eq_dec) C C' then true
     else negb (eqb_listnat (hd pid6 C) (hd pid6 C')))) all_cls) all_cls = true)
    by (vm_compute; reflexivity).
  assert (Hne : forall C C', In C all_cls -> In C' all_cls -> C <> C' ->
    hd pid6 C <> hd pid6 C').
  { intros C C' HC HC' Hne.
    pose proof (proj1 (forallb_forall _ all_cls) Hfirst C HC) as Hrow.
    pose proof (proj1 (forallb_forall _ all_cls) Hrow C' HC') as Hcell.
    cbv beta in Hcell.
    revert Hcell.
    destruct (list_eq_dec (list_eq_dec Nat.eq_dec) C C') as [E | _];
      [contradiction |].
    intro Hcell.
    rewrite negb_true_iff in Hcell.
    intro Hh. apply eqb_listnat_spec in Hh.
    rewrite Hh in Hcell. discriminate. }
  assert (Hpair : forall C C', In C all_cls -> In C' all_cls ->
    hd pid6 C = hd pid6 C' -> C = C').
  { intros C C' HC HC' Hh.
    destruct (list_eq_dec (list_eq_dec Nat.eq_dec) C C') as [E | Hne2];
      [exact E |].
    exfalso. exact (Hne C C' HC HC' Hne2 Hh). }
  assert (Hhd_nd : NoDup (map (hd pid6) all_cls))
    by (vm_compute;
        repeat constructor;
        cbn [In]; intuition discriminate).
  apply (NoDup_map_inv (hd pid6)).
  exact Hhd_nd.
Qed.

(** Conjugation composes: conjugating a conjugate is conjugating by the product. *)
Lemma conj_of_conj : forall h h0 r,
  In h S6list -> In h0 S6list -> In r S6list ->
  conj_of h (conj_of h0 r) = conj_of (pcomp h h0) r.
Proof.
  intros h h0 r Hh Hh0 Hr.
  assert (Hih : In (pinv h) S6list) by (apply S6_inv_in; exact Hh).
  assert (Hih0 : In (pinv h0) S6list) by (apply S6_inv_in; exact Hh0).
  assert (Hhh0 : In (pcomp h h0) S6list) by (apply S6_comp_in; assumption).
  assert (Hhh0r : In (pcomp (pcomp h h0) r) S6list) by (apply S6_comp_in; assumption).
  set (L := pcomp (pcomp (pcomp (pcomp h h0) r) (pinv h0)) (pinv h)).
  transitivity L.
  - unfold conj_of, L.
    rewrite <- (pcomp_assoc h (pcomp h0 (pcomp r (pinv h0))) (pinv h));
      [| exact Hh
       | apply S6_comp_in; [exact Hh0 | apply S6_comp_in; assumption]
       | exact Hih].
    f_equal.
    rewrite <- (pcomp_assoc h h0 (pcomp r (pinv h0)));
      [| exact Hh | exact Hh0 | apply S6_comp_in; assumption].
    rewrite <- (pcomp_assoc (pcomp h h0) r (pinv h0));
      [| exact Hhh0 | exact Hr | exact Hih0].
    reflexivity.
  - unfold conj_of, L.
    rewrite (pinv_pcomp h h0 Hh Hh0).
    rewrite <- (pcomp_assoc (pcomp h h0) r (pcomp (pinv h0) (pinv h)));
      [| exact Hhh0 | exact Hr | apply S6_comp_in; assumption].
    rewrite <- (pcomp_assoc (pcomp (pcomp h h0) r) (pinv h0) (pinv h));
      [| exact Hhh0r | exact Hih0 | exact Hih].
    reflexivity.
Qed.

Lemma cls_conj_closed : forall C, In C all_cls ->
  forall x h, In x C -> In h A6list -> In (conj_of h x) C.
Proof.
  intros C HC x h Hx Hh.
  assert (Hrep : exists r, In r S6list /\ C = cls r).
  { unfold all_cls in HC.
    cbn [In] in HC.
    destruct HC as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
      [ exists ((1 :: 2 :: 0 :: 3 :: 4 :: 5 :: nil)%nat)
      | exists ((1 :: 2 :: 0 :: 4 :: 5 :: 3 :: nil)%nat)
      | exists ((1 :: 0 :: 3 :: 2 :: 4 :: 5 :: nil)%nat)
      | exists ((1 :: 2 :: 3 :: 0 :: 5 :: 4 :: nil)%nat)
      | exists ((1 :: 2 :: 3 :: 4 :: 0 :: 5 :: nil)%nat)
      | exists ((2 :: 3 :: 4 :: 0 :: 1 :: 5 :: nil)%nat) ];
      (split; [apply memb_spec; vm_compute; reflexivity | reflexivity]).
  }
  destruct Hrep as [r [HrS ->]].
  destruct (cls_from_rep r x Hx) as [h0 [Hh0 Hxc]].
  rewrite Hxc.
  rewrite conj_of_conj;
    [| apply A6_sub_S6; exact Hh | apply A6_sub_S6; exact Hh0 | exact HrS].
  apply cls_to_rep.
  apply (pg_comp A6list A6_pgroup); assumption.
Qed.

(** Any two members of a class are conjugate to each other. *)
Lemma cls_transitive : forall C, In C all_cls ->
  forall x y, In x C -> In y C ->
  exists h, In h A6list /\ y = conj_of h x.
Proof.
  intros C HC x y Hx Hy.
  assert (Hrep : exists r, In r S6list /\ C = cls r).
  { unfold all_cls in HC.
    cbn [In] in HC.
    destruct HC as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
      [ exists ((1 :: 2 :: 0 :: 3 :: 4 :: 5 :: nil)%nat)
      | exists ((1 :: 2 :: 0 :: 4 :: 5 :: 3 :: nil)%nat)
      | exists ((1 :: 0 :: 3 :: 2 :: 4 :: 5 :: nil)%nat)
      | exists ((1 :: 2 :: 3 :: 0 :: 5 :: 4 :: nil)%nat)
      | exists ((1 :: 2 :: 3 :: 4 :: 0 :: 5 :: nil)%nat)
      | exists ((2 :: 3 :: 4 :: 0 :: 1 :: 5 :: nil)%nat) ];
      (split; [apply memb_spec; vm_compute; reflexivity | reflexivity]).
  }
  destruct Hrep as [r [HrS ->]].
  destruct (cls_from_rep r x Hx) as [h1 [Hh1 Hxc]].
  destruct (cls_from_rep r y Hy) as [h2 [Hh2 Hyc]].
  assert (Hh1S : In h1 S6list) by (apply A6_sub_S6; exact Hh1).
  assert (Hh2S : In h2 S6list) by (apply A6_sub_S6; exact Hh2).
  exists (pcomp h2 (pinv h1)).
  split.
  - apply (pg_comp A6list A6_pgroup); [exact Hh2 |].
    apply pgroup_inv; [exact A6_pgroup | exact Hh1].
  - rewrite Hxc, Hyc.
    rewrite conj_of_conj;
      [| apply S6_comp_in; [exact Hh2S | apply S6_inv_in; exact Hh1S]
       | exact Hh1S | exact HrS].
    f_equal.
    rewrite pcomp_assoc;
      [| exact Hh2S | apply S6_inv_in; exact Hh1S | exact Hh1S].
    rewrite S6_inv_left by exact Hh1S.
    rewrite S6_id_right by exact Hh2S.
    reflexivity.
Qed.

Lemma NoDup_app_disjoint : forall (u v : list (list nat)),
  NoDup u -> NoDup v -> (forall x, In x u -> ~ In x v) ->
  NoDup (u ++ v).
Proof.
  induction u as [|a u IH]; intros v Hu Hv Hdisj; cbn [app].
  - exact Hv.
  - inversion Hu; subst.
    constructor.
    + intro Hc. apply in_app_or in Hc.
      destruct Hc as [Hc | Hc]; [contradiction |].
      apply (Hdisj a); [left; reflexivity | exact Hc].
    + apply IH; [assumption | exact Hv |].
      intros x Hx. apply Hdisj. right. exact Hx.
Qed.

(** Concatenation of positionally disjoint NoDup lists is NoDup. *)
Lemma NoDup_concat_disjoint :
  forall (ls : list (list (list nat))),
  (forall C, In C ls -> NoDup C) ->
  (forall i j x, (i < j)%nat -> (j < length ls)%nat ->
     In x (nth i ls nil) -> ~ In x (nth j ls nil)) ->
  NoDup (concat ls).
Proof.
  induction ls as [|C ls IH]; intros Hnd Hdisj; cbn [concat].
  - constructor.
  - apply NoDup_app_disjoint.
    + apply Hnd. left. reflexivity.
    + apply IH.
      * intros C' HC'. apply Hnd. right. exact HC'.
      * intros i j x Hij Hj Hx.
        apply (Hdisj (Datatypes.S i) (Datatypes.S j) x);
          [lia | cbn [length]; lia | exact Hx].
    + intros x Hx Hc.
      apply in_concat in Hc.
      destruct Hc as [C' [HC' HxC']].
      destruct (In_nth ls C' nil HC') as [j [Hj Hnth]].
      apply (Hdisj 0%nat (Datatypes.S j) x);
        [lia | cbn [length]; lia | exact Hx |].
      cbn [nth]. rewrite Hnth. exact HxC'.
Qed.

(** Selecting the classes meeting a normal subgroup. *)
Lemma subset_sums_In : forall (l : list nat) (mask : list bool),
  length mask = length l ->
  In (fold_right Nat.add 0%nat
       (map (fun p : bool * nat => if fst p then snd p else 0%nat)
         (combine mask l)))
     (fold_right (fun x acc => acc ++ map (Nat.add x) acc) (0%nat :: nil) l).
Proof.
  induction l as [|x l IH]; intros mask Hlen.
  - destruct mask; cbn; left; reflexivity.
  - destruct mask as [|b mask]; [cbn [length] in Hlen; lia |].
    cbn [length] in Hlen.
    cbn [combine map fold_right].
    destruct b.
    + cbn [fst snd].
      apply in_or_app. right.
      apply in_map_iff.
      exists (fold_right Nat.add 0%nat
        (map (fun p : bool * nat => if fst p then snd p else 0%nat)
          (combine mask l))).
      split; [reflexivity | apply IH; lia].
    + cbn [fst snd].
      apply in_or_app. left.
      replace (0 + fold_right Nat.add 0%nat
        (map (fun p : bool * nat => if fst p then snd p else 0%nat)
          (combine mask l)))%nat
        with (fold_right Nat.add 0%nat
        (map (fun p : bool * nat => if fst p then snd p else 0%nat)
          (combine mask l)))
        by lia.
      apply IH. lia.
Qed.

Lemma cover_index : forall x, In x A6list ->
  x = pid6 \/ exists j, (j < length all_cls)%nat /\ In x (nth j all_cls nil).
Proof.
  intros x HxA.
  pose proof (proj1 (forallb_forall _ A6list) cls_cover x HxA) as Hcov.
  apply orb_prop in Hcov. destruct Hcov as [Hcov | H6].
  apply orb_prop in Hcov. destruct Hcov as [Hcov | H5].
  apply orb_prop in Hcov. destruct Hcov as [Hcov | H4].
  apply orb_prop in Hcov. destruct Hcov as [Hcov | H3].
  apply orb_prop in Hcov. destruct Hcov as [Hcov | H2].
  apply orb_prop in Hcov. destruct Hcov as [Hid | H1].
  - left. apply eqb_listnat_spec in Hid. exact Hid.
  - right. exists 0%nat. split; [cbn; lia | apply memb_spec; exact H1].
  - right. exists 1%nat. split; [cbn; lia | apply memb_spec; exact H2].
  - right. exists 2%nat. split; [cbn; lia | apply memb_spec; exact H3].
  - right. exists 3%nat. split; [cbn; lia | apply memb_spec; exact H4].
  - right. exists 4%nat. split; [cbn; lia | apply memb_spec; exact H5].
  - right. exists 5%nat. split; [cbn; lia | apply memb_spec; exact H6].
Qed.

Lemma all_cls_NoDup_each : forall C, In C all_cls -> NoDup C.
Proof.
  intros C HC.
  unfold all_cls in HC. cbn [In] in HC.
  destruct HC as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
    apply NoDup_nodup.
Qed.

Lemma all_cls_pair_disjoint : forall i j x,
  (i < j)%nat -> (j < length all_cls)%nat ->
  In x (nth i all_cls nil) -> ~ In x (nth j all_cls nil).
Proof.
  intros i j x Hij Hj Hx Hx'.
  assert (Hi : (i < length all_cls)%nat) by lia.
  set (Ci := nth i all_cls nil) in *.
  set (Cj := nth j all_cls nil) in *.
  assert (HCi : In Ci all_cls) by (apply nth_In; exact Hi).
  assert (HCj : In Cj all_cls) by (apply nth_In; exact Hj).
  assert (Hne : Ci <> Cj).
  { intro E.
    pose proof (proj1 (NoDup_nth all_cls nil) all_cls_distinct i j Hi Hj E) as Heq.
    lia. }
  pose proof (proj1 (forallb_forall _ all_cls) cls_disjoint Ci HCi) as Hrow.
  pose proof (proj1 (forallb_forall _ all_cls) Hrow Cj HCj) as Hcell.
  cbv beta in Hcell.
  revert Hcell.
  destruct (list_eq_dec (list_eq_dec Nat.eq_dec) Ci Cj) as [E | _];
    [contradiction |].
  intro Hcell.
  pose proof (proj1 (forallb_forall _ Ci) Hcell x Hx) as Hneg.
  rewrite negb_true_iff in Hneg.
  apply memb_spec in Hx'.
  rewrite Hx' in Hneg. discriminate.
Qed.

Lemma length_concat_sum : forall (ls : list (list (list nat))),
  length (concat ls)
  = fold_right Nat.add 0%nat (map (@length (list nat)) ls).
Proof.
  induction ls as [|C ls IH]; cbn [concat map fold_right].
  - reflexivity.
  - rewrite length_app, IH. reflexivity.
Qed.

(** THE SIMPLICITY OF A6. *)
Lemma A6_simple : forall (N : list (list nat)),
  pgroup N -> incl N A6list ->
  (forall x g, In x A6list -> In g N -> In (conj_of x g) N) ->
  (exists g, In g N /\ g <> pid6) ->
  incl A6list N.
Proof.
  intros N HN HNA Hnorm [g [HgN Hgne]].
  assert (Hclass_in : forall C, In C all_cls ->
    (exists y, In y C /\ In y N) -> forall x, In x C -> In x N).
  { intros C HC [y [HyC HyN]] x HxC.
    destruct (cls_transitive C HC y x HyC HxC) as [h [Hh Hxc]].
    rewrite Hxc.
    apply Hnorm; assumption. }
  assert (Hsel : exists (mask : list bool),
    length mask = length all_cls /\
    (forall j, (j < length all_cls)%nat ->
       (nth j mask false = true ->
          forall x, In x (nth j all_cls nil) -> In x N) /\
       (nth j mask false = false ->
          forall x, In x (nth j all_cls nil) -> ~ In x N))).
  { assert (Hgen : forall (ls : list (list (list nat))),
      (forall C, In C ls -> In C all_cls) ->
      exists mask : list bool,
        length mask = length ls /\
        forall j, (j < length ls)%nat ->
          (nth j mask false = true ->
             forall x, In x (nth j ls nil) -> In x N) /\
          (nth j mask false = false ->
             forall x, In x (nth j ls nil) -> ~ In x N)).
    { induction ls as [|C ls IHls]; intro Hls.
      - exists nil. split; [reflexivity | intros j Hj; cbn [length] in Hj; lia].
      - destruct IHls as [mask [Hlm Hm]];
          [intros C' HC'; apply Hls; right; exact HC' |].
        destruct (classic (exists y, In y C /\ In y N)) as [Hyes | Hno].
        + exists (true :: mask).
          split; [cbn [length]; lia |].
          intros j Hj.
          destruct j as [|j'].
          * cbn [nth].
            split; [| discriminate].
            intros _ x HxC.
            apply (Hclass_in C (Hls C (or_introl eq_refl)) Hyes x HxC).
          * cbn [nth].
            cbn [length] in Hj.
            apply Hm. lia.
        + exists (false :: mask).
          split; [cbn [length]; lia |].
          intros j Hj.
          destruct j as [|j'].
          * cbn [nth].
            split; [discriminate |].
            intros _ x HxC HxN.
            apply Hno. exists x. split; assumption.
          * cbn [nth].
            cbn [length] in Hj.
            apply Hm. lia. }
    apply (Hgen all_cls (fun C HC => HC)). }
  destruct Hsel as [mask [Hlm Hmask]].
  set (sel := map (fun p : bool * list (list nat) =>
                     if fst p then snd p else nil)
                (combine mask all_cls)).
  assert (Hlsel : length sel = length all_cls)
    by (unfold sel; rewrite length_map, length_combine; lia).
  assert (Hsel_nth : forall j, (j < length all_cls)%nat ->
    nth j sel nil = if nth j mask false then nth j all_cls nil else nil).
  { intros j Hj.
    unfold sel.
    rewrite (nth_indep _ nil
      ((fun p : bool * list (list nat) => if fst p then snd p else nil)
         (false, @nil (list nat))))
      by (rewrite length_map, length_combine; lia).
    rewrite (map_nth (fun p : bool * list (list nat) =>
                        if fst p then snd p else nil)
               (combine mask all_cls) (false, @nil (list nat)) j).
    rewrite combine_nth by lia.
    cbn [fst snd]. reflexivity. }
  assert (Hset : forall x, In x N <-> (x = pid6 \/ In x (concat sel))).
  { intro x. split.
    - intro HxN.
      destruct (cover_index x (HNA x HxN)) as [-> | [j [Hj HxC]]];
        [left; reflexivity |].
      right.
      destruct (Hmask j Hj) as [Htrue Hfalse].
      destruct (nth j mask false) eqn:Em.
      + apply in_concat.
        exists (nth j sel nil).
        split.
        * apply nth_In. rewrite Hlsel. exact Hj.
        * rewrite (Hsel_nth j Hj), Em. exact HxC.
      + exfalso. exact (Hfalse eq_refl x HxC HxN).
    - intros [-> | Hx]; [exact (pg_id N HN) |].
      apply in_concat in Hx.
      destruct Hx as [S' [HS' HxS']].
      destruct (In_nth sel S' nil HS') as [j [Hj Hnth]].
      rewrite Hlsel in Hj.
      rewrite (Hsel_nth j Hj) in Hnth.
      destruct (nth j mask false) eqn:Em.
      + destruct (Hmask j Hj) as [Htrue _].
        apply (Htrue Em).
        rewrite Hnth. exact HxS'.
      + rewrite <- Hnth in HxS'. contradiction. }
  assert (Hnd_sel : NoDup (pid6 :: concat sel)).
  { constructor.
    - intro Hc.
      apply in_concat in Hc.
      destruct Hc as [S' [HS' HxS']].
      destruct (In_nth sel S' nil HS') as [j [Hj Hnth]].
      rewrite Hlsel in Hj.
      rewrite (Hsel_nth j Hj) in Hnth.
      destruct (nth j mask false) eqn:Em.
      + assert (HCj : In (nth j all_cls nil) all_cls)
          by (apply nth_In; exact Hj).
        pose proof (proj1 (forallb_forall _ all_cls) cls_no_id _ HCj) as Hno.
        rewrite negb_true_iff in Hno.
        rewrite <- Hnth in HxS'.
        apply memb_spec in HxS'.
        rewrite HxS' in Hno. discriminate.
      + rewrite <- Hnth in HxS'. contradiction.
    - apply NoDup_concat_disjoint.
      + intros C HC.
        destruct (In_nth sel C nil HC) as [j [Hj Hnth]].
        rewrite Hlsel in Hj.
        rewrite (Hsel_nth j Hj) in Hnth.
        destruct (nth j mask false).
        * rewrite <- Hnth.
          apply all_cls_NoDup_each.
          apply nth_In. exact Hj.
        * rewrite <- Hnth. constructor.
      + intros i j x Hij Hj Hx Hx'.
        rewrite Hlsel in Hj.
        assert (Hi : (i < length all_cls)%nat) by lia.
        rewrite (Hsel_nth i Hi) in Hx.
        rewrite (Hsel_nth j Hj) in Hx'.
        destruct (nth i mask false); [| contradiction].
        destruct (nth j mask false); [| contradiction].
        exact (all_cls_pair_disjoint i j x Hij Hj Hx Hx'). }
  assert (Hcount : length N = Datatypes.S (length (concat sel))).
  { assert (Hcl : length N = length (pid6 :: concat sel)).
    { apply NoDup_same_set_length.
      - exact (pg_nd N HN).
      - exact Hnd_sel.
      - intros x Hx.
        destruct (proj1 (Hset x) Hx) as [-> | Hc];
          [left; reflexivity | right; exact Hc].
      - intros x Hx.
        apply (proj2 (Hset x)).
        destruct Hx as [<- | Hc]; [left; reflexivity | right; exact Hc]. }
    rewrite Hcl. reflexivity. }
  assert (Hsum : length (concat sel)
    = fold_right Nat.add 0%nat
        (map (fun p : bool * nat => if fst p then snd p else 0%nat)
          (combine mask (map (@length (list nat)) all_cls)))).
  { rewrite length_concat_sum.
    unfold sel.
    clear - Hlm.
    revert mask Hlm.
    induction all_cls as [|C ls IH]; intros mask Hlm.
    - destruct mask; [reflexivity | cbn [length] in Hlm; lia].
    - destruct mask as [|b mask]; [cbn [length] in Hlm; lia |].
      cbn [length] in Hlm.
      cbn [combine map fold_right].
      destruct b; cbn [fst snd length].
      + f_equal. apply IH. lia.
      + rewrite (IH mask ltac:(lia)). reflexivity. }
  destruct (lagrange A6list N A6_pgroup HN HNA) as [m Hlag].
  rewrite A6list_length in Hlag.
  assert (Hs_in := subset_sums_In (map (@length (list nat)) all_cls) mask
                     ltac:(rewrite length_map; exact Hlm)).
  set (s := fold_right Nat.add 0%nat
        (map (fun p : bool * nat => if fst p then snd p else 0%nat)
          (combine mask (map (@length (list nat)) all_cls)))) in *.
  assert (Hcheck := proj1 (forallb_forall _ _) cls_sizes_ok s Hs_in).
  assert (Hmod : (360 mod (Datatypes.S s) = 0)%nat).
  { rewrite Hlag, Hcount, Hsum.
    apply Nat.Div0.mod_mul. }
  assert (Hs_ne : s <> 0%nat).
  { intro Hs0.
    assert (HgC : In g (concat sel)).
    { destruct (proj1 (Hset g) HgN) as [E | Hc]; [contradiction | exact Hc]. }
    assert (Hlen0 : length (concat sel) = 0%nat) by (rewrite Hsum; lia).
    destruct (concat sel); [contradiction | cbn [length] in Hlen0; lia]. }
  apply orb_prop in Hcheck.
  destruct Hcheck as [Hcheck | Hbad].
  2:{ exfalso.
      rewrite negb_true_iff in Hbad.
      apply Nat.eqb_neq in Hbad.
      contradiction. }
  apply orb_prop in Hcheck.
  destruct Hcheck as [Hz | Hfull].
  { exfalso. apply Hs_ne. apply Nat.eqb_eq in Hz. exact Hz. }
  apply Nat.eqb_eq in Hfull.
  assert (HlenN : length N = 360%nat) by (rewrite Hcount, Hsum; lia).
  apply (NoDup_length_incl (pg_nd N HN));
    [rewrite A6list_length, HlenN; lia | exact HNA].
Qed.

(* no large proper subgroup of A6 -- coset fingerprints inject the group into fingerprints times kernel, forcing a nontrivial normal kernel, and simplicity closes. *)

Definition idxof (x : list nat) (l : list (list nat)) : nat :=
  find_left (fun j => eqb_listnat (nth j l pid6) x) (seq 0 (length l)) 0%nat.

Lemma idxof_spec : forall x l, In x l ->
  (idxof x l < length l)%nat /\ nth (idxof x l) l pid6 = x.
Proof.
  intros x l Hx.
  destruct (In_nth l x pid6 Hx) as [j [Hj Hnth]].
  destruct (find_left_spec (fun j0 => eqb_listnat (nth j0 l pid6) x)
              (seq 0 (length l)) 0%nat) as [Hin Htest].
  - exists j.
    split; [apply in_seq; lia |].
    apply eqb_listnat_spec. exact Hnth.
  - apply in_seq in Hin.
    unfold idxof.
    split; [lia |].
    apply eqb_listnat_spec. exact Htest.
Qed.

Lemma A6_subgroup_large : forall (H0 : list (list nat)),
  pgroup H0 -> incl H0 A6list -> (360 <= 5 * length H0)%nat ->
  incl A6list H0.
Proof.
  intros H0 HH0 HH0A Hbig.
  destruct (lagrange A6list H0 A6_pgroup HH0 HH0A) as [k Hlag].
  rewrite A6list_length in Hlag.
  assert (HlenH1 : (1 <= length H0)%nat).
  { pose proof (pg_id H0 HH0) as Hid.
    destruct H0; [contradiction | cbn [length]; lia]. }
  assert (Hk5 : (k <= 5)%nat) by nia.
  assert (Hk1 : (1 <= k)%nat) by nia.
  destruct (Nat.eq_dec k 1%nat) as [-> | Hk2'].
  { apply (NoDup_length_incl (pg_nd H0 HH0));
      [rewrite A6list_length; lia | exact HH0A]. }
  assert (Hk2 : (2 <= k)%nat) by lia.
  destruct (coset_decomp A6list H0 A6_pgroup HH0 HH0A)
    as [reps [Hr1 [Hr0 [HrA [Hrlen [Hcov Hdisj]]]]]].
  rewrite A6list_length in Hrlen.
  assert (Hkreps : length reps = k).
  { apply (Nat.mul_cancel_r _ _ (length H0)); [lia | lia]. }
  set (kk := length reps) in *.
  assert (HrS : forall i, (i < kk)%nat -> In (nth i reps pid6) S6list).
  { intros i Hi. apply A6_sub_S6. apply HrA. apply nth_In. exact Hi. }
  assert (HrA6 : forall i, (i < kk)%nat -> In (nth i reps pid6) A6list).
  { intros i Hi. apply HrA. apply nth_In. exact Hi. }
  set (cosetb := fun (g : list nat) (i j : nat) =>
    existsb (fun h => eqb_listnat (pcomp g (nth i reps pid6))
                       (pcomp (nth j reps pid6) h)) H0).
  assert (Hcosetb_iff : forall g i j,
    cosetb g i j = true <->
    exists h, In h H0 /\
      pcomp g (nth i reps pid6) = pcomp (nth j reps pid6) h).
  { intros g i j. unfold cosetb.
    rewrite existsb_exists.
    split.
    - intros [h [Hh He]].
      apply eqb_listnat_spec in He.
      exists h. split; assumption.
    - intros [h [Hh He]].
      exists h.
      split; [exact Hh | apply eqb_listnat_spec; exact He]. }
  assert (Hcover_j : forall g i, In g A6list -> (i < kk)%nat ->
    exists j, (j < kk)%nat /\ cosetb g i j = true).
  { intros g i Hg Hi.
    assert (Hgr : In (pcomp g (nth i reps pid6)) A6list)
      by (apply (pg_comp A6list A6_pgroup); [exact Hg | apply HrA6; exact Hi]).
    destruct (Hcov _ Hgr) as [j [h [Hj [Hh He]]]].
    exists j.
    split; [exact Hj |].
    apply Hcosetb_iff.
    exists h. split; assumption. }
  assert (Hcoset_unique : forall g i j j',
    cosetb g i j = true -> cosetb g i j' = true ->
    (j < kk)%nat -> (j' < kk)%nat -> j = j').
  { intros g i j j' Hj Hj' Hjk Hj'k.
    apply Hcosetb_iff in Hj. destruct Hj as [h [Hh He]].
    apply Hcosetb_iff in Hj'. destruct Hj' as [h' [Hh' He']].
    apply (Hdisj j j' h h' Hjk Hj'k Hh Hh').
    rewrite <- He, <- He'. reflexivity. }
  assert (Hcoset_inj : forall g i i' j,
    In g A6list -> (i < kk)%nat -> (i' < kk)%nat -> (j < kk)%nat ->
    cosetb g i j = true -> cosetb g i' j = true -> i = i').
  { intros g i i' j Hg Hi Hi' Hj HA HB.
    apply Hcosetb_iff in HA. destruct HA as [h [Hh He]].
    apply Hcosetb_iff in HB. destruct HB as [h' [Hh' He']].
    set (ri := nth i reps pid6) in *.
    set (ri' := nth i' reps pid6) in *.
    set (rj := nth j reps pid6) in *.
    assert (HgS : In g S6list) by (apply A6_sub_S6; exact Hg).
    assert (HriS : In ri S6list) by (apply HrS; exact Hi).
    assert (Hri'S : In ri' S6list) by (apply HrS; exact Hi').
    assert (HrjS : In rj S6list) by (apply HrS; exact Hj).
    assert (HhS : In h S6list)
      by (apply A6_sub_S6; apply HH0A; exact Hh).
    assert (Hh'S : In h' S6list)
      by (apply A6_sub_S6; apply HH0A; exact Hh').
    assert (Hstep : pcomp ri (pcomp (pinv h) h') = ri').
    { assert (H1 : pcomp (pcomp g ri) (pcomp (pinv h) h')
                   = pcomp (pcomp rj h) (pcomp (pinv h) h'))
        by (rewrite He; reflexivity).
      rewrite (pcomp_assoc g ri (pcomp (pinv h) h')) in H1;
        [| exact HgS | exact HriS
         | apply S6_comp_in; [apply S6_inv_in; exact HhS | exact Hh'S]].
      rewrite (pcomp_assoc rj h (pcomp (pinv h) h')) in H1;
        [| exact HrjS | exact HhS
         | apply S6_comp_in; [apply S6_inv_in; exact HhS | exact Hh'S]].
      rewrite <- (pcomp_assoc h (pinv h) h') in H1;
        [| exact HhS | apply S6_inv_in; exact HhS | exact Hh'S].
      rewrite S6_inv_right in H1 by exact HhS.
      rewrite S6_id_left in H1 by exact Hh'S.
      rewrite <- He' in H1.
      apply (pcomp_cancel_l g); [exact HgS | | exact Hri'S | exact H1].
      apply S6_comp_in; [exact HriS |].
      apply S6_comp_in; [apply S6_inv_in; exact HhS | exact Hh'S]. }
    assert (Hmem : In (pcomp (pinv h) h') H0).
    { apply (pg_comp H0 HH0); [| exact Hh'].
      apply pgroup_inv; [exact HH0 | exact Hh]. }
    apply (Hdisj i i' (pcomp (pinv h) h') pid6 Hi Hi' Hmem (pg_id H0 HH0)).
    fold ri. fold ri'.
    rewrite Hstep.
    rewrite S6_id_right by exact Hri'S.
    reflexivity. }
  set (fp := fun g =>
    map (fun i => find_left (fun j => cosetb g i j) (seq 0 kk) 0%nat)
      (seq 0 kk)).
  assert (Hfp_len : forall g, length (fp g) = kk)
    by (intro g; unfold fp; rewrite length_map, length_seq; reflexivity).
  assert (Hfp_nth : forall g i, (i < kk)%nat ->
    nth i (fp g) 0%nat
    = find_left (fun j => cosetb g i j) (seq 0 kk) 0%nat).
  { intros g i Hi. unfold fp.
    rewrite (nth_indep _ 0%nat
      (find_left (fun j => cosetb g 0%nat j) (seq 0 kk) 0%nat))
      by (rewrite length_map, length_seq; exact Hi).
    rewrite (map_nth (fun i0 => find_left (fun j => cosetb g i0 j)
                        (seq 0 kk) 0%nat) (seq 0 kk) 0%nat i).
    rewrite seq_nth by exact Hi.
    reflexivity. }
  assert (Hfp_spec : forall g i, In g A6list -> (i < kk)%nat ->
    (nth i (fp g) 0%nat < kk)%nat /\ cosetb g i (nth i (fp g) 0%nat) = true).
  { intros g i Hg Hi.
    destruct (Hcover_j g i Hg Hi) as [j [Hj Hcj]].
    rewrite (Hfp_nth g i Hi).
    destruct (find_left_spec (fun j0 => cosetb g i j0) (seq 0 kk) 0%nat)
      as [Hin Htest].
    - exists j. split; [apply in_seq; lia | exact Hcj].
    - apply in_seq in Hin.
      split; [lia | exact Htest]. }
  assert (Hfp_nd : forall g, In g A6list -> NoDup (fp g)).
  { intros g Hg.
    apply (proj2 (NoDup_nth (fp g) 0%nat)).
    intros a b Ha Hb He.
    rewrite Hfp_len in Ha, Hb.
    destruct (Hfp_spec g a Hg Ha) as [Hva Hca].
    destruct (Hfp_spec g b Hg Hb) as [Hvb Hcb].
    rewrite He in Hca.
    apply (Hcoset_inj g a b (nth b (fp g) 0%nat) Hg Ha Hb Hvb Hca Hcb). }
  assert (Hfp_perm : forall g, In g A6list -> In (fp g) (perms_of (seq 0 kk))).
  { intros g Hg.
    apply perms_of_complete.
    apply NoDup_Permutation_bis.
    - apply seq_NoDup.
    - rewrite length_seq, Hfp_len. lia.
    - assert (Hincl_fp : incl (fp g) (seq 0 kk)).
      { intros v Hv.
        destruct (In_nth (fp g) v 0%nat Hv) as [i [Hi Hnth]].
        rewrite Hfp_len in Hi.
        apply in_seq.
        destruct (Hfp_spec g i Hg Hi) as [Hlt _].
        rewrite Hnth in Hlt. lia. }
      apply (NoDup_length_incl (Hfp_nd g Hg));
        [rewrite length_seq, Hfp_len; lia | exact Hincl_fp]. }
  set (ktest := fun g => forallb (fun i => cosetb g i i) (seq 0 kk)).
  set (Klist := filter ktest A6list).
  assert (HK_iff : forall g, In g Klist <->
    In g A6list /\ forall i, (i < kk)%nat -> cosetb g i i = true).
  { intro g. unfold Klist.
    rewrite filter_In.
    split.
    - intros [HgA Hkt].
      split; [exact HgA |].
      intros i Hi.
      apply (proj1 (forallb_forall _ (seq 0 kk)) Hkt).
      apply in_seq. lia.
    - intros [HgA Hall].
      split; [exact HgA |].
      apply forallb_forall.
      intros i Hi. apply in_seq in Hi. apply Hall. lia. }
  assert (HK_pg : pgroup Klist).
  { constructor.
    - intros g Hg. apply A6_sub_S6.
      apply (proj1 (HK_iff g)) in Hg. exact (proj1 Hg).
    - unfold Klist. apply NoDup_filter. exact (pg_nd A6list A6_pgroup).
    - apply HK_iff.
      split; [exact (pg_id A6list A6_pgroup) |].
      intros i Hi.
      apply Hcosetb_iff.
      exists pid6.
      split; [exact (pg_id H0 HH0) |].
      rewrite S6_id_left by (apply HrS; exact Hi).
      rewrite S6_id_right by (apply HrS; exact Hi).
      reflexivity.
    - intros p q Hp Hq.
      apply (proj1 (HK_iff p)) in Hp. destruct Hp as [HpA Hpc].
      apply (proj1 (HK_iff q)) in Hq. destruct Hq as [HqA Hqc].
      apply HK_iff.
      split; [apply (pg_comp A6list A6_pgroup); assumption |].
      intros i Hi.
      destruct (proj1 (Hcosetb_iff q i i) (Hqc i Hi)) as [h' [Hh' He']].
      destruct (proj1 (Hcosetb_iff p i i) (Hpc i Hi)) as [h [Hh He]].
      apply Hcosetb_iff.
      exists (pcomp h h').
      set (ri := nth i reps pid6) in *.
      assert (HriS : In ri S6list) by (apply HrS; exact Hi).
      assert (HpS : In p S6list) by (apply A6_sub_S6; exact HpA).
      assert (HqS : In q S6list) by (apply A6_sub_S6; exact HqA).
      assert (HhS : In h S6list) by (apply A6_sub_S6; apply HH0A; exact Hh).
      assert (Hh'S : In h' S6list) by (apply A6_sub_S6; apply HH0A; exact Hh').
      split; [apply (pg_comp H0 HH0); assumption |].
      rewrite (pcomp_assoc p q ri); [| exact HpS | exact HqS | exact HriS].
      rewrite He'.
      rewrite <- (pcomp_assoc p ri h'); [| exact HpS | exact HriS | exact Hh'S].
      rewrite He.
      rewrite (pcomp_assoc ri h h'); [| exact HriS | exact HhS | exact Hh'S].
      reflexivity. }
  assert (HK_H0 : incl Klist H0).
  { intros g Hg.
    apply (proj1 (HK_iff g)) in Hg.
    destruct Hg as [HgA Hgc].
    destruct (proj1 (Hcosetb_iff g 0%nat 0%nat) (Hgc 0%nat ltac:(lia)))
      as [h [Hh He]].
    rewrite Hr0 in He.
    rewrite S6_id_right in He by (apply A6_sub_S6; exact HgA).
    rewrite S6_id_left in He by (apply A6_sub_S6; apply HH0A; exact Hh).
    rewrite He. exact Hh. }
  (* elements with equal fingerprints differ by the kernel *)
  assert (Hquo : forall g g', In g A6list -> In g' A6list ->
    fp g = fp g' -> In (pcomp (pinv g') g) Klist).
  { intros g g' Hg Hg' Hfpe.
    assert (HgS : In g S6list) by (apply A6_sub_S6; exact Hg).
    assert (Hg'S : In g' S6list) by (apply A6_sub_S6; exact Hg').
    apply HK_iff.
    split.
    { apply (pg_comp A6list A6_pgroup); [| exact Hg].
      apply pgroup_inv; [exact A6_pgroup | exact Hg']. }
    intros i Hi.
    destruct (Hfp_spec g i Hg Hi) as [Hvi Hci].
    destruct (Hfp_spec g' i Hg' Hi) as [Hvi' Hci'].
    set (v := nth i (fp g) 0%nat) in *.
    assert (Hv' : nth i (fp g') 0%nat = v) by (rewrite <- Hfpe; reflexivity).
    rewrite Hv' in Hci'.
    destruct (proj1 (Hcosetb_iff g i v) Hci) as [h [Hh He]].
    destruct (proj1 (Hcosetb_iff g' i v) Hci') as [h' [Hh' He']].
    apply Hcosetb_iff.
    exists (pcomp (pinv h') h).
    set (ri := nth i reps pid6) in *.
    set (rv := nth v reps pid6) in *.
    assert (HriS : In ri S6list) by (apply HrS; exact Hi).
    assert (HrvS : In rv S6list) by (apply HrS; exact Hvi).
    assert (HhS : In h S6list) by (apply A6_sub_S6; apply HH0A; exact Hh).
    assert (Hh'S : In h' S6list) by (apply A6_sub_S6; apply HH0A; exact Hh').
    split; [apply (pg_comp H0 HH0);
            [apply pgroup_inv; [exact HH0 | exact Hh'] | exact Hh] |].
    (* pinv g' (rv h') = ri, so pinv g' rv = ri (pinv h') *)
    assert (Hback : pcomp (pinv g') rv = pcomp ri (pinv h')).
    { assert (H1 : pcomp (pinv g') (pcomp g' ri) = ri).
      { rewrite <- pcomp_assoc;
          [| apply S6_inv_in; exact Hg'S | exact Hg'S | exact HriS].
        rewrite S6_inv_left by exact Hg'S.
        apply S6_id_left. exact HriS. }
      rewrite He' in H1.
      assert (H2 : pcomp (pcomp (pinv g') (pcomp rv h')) (pinv h')
                   = pcomp ri (pinv h'))
        by (rewrite H1; reflexivity).
      rewrite <- H2.
      rewrite <- (pcomp_assoc (pinv g') rv h') at 1;
        [| apply S6_inv_in; exact Hg'S | exact HrvS | exact Hh'S].
      rewrite (pcomp_assoc (pcomp (pinv g') rv) h' (pinv h'));
        [| apply S6_comp_in; [apply S6_inv_in; exact Hg'S | exact HrvS]
         | exact Hh'S | apply S6_inv_in; exact Hh'S].
      rewrite S6_inv_right by exact Hh'S.
      rewrite S6_id_right
        by (apply S6_comp_in; [apply S6_inv_in; exact Hg'S | exact HrvS]).
      reflexivity. }
    rewrite (pcomp_assoc (pinv g') g ri);
      [| apply S6_inv_in; exact Hg'S | exact HgS | exact HriS].
    rewrite He.
    rewrite <- (pcomp_assoc (pinv g') rv h);
      [| apply S6_inv_in; exact Hg'S | exact HrvS | exact HhS].
    rewrite Hback.
    rewrite (pcomp_assoc ri (pinv h') h);
      [| exact HriS | apply S6_inv_in; exact Hh'S | exact HhS].
    reflexivity. }
  (* the counting injection *)
  set (vals := nodup (list_eq_dec Nat.eq_dec) (map fp A6list)).
  assert (Hvals_len : (length vals <= 120)%nat).
  { assert (Hincl_v : incl vals (perms_of (seq 0 kk))).
    { intros v Hv.
      unfold vals in Hv.
      apply nodup_In in Hv.
      apply in_map_iff in Hv.
      destruct Hv as [g [Hvg Hg]].
      rewrite <- Hvg.
      apply Hfp_perm. exact Hg. }
    pose proof (NoDup_incl_length (NoDup_nodup _ _) Hincl_v) as Hle.
    assert (Hkf : (length (perms_of (seq 0 kk)) <= 120)%nat).
    { rewrite Hkreps.
      destruct k as [|[|[|[|[|[|k']]]]]]; try lia;
        vm_compute; lia. }
    exact (Nat.le_trans _ _ _ Hle Hkf). }
  set (gcidx := fun v =>
    find_left (fun j => eqb_listnat (fp (nth j A6list pid6)) v)
      (seq 0 (length A6list)) 0%nat).
  set (gcrep := fun v => nth (gcidx v) A6list pid6).
  assert (Hgc_spec : forall g, In g A6list ->
    In (gcrep (fp g)) A6list /\ fp (gcrep (fp g)) = fp g).
  { intros g Hg.
    destruct (In_nth A6list g pid6 Hg) as [j0 [Hj0 Hnth0]].
    destruct (find_left_spec
                (fun j => eqb_listnat (fp (nth j A6list pid6)) (fp g))
                (seq 0 (length A6list)) 0%nat) as [Hin Htest].
    - exists j0.
      split; [apply in_seq; lia |].
      apply eqb_listnat_spec.
      rewrite Hnth0. reflexivity.
    - apply in_seq in Hin.
      unfold gcrep, gcidx.
      split.
      + apply nth_In. lia.
      + apply eqb_listnat_spec. exact Htest. }
  set (code := fun g =>
    (idxof (fp g) vals * length Klist
     + idxof (pcomp (pinv (gcrep (fp g))) g) Klist)%nat).
  assert (HKlen1 : (1 <= length Klist)%nat).
  { pose proof (pg_id Klist HK_pg) as Hid.
    destruct Klist; [contradiction | cbn [length]; lia]. }
  assert (Hcode_data : forall g, In g A6list ->
    In (fp g) vals /\
    In (pcomp (pinv (gcrep (fp g))) g) Klist).
  { intros g Hg.
    split.
    - unfold vals. apply nodup_In.
      apply in_map_iff. exists g. split; [reflexivity | exact Hg].
    - destruct (Hgc_spec g Hg) as [HgcA Hgcf].
      apply Hquo; [exact Hg | exact HgcA |].
      symmetry. exact Hgcf. }
  assert (Hcode_bound : forall g, In g A6list ->
    (code g < length vals * length Klist)%nat).
  { intros g Hg.
    destruct (Hcode_data g Hg) as [Hv HqK].
    destruct (idxof_spec _ _ Hv) as [Hb1 _].
    destruct (idxof_spec _ _ HqK) as [Hb2 _].
    unfold code. nia. }
  assert (Hcode_inj : forall g g', In g A6list -> In g' A6list ->
    code g = code g' -> g = g').
  { intros g g' Hg Hg' Hce.
    destruct (Hcode_data g Hg) as [Hv HqK].
    destruct (Hcode_data g' Hg') as [Hv' HqK'].
    destruct (idxof_spec _ _ Hv) as [Hb1 Hn1].
    destruct (idxof_spec _ _ HqK) as [Hb2 Hn2].
    destruct (idxof_spec _ _ Hv') as [Hb1' Hn1'].
    destruct (idxof_spec _ _ HqK') as [Hb2' Hn2'].
    unfold code in Hce.
    assert (Hc1 : idxof (fp g) vals = idxof (fp g') vals).
    { assert (Hd : ((idxof (fp g) vals * length Klist
                     + idxof (pcomp (pinv (gcrep (fp g))) g) Klist)
                    / length Klist
                    = (idxof (fp g') vals * length Klist
                       + idxof (pcomp (pinv (gcrep (fp g'))) g') Klist)
                      / length Klist)%nat)
        by (rewrite Hce; reflexivity).
      rewrite !Nat.div_add_l in Hd by lia.
      rewrite !Nat.div_small in Hd by lia.
      lia. }
    assert (Hfpe : fp g = fp g') by (rewrite <- Hn1, <- Hn1', Hc1; reflexivity).
    assert (Hc2 : idxof (pcomp (pinv (gcrep (fp g))) g) Klist
                  = idxof (pcomp (pinv (gcrep (fp g'))) g') Klist)
      by nia.
    assert (Hqe : pcomp (pinv (gcrep (fp g))) g
                  = pcomp (pinv (gcrep (fp g'))) g')
      by (rewrite <- Hn2, <- Hn2', Hc2; reflexivity).
    rewrite Hfpe in Hqe.
    assert (HgcS : In (gcrep (fp g')) S6list).
    { apply A6_sub_S6.
      exact (proj1 (Hgc_spec g' Hg')). }
    apply (pcomp_cancel_l (pinv (gcrep (fp g'))) g g');
      [apply S6_inv_in; exact HgcS
       | apply A6_sub_S6; exact Hg
       | apply A6_sub_S6; exact Hg'
       | exact Hqe]. }
  assert (Hmain : (360 <= length vals * length Klist)%nat).
  { assert (Hnd_codes : NoDup (map code A6list)).
    { apply NoDup_map_inj_gen; [| exact (pg_nd A6list A6_pgroup)].
      intros x y Hx Hy He.
      apply Hcode_inj; assumption. }
    assert (Hlen_codes : length (map code A6list) = 360%nat)
      by (rewrite length_map; exact A6list_length).
    rewrite <- Hlen_codes.
    apply nat_list_bounded_NoDup_length; [exact Hnd_codes |].
    intros c Hc.
    apply in_map_iff in Hc.
    destruct Hc as [g [Hcg Hg]].
    rewrite <- Hcg.
    apply Hcode_bound. exact Hg. }
  assert (HKbig : (3 <= length Klist)%nat) by nia.
  destruct (nonid_element Klist (pg_nd Klist HK_pg) ltac:(lia))
    as [g0 [Hg0K Hg0ne]].
  (* the kernel is normal in A6 *)
  assert (HK_norm : forall x g, In x A6list -> In g Klist ->
    In (conj_of x g) Klist).
  { intros x g HxA HgK.
    apply (proj1 (HK_iff g)) in HgK.
    destruct HgK as [HgA Hgc].
    assert (HxS : In x S6list) by (apply A6_sub_S6; exact HxA).
    assert (HgS : In g S6list) by (apply A6_sub_S6; exact HgA).
    apply HK_iff.
    split.
    { unfold conj_of.
      apply (pg_comp A6list A6_pgroup); [exact HxA |].
      apply (pg_comp A6list A6_pgroup); [exact HgA |].
      apply pgroup_inv; [exact A6_pgroup | exact HxA]. }
    intros i Hi.
    set (ri := nth i reps pid6) in *.
    assert (HriS : In ri S6list) by (apply HrS; exact Hi).
    assert (Hxinv_ri : In (pcomp (pinv x) ri) A6list).
    { apply (pg_comp A6list A6_pgroup); [| apply HrA6; exact Hi].
      apply pgroup_inv; [exact A6_pgroup | exact HxA]. }
    destruct (Hcov _ Hxinv_ri) as [j [h1 [Hj [Hh1 He1]]]].
    destruct (proj1 (Hcosetb_iff g j j) (Hgc j Hj)) as [h2 [Hh2 He2]].
    set (rj := nth j reps pid6) in *.
    assert (HrjS : In rj S6list) by (apply HrS; exact Hj).
    assert (Hh1S : In h1 S6list) by (apply A6_sub_S6; apply HH0A; exact Hh1).
    assert (Hh2S : In h2 S6list) by (apply A6_sub_S6; apply HH0A; exact Hh2).
    (* x rj = ri (pinv h1) *)
    assert (Hxrj : pcomp x rj = pcomp ri (pinv h1)).
    { assert (H1 : pcomp x (pcomp (pinv x) ri) = ri).
      { rewrite <- pcomp_assoc;
          [| exact HxS | apply S6_inv_in; exact HxS | exact HriS].
        rewrite S6_inv_right by exact HxS.
        apply S6_id_left. exact HriS. }
      rewrite He1 in H1.
      assert (H2 : pcomp (pcomp x (pcomp rj h1)) (pinv h1)
                   = pcomp ri (pinv h1)) by (rewrite H1; reflexivity).
      rewrite <- H2.
      rewrite <- (pcomp_assoc x rj h1);
        [| exact HxS | exact HrjS | exact Hh1S].
      rewrite (pcomp_assoc (pcomp x rj) h1 (pinv h1));
        [| apply S6_comp_in; [exact HxS | exact HrjS]
         | exact Hh1S | apply S6_inv_in; exact Hh1S].
      rewrite S6_inv_right by exact Hh1S.
      rewrite S6_id_right by (apply S6_comp_in; [exact HxS | exact HrjS]).
      reflexivity. }
    apply Hcosetb_iff.
    exists (pcomp (pinv h1) (pcomp h2 h1)).
    split.
    { apply (pg_comp H0 HH0);
        [apply pgroup_inv; [exact HH0 | exact Hh1] |].
      apply (pg_comp H0 HH0); assumption. }
    (* (x g x^-1) ri = x g (rj h1) = x (rj h2) h1 = ri h1^-1 h2 h1 *)
    unfold conj_of.
    fold ri.
    assert (Hstep1 : pcomp (pcomp x (pcomp g (pinv x))) ri
                     = pcomp x (pcomp g (pcomp (pinv x) ri))).
    { rewrite (pcomp_assoc x (pcomp g (pinv x)) ri);
        [| exact HxS
         | apply S6_comp_in; [exact HgS | apply S6_inv_in; exact HxS]
         | exact HriS].
      f_equal.
      rewrite (pcomp_assoc g (pinv x) ri);
        [| exact HgS | apply S6_inv_in; exact HxS | exact HriS].
      reflexivity. }
    rewrite Hstep1, He1.
    assert (Hstep2 : pcomp g (pcomp rj h1) = pcomp rj (pcomp h2 h1)).
    { rewrite <- (pcomp_assoc g rj h1);
        [| exact HgS | exact HrjS | exact Hh1S].
      rewrite He2.
      rewrite (pcomp_assoc rj h2 h1);
        [| exact HrjS | exact Hh2S | exact Hh1S].
      reflexivity. }
    rewrite Hstep2.
    rewrite <- (pcomp_assoc x rj (pcomp h2 h1));
      [| exact HxS | exact HrjS | apply S6_comp_in; assumption].
    rewrite Hxrj.
    rewrite (pcomp_assoc ri (pinv h1) (pcomp h2 h1));
      [| exact HriS | apply S6_inv_in; exact Hh1S
       | apply S6_comp_in; assumption].
    reflexivity. }
  assert (Hfinal : incl A6list Klist).
  { apply A6_simple.
    - exact HK_pg.
    - intros g Hg.
      apply (proj1 (HK_iff g)) in Hg. exact (proj1 Hg).
    - exact HK_norm.
    - exists g0. split; assumption. }
  intros q Hq.
  apply HK_H0.
  apply Hfinal.
  exact Hq.
Qed.

(* THE SANDWICH DESCENT -- the descent step through a simple sandwich, over an abstract group pair, an index bound, and their certificates; the S6 instance recovers the chain invariant, and the A10 instance costs only its certificates. *)

Section SandwichDescent.

Variables (PG : list (list nat) -> Prop) (Amin Smax : list (list nat)) (idxbound : nat).
Hypothesis PG_nd : forall G, PG G -> NoDup G.
Hypothesis HAnd : NoDup Amin.
Hypothesis HSnd : NoDup Smax.
Hypothesis HAS : incl Amin Smax.
Hypothesis Hindex2 : (2 * length Amin <= length Smax)%nat.
Hypothesis Hsandwich : forall P, PG P -> incl Amin P ->
  (incl P Amin /\ incl Amin P) \/ (incl P Smax /\ incl Smax P).
Hypothesis Hlarge : forall H0 : list (list nat), PG H0 -> incl H0 Amin ->
  (length Amin <= idxbound * length H0)%nat -> incl Amin H0.
Hypothesis Hhalfpart : forall P, PG P -> incl P Smax ->
  exists Pe, PG Pe /\ incl Pe P /\ incl Pe Amin /\
    (length P <= 2 * length Pe)%nat.

(** THE DESCENT STEP: a subgroup of bounded index in a sandwiched group is again sandwiched. *)
Lemma sandwich_step : forall (P P' : list (list nat)),
  PG P -> PG P' -> incl P' P ->
  (length P <= idxbound * length P')%nat ->
  ((incl P Amin /\ incl Amin P) \/ (incl P Smax /\ incl Smax P)) ->
  ((incl P' Amin /\ incl Amin P') \/ (incl P' Smax /\ incl Smax P')).
Proof.
  intros P P' HP HP' Hsub Hidx Hcase.
  destruct Hcase as [[HPA HAP] | [HPS HSP]].
  - assert (HlenP : length P = length Amin).
    { apply NoDup_same_set_length;
        [exact (PG_nd P HP) | exact HAnd | exact HPA | exact HAP]. }
    assert (HP'A : incl P' Amin)
      by (intros x Hx; apply HPA; apply Hsub; exact Hx).
    assert (HAP' : incl Amin P').
    { apply Hlarge; [exact HP' | exact HP'A | lia]. }
    left. split; assumption.
  - assert (HP'S : incl P' Smax)
      by (intros x Hx; apply HPS; apply Hsub; exact Hx).
    assert (HlenP : length P = length Smax).
    { apply NoDup_same_set_length;
        [exact (PG_nd P HP) | exact HSnd | exact HPS | exact HSP]. }
    destruct (Hhalfpart P' HP' HP'S) as [Pe [HPe_g [HPeP' [HPeA HPe_half]]]].
    assert (Hmono : (idxbound * length P' <= idxbound * (2 * length Pe))%nat)
      by (apply Nat.mul_le_mono_l; exact HPe_half).
    assert (HAPe : incl Amin Pe).
    { apply Hlarge; [exact HPe_g | exact HPeA | lia]. }
    assert (HAP' : incl Amin P').
    { intros x Hx. apply HPeP'. apply HAPe. exact Hx. }
    apply Hsandwich; [exact HP' | exact HAP'].
Qed.

(** Either sandwich case contains the small group. *)
Lemma sandwich_contains : forall P,
  ((incl P Amin /\ incl Amin P) \/ (incl P Smax /\ incl Smax P)) ->
  incl Amin P.
Proof.
  intros P [[_ H] | [_ H]]; [exact H |].
  intros q Hq. apply H. apply HAS. exact Hq.
Qed.

End SandwichDescent.

(** THE CHAIN INVARIANT, as the S6 instance: a subgroup of index at most five in an A6-or-S6 group is again A6 or S6. *)
Lemma chain_step_perm : forall (P P' : list (list nat)),
  pgroup P -> pgroup P' -> incl P' P ->
  (length P <= 5 * length P')%nat ->
  ((incl P A6list /\ incl A6list P) \/ (incl P S6list /\ incl S6list P)) ->
  ((incl P' A6list /\ incl A6list P') \/ (incl P' S6list /\ incl S6list P')).
Proof.
  apply (sandwich_step pgroup A6list S6list 5).
  - exact pg_nd.
  - exact (pg_nd A6list A6_pgroup).
  - exact (pg_nd S6list S6_pgroup).
  - rewrite A6list_length, S6list_length. lia.
  - exact between_A6_S6.
  - intros H0 HH0 HH0A Hbig.
    apply A6_subgroup_large; [exact HH0 | exact HH0A |].
    rewrite A6list_length in Hbig. exact Hbig.
  - intros Q HQ HQS.
    destruct (even_part_group Q HQ) as [HQe_g [HQe_half HQe_A]].
    exists (filter even_perm Q).
    split; [exact HQe_g |].
    split; [intros x Hx; apply filter_In in Hx; exact (proj1 Hx) |].
    split; [exact HQe_A | exact HQe_half].
Qed.

(* embeddings fixing the base induce a permutation group on the roots, over an arbitrary base subfield and root count, complete for all embeddings; the six-letter rational-base instance lands in pgroup. *)

Lemma cpeval_in_K : forall (K : C -> Prop) (cs : list C) (w : C),
  is_Csubfield K -> Forall K cs -> K w -> K (cpeval cs w).
Proof.
  intros K cs w HK Hcs Hw.
  induction Hcs as [|c cs Hc Hcs IH]; cbn [cpeval].
  - apply (Csubfield_0 K HK).
  - apply Csubfield_add; [exact HK | exact Hc |].
    apply Csubfield_mul; [exact HK | exact Hw | exact IH].
Qed.

Lemma RootChain_rs_in_rho : forall K0 rho rs js K,
  RootChain K0 rho rs js K -> incl rs rho.
Proof.
  intros K0 rho rs js K Hch.
  induction Hch as [| rs js K r j dt Hch IH Hin]; [intros x Hx; contradiction |].
  intros x Hx.
  apply in_app_or in Hx.
  destruct Hx as [Hx | [<- | []]]; [apply IH; exact Hx | exact Hin].
Qed.

(** Two embeddings agreeing on the base and at every adjoined root agree on the chain field. *)
Lemma RootChain_agree : forall K0 rho rs js K,
  is_Csubfield K0 -> RootChain K0 rho rs js K ->
  forall tau tau',
  CCembeds K tau -> CCembeds K tau' ->
  (forall x, K0 x -> tau x = tau' x) ->
  (forall r, In r rs -> tau r = tau' r) ->
  forall x, K x -> tau x = tau' x.
Proof.
  intros K0 rho rs js K HK0 Hch.
  induction Hch as [| rs js K r j dt Hch IH Hin Hj1 Hjn Hldt HKdt Hrel Hindep];
    intros tau tau' Htau Htau' Hbase Hroots x Hx.
  - apply Hbase. exact Hx.
  - assert (HKsub : is_Csubfield K)
      by (apply (RootChain_subfield K0 rho rs js K HK0 Hch)).
    apply (extensions_agree K r j dt tau tau' HKsub Hj1 Hldt HKdt Hrel
             Htau Htau'); [| | exact Hx].
    + intros y Hy.
      apply (IH tau tau').
      * apply (CCembeds_mono K (CPolyF K j r));
          [intros z Hz;
           apply (CPolyF_contains K r j dt HKsub Hj1 Hldt HKdt Hrel z Hz)
          | exact Htau].
      * apply (CCembeds_mono K (CPolyF K j r));
          [intros z Hz;
           apply (CPolyF_contains K r j dt HKsub Hj1 Hldt HKdt Hrel z Hz)
          | exact Htau'].
      * exact Hbase.
      * intros r0 Hr0. apply Hroots. apply in_or_app. left. exact Hr0.
      * exact Hy.
    + apply Hroots. apply in_or_app. right. left. reflexivity.
Qed.

(** The image of a chain field under an embedding sending base and roots into a field lands in that field. *)
Lemma RootChain_image : forall K0 rho rs js K',
  is_Csubfield K0 -> RootChain K0 rho rs js K' ->
  forall (K KE : C -> Prop) (tau : C -> C),
  is_Csubfield K -> CCembeds KE tau ->
  (forall x, K' x -> KE x) ->
  (forall x, K0 x -> K (tau x)) ->
  (forall r, In r rs -> K (tau r)) ->
  forall x, K' x -> K (tau x).
Proof.
  intros K0 rho rs js K' HK0 Hch.
  induction Hch as [| rs js Kp r j dt Hch IH Hin Hj1 Hjn Hldt HKdt Hrel Hindep];
    intros K KE tau HK Htau Hsub Hbase Hroots x Hx.
  - apply Hbase. exact Hx.
  - assert (HKpsub : is_Csubfield Kp)
      by (apply (RootChain_subfield K0 rho rs js Kp HK0 Hch)).
    assert (Hsub' : forall y, Kp y -> KE y).
    { intros y Hy. apply Hsub.
      apply (CPolyF_contains Kp r j dt HKpsub Hj1 Hldt HKdt Hrel y Hy). }
    assert (Htau_step : CCembeds (CPolyF Kp j r) tau)
      by (apply (CCembeds_mono (CPolyF Kp j r) KE tau Hsub Htau)).
    destruct Hx as [cs [Hlcs [Hcs Hxe]]].
    assert (HKcs : Forall Kp cs) by exact Hcs.
    assert (Hspan : tau x = cpeval (map tau cs) (tau r)).
    { rewrite Hxe.
      rewrite (CCembeds_value_on_span Kp r j dt tau HKpsub Hj1 Hldt HKdt Hrel
                 Htau_step cs HKcs).
      apply CCevalMap_cpeval_map. }
    rewrite Hspan.
    apply cpeval_in_K; [exact HK | |].
    + apply Forall_map_intro.
      intros c Hc.
      apply (IH K KE tau HK Htau Hsub' Hbase).
      * intros r0 Hr0. apply Hroots. apply in_or_app. left. exact Hr0.
      * exact (proj1 (Forall_forall Kp cs) HKcs c Hc).
    + apply Hroots. apply in_or_app. right. left. reflexivity.
Qed.

(** Embeddings fixing the coefficients of a split polynomial send its roots to roots. *)
Lemma embedding_root_to_root_over :
  forall (K : C -> Prop) (tau : C -> C) (rho Fcf : list C) (lead : C),
  is_Csubfield K -> CCembeds K tau ->
  lead <> C0 ->
  (forall z, cpeval Fcf z = (lead * prod_linear rho z)%C) ->
  Forall K Fcf ->
  (forall c, In c Fcf -> tau c = c) ->
  (forall z, In z rho -> K z) ->
  forall r, In r rho -> In (tau r) rho.
Proof.
  intros K tau rho Fcf lead HK Htau Hlead Hsplit HKF Hfixcf Hrho r Hr.
  assert (Hfix : Forall (fun c => tau c = c) Fcf)
    by (apply Forall_forall; exact Hfixcf).
  assert (HFr : cpeval Fcf r = C0).
  { rewrite Hsplit, (prod_linear_root rho r Hr r eq_refl). ring. }
  assert (HFtr : cpeval Fcf (tau r) = C0).
  { rewrite <- (tau_cpeval_fixed K tau HK Htau Fcf r HKF Hfix (Hrho r Hr)).
    rewrite HFr. exact (proj1 Htau). }
  rewrite Hsplit in HFtr.
  apply prod_linear_zero_in.
  destruct (Cmul_integral _ _ HFtr) as [E | E]; [contradiction | exact E].
Qed.

(** Embeddings fixing the base send roots to roots, on the rational base. *)
Lemma embedding_root_to_root :
  forall (K : C -> Prop) (tau : C -> C) (rho Fcf : list C) (lead : C),
  is_Csubfield K -> CCembeds K tau ->
  lead <> C0 ->
  (forall z, cpeval Fcf z = (lead * prod_linear rho z)%C) ->
  Forall CQ Fcf ->
  (forall z, CQ z -> K z) ->
  (forall z, In z rho -> K z) ->
  forall r, In r rho -> In (tau r) rho.
Proof.
  intros K tau rho Fcf lead HK Htau Hlead Hsplit HFQ HQK Hrho.
  apply (embedding_root_to_root_over K tau rho Fcf lead HK Htau Hlead Hsplit).
  - apply Forall_forall. intros c Hc.
    apply HQK. exact (proj1 (Forall_forall CQ Fcf) HFQ c Hc).
  - intros c Hc.
    apply (CCembeds_fixes_CQ K tau HK Htau HQK).
    exact (proj1 (Forall_forall CQ Fcf) HFQ c Hc).
  - exact Hrho.
Qed.

(** The index list of an embedding on a root list. *)
Lemma perm_of_embedding :
  forall (rho : list C) (tau : C -> C) (n : nat),
  NoDup rho -> length rho = n ->
  (forall i, (i < n)%nat -> In (tau (nth i rho C0)) rho) ->
  exists pm : list nat,
    length pm = n /\
    forall i, (i < n)%nat ->
      (nth i pm 0%nat < n)%nat /\
      nth (nth i pm 0%nat) rho C0 = tau (nth i rho C0).
Proof.
  intros rho tau n Hnd Hlen Himg.
  assert (Hgen : forall k, (k <= n)%nat ->
    exists pm : list nat,
      length pm = k /\
      forall i, (i < k)%nat ->
        (nth i pm 0%nat < n)%nat /\
        nth (nth i pm 0%nat) rho C0 = tau (nth i rho C0)).
  { intro k. induction k as [|k IHk]; intro Hk.
    - exists nil. split; [reflexivity | intros i Hi; lia].
    - destruct IHk as [pm [Hlpm Hpm]]; [lia |].
      destruct (In_nth rho (tau (nth k rho C0)) C0 (Himg k ltac:(lia)))
        as [jn [Hjn Hnthjn]].
      rewrite Hlen in Hjn.
      exists (pm ++ jn :: nil).
      split; [rewrite length_app, Hlpm; cbn [length]; lia |].
      intros i Hi.
      destruct (Nat.eq_dec i k) as [-> | Hne].
      + rewrite app_nth2 by lia.
        rewrite Hlpm, Nat.sub_diag. cbn [nth].
        split; [exact Hjn | exact Hnthjn].
      + rewrite app_nth1 by lia.
        apply Hpm. lia. }
  apply (Hgen n (Nat.le_refl _)).
Qed.

(** The induced index list is a permutation when the embedding is injective on the roots. *)
Lemma perm_of_embedding_in_perms_of :
  forall (rho : list C) (pm : list nat) (tau : C -> C) (n : nat),
  NoDup rho -> length rho = n ->
  (forall x y, In x rho -> In y rho -> tau x = tau y -> x = y) ->
  length pm = n ->
  (forall i, (i < n)%nat ->
     (nth i pm 0%nat < n)%nat /\
     nth (nth i pm 0%nat) rho C0 = tau (nth i rho C0)) ->
  In pm (perms_of (seq 0 n)).
Proof.
  intros rho pm tau n Hnd Hlen Hinj Hlpm Hpm.
  assert (Hpm_nd : NoDup pm).
  { apply (proj2 (NoDup_nth pm 0%nat)).
    intros a b Ha Hb He.
    rewrite Hlpm in Ha, Hb.
    destruct (Hpm a Ha) as [Hva Hna].
    destruct (Hpm b Hb) as [Hvb Hnb].
    assert (Hteq : tau (nth a rho C0) = tau (nth b rho C0))
      by (rewrite <- Hna, <- Hnb, He; reflexivity).
    assert (Hreq : nth a rho C0 = nth b rho C0).
    { apply Hinj; [apply nth_In; lia | apply nth_In; lia | exact Hteq]. }
    apply (proj1 (NoDup_nth rho C0) Hnd a b ltac:(lia) ltac:(lia) Hreq). }
  apply is_permn_in_perms_of; [exact Hlpm |].
  intros i Hi.
  assert (Hincl : incl (seq 0 n) pm).
  { apply (NoDup_length_incl Hpm_nd);
      [rewrite length_seq, Hlpm; lia |].
    intros v Hv.
    destruct (In_nth pm v 0%nat Hv) as [a [Ha Hnth]].
    rewrite Hlpm in Ha.
    apply in_seq.
    destruct (Hpm a Ha) as [Hva _].
    rewrite Hnth in Hva. lia. }
  assert (HiIn : In i pm) by (apply Hincl; apply in_seq; lia).
  destruct (In_nth pm i 0%nat HiIn) as [j [Hj Hnth]].
  rewrite Hlpm in Hj.
  exists j. split; [lia | exact Hnth].
Qed.

(** Composition of embeddings along an image-closed field. *)
Lemma CCembeds_compose :
  forall (K : C -> Prop) (sigma tau : C -> C),
  CCembeds K sigma -> CCembeds K tau ->
  (forall x, K x -> K (tau x)) ->
  CCembeds K (fun z => sigma (tau z)).
Proof.
  intros K sigma tau [Hs0 [Hs1 [Hsa Hsm]]] [Ht0 [Ht1 [Hta Htm]]] Himg.
  split; [rewrite Ht0; exact Hs0 |].
  split; [rewrite Ht1; exact Hs1 |].
  split.
  - intros x y Hx Hy.
    rewrite (Hta x y Hx Hy).
    apply Hsa; apply Himg; assumption.
  - intros x y Hx Hy.
    rewrite (Htm x y Hx Hy).
    apply Hsm; apply Himg; assumption.
Qed.

(** THE PERMUTATION GROUP OF AN EMBEDDING LIST, over an arbitrary base subfield and root count: a complete distinct embedding list induces a composition-closed NoDup list of root permutations containing the identity, complete for all embeddings fixing the base. *)
Theorem perm_group_of_embeddings_over :
  forall (K0 K : C -> Prop) (rho Fcf : list C) (lead : C)
         (rs : list C) (js : list nat) (sigmas : list (C -> C)) (N n : nat),
  is_Csubfield K0 -> NoDup rho -> length rho = n -> lead <> C0 ->
  (forall z, cpeval Fcf z = (lead * prod_linear rho z)%C) ->
  Forall K0 Fcf ->
  RootChain K0 rho rs js K ->
  incl rho rs ->
  length sigmas = N ->
  (forall i, (i < N)%nat ->
     CCembeds K (nth i sigmas (fun z => z)) /\
     (forall x, K0 x -> nth i sigmas (fun z => z) x = x)) ->
  (forall tau, CCembeds K tau -> (forall x, K0 x -> tau x = x) ->
     exists i, (i < N)%nat /\
       (forall x, K x -> tau x = nth i sigmas (fun z => z) x)) ->
  (forall i i', (i < N)%nat -> (i' < N)%nat -> i <> i' ->
     exists x, K x /\
       nth i sigmas (fun z => z) x <> nth i' sigmas (fun z => z) x) ->
  exists Perm : list (list nat),
    length Perm = N /\
    incl Perm (perms_of (seq 0 n)) /\
    NoDup Perm /\
    In (seq 0 n) Perm /\
    (forall p q, In p Perm -> In q Perm -> In (pcomp p q) Perm) /\
    (forall m, (m < N)%nat -> forall i, (i < n)%nat ->
       (nth i (nth m Perm (seq 0 n)) 0%nat < n)%nat /\
       nth (nth i (nth m Perm (seq 0 n)) 0%nat) rho C0
       = nth m sigmas (fun z => z) (nth i rho C0)) /\
    (forall tau, CCembeds K tau -> (forall x, K0 x -> tau x = x) ->
       exists m, (m < N)%nat /\
         forall i, (i < n)%nat ->
           tau (nth i rho C0) = nth (nth i (nth m Perm (seq 0 n)) 0%nat) rho C0).
Proof.
  intros K0 K rho Fcf lead rs js sigmas N n
         HK0 Hnd Hlenn Hlead Hsplit HKFcf Hch Hrhors Hlsig Hwf Hcomp Hdist.
  assert (HKsub : is_Csubfield K)
    by (apply (RootChain_subfield K0 rho rs js K HK0 Hch)).
  assert (HKF : Forall K Fcf).
  { apply Forall_forall. intros c Hc.
    apply (RootChain_incl K0 rho rs js K HK0 Hch).
    exact (proj1 (Forall_forall K0 Fcf) HKFcf c Hc). }
  assert (HrhoK : forall r, In r rho -> K r).
  { intros r Hr.
    apply (RootChain_roots_in K0 rho rs js K HK0 Hch).
    apply Hrhors. exact Hr. }
  (* each listed embedding sends roots to roots injectively *)
  assert (Hroot_img : forall m, (m < N)%nat -> forall i, (i < n)%nat ->
    In (nth m sigmas (fun z => z) (nth i rho C0)) rho).
  { intros m Hm i Hi.
    apply (embedding_root_to_root_over K (nth m sigmas (fun z => z)) rho Fcf lead
             HKsub (proj1 (Hwf m Hm)) Hlead Hsplit HKF).
    - intros c Hc.
      apply (proj2 (Hwf m Hm)).
      exact (proj1 (Forall_forall K0 Fcf) HKFcf c Hc).
    - exact HrhoK.
    - apply nth_In. lia. }
  assert (Hinj : forall m, (m < N)%nat ->
    forall x y, In x rho -> In y rho ->
    nth m sigmas (fun z => z) x = nth m sigmas (fun z => z) y -> x = y).
  { intros m Hm x y Hx Hy He.
    apply (CCembeds_injective_on K (nth m sigmas (fun z => z)) HKsub
             (proj1 (Hwf m Hm)) x y (HrhoK x Hx) (HrhoK y Hy) He). }
  (* materialize the permutation list *)
  assert (Hbuild : forall k, (k <= N)%nat ->
    exists Perm : list (list nat),
      length Perm = k /\
      forall m, (m < k)%nat ->
        length (nth m Perm (seq 0 n)) = n /\
        forall i, (i < n)%nat ->
          (nth i (nth m Perm (seq 0 n)) 0%nat < n)%nat /\
          nth (nth i (nth m Perm (seq 0 n)) 0%nat) rho C0
          = nth m sigmas (fun z => z) (nth i rho C0)).
  { intro k. induction k as [|k IHk]; intro Hk.
    - exists nil. split; [reflexivity | intros m Hm; lia].
    - destruct IHk as [Perm [HlP HP]]; [lia |].
      destruct (perm_of_embedding rho (nth k sigmas (fun z => z)) n Hnd Hlenn
                  (Hroot_img k ltac:(lia))) as [pm [Hlpm Hpm]].
      exists (Perm ++ pm :: nil).
      split; [rewrite length_app, HlP; cbn [length]; lia |].
      intros m Hm.
      destruct (Nat.eq_dec m k) as [-> | Hne].
      + rewrite app_nth2 by lia.
        rewrite HlP, Nat.sub_diag. cbn [nth].
        split; [exact Hlpm | exact Hpm].
      + rewrite app_nth1 by lia.
        apply HP. lia. }
  destruct (Hbuild N (Nat.le_refl _)) as [Perm [HlP HP]].
  (* index determination *)
  assert (Hdet : forall (pm pm' : list nat),
    length pm = n -> length pm' = n ->
    (forall i, (i < n)%nat -> (nth i pm 0%nat < n)%nat) ->
    (forall i, (i < n)%nat -> (nth i pm' 0%nat < n)%nat) ->
    (forall i, (i < n)%nat ->
       nth (nth i pm 0%nat) rho C0 = nth (nth i pm' 0%nat) rho C0) ->
    pm = pm').
  { intros pm pm' Hl Hl' Hb Hb' He.
    apply (nth_ext pm pm' 0%nat 0%nat); [lia |].
    intros i Hi.
    rewrite Hl in Hi.
    apply (proj1 (NoDup_nth rho C0) Hnd);
      [rewrite Hlenn; apply Hb; exact Hi
       | rewrite Hlenn; apply Hb'; exact Hi
       | apply He; exact Hi]. }
  exists Perm.
  split; [exact HlP |].
  assert (HPin : forall m, (m < N)%nat ->
    In (nth m Perm (seq 0 n)) (perms_of (seq 0 n))).
  { intros m Hm.
    apply (perm_of_embedding_in_perms_of rho (nth m Perm (seq 0 n))
             (nth m sigmas (fun z => z)) n Hnd Hlenn (Hinj m Hm)
             (proj1 (HP m Hm)) (proj2 (HP m Hm))). }
  (* completeness at the permutation level *)
  assert (Hpcomplete : forall tau, CCembeds K tau ->
    (forall x, K0 x -> tau x = x) ->
    exists m, (m < N)%nat /\
      forall i, (i < n)%nat ->
        tau (nth i rho C0) = nth (nth i (nth m Perm (seq 0 n)) 0%nat) rho C0).
  { intros tau Htau Hfix.
    destruct (Hcomp tau Htau Hfix) as [m [Hm Hagr]].
    exists m.
    split; [exact Hm |].
    intros i Hi.
    assert (Hin_i : In (nth i rho C0) rho)
      by (apply nth_In; rewrite Hlenn; lia).
    rewrite (Hagr (nth i rho C0) (HrhoK _ Hin_i)).
    symmetry.
    exact (proj2 ((proj2 (HP m Hm)) i Hi)).
  }
  split; [| split; [| split; [| split; [| split]]]].
  - (* the images are permutations *)
    intros pm Hpm.
    destruct (In_nth Perm pm (seq 0 n) Hpm) as [m [Hm Hnth]].
    rewrite HlP in Hm.
    rewrite <- Hnth.
    apply HPin. exact Hm.
  - (* NoDup: distinct embeddings differ at a root *)
    apply (proj2 (NoDup_nth Perm (seq 0 n))).
    intros a b Ha Hb He.
    rewrite HlP in Ha, Hb.
    destruct (Nat.eq_dec a b) as [E | Hne]; [exact E | exfalso].
    destruct (Hdist a b Ha Hb Hne) as [x [HxK Hxne]].
    apply Hxne.
    apply (RootChain_agree K0 rho rs js K HK0 Hch
             (nth a sigmas (fun z => z)) (nth b sigmas (fun z => z))
             (proj1 (Hwf a Ha)) (proj1 (Hwf b Hb))); [| | exact HxK].
    + intros y Hy.
      rewrite (proj2 (Hwf a Ha) y Hy), (proj2 (Hwf b Hb) y Hy).
      reflexivity.
    + intros r Hr.
      assert (Hrrho : In r rho)
        by (apply (RootChain_rs_in_rho K0 rho rs js K Hch); exact Hr).
      destruct (In_nth rho r C0 Hrrho) as [i [Hi Hnthi]].
      rewrite Hlenn in Hi.
      rewrite <- Hnthi.
      rewrite <- (proj2 ((proj2 (HP a Ha)) i Hi)).
      rewrite <- (proj2 ((proj2 (HP b Hb)) i Hi)).
      rewrite He.
      reflexivity.
  - (* identity *)
    assert (Hid : exists m, (m < N)%nat /\
      forall i, (i < n)%nat ->
        nth i rho C0 = nth (nth i (nth m Perm (seq 0 n)) 0%nat) rho C0).
    { destruct (Hpcomplete (fun z => z) (CCembeds_id K)
                  (fun x _ => eq_refl)) as [m [Hm Hagr]].
      exists m. split; [exact Hm | exact Hagr]. }
    destruct Hid as [m [Hm Hagr]].
    assert (Hlseq : length (seq 0 n) = n) by (rewrite length_seq; reflexivity).
    assert (Hpid : nth m Perm (seq 0 n) = seq 0 n).
    { apply (Hdet (nth m Perm (seq 0 n)) (seq 0 n)
               (proj1 (HP m Hm)) Hlseq).
      - intros i Hi. exact (proj1 ((proj2 (HP m Hm)) i Hi)).
      - intros i Hi.
        assert (Hnth_pid : nth i (seq 0 n) 0%nat = i).
        { rewrite seq_nth by exact Hi. reflexivity. }
        rewrite Hnth_pid. exact Hi.
      - intros i Hi.
        assert (Hnth_pid : nth i (seq 0 n) 0%nat = i).
        { rewrite seq_nth by exact Hi. reflexivity. }
        rewrite Hnth_pid.
        symmetry. apply Hagr. exact Hi. }
    rewrite <- Hpid.
    apply nth_In. rewrite HlP. exact Hm.
  - (* closure under composition *)
    intros pa pb Hpa Hpb.
    destruct (In_nth Perm pa (seq 0 n) Hpa) as [a [Ha Hnth_a]].
    destruct (In_nth Perm pb (seq 0 n) Hpb) as [b [Hb Hnth_b]].
    rewrite HlP in Ha, Hb.
    set (sa := nth a sigmas (fun z => z)) in *.
    set (sb := nth b sigmas (fun z => z)) in *.
    assert (Hsb_img : forall x, K x -> K (sb x)).
    { intros x Hx.
      apply (RootChain_image K0 rho rs js K HK0 Hch K K sb HKsub
               (proj1 (Hwf b Hb)) (fun y Hy => Hy)); [| | exact Hx].
      - intros y Hy.
        unfold sb.
        rewrite (proj2 (Hwf b Hb) y Hy).
        apply (RootChain_incl K0 rho rs js K HK0 Hch y Hy).
      - intros r Hr.
        assert (Hrrho : In r rho)
          by (apply (RootChain_rs_in_rho K0 rho rs js K Hch); exact Hr).
        destruct (In_nth rho r C0 Hrrho) as [i [Hi Hnthi]].
        rewrite Hlenn in Hi.
        apply HrhoK.
        unfold sb.
        rewrite <- Hnthi.
        rewrite <- (proj2 ((proj2 (HP b Hb)) i Hi)).
        apply nth_In.
        rewrite Hlenn.
        exact (proj1 ((proj2 (HP b Hb)) i Hi)). }
    assert (Hcompemb : CCembeds K (fun z => sa (sb z))).
    { apply CCembeds_compose;
        [exact (proj1 (Hwf a Ha)) | exact (proj1 (Hwf b Hb)) | exact Hsb_img]. }
    assert (Hcompfix : forall x, K0 x -> sa (sb x) = x).
    { intros x Hx.
      unfold sa, sb.
      rewrite (proj2 (Hwf b Hb) x Hx).
      exact (proj2 (Hwf a Ha) x Hx). }
    destruct (Hpcomplete (fun z => sa (sb z)) Hcompemb Hcompfix)
      as [c [Hc Hagr]].
    assert (Hceq : nth c Perm (seq 0 n) = pcomp pa pb).
    { apply (Hdet (nth c Perm (seq 0 n)) (pcomp pa pb)
               (proj1 (HP c Hc))).
      - unfold pcomp. rewrite length_map, <- Hnth_b.
        exact (proj1 (HP b Hb)).
      - intros i Hi. exact (proj1 ((proj2 (HP c Hc)) i Hi)).
      - intros i Hi.
        unfold pcomp.
        rewrite (nth_indep _ 0%nat (nth 0%nat pa 0%nat))
          by (rewrite length_map, <- Hnth_b; rewrite (proj1 (HP b Hb)); exact Hi).
        rewrite (map_nth (fun k => nth k pa 0%nat) pb 0%nat i).
        rewrite <- Hnth_a, <- Hnth_b.
        assert (Hbb := (proj2 (HP b Hb)) i Hi).
        destruct Hbb as [Hbv _].
        exact (proj1 ((proj2 (HP a Ha)) (nth i (nth b Perm (seq 0 n)) 0%nat) Hbv)).
      - intros i Hi.
        rewrite <- (Hagr i Hi).
        unfold pcomp.
        rewrite (nth_indep _ 0%nat (nth 0%nat pa 0%nat))
          by (rewrite length_map, <- Hnth_b;
              rewrite (proj1 (HP b Hb)); exact Hi).
        rewrite (map_nth (fun k => nth k pa 0%nat) pb 0%nat i).
        rewrite <- Hnth_a, <- Hnth_b.
        assert (Hbb := (proj2 (HP b Hb)) i Hi).
        destruct Hbb as [Hbv Hbe].
        rewrite (proj2 ((proj2 (HP a Ha)) (nth i (nth b Perm (seq 0 n)) 0%nat) Hbv)).
        rewrite Hbe.
        reflexivity. }
    rewrite <- Hceq.
    apply nth_In. rewrite HlP. exact Hc.
  - (* the per-index specification *)
    intros m Hm i Hi.
    exact ((proj2 (HP m Hm)) i Hi).
  - exact Hpcomplete.
Qed.

(** THE PERMUTATION GROUP OF AN EMBEDDING LIST, as the six-letter rational-base instance landing in pgroup. *)
Theorem perm_group_of_embeddings :
  forall (K0 K : C -> Prop) (rho Fcf : list C) (lead : C)
         (rs : list C) (js : list nat) (sigmas : list (C -> C)) (N : nat),
  is_Csubfield K0 -> NoDup rho -> length rho = 6%nat -> lead <> C0 ->
  (forall z, cpeval Fcf z = (lead * prod_linear rho z)%C) ->
  Forall CQ Fcf ->
  (forall z, CQ z -> K0 z) ->
  RootChain K0 rho rs js K ->
  incl rho rs ->
  length sigmas = N ->
  (forall i, (i < N)%nat ->
     CCembeds K (nth i sigmas (fun z => z)) /\
     (forall x, K0 x -> nth i sigmas (fun z => z) x = x)) ->
  (forall tau, CCembeds K tau -> (forall x, K0 x -> tau x = x) ->
     exists i, (i < N)%nat /\
       (forall x, K x -> tau x = nth i sigmas (fun z => z) x)) ->
  (forall i i', (i < N)%nat -> (i' < N)%nat -> i <> i' ->
     exists x, K x /\
       nth i sigmas (fun z => z) x <> nth i' sigmas (fun z => z) x) ->
  exists Perm : list (list nat),
    length Perm = N /\
    pgroup Perm /\
    (forall m, (m < N)%nat -> forall i, (i < 6)%nat ->
       (nth i (nth m Perm pid6) 0%nat < 6)%nat /\
       nth (nth i (nth m Perm pid6) 0%nat) rho C0
       = nth m sigmas (fun z => z) (nth i rho C0)) /\
    (forall tau, CCembeds K tau -> (forall x, K0 x -> tau x = x) ->
       exists m, (m < N)%nat /\
         forall i, (i < 6)%nat ->
           tau (nth i rho C0) = nth (nth i (nth m Perm pid6) 0%nat) rho C0).
Proof.
  intros K0 K rho Fcf lead rs js sigmas N
         HK0 Hnd Hlen6 Hlead Hsplit HFQ HQK0 Hch Hrhors Hlsig Hwf Hcomp Hdist.
  assert (HK0F : Forall K0 Fcf).
  { apply Forall_forall. intros c Hc.
    apply HQK0. exact (proj1 (Forall_forall CQ Fcf) HFQ c Hc). }
  destruct (perm_group_of_embeddings_over K0 K rho Fcf lead rs js sigmas N 6
              HK0 Hnd Hlen6 Hlead Hsplit HK0F Hch Hrhors Hlsig Hwf Hcomp Hdist)
    as [Perm [HlP [Hincl [HndP [Hid [Hclos [Hspec Hcompl]]]]]]].
  exists Perm.
  split; [exact HlP |].
  split; [| split].
  - constructor.
    + exact Hincl.
    + exact HndP.
    + exact Hid.
    + exact Hclos.
  - exact Hspec.
  - exact Hcompl.
Qed.

(* monic divisors of split polynomials split, the quartic step split, and the one-step descent wiring for the count. *)

Lemma prod_linear_app : forall u v z,
  prod_linear (u ++ v) z = (prod_linear u z * prod_linear v z)%C.
Proof.
  induction u as [|a u IH]; intros v z; cbn [app prod_linear].
  - ring.
  - rewrite IH. ring.
Qed.

Lemma prod_linear_extract : forall ws w, In w ws ->
  exists u v, ws = u ++ w :: v /\
  forall z, prod_linear ws z = ((z - w) * prod_linear (u ++ v) z)%C.
Proof.
  intros ws w Hw.
  destruct (in_split w ws Hw) as [u [v Hsplit]].
  exists u, v.
  split; [exact Hsplit |].
  intro z.
  rewrite Hsplit.
  rewrite !prod_linear_app.
  cbn [prod_linear].
  ring.
Qed.

Lemma cpdiv_head_monic : forall (A' : list C) (w : C),
  hd C0 A' = C1 -> (2 <= length A')%nat ->
  hd C0 (fst (cpdiv_lf (length A') A' (Copp w :: nil))) = C1 /\
  length (fst (cpdiv_lf (length A') A' (Copp w :: nil)))
    = (length A' - 1)%nat.
Proof.
  intros A' w Hhd Hlen.
  destruct A' as [|a p']; [cbn [length] in Hlen; lia |].
  cbn [hd] in Hhd. subst a.
  assert (Hp1 : (1 <= length p')%nat) by (cbn [length] in Hlen; lia).
  rewrite (cpdiv_head_linear C1 (Copp w) p' Hp1).
  split; [reflexivity |].
  cbn [length].
  rewrite (cpdiv_lf_qlen (length p')
             (cpadd p' (cpscale (Copp C1) (cpscale C1 (Copp w :: nil))))
             (Copp w :: nil)).
  - rewrite cpadd_length, !cpscale_length.
    cbn [length]. lia.
  - rewrite cpadd_length, !cpscale_length.
    cbn [length]. lia.
Qed.

(** THE FULL SPLIT OF A DIVISOR. *)
Lemma split_divisor_splits :
  forall (n : nat) (ws A B : list C),
  length A = n ->
  hd C0 A = C1 -> (1 <= length A)%nat ->
  (forall z, prod_linear ws z = (cpeval_lf A z * cpeval_lf B z)%C) ->
  exists wsA, length wsA = (length A - 1)%nat /\
  forall z, cpeval_lf A z = prod_linear wsA z.
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros ws A B Hn Hhd Hlen Hsplit.
  destruct (Nat.eq_dec (length A) 1%nat) as [H1 | H2].
  - destruct A as [|a [|? ?]]; try (cbn [length] in H1; lia).
    cbn [hd] in Hhd. subst a.
    exists nil.
    split; [cbn [length]; lia |].
    intro z. cbn [cpeval_lf prod_linear length Cpow]. ring.
  - assert (Hlen2 : (2 <= length A)%nat) by lia.
    destruct (split_divisor_has_root ws A B Hhd Hlen2 Hsplit) as [w [Hw HAw]].
    set (A' := fst (cpdiv_lf (length A) A (Copp w :: nil))).
    assert (Hfac : forall z, cpeval_lf A z = (cpeval_lf A' z * (z - w))%C)
      by (intro z; apply (cp_root_factor A w HAw z)).
    destruct (cpdiv_head_monic A w Hhd Hlen2) as [Hhd' Hlen'].
    fold A' in Hhd', Hlen'.
    destruct (prod_linear_extract ws w Hw) as [u [v [Hws Hprod]]].
    assert (Hcancel : forall z,
      prod_linear (u ++ v) z = (cpeval_lf A' z * cpeval_lf B z)%C).
    { intro z.
      assert (Hid : forall y,
        (cpeval_lf (plin_list (u ++ v)) y * (y - w))%C
        = (cpeval_lf (cpmul_lf A' B) y * (y - w))%C).
      { intro y.
        rewrite plin_list_eval, cpmul_lf_eval.
        pose proof (Hsplit y) as Hy.
        rewrite (Hprod y) in Hy.
        rewrite (Hfac y) in Hy.
        transitivity ((y - w) * prod_linear (u ++ v) y)%C; [ring |].
        rewrite Hy. ring. }
      pose proof (cancel_linear_factor (plin_list (u ++ v)) (cpmul_lf A' B)
                    w Hid z) as Hc.
      rewrite plin_list_eval, cpmul_lf_eval in Hc.
      exact Hc. }
    destruct (IHn (length A') ltac:(lia) (u ++ v) A' B eq_refl Hhd'
                ltac:(lia) Hcancel) as [wsA' [HlwsA' HevA']].
    exists (w :: wsA').
    split; [cbn [length]; lia |].
    intro z.
    cbn [prod_linear].
    rewrite <- HevA'.
    rewrite (Hfac z). ring.
Qed.

(** Degree-4 split, real coefficients, closing the two-fold step degrees. *)
Lemma monic_step_splits_4 : forall a3 a2 a1 a0 : R,
  exists ws : list C, length ws = 4%nat /\
  forall z, (cpeval (map RtoC (a0 :: a1 :: a2 :: a3 :: nil)) z + Cpow z 4)%C
            = prod_linear ws z.
Proof.
  intros a3 a2 a1 a0.
  destruct (Cquartic_split (RtoC a3) (RtoC a2) (RtoC a1) (RtoC a0))
    as [z1 [z2 [z3 [z4 Hq]]]].
  exists (z1 :: z2 :: z3 :: z4 :: nil).
  split; [reflexivity |].
  intro z.
  cbn [map cpeval prod_linear].
  assert (Hp4 : Cpow z 4 = (z * z * (z * z))%C) by (cbn [Cpow]; ring).
  rewrite Hp4.
  transitivity ((z * z * (z * z) + RtoC a3 * (z * z * z)
                 + RtoC a2 * (z * z) + RtoC a1 * z + RtoC a0)%C); [ring |].
  rewrite (Hq z). ring.
Qed.

(** THE STEP SPLIT for all two-fold degrees. *)
Lemma monic_real_step_splits_all : forall (d : nat) (rt : list R),
  (2 <= d)%nat -> (d <= 5)%nat -> length rt = d ->
  exists ws : list C, length ws = d /\
  forall z, (cpeval (map RtoC rt) z + Cpow z d)%C = prod_linear ws z.
Proof.
  intros d rt Hd2 Hd5 Hlen.
  destruct (Nat.eq_dec d 4%nat) as [-> | Hne4].
  - destruct rt as [|c0 [|c1 [|c2 [|c3 [|? ?]]]]];
      try (cbn [length] in Hlen; lia).
    destruct (monic_step_splits_4 c3 c2 c1 c0) as [ws [Hlw Hws]].
    exists ws. split; [exact Hlw | exact Hws].
  - apply monic_real_step_splits; [lia | exact Hlen].
Qed.

(** THE TOWER-STEP DESCENT: chain counts over the base and the extended base, for one real step element of degree at most five. *)
Theorem tower_step_descent :
  forall (B : C -> Prop) (rho Fcf : list C) (lead : C)
         (rt : list R) (db : nat) (beta : C)
         (rsB : list C) (jsB : list nat) (K : C -> Prop)
         (rsB' : list C) (jsB' : list nat) (K' : C -> Prop),
  is_Csubfield B -> NoDup rho -> lead <> C0 ->
  (forall z, cpeval Fcf z = (lead * prod_linear rho z)%C) ->
  Forall B Fcf -> length Fcf = Datatypes.S (length rho) ->
  Forall CQ Fcf ->
  (forall z, CQ z -> B z) ->
  (2 <= db)%nat -> (db <= 5)%nat -> length rt = db ->
  Forall B (map RtoC rt) ->
  (cpeval (map RtoC rt) beta + Cpow beta db)%C = C0 ->
  RootChain B rho rsB jsB K -> incl rho rsB ->
  RootChain (CPolyF B db beta) rho rsB' jsB' K' -> incl rho rsB' ->
  (prodl jsB <= db * prodl jsB')%nat.
Proof.
  intros B rho Fcf lead rt db beta rsB jsB K rsB' jsB' K'
         HB Hnd Hlead Hsplit HBF HlF HFQ HQB
         Hdb2 Hdb5 Hlrt HBrt Hrel HchB HrhoB HchB' HrhoB'.
  set (dtB := map RtoC rt) in *.
  assert (HldtB : length dtB = db)
    by (unfold dtB; rewrite length_map; exact Hlrt).
  assert (HKsub : is_Csubfield K)
    by (apply (RootChain_subfield B rho rsB jsB K HB HchB)).
  assert (HB'sub : is_Csubfield (CPolyF B db beta)).
  { apply (CPolyF_Csubfield B beta db dtB HB ltac:(lia) HldtB HBrt Hrel). }
  assert (HK'sub : is_Csubfield K')
    by (apply (RootChain_subfield _ rho rsB' jsB' K' HB'sub HchB')).
  assert (HBK : forall x, B x -> K x)
    by (apply (RootChain_incl B rho rsB jsB K HB HchB)).
  (* the relation of beta over K, minimized *)
  assert (HdtBK : Forall K dtB).
  { apply Forall_forall. intros c Hc.
    apply HBK. exact (proj1 (Forall_forall B dtB) HBrt c Hc). }
  destruct (cpowers_max_prefix K beta db HKsub ltac:(lia))
    as [jb [Hjb_le [Hjb_ind Hjb_case]]].
  assert (Hjb_rel : exists dtK, length dtK = jb /\ Forall K dtK /\
    (cpeval dtK beta + Cpow beta jb)%C = C0).
  { destruct Hjb_case as [-> | Hex].
    - exists dtB. repeat split; assumption.
    - exact Hex. }
  destruct Hjb_rel as [dtK [HldtK [HKdtK HrelK]]].
  assert (Hjb1 : (1 <= jb)%nat) by lia.
  set (M := CPolyF K jb beta).
  assert (HMsub : is_Csubfield M)
    by (apply (CPolyF_Csubfield K beta jb dtK HKsub Hjb1 HldtK HKdtK HrelK)).
  (* field equality M = K' *)
  assert (HKK' : forall x, K x -> K' x).
  { apply (RootChain_contained B rho rsB jsB K K' HB HchB HK'sub).
    - intros x Hx.
      apply (RootChain_incl _ rho rsB' jsB' K' HB'sub HchB').
      apply (CPolyF_contains B beta db dtB HB ltac:(lia) HldtB HBrt Hrel x Hx).
    - intros r Hr.
      apply (RootChain_roots_in _ rho rsB' jsB' K' HB'sub HchB').
      apply HrhoB'.
      apply (RootChain_rs_in_rho B rho rsB jsB K HchB).
      exact Hr. }
  assert (HbetaK' : K' beta).
  { apply (RootChain_incl _ rho rsB' jsB' K' HB'sub HchB').
    apply (CPolyF_r_mem B beta db dtB HB ltac:(lia) HldtB HBrt Hrel). }
  assert (HMK' : forall x, M x -> K' x).
  { intros x [cs [Hlcs [HKcs Hxe]]].
    rewrite Hxe.
    apply cpeval_in_K; [exact HK'sub | | exact HbetaK'].
    apply Forall_forall. intros c Hc.
    apply HKK'. exact (proj1 (Forall_forall K cs) HKcs c Hc). }
  assert (HbetaM : M beta)
    by (apply (CPolyF_r_mem K beta jb dtK HKsub Hjb1 HldtK HKdtK HrelK)).
  assert (HB'M : forall x, CPolyF B db beta x -> M x).
  { intros x [cs [Hlcs [HBcs Hxe]]].
    rewrite Hxe.
    apply cpeval_in_K; [exact HMsub | | exact HbetaM].
    apply Forall_forall. intros c Hc.
    apply (CPolyF_contains K beta jb dtK HKsub Hjb1 HldtK HKdtK HrelK).
    apply HBK.
    exact (proj1 (Forall_forall B cs) HBcs c Hc). }
  assert (HK'M : forall x, K' x -> M x).
  { apply (RootChain_contained _ rho rsB' jsB' K' M HB'sub HchB' HMsub).
    - exact HB'M.
    - intros r Hr.
      apply (CPolyF_contains K beta jb dtK HKsub Hjb1 HldtK HKdtK HrelK).
      apply (RootChain_roots_in B rho rsB jsB K HB HchB).
      apply HrhoB.
      apply (RootChain_rs_in_rho _ rho rsB' jsB' K' HchB').
      exact Hr. }
  (* the G-list over B *)
  destruct (RootChain_embeddings B rho Fcf lead HB Hnd Hlead Hsplit HBF HlF
              rsB jsB K HchB) as [sigmas [Hlsig [Hwf [_ Hdist]]]].
  (* apply the descent counting *)
  apply (descent_step B K beta db dtB jb dtK sigmas
           (prodl jsB) (prodl jsB') HB HKsub HBK
           ltac:(lia) HldtB HBrt Hrel Hjb1 HldtK HKdtK HrelK Hjb_ind).
  - (* the split certificate *)
    intros sigma Hemb Hfix.
    assert (Hg : forall z, cpeval (dtB ++ C1 :: nil) z
                 = (cpeval dtB z + Cpow z db * C1)%C).
    { intro z. rewrite cpeval_app, HldtB. cbn [cpeval]. ring. }
    assert (Hgroot : cpeval (dtB ++ C1 :: nil) beta = C0).
    { rewrite Hg.
      transitivity ((cpeval dtB beta + Cpow beta db)%C); [ring | exact Hrel]. }
    assert (HKg : Forall K (dtB ++ C1 :: nil)).
    { apply Forall_app_intro_c; [exact HdtBK |].
      constructor; [apply (Csubfield_1 K HKsub) | constructor]. }
    destruct (cminpoly_divides K beta jb dtK HKsub Hjb1 HldtK HKdtK HrelK
                Hjb_ind (dtB ++ C1 :: nil) HKg Hgroot) as [HKQ Hdiv].
    set (Q := fst (cpdiv_lf (length (rev (dtB ++ C1 :: nil)))
                     (rev (dtB ++ C1 :: nil)) (rev dtK))) in *.
    (* sigma-image of the divides identity *)
    assert (Hfixdt : Forall (fun c => sigma c = c) dtB).
    { apply Forall_forall. intros c Hc.
      apply Hfix. exact (proj1 (Forall_forall B dtB) HBrt c Hc). }
    destruct (monic_real_step_splits_all db rt Hdb2 Hdb5 Hlrt)
      as [ws [Hlws Hws]].
    (* coefficient-level factorization *)
    assert (HlQ : length Q = Datatypes.S (db - jb)).
    { unfold Q. rewrite (cpdiv_lf_qlen _ _ _ (Nat.le_refl _)).
      rewrite !length_rev, length_app, HldtB, HldtK.
      cbn [length]. lia. }
    assert (Hcoeff : (dtB ++ C1 :: nil) = cpmul (rev Q) (dtK ++ C1 :: nil)).
    { apply cpeval_ext_coeffs.
      - rewrite cpmul_length;
          [| rewrite length_rev, HlQ; lia
           | rewrite length_app, HldtK; cbn [length]; lia].
        rewrite length_rev, HlQ, !length_app, HldtK, HldtB.
        cbn [length]. lia.
      - intro z.
        rewrite cpeval_cpmul.
        rewrite (Hdiv z).
        assert (HQz : cpeval (rev Q) z = cpeval_lf Q z)
          by (rewrite cpeval_lf_rev_c; reflexivity).
        assert (HMz : cpeval (dtK ++ C1 :: nil) z = (Cpow z jb + cpeval dtK z)%C).
        { rewrite cpeval_app, HldtK. cbn [cpeval]. ring. }
        rewrite HQz, HMz. ring. }
    (* image identity: P = (sigma Q) * (sigma M) *)
    assert (Himg : forall z,
      prod_linear ws z
      = (cpeval_lf (C1 :: rev (map sigma dtK)) z
         * cpeval_lf (map sigma Q) z)%C).
    { intro z.
      assert (HPfix : CCevalMap sigma (dtB ++ C1 :: nil) z
                      = cpeval (dtB ++ C1 :: nil) z).
      { rewrite (CCevalMap_ext_on sigma (fun c => c));
          [apply CCevalMap_id |].
        apply Forall_app_intro_c;
          [exact Hfixdt
          | constructor; [exact (proj1 (proj2 Hemb)) | constructor]]. }
      assert (HP : cpeval (dtB ++ C1 :: nil) z = prod_linear ws z).
      { rewrite Hg.
        transitivity ((cpeval dtB z + Cpow z db)%C); [ring |].
        apply Hws. }
      assert (Ht1 : CCevalMap sigma (rev Q) z = cpeval_lf (map sigma Q) z).
      { rewrite CCevalMap_cpeval_map.
        rewrite map_rev.
        rewrite (cpeval_lf_rev_c (map sigma Q) z).
        reflexivity. }
      assert (Ht2 : CCevalMap sigma (dtK ++ C1 :: nil) z
                    = cpeval_lf (C1 :: rev (map sigma dtK)) z).
      { rewrite CCevalMap_app, HldtK.
        cbn [CCevalMap].
        rewrite (proj1 (proj2 Hemb)).
        cbn [cpeval_lf].
        rewrite length_rev, length_map, HldtK.
        rewrite cpeval_lf_rev_c, rev_involutive.
        rewrite <- CCevalMap_cpeval_map.
        ring. }
      rewrite <- HP, <- HPfix.
      rewrite Hcoeff at 1.
      rewrite (CCevalMap_cpmul K sigma Hemb HKsub);
        [| apply Forall_rev; exact HKQ
         | apply Forall_app_intro_c;
             [exact HKdtK
             | constructor; [apply (Csubfield_1 K HKsub) | constructor]]].
      rewrite Ht1, Ht2.
      ring. }
    destruct (split_divisor_splits (length (C1 :: rev (map sigma dtK))) ws
                (C1 :: rev (map sigma dtK)) (map sigma Q) eq_refl
                ltac:(reflexivity)
                ltac:(cbn [length]; lia) Himg) as [ws' [Hlws' Hevws']].
    exists ws'.
    split.
    { rewrite Hlws'. cbn [length].
      rewrite length_rev, length_map, HldtK. lia. }
    intro z.
    rewrite <- (Hevws' z).
    cbn [cpeval_lf].
    rewrite length_rev, length_map, HldtK.
    rewrite cpeval_lf_rev_c, rev_involutive.
    rewrite <- CCevalMap_cpeval_map.
    ring.
  - exact Hlsig.
  - exact Hwf.
  - exact Hdist.
  - (* the equal fibers over the extended base *)
    intros nu Hnuemb Hnufix.
    assert (HnuF : Forall (fun c => nu c = c) Fcf).
    { apply Forall_forall. intros c Hc.
      apply Hnufix.
      apply HQB.
      exact (proj1 (Forall_forall CQ Fcf) HFQ c Hc). }
    assert (HB'F : Forall (CPolyF B db beta) Fcf).
    { apply Forall_forall. intros c Hc.
      apply (CPolyF_contains B beta db dtB HB ltac:(lia) HldtB HBrt Hrel).
      exact (proj1 (Forall_forall B Fcf) HBF c Hc). }
    destruct (RootChain_embeddings_over (CPolyF B db beta) rho Fcf lead nu
                HB'sub Hnd Hlead Hsplit HB'F HlF Hnuemb HnuF
                rsB' jsB' K' HchB')
      as [sigmas' [Hlsig' [Hwf' [Hcomp' _]]]].
    exists sigmas'.
    split; [exact Hlsig' |].
    intros tau Htau Hagr.
    assert (Htau' : CCembeds K' tau).
    { apply (CCembeds_ext_pred M K' tau); [| exact Htau].
      intro x. split; [apply HMK' | apply HK'M]. }
    destruct (Hcomp' tau Htau' Hagr) as [k [Hk Hagrk]].
    exists k.
    split; [exact Hk |].
    intros x Hx.
    apply Hagrk.
    apply HMK'.
    exact Hx.
Qed.

(* the witness certificates -- the integer sextic, its monicized difference-resolvent quotient S15, the Bezout cofactors, and the dyadic root brackets. *)

Open Scope Z_scope.
Definition witFz : list Z :=
  (2795309191751463646995099641203274900592260%Z :: (-250439519908253635661434543391737596)%Z :: (-71579381792837368681196275607)%Z :: 12528974921812564304936%Z :: (-1034347114106394)%Z :: 347428%Z :: 1%Z :: nil).

Definition witS15z : list Z :=
  (9755936680303407142079972936243184006105618289993480551583696655989494509066190903385872600389761080309386898179183017279725047838318446797842220094414032867997743389716619663930482256849639499622524263602742886400000000%Z :: 131796984686304770021010627023096159345405758159826712099066559059529230068702433020955181979275772741453916694003022261709845634592810122496524862462898804262255561928368914122070212242435789282544457875456%Z :: (-1323120843744956372195472026818140943434383821739726553964132418772421915119817225961914436055952477897524958707943685756434113759949829945858605255538179842075662124388813360988453020622913536)%Z :: (-7975929178474211921590965248946150234124484113224202289934038164919183233165061969767903851285939408473315439615064060289173162576937287180658784598865231040568976679501369171712)%Z :: 120735410747479230550071881012036017251645259375546049539402704484300149125462952482001055441835985155796354833286357033907038878569212828930453571526639091101391104%Z :: (-998948913431351249002363014758809712400081376649103246631826776553849194624905401309207808016924299489595386835387837922210439517544681620939715675040)%Z :: 3124902711748894862876582155104005081745015996725665338389424135936707370891017381457423176935940649761170894138086138238925238987836432%Z :: 3513677485573415932545607796750390600028428565788116941356797636572806847706931630559193907225454664010189399558019119969%Z :: (-52494786796451316139104625624096951790108785395766922117425101321063986171520623278310237822796089518476440)%Z :: 168583619128104983726196509878089322293647531541928492490440308406617503616618972974764876732%Z :: (-285737767130987821014999902415787126447079687695471622674856734171479905650504)%Z :: 286963707450257891078343719417905013708590016397363842828986982%Z :: (-174971952394403973484572862012705358961205507624)%Z :: 63313360113620434663257501149596%Z :: (-12412768900352648)%Z :: 1%Z :: nil).

Definition bezA : list (list Z) :=
  ((0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: (-8683395562193285449878684757137990736493687638888807003196315108470585353829524430999345665286578480977487188598971404737591994013694527870907404812611305377640238016794694466572124160)%Z :: 1908644043271831723660718678860637875133117757576526687832547696582798549635472487324972153175082908136852662536028733319255842063497494096628347025977918914295146214805496397824%Z :: 105425652420594553311258563969862456263160252603083469828320054373621446707691178522577336934324467995611626030574495903550240382743738459255499712213266190183853249789952%Z :: 87402735462860550693928805258058618825211202706296786132519559400293311689674303762469602425980241197736283508896023036033620603922376809015642590290413473400487936%Z :: 8398474010108994563550599326690823261527139127621082324622140536154608193905502156166696617368886795731833305566250845004703731719983498496424868050340527104%Z :: 484611075989961849756124082010163953159569578584483705333679364979529964824186973881548541079113062769770411651693917328412575913904608539919443427200%Z :: 18491455758149851074998690410600986298591917521048582246720101033622180671779057028366041334452489995965924069146856213132418712399695387787648%Z :: (-2986600637840900809934431892282385296470690761682804248775856272138760526381244445232889845851336487304546000766214075813332393709136480)%Z :: 109199381379337561358908564053478761151820857343087309175095689116741929034046320674970728218145095498553669452452295389963397248%Z :: 85704521392606507839186454345307555771294724560905345662207546814188983655677550973270391794725602188414654177782113120648%Z :: (-2568284772047443398340198152973374757141969921082767738245291246461645555047271379733073496781140502583400948948456)%Z :: (-859666865369623052040971651973045241957378150696753511303611014211528836743966927306982408657627394579860466)%Z :: 10221899652855723765580536433495967410301293758234938708323055310551077448740658901250432965272180520%Z :: 3939748196058259352477291020785640812088126647494824676420749063768734303255769194108249257722%Z :: (-16055647939649656515437322522077140169264273440716514335974942892807286207575810867592)%Z :: (-10341327944569662448761395214036622847547058421764088515610087105767800041527370)%Z :: (-2805209496099215310956845197841242671722696403615292290926536984132024)%Z :: 16498411487943793426248269274195205410644882687451988090843824994%Z :: 29595171142349059575409867667327683936132883622746123336%Z :: (-16094543829779747040625886887982662179358940629174)%Z :: (-26139683828664497411841240103174505268104)%Z :: 9420734792598783307088806779912526%Z :: 7614904729374266224181160%Z :: (-3106283799340038702)%Z :: (-114651240)%Z :: 462%Z :: nil)
  :: (0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: (-1105147588131019130425201134399133383362626410461608617099928792608642713742928462691395421249575575455278460272729394379222879666138121883989950400796330001338784298644468137984)%Z :: (-319512955941123618785970226603943861260006310773598057875685904760686860833102848643487945792623680987747564762724701291252952990251699452616677390649820726599995508129792)%Z :: (-146217708888042916332160186539675872235069878918410240547705070127861967846381687789404309118536312842552086590473433580369439855286611908041709897384066189476233216)%Z :: (-11410081721421074626339464234319742126494581027549145065142224039979881551122392410963472683833542634499629181246868002454436741486291595261863369905522737152)%Z :: (-697261819519689324119832876892314248892138872505925949428022592413068504506298006557396476414956915198978783526394218577465311786284275613254587202304)%Z :: (-32501637564045731363156005997914285703489952252262005832764947706270594847819332039591661639489394792359469268579044088998116900233341636627072)%Z :: 5788825796984280793871252440290224109069030848239143738880958589460501098872061794923904400302795403056076726523574954369236694119375616%Z :: (-145290661474844925424998278439132083832305295739959288244425866893143828917370194359575947650854561864384136249954453598359571712)%Z :: (-218975778709094163680034948439006323701138032158143692483622219784321912214016185727799838346100415444148054078219209427184)%Z :: 3195501595990819831807628738962711176517846940176273106691307194344938676845110629383927439942642033053157834922072%Z :: 2331456987265525103870148557225755868757643424104653389586019482514741455778856346237601911789019098128824120%Z :: (-9111886988584701744781497007138631143995043627487110789760183349025618296521179309914463475872467524)%Z :: (-11373303839815642161997106068117394826912541576266345498603196714905664864779328968094849673820)%Z :: (-2573294070959435250693473296414038108923023084874261899136398904841451309377478302992)%Z :: 31906463330481819939415944830578140330578866157119684785222427201135953914374752%Z :: 75539984838565672521348403062571590554535880013061104160613167465895348%Z :: (-55051019602294107086049160970095648762860922437242612579778042228)%Z :: (-140936073074933949792721769435084434996949626705670960616)%Z :: 57946663389269104965737099113865446845945243180568%Z :: 101733741666119988174691029871454591317156%Z :: (-36237803293999717487644570149162244)%Z :: (-27748516229349614070234720)%Z :: 12652718117830901968%Z :: 401279340%Z :: (-1980)%Z :: 0%Z :: nil)
  :: (0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 169145039228607761437179995100040752118724150209351027282317203477806069192223087933351845531122470704032565065402788685409402662984783692331009954893076647916586395500544%Z :: 104269392329374382952768967664651447167254870382231476402667725707113956065547168163687410951912552975793572083209653001693424408618654449272584600874708309010022400%Z :: 5703008206328988943234144795083453039334570793568875093991918856358962825471717628226988552752089478389750455659299314408602478842845608991175394732005392384%Z :: 261827613813308190826369295116783046969881122887528886437911017270269897554691221984724127313759523553145963165863000571634122567995457159724070305792%Z :: 324267204924562387158966784618219778974574379162418950176630398118932918244827719920620681904518812906927471656330568706237734915418669321984%Z :: (-6364530189775844934920971773694937835171552616231845603600784316211173547316553830299664661870436169555177719369733106429703346851064544)%Z :: (-16803305805759856913606172310178808043965826283499361399882446032573132011607923531596560069963488734538157994558456073592523136)%Z :: 200874891675395538134501241471216297140789368817732422477337979335480391022590723780799088270018871642196225778290855403200%Z :: 810456286980033371797267556751821580683408329854574588352847187166856016939823018853048764742059237293786229732272%Z :: (-2374243420429886274895650620957544299491139172627841317702079011898183949173785393884141201625378364973203758)%Z :: (-10960182941294202275302906956151177434817537047265860078959792359372558335556400155770067125073088192)%Z :: 12994900491023024616521353507894352457822889593821892230030222494786031895322389692781307341437%Z :: 53905163696458095944639613552250852047158617339030688968257892505711103735453941524576%Z :: (-40302987215486256467749915120384968799660471928650365084577888884135000669776628)%Z :: (-154551032058920285207196060714754069155076541531798205454323518189610832)%Z :: 76736426020399280463922021498110100714320748236433106074446417919%Z :: 214373635635391120826222378428589781415096736784298343664%Z :: (-87566164547791187130883542466048737513171377927150)%Z :: (-140113242710459701349496199892247559749856)%Z :: 58196973371648764448359421336985627%Z :: 36759986548612011004676864%Z :: (-21300283549869436464)%Z :: (-535039120)%Z :: 3465%Z :: 0%Z :: 0%Z :: nil)
  :: (0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: (-30238992767430737449638752029700036724100855356740288140537212047442662784171173354412835790517258631206362510135822538906476247531719668368640709678739637967781888)%Z :: (-1120172295376189756172220327607382745141276623133477718306117428508576243137471677483379161299446921513430966273351780395682235661539445421212347422136598528)%Z :: 181806165061665671433179600367953337525673440306359509458076082670537268146395546920918673980992829521699555979627147218657832410171222768559411494912%Z :: 5788768105671264287778480711451202173143906576655553643945383452050037060659753159202994813638372557553708880449126435811877182428370495733760%Z :: 3374582165953213604704763767684245255144529902875474580399148906378728927203268046461170417221654680414928062800254124415597788894235840%Z :: 130219108981440131819894765300672893382965641021680892903289287662556518243131272513294240397850532509699595508781862557555497088%Z :: (-67847325682338638794062102386957424162990132339298684142628208143436925388852310996837029001850854612904443545184904827296)%Z :: (-2109911640672982046574070250527800324158254158795261096382495352970897075401221432833491670063105202652378552555200)%Z :: 1116259699473798772606660454040057002603958774229531820187997612424736341452306077565125642875522071762023068%Z :: 13231676499012738163622057884423956947696407283323460896972037251386442146238833534726475717134824040%Z :: (-7591296038538543709669681479276743359101319154942641250710640553979528926845895240611308065580)%Z :: (-45627515553162374783067430126145781896994526598576013834840907341925613649352336858904)%Z :: 26960895162420986303103687816162116779602168694301128607195347815859199090908072%Z :: 103737916393259843480885239998237084781930521515728230373173048106480128%Z :: (-57028008404977609084946844969665026217825698234856558139481070752)%Z :: (-129635917605261030320967363518588150573351026959520968112)%Z :: 69931559542702563332216966562556135630062922341932%Z :: 80961496039934030933928955572979995701288%Z :: (-48736905332848944024691243325909580)%Z :: (-20858825957502678852583800)%Z :: 18445366136488972048%Z :: 321023472%Z :: (-3080)%Z :: 0%Z :: 0%Z :: 0%Z :: nil)
  :: (0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 225104047912103680139254388545991069781731889045669370915598930265743663042036676063176144504119472390453703191094514578956912800896063288985872975295152128%Z :: (-169322524458636292309680757878750824462078597705310162078616147868228216493284165805626413048616820829677074108387111833604694418266752423199028281344)%Z :: (-1151380003550669501533297300311993997938323686404534488474091097694450421275047883639199163222622724149689822758540568982630952352381450059776)%Z :: (-1008983061518025551285262871166267594941022574351212963043299904888594175281356571942931982390159413915566486353027101689980736529858560)%Z :: (-26086082765915712248551569406976029859705206199191664874135847953623756131060876155406932138284211652748969719173579303652708608)%Z :: 6690172725061663572003117412182711442843667513993535757882131437837153407048916325525355553598970993983743273272083907424%Z :: 423807299420254309810064791531245410727381977963380847116803753520543101528410070240597768679717489557665384020992%Z :: (-288904235442119021031093574532547820743328232721814393821907160476423185952537222286254725267694879213627120)%Z :: (-2662544659910750252079044145058775624620991880285454686650961503021738048741214346587460775106055568)%Z :: 2566041902066454242331623385475934379192446490040923296655631960995455381085059869438012314350%Z :: 9190064798174007565495980730826549531128696824545920132830671856488399353884878069624%Z :: (-10220514221030813545647468850687403850980729145864625540937896040849368274268592)%Z :: (-20894386469493548009040242960811586981886400038621806698414216553466888)%Z :: 23239852563083177543190885202198301238001155494631504391926906494%Z :: 26115112167816902717333374691336993436020953477704033008%Z :: (-29750266449619247506518211885815140617023224147136)%Z :: (-16326704615342068016632783791165536607456)%Z :: 21277206801234790061781425824414154%Z :: 4223515713182676407988888%Z :: (-8192427474232747680)%Z :: (-72959880)%Z :: 1386%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: nil)
  :: (0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 30785913537933871329032865068863786265832472310056393105202935976041493907869848328295711463384876514486740746979474878837217166957591349672550596608%Z :: 0%Z :: 183451465730550100233684158393866835443822286245675084189690891797926213687519376716896724070938075257375724791459473034541952096337920%Z :: 0%Z :: (-1216395040920302467636930438578674807789757729817006501433114806879482437645257513731882827927085635269771504231287983168)%Z :: 0%Z :: 52528042807658003823835195369554149226059678676693526149437665541167851991370404052046313685035432584295840%Z :: 0%Z :: (-466553073102991680423931524631988068944081180007440599391933083817355523833647248988729511700)%Z :: 0%Z :: 1858275312914693371935903427397709791087405299248113734715981098336248777139744%Z :: 0%Z :: (-4225427738742395916943797309490600225091119180842091707623073908)%Z :: 0%Z :: 5409139354476226819366947615602752839458768026752%Z :: 0%Z :: (-3868583054769961829414804695348028)%Z :: 0%Z :: 1489532268042317760%Z :: 0%Z :: (-252)%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: nil)
  :: nil).

Definition bezB : list (list Z) :=
  ((0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 8683395562193285449878684757137990736493687638888807003196315108470585353829524430999345665286578480977487188598971404737591994013694527870907404812611305377640238016794694466572124160%Z :: 803496455140812593235517544461504491770491347114918070732618903974155835892544024633576731925507332681574202263299338940032962397359372212638396625181588912956361916161028259840%Z :: 44942264291921304037531667534040652878121907961163560765048646909259344933188582187558763327176742288103373666747416702293309944523177301030167723543477888499555862839296%Z :: 15215426136761279864898834353334157033295338813377733846945002932102637124668610782339868468839222699771406491496419918451128909722699681877876584102315954966495232%Z :: (-1796332247552822804412313948393142499007584159553004006081316854290856888159392372010009469492106190498977316896424891142144146215894130093510418429981735936)%Z :: 92446424424543966915192207792699050566739143877192382828230660615081903433561418752464164373676556330446813909382209586471741854477851781421860340864%Z :: 9048526498850723114753165391555871450717877461799985480396923920173894618410742015741203972716636150082598670085271440330214222842238533843456%Z :: (-1013254460466726797330966170775254526925882914905569411950142105601372009216305629373514948516543912046909692373685732113640041980110208)%Z :: (-51238440314257198591647309197864732798810170142117887559940815899957730217138599141685528756893365756582000997547668971914090880)%Z :: 5230086360710604603956831964164141683009838665371920769744114852868208044803436841226085442465089132272354101709650193624%Z :: 248431230329317931499307316255396913371586831883800292466828464400204835135149094088991193479826945331170052828320%Z :: (-22569791694646467667071640827770341604183679035530486904142426105490322647756715622604467201124036291548316)%Z :: (-718961562078807657039146209571340154564128486519974049924155350517604914160698623704917306355393276)%Z :: 69537637690560659239548842129801394145520820141212854400833166847672264204347298632681662409%Z :: 1161229069139363039062631661559558596894508960590180968863684777374848076966806435288%Z :: (-139195575269232847703243110971028596919819345610152013992115915420767203150022)%Z :: (-1027273207312467475040494187401776527780763554754030090121943845165732)%Z :: 170234325412139345421372725252332157189046565575336130334962519%Z :: 488071734637896994723512166418126783050079780443428720%Z :: (-123612540742286560706627947822204994086609154208)%Z :: (-115606551587752330649761657846985393028)%Z :: 51623283863714475479035770892455%Z :: 8935195683339285971608%Z :: (-11378301080031070)%Z :: 347428%Z :: 1%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: nil)
  :: (0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 1105147588131019130425201134399133383362626410461608617099928792608642713742928462691395421249575575455278460272729394379222879666138121883989950400796330001338784298644468137984%Z :: 18777122516091904088389763596137642977441989645103996688948502194925277551343327223215745269621260420317565368080876079565852335717867932045342519136332569233177282871296%Z :: 28395902531586362775538507299473088072862704224168152163981254855962044067800871525267994586262982784584029954461595193702019780644462014602462824670868485359534080%Z :: (-2464166003243251287830818072791020004122341753629150548414342891724709977423225482706928484211226552698606355983946656508450839581634460387206130806741139456)%Z :: 151548626852951740761114191725572508894508335082748330966422221453622301391516343406219294722002280273862781954437848718456261258058745932561572248320%Z :: (-19092318851385491731635819495572215617862378509588644954471900944660419514450608656698232487655730390483246974953165920080533692526918611020928)%Z :: (-64836997872880034170969503257348001614536458225399841652091515609595153160928869520842019020939825815118154730060073169410181462209408)%Z :: 107415722794292907213267395214624860789839149961318008169133712214884437264564271495485924849633211584642455410579904712511038848%Z :: 89256709673861843390955201608530176103810133685789432467933826720704895422293423270740736854780198882817585260317388816%Z :: 181908445612957674920212267007935008319429035353162382716730523848131890634732649551941033956314857914256172804984%Z :: (-38772517096962806893630356148417740744226864033776270205413981792729097934906922279909104519226229535456528)%Z :: (-1987402013777892812837313846404217669024863393190267003367502325698360723882336403625013675038394060)%Z :: 225988730634365490756607571415122816521339793323994601011810962377143949500232071557757488786%Z :: 5114745855165662551367386352956518418925419095642755064179351506757512629012906447944%Z :: (-592494067222478590316819772533486621578538295504406947481014208727320636170064)%Z :: (-5925875977469559486548970215471641337371238657837842422171590807753484)%Z :: 829921217807642825001098621530322161147494594630515819736162210%Z :: 3363894051332811766154395631678649857274579895178954408%Z :: (-653643895698564771382804404189580438992197897280)%Z :: (-915074096365593789045638358762687508516)%Z :: 288660618159669564947777632003254%Z :: 89041848097077013323160%Z :: (-66200870839543264)%Z :: 2431996%Z :: 6%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: nil)
  :: (0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: (-169145039228607761437179995100040752118724150209351027282317203477806069192223087933351845531122470704032565065402788685409402662984783692331009954893076647916586395500544)%Z :: 13552414027082170603852711575551336994952304312010611981056089564785967713033648100448903580360777082174484552802185384973995666023495444166662471838489395106676736%Z :: (-3693115607673041755553010143537251222601132258442458164567160152427696074311522652155907935878465548192179775985811060695297248663603652461453590317366509568)%Z :: 99170097625826164558152199636775975432754580675310373392471737832927342112871351196678785598885852285049593924216520014351624958484524422933641068544%Z :: (-10782291500634338241294625117099862310776351990701872951168234168102341572573799895694410143483900140669915176452466462246083568086241456164608)%Z :: (-460167403718856426181416113701139284945875491255948798766228108427289680519695355404778063837047859230035201172538612977374878384129184)%Z :: (-217337524543066265054768707149983692946699859586393328065170329233353885931420637075844568293882838878066810216745655777157716480)%Z :: 25310000569546578507964334397653545230983399585627519582414995463397710921874713606121306306789277414687639740055764534176%Z :: 2976434838517386909064554445644106927427062278750923618093816350622576600093380858203839633368951433317357123807376%Z :: (-233609306584624045023878752337118723878635459503196958575152482070835520618386454385829487754627099125938874)%Z :: (-12759578596279510703089001826768039660545733520991794492050550376656339810712814368884595375695050520)%Z :: 951733056776202137262734136599847966232799269165102263912761760646622162958590697688161913797%Z :: 27836994173984983011586792441227196457052781509421831739280798381135341089293800634392%Z :: (-2160633925261245112964630502045943655864287728453595161459410698291125271266524)%Z :: (-31296398303897957181218201515087663299396622783655645474710326809028224)%Z :: 2837238796541559298788824707398827237939394691231540931333905547%Z :: 17843444173490553832679463979152709688830623228040362624%Z :: (-2181691072636713979672437937243645930534275516650)%Z :: (-4811017717289983352493964079699207709272)%Z :: 963667632811054450826199352261531%Z :: 475397044799967105141208%Z :: (-223427305375828800)%Z :: 9727984%Z :: 21%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: nil)
  :: (0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 30238992767430737449638752029700036724100855356740288140537212047442662784171173354412835790517258631206362510135822538906476247531719668368640709678739637967781888%Z :: (-219756103727775035615202773423418466014349066950800234643721707445601590969324973230674583282969031951616153508973722079854584457955192265268855520955990016)%Z :: 187624797393540784515214780458412097664316227414317207804359149041960658748042633018629863579625688652141332984126551327388773593319873427511195664384%Z :: 1183248091468586281645291510203226181390611831037415690049019061272235375559561624646198160747881660954949589414964159881353373018844695494656%Z :: (-1173164577186612401900553866957843229818662467927373570122858204803614362953035525858409728370397777326419365302740448001094363738180800)%Z :: 25874777917777282825688487672768773944144816224914233406745895848061493718887767891666511844713685898703716632087545342944662656%Z :: 53250585191295009182418937124013326469513039581494606125430830460883136137109220832054435066725826989667185494409449029280%Z :: (-414682442991964807333811084402818681248726246941737707915280338888724669287581151871100595344235244421717016471232)%Z :: (-485923185781902726720638109605407211891242630109209506394745625930722117555861228940569878655096880750472988)%Z :: 2581497859369737155305881304188854449212439762181642150368191239299489951273976148376632616710601768%Z :: 1992659161302643544582503183692886531772344994853354058007443548171262640842128252746553925180%Z :: (-8867256360466344521083507202839583772479739300392333303518219915972016233812824580408)%Z :: (-4661591407444665839872846687389599286553305103323763790603574635824213765231144)%Z :: 20160370515285651444724268154990736854384921361241003579516181892612576%Z :: 6322875540068858081621277255777823516732268064751457648004183856%Z :: (-25175468933993419451633864753240176829267213048704836080)%Z :: (-5021887288987841499813595175323101556557706020908)%Z :: 15654677578565758867397820408317849271464%Z :: 2313908675609402071713586981733244%Z :: (-3964763104771973220628248)%Z :: (-570978919981158928)%Z :: 29183952%Z :: 56%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: nil)
  :: (0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: (-225104047912103680139254388545991069781731889045669370915598930265743663042036676063176144504119472390453703191094514578956912800896063288985872975295152128)%Z :: (-15392956768966935664516432534431893132916236155028196552601467988020746953934924164147855731692438257243370373489737439418608583478795674836275298304)%Z :: 1151380003550669501533297300311993997938323686404534488474091097694450421275047883639199163222622724149689822758540568982630952352381450059776%Z :: (-91725732865275050116842079196933417721911143122837542094845445898963106843759688358448362035469037628687862395729736517270976048168960)%Z :: 26086082765915712248551569406976029859705206199191664874135847953623756131060876155406932138284211652748969719173579303652708608%Z :: 608197520460151233818465219289337403894878864908503250716557403439741218822628756865941413963542817634885752115643991584%Z :: (-423807299420254309810064791531245410727381977963380847116803753520543101528410070240597768679717489557665384020992)%Z :: (-26264021403829001911917597684777074613029839338346763074718832770583925995685202026023156842517716292147920)%Z :: 2662544659910750252079044145058775624620991880285454686650961503021738048741214346587460775106055568%Z :: 233276536551495840211965762315994034472040590003720299695966541908677761916823624494364755850%Z :: (-9190064798174007565495980730826549531128696824545920132830671856488399353884878069624)%Z :: (-929137656457346685967951713698854895543702649624056867357990549168124388569872)%Z :: 20894386469493548009040242960811586981886400038621806698414216553466888%Z :: 2112713869371197958471898654745300112545559590421045853811536954%Z :: (-26115112167816902717333374691336993436020953477704033008)%Z :: (-2704569677238113409683473807801376419729384013376)%Z :: 16326704615342068016632783791165536607456%Z :: 1934291527384980914707402347674014%Z :: (-4223515713182676407988888)%Z :: (-744766134021158880)%Z :: 72959880%Z :: 126%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: nil)
  :: (0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: (-30785913537933871329032865068863786265832472310056393105202935976041493907869848328295711463384876514486740746979474878837217166957591349672550596608)%Z :: 0%Z :: (-183451465730550100233684158393866835443822286245675084189690891797926213687519376716896724070938075257375724791459473034541952096337920)%Z :: 0%Z :: 1216395040920302467636930438578674807789757729817006501433114806879482437645257513731882827927085635269771504231287983168%Z :: 0%Z :: (-52528042807658003823835195369554149226059678676693526149437665541167851991370404052046313685035432584295840)%Z :: 0%Z :: 466553073102991680423931524631988068944081180007440599391933083817355523833647248988729511700%Z :: 0%Z :: (-1858275312914693371935903427397709791087405299248113734715981098336248777139744)%Z :: 0%Z :: 4225427738742395916943797309490600225091119180842091707623073908%Z :: 0%Z :: (-5409139354476226819366947615602752839458768026752)%Z :: 0%Z :: 3868583054769961829414804695348028%Z :: 0%Z :: (-1489532268042317760)%Z :: 0%Z :: 252%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: nil)
  :: nil).

Definition witR36z : list Z :=
  (0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 9755936680303407142079972936243184006105618289993480551583696655989494509066190903385872600389761080309386898179183017279725047838318446797842220094414032867997743389716619663930482256849639499622524263602742886400000000%Z :: 0%Z :: 131796984686304770021010627023096159345405758159826712099066559059529230068702433020955181979275772741453916694003022261709845634592810122496524862462898804262255561928368914122070212242435789282544457875456%Z :: 0%Z :: (-1323120843744956372195472026818140943434383821739726553964132418772421915119817225961914436055952477897524958707943685756434113759949829945858605255538179842075662124388813360988453020622913536)%Z :: 0%Z :: (-7975929178474211921590965248946150234124484113224202289934038164919183233165061969767903851285939408473315439615064060289173162576937287180658784598865231040568976679501369171712)%Z :: 0%Z :: 120735410747479230550071881012036017251645259375546049539402704484300149125462952482001055441835985155796354833286357033907038878569212828930453571526639091101391104%Z :: 0%Z :: (-998948913431351249002363014758809712400081376649103246631826776553849194624905401309207808016924299489595386835387837922210439517544681620939715675040)%Z :: 0%Z :: 3124902711748894862876582155104005081745015996725665338389424135936707370891017381457423176935940649761170894138086138238925238987836432%Z :: 0%Z :: 3513677485573415932545607796750390600028428565788116941356797636572806847706931630559193907225454664010189399558019119969%Z :: 0%Z :: (-52494786796451316139104625624096951790108785395766922117425101321063986171520623278310237822796089518476440)%Z :: 0%Z :: 168583619128104983726196509878089322293647531541928492490440308406617503616618972974764876732%Z :: 0%Z :: (-285737767130987821014999902415787126447079687695471622674856734171479905650504)%Z :: 0%Z :: 286963707450257891078343719417905013708590016397363842828986982%Z :: 0%Z :: (-174971952394403973484572862012705358961205507624)%Z :: 0%Z :: 63313360113620434663257501149596%Z :: 0%Z :: (-12412768900352648)%Z :: 0%Z :: 1%Z :: nil).

Definition wbrA1 : Z := (-633045697807735)%Z.
Definition wbrB1 : Z := (-633045697807732)%Z.
Definition wbrA2 : Z := (-84410879089805)%Z.
Definition wbrB2 : Z := (-84410879089802)%Z.
Definition wbrA3 : Z := (104252567179735)%Z.
Definition wbrB3 : Z := (104252567179738)%Z.
Definition wbrA4 : Z := (428820087806213)%Z.
Definition wbrB4 : Z := (428820087806216)%Z.

(* The bivariate integer polynomial engine: x-major dense lists with addition, scaling, multiplication, the Horner substitution for F(x - T), and the zero test. *)

Fixpoint bp_add (p q : list (list Z)) : list (list Z) :=
  match p, q with
  | nil, _ => q
  | _, nil => p
  | r :: p', s :: q' => Zpadd r s :: bp_add p' q'
  end.

Definition bp_scale_row (c : list Z) (q : list (list Z)) : list (list Z) :=
  map (Zpmul c) q.

Fixpoint bp_mul (p q : list (list Z)) : list (list Z) :=
  match p with
  | nil => nil
  | r :: p' => bp_add (bp_scale_row r q) (nil :: bp_mul p' q)
  end.

Definition bp_opp (p : list (list Z)) : list (list Z) :=
  map (map Z.opp) p.

Definition bp_zerob (p : list (list Z)) : bool :=
  forallb (forallb (Z.eqb 0)) p.

(** The Horner substitution: evaluate an integer coefficient list at a bivariate argument. *)
Fixpoint bp_horner (l : list Z) (w : list (list Z)) : list (list Z) :=
  match l with
  | nil => nil
  | c :: l' => bp_add ((c :: nil) :: nil) (bp_mul w (bp_horner l' w))
  end.

(** x - T as a bivariate. *)
Definition bp_xmT : list (list Z) := (0 :: (-1) :: nil) :: (1 :: nil) :: nil.

(** F(x) as a bivariate: constant rows. *)
Definition bp_ofpoly (l : list Z) : list (list Z) :=
  map (fun c => c :: nil) l.

(** THE BEZOUT IDENTITY, checked by vm: A F(x) + B F(x-T) = R36(T). *)
Lemma bezout_identity_vm :
  bp_zerob (bp_add (bp_add (bp_mul bezA (bp_ofpoly witFz))
                      (bp_mul bezB (bp_horner witFz bp_xmT)))
              (bp_opp (witR36z :: nil))) = true.
Proof. vm_compute. reflexivity. Qed.

(** R36 is T^6 times S15 at T squared, at the coefficient level. *)
Fixpoint interleave0 (l : list Z) : list Z :=
  match l with
  | nil => nil
  | c :: nil => c :: nil
  | c :: l' => c :: 0 :: interleave0 l'
  end.

Lemma R36_expand_vm :
  witR36z = repeat 0 6 ++ interleave0 witS15z.
Proof. vm_compute. reflexivity. Qed.

Close Scope Z_scope.

(* Evaluation bridges: integer bivariates evaluate homomorphically into C. *)

Definition castZ (n : Z) : C := RtoC (IZR n).

Lemma castZ_add : forall a b, castZ (a + b)%Z = (castZ a + castZ b)%C.
Proof.
  intros a b. unfold castZ.
  rewrite plus_IZR, RtoC_add. reflexivity.
Qed.

Lemma castZ_mul : forall a b, castZ (a * b)%Z = (castZ a * castZ b)%C.
Proof.
  intros a b. unfold castZ.
  rewrite mult_IZR, RtoC_mul. reflexivity.
Qed.

Lemma castZ_opp : forall a, castZ (- a)%Z = (Copp (castZ a)).
Proof.
  intros a. unfold castZ.
  rewrite opp_IZR.
  unfold RtoC, Copp. cbn. f_equal. ring.
Qed.

Lemma castZ_0 : castZ 0%Z = C0.
Proof. reflexivity. Qed.

Lemma map_castZ_Zpadd : forall u v,
  map castZ (Zpadd u v) = cpadd (map castZ u) (map castZ v).
Proof.
  induction u as [|a u IH]; intros v; cbn [Zpadd map cpadd].
  - reflexivity.
  - destruct v as [|b v]; cbn [map cpadd].
    + reflexivity.
    + rewrite castZ_add, IH. reflexivity.
Qed.

Lemma map_castZ_scale : forall a q,
  map castZ (map (Z.mul a) q) = cpscale (castZ a) (map castZ q).
Proof.
  induction q as [|b q IH]; cbn [map cpscale].
  - reflexivity.
  - rewrite castZ_mul, IH. reflexivity.
Qed.

Lemma map_castZ_Zpmul : forall u v,
  map castZ (Zpmul u v) = cpmul (map castZ u) (map castZ v).
Proof.
  induction u as [|a u IH]; intros v; cbn [Zpmul map cpmul].
  - reflexivity.
  - rewrite map_castZ_Zpadd, map_castZ_scale.
    cbn [map].
    rewrite castZ_0, IH.
    reflexivity.
Qed.

Definition bieval (p : list (list Z)) (zx zT : C) : C :=
  cpeval (map (fun r => cpeval (map castZ r) zT) p) zx.

Lemma bieval_add : forall p q zx zT,
  bieval (bp_add p q) zx zT = (bieval p zx zT + bieval q zx zT)%C.
Proof.
  induction p as [|r p IH]; intros q zx zT; unfold bieval;
    cbn [bp_add map cpeval].
  - ring.
  - destruct q as [|s q]; cbn [map cpeval].
    + ring.
    + rewrite map_castZ_Zpadd, cpeval_cpadd.
      unfold bieval in IH.
      rewrite IH. ring.
Qed.

Lemma bieval_scale_row : forall r q zx zT,
  bieval (bp_scale_row r q) zx zT
  = (cpeval (map castZ r) zT * bieval q zx zT)%C.
Proof.
  intros r q zx zT.
  unfold bp_scale_row, bieval.
  induction q as [|s q IH]; cbn [map cpeval].
  - ring.
  - rewrite map_castZ_Zpmul, cpeval_cpmul.
    rewrite IH. ring.
Qed.

Lemma bieval_mul : forall p q zx zT,
  bieval (bp_mul p q) zx zT = (bieval p zx zT * bieval q zx zT)%C.
Proof.
  induction p as [|r p IH]; intros q zx zT.
  - unfold bieval. cbn [bp_mul map cpeval]. ring.
  - cbn [bp_mul].
    rewrite bieval_add, bieval_scale_row.
    assert (Hcons : bieval (nil :: bp_mul p q) zx zT
                    = (zx * bieval (bp_mul p q) zx zT)%C).
    { unfold bieval. cbn [map cpeval]. ring. }
    rewrite Hcons, IH.
    assert (Hhead : bieval (r :: p) zx zT
                    = (cpeval (map castZ r) zT + zx * bieval p zx zT)%C).
    { unfold bieval. cbn [map cpeval]. reflexivity. }
    rewrite Hhead. ring.
Qed.

Lemma bieval_opp : forall p zx zT,
  bieval (bp_opp p) zx zT = (Copp (bieval p zx zT)).
Proof.
  induction p as [|r p IH]; intros zx zT; unfold bieval;
    cbn [bp_opp map cpeval].
  - ring.
  - assert (Hrow : cpeval (map castZ (map Z.opp r)) zT
                   = Copp (cpeval (map castZ r) zT)).
    { induction r as [|a r IHr]; cbn [map cpeval].
      - ring.
      - rewrite castZ_opp, IHr. ring. }
    rewrite Hrow.
    unfold bieval in IH.
    rewrite IH. ring.
Qed.

Lemma bieval_zero : forall p zx zT,
  bp_zerob p = true -> bieval p zx zT = C0.
Proof.
  induction p as [|r p IH]; intros zx zT Hz; unfold bieval;
    cbn [map cpeval].
  - reflexivity.
  - unfold bp_zerob in Hz. cbn [forallb] in Hz.
    apply andb_prop in Hz. destruct Hz as [Hr Hp].
    assert (Hrow : cpeval (map castZ r) zT = C0).
    { clear IH Hp.
      induction r as [|a r IHr]; cbn [map cpeval].
      - reflexivity.
      - cbn [forallb] in Hr.
        apply andb_prop in Hr. destruct Hr as [Ha Hr].
        apply Z.eqb_eq in Ha. subst a.
        rewrite castZ_0, IHr by exact Hr. ring. }
    rewrite Hrow.
    unfold bieval in IH.
    rewrite (IH zx zT Hp). ring.
Qed.

Lemma bieval_horner : forall (l : list Z) (w : list (list Z)) zx zT,
  bieval (bp_horner l w) zx zT
  = cpeval (map castZ l) (bieval w zx zT).
Proof.
  induction l as [|c l IH]; intros w zx zT.
  - unfold bieval. cbn [bp_horner map cpeval]. reflexivity.
  - cbn [bp_horner].
    rewrite bieval_add, bieval_mul, IH.
    cbn [map cpeval].
    assert (Hconst : bieval ((c :: nil) :: nil) zx zT = castZ c).
    { unfold bieval. cbn [map cpeval]. ring. }
    rewrite Hconst. ring.
Qed.

Lemma bieval_ofpoly : forall (l : list Z) zx zT,
  bieval (bp_ofpoly l) zx zT = cpeval (map castZ l) zx.
Proof.
  induction l as [|c l IH]; intros zx zT; unfold bieval, bp_ofpoly in *;
    cbn [map cpeval].
  - reflexivity.
  - rewrite <- (IH zx zT). ring.
Qed.

Lemma castZ_m1 : castZ (-1)%Z = Copp C1.
Proof.
  unfold castZ, RtoC, Copp, C1. cbn. f_equal; ring.
Qed.

Lemma bieval_xmT : forall zx zT, bieval bp_xmT zx zT = (zx - zT)%C.
Proof.
  intros zx zT. unfold bieval, bp_xmT.
  cbn [map cpeval].
  rewrite castZ_0, castZ_m1.
  assert (H1 : castZ 1%Z = C1) by reflexivity.
  rewrite H1. ring.
Qed.

(** Evaluation of the interleaved list is evaluation at the square. *)
Lemma cpeval_interleave0 : forall (s : list Z) (w : C),
  cpeval (map castZ (interleave0 s)) w
  = cpeval (map castZ s) ((w * w)%C).
Proof.
  induction s as [|c s IH]; intro w.
  - reflexivity.
  - destruct s as [|c' s'].
    + cbn [interleave0 map cpeval]. ring.
    + change (interleave0 (c :: c' :: s'))
        with (c :: 0%Z :: interleave0 (c' :: s')).
      cbn [map cpeval].
      rewrite castZ_0.
      rewrite IH.
      cbn [map cpeval].
      ring.
Qed.

(** THETA SQUARED ROOTS S15: the squared difference of any two distinct witness roots roots the monicized S15. *)
Lemma theta_sq_roots_S15 : forall rho1 rho2 : C,
  cpeval (map castZ witFz) rho1 = C0 ->
  cpeval (map castZ witFz) rho2 = C0 ->
  rho1 <> rho2 ->
  cpeval (map castZ witS15z) (((rho1 - rho2) * (rho1 - rho2))%C) = C0.
Proof.
  intros rho1 rho2 HF1 HF2 Hne.
  set (th := (rho1 - rho2)%C).
  assert (Hthne : th <> C0).
  { intro E. apply Hne.
    transitivity ((rho1 - rho2) + rho2)%C; [ring |].
    unfold th in E. rewrite E. ring. }
  pose proof (bieval_zero _ rho1 th bezout_identity_vm) as Hz.
  rewrite !bieval_add, !bieval_mul, bieval_opp in Hz.
  rewrite bieval_ofpoly in Hz.
  rewrite bieval_horner, bieval_xmT in Hz.
  assert (Hr2 : (rho1 - th)%C = rho2) by (unfold th; ring).
  rewrite Hr2, HF1, HF2 in Hz.
  set (A' := bieval bezA rho1 th) in *.
  set (B' := bieval bezB rho1 th) in *.
  set (R' := bieval (witR36z :: nil) rho1 th) in *.
  assert (HR36 : R' = C0).
  { transitivity ((A' * C0 + B' * C0) - (A' * C0 + B' * C0 + Copp R'))%C;
      [ring |].
    rewrite Hz. ring. }
  assert (HRval : R' = cpeval (map castZ witR36z) th).
  { unfold R', bieval. cbn [map cpeval]. ring. }
  rewrite HRval in HR36.
  rewrite R36_expand_vm in HR36.
  rewrite map_app in HR36.
  rewrite cpeval_app in HR36.
  assert (Hzeros : cpeval (map castZ (repeat 0%Z 6)) th = C0)
    by (cbn [repeat map cpeval]; rewrite castZ_0; ring).
  assert (Hlen6r : length (map castZ (repeat 0%Z 6)) = 6%nat)
    by (rewrite length_map, repeat_length; reflexivity).
  rewrite Hzeros, Hlen6r in HR36.
  rewrite cpeval_interleave0 in HR36.
  assert (Hfac : (Cpow th 6 * cpeval (map castZ witS15z) ((th * th)%C))%C = C0).
  { rewrite <- HR36. ring. }
  destruct (Cmul_integral _ _ Hfac) as [E | E].
  - exfalso. exact (Cpow_nonzero th 6 Hthne E).
  - exact E.
Qed.

(* exclusion plumbing -- a monic CQ-factor transports to a monic rational real factor refuted by the sweeps, and the mirror closes the upper degrees. *)

Lemma cpeval_map_RtoC_global : forall (l : list R) (z : C),
  cpeval (map RtoC l) z = CevalR l z.
Proof.
  intros l z. induction l as [|a l IHl]; cbn [map cpeval CevalR].
  - reflexivity.
  - rewrite IHl. reflexivity.
Qed.

Lemma castZ_as_RtoC : forall (l : list Z),
  map castZ l = map RtoC (map IZR l).
Proof.
  induction l as [|a l IH]; cbn [map].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma CQ_list_preimage : forall (l : list C),
  Forall CQ l ->
  exists lr : list R, Forall is_rational lr /\ l = map RtoC lr.
Proof.
  intros l Hl. induction Hl as [|c l [x [Hx Hcx]] Hl IH].
  - exists nil. split; [constructor | reflexivity].
  - destruct IH as [lr [Hlr Hmap]].
    exists (x :: lr).
    split; [constructor; assumption |].
    cbn [map]. rewrite <- Hmap, Hcx. reflexivity.
Qed.

(** Heads of reversals and of leading-first products. *)
Lemma hd_app_left : forall (x y : list C) (d : C),
  x <> nil -> hd d (x ++ y) = hd d x.
Proof.
  intros x y d Hx. destruct x; [congruence | reflexivity].
Qed.

Lemma hd_rev_nth : forall (u : list C),
  u <> nil -> hd C0 (rev u) = nth (length u - 1) u C0.
Proof.
  induction u as [|a u IH]; intros _; [reflexivity |].
  destruct u as [|b u'].
  - reflexivity.
  - change (rev (a :: b :: u')) with (rev (b :: u') ++ a :: nil).
    rewrite hd_app_left.
    + rewrite (IH ltac:(discriminate)).
      cbn [length nth].
      replace (Datatypes.S (length u') - 0)%nat
        with (Datatypes.S (length u')) by lia.
      destruct (length u') as [|k]; cbn [nth].
      * reflexivity.
      * replace (Datatypes.S (Datatypes.S k) - 1)%nat
          with (Datatypes.S k) by lia.
        replace (Datatypes.S k - 1)%nat with k by lia.
        reflexivity.
    + intro E.
      apply (f_equal (@length C)) in E.
      rewrite length_rev in E.
      cbn [length] in E. lia.
Qed.

Lemma cpmul_lf_head : forall (a b : list C),
  (1 <= length a)%nat -> (1 <= length b)%nat ->
  hd C0 (cpmul_lf a b) = (hd C0 a * hd C0 b)%C.
Proof.
  intros a b Ha Hb.
  unfold cpmul_lf.
  assert (Hlen : length (cpmul (rev a) (rev b)) = (length a + length b - 1)%nat).
  { rewrite cpmul_length by (rewrite length_rev; lia).
    rewrite !length_rev. reflexivity. }
  rewrite hd_rev_nth.
  2:{ intro E.
      apply (f_equal (@length C)) in E.
      rewrite Hlen in E. cbn [length] in E. lia. }
  rewrite Hlen.
  replace (length a + length b - 1 - 1)%nat
    with ((length a - 1) + (length b - 1))%nat by lia.
  rewrite (cpmul_top (rev a) (rev b) (length a - 1) (length b - 1));
    [| rewrite length_rev; lia | rewrite length_rev; lia].
  rewrite rev_nth by lia.
  rewrite (rev_nth b) by lia.
  replace (length a - Datatypes.S (length a - 1))%nat with 0%nat by lia.
  replace (length b - Datatypes.S (length b - 1))%nat with 0%nat by lia.
  destruct a; destruct b; cbn [hd nth]; try (cbn [length] in Ha, Hb; lia).
  reflexivity.
Qed.

(** Prepending zeros to a leading-first list preserves evaluation. *)
Lemma cpeval_lf_pad : forall (k : nat) (l : list C) (z : C),
  cpeval_lf (repeat C0 k ++ l) z = cpeval_lf l z.
Proof.
  induction k as [|k IH]; intros l z; cbn [repeat app].
  - reflexivity.
  - cbn [cpeval_lf].
    rewrite IH. ring.
Qed.

(** A monic list times a nonzero list cannot be a lower-degree function. *)
Lemma monic_mul_degree_bound : forall (Mlf elf Rlf : list C),
  hd C0 Mlf = C1 -> (1 <= length Mlf)%nat ->
  (length Rlf < length (clnorm elf) + length Mlf - 1)%nat \/
  (length Rlf < length Mlf)%nat /\ (1 <= length (clnorm elf))%nat ->
  (forall z, (cpeval_lf Mlf z * cpeval_lf elf z)%C = cpeval_lf Rlf z) ->
  clnorm elf = nil.
Proof.
  intros Mlf elf Rlf Hmon HlM Hbound Hid.
  destruct (clnorm elf) as [|e0 etail] eqn:EN; [reflexivity | exfalso].
  assert (Hhd : hd C0 (clnorm elf) <> C0).
  { destruct (clnorm_head elf) as [Hc | Hc];
      [rewrite EN in Hc; discriminate | exact Hc]. }
  rewrite EN in Hhd. cbn [hd] in Hhd.
  set (N' := e0 :: etail) in *.
  assert (HlN : (1 <= length N')%nat) by (unfold N'; cbn [length]; lia).
  assert (Hid' : forall z, cpeval_lf (cpmul_lf Mlf N') z = cpeval_lf Rlf z).
  { intro z.
    rewrite cpmul_lf_eval.
    rewrite <- (Hid z).
    f_equal.
    rewrite <- (clnorm_eval elf z), EN.
    reflexivity. }
  assert (Hlprod : length (cpmul_lf Mlf N')
                   = (length Mlf + length N' - 1)%nat).
  { unfold cpmul_lf.
    rewrite length_rev.
    rewrite cpmul_length by (rewrite length_rev; lia).
    rewrite !length_rev. reflexivity. }
  assert (Hlt : (length Rlf < length (cpmul_lf Mlf N'))%nat).
  { rewrite Hlprod.
    destruct Hbound as [Hb | [Hb He1]]; lia. }
  set (k := (length (cpmul_lf Mlf N') - length Rlf)%nat).
  assert (Hpadlen : length (repeat C0 k ++ Rlf) = length (cpmul_lf Mlf N')).
  { rewrite length_app, repeat_length. unfold k. lia. }
  assert (Hlists : cpmul_lf Mlf N' = repeat C0 k ++ Rlf).
  { apply cpeval_lf_ext_coeffs; [lia |].
    intro z.
    rewrite cpeval_lf_pad.
    apply Hid'. }
  assert (Hheadprod : hd C0 (cpmul_lf Mlf N') = (C1 * e0)%C).
  { rewrite cpmul_lf_head by lia.
    rewrite Hmon. reflexivity. }
  assert (Hk1 : (1 <= k)%nat) by (unfold k; lia).
  assert (Hheadpad : hd C0 (repeat C0 k ++ Rlf) = C0).
  { destruct k as [|k']; [lia |].
    cbn [repeat app hd]. reflexivity. }
  rewrite Hlists, Hheadpad in Hheadprod.
  apply Hhd.
  transitivity ((C1 * e0)%C); [ring | rewrite <- Hheadprod; reflexivity].
Qed.

(** Leading-first lists with nonzero heads and one polynomial function are equal. *)
Lemma lf_eq_of_eval : forall (u v : list C),
  hd C0 u <> C0 -> hd C0 v <> C0 ->
  (forall z, cpeval_lf u z = cpeval_lf v z) ->
  u = v.
Proof.
  intros u v Hu Hv Hev.
  destruct (Nat.lt_trichotomy (length u) (length v)) as [Hlt | [Heq | Hgt]].
  - exfalso.
    set (k := (length v - length u)%nat).
    assert (Hk1 : (1 <= k)%nat) by (unfold k; lia).
    assert (Hpad : repeat C0 k ++ u = v).
    { apply cpeval_lf_ext_coeffs.
      - rewrite length_app, repeat_length. unfold k. lia.
      - intro z. rewrite cpeval_lf_pad. apply Hev. }
    apply Hv.
    rewrite <- Hpad.
    destruct k as [|k']; [lia |].
    cbn [repeat app hd]. reflexivity.
  - apply cpeval_lf_ext_coeffs; [exact Heq | exact Hev].
  - exfalso.
    set (k := (length u - length v)%nat).
    assert (Hk1 : (1 <= k)%nat) by (unfold k; lia).
    assert (Hpad : repeat C0 k ++ v = u).
    { apply cpeval_lf_ext_coeffs.
      - rewrite length_app, repeat_length. unfold k. lia.
      - intro z. rewrite cpeval_lf_pad. symmetry. apply Hev. }
    apply Hu.
    rewrite <- Hpad.
    destruct k as [|k']; [lia |].
    cbn [repeat app hd]. reflexivity.
Qed.

(** THE CQ EXCLUSION PREDICATE: no monic CQ-factorization of the given degree. *)
Definition CQ_excl (Fz : list Z) (d : nat) : Prop :=
  forall (dt Q : list C),
  Forall CQ dt -> length dt = d -> Forall CQ Q ->
  (forall z, cpeval (map castZ Fz) z
             = (cpeval_lf Q z * (Cpow z d + cpeval dt z))%C) ->
  False.

(** A CQ-factorization transports to a rational real factorization and dies on the sweep. *)
Lemma CQ_excl_of_sweep : forall (Fz : list Z) (N : nat) (m : Z) (d : nat),
  length Fz = Datatypes.S N -> nth N Fz 0%Z = 1%Z -> Zcontent Fz = 1%Z ->
  (1 < m)%Z -> (1 <= d)%nat -> (d <= N)%nat ->
  forallb (refute_factor m Fz) (monic_candidates m d) = true ->
  CQ_excl Fz d.
Proof.
  intros Fz N m d HlF HmF HcF Hm Hd1 HdN Hsweep dt Q Hdt Hldt HQ Hid.
  destruct (CQ_list_preimage dt Hdt) as [dtr [Hdtr Hdte]].
  destruct (CQ_list_preimage Q HQ) as [Qr [HQr HQe]].
  set (mu := dtr ++ (1 :: nil)%R).
  set (q := rev Qr).
  apply (sweep_excludes_degree Fz N m d HlF HmF HcF Hm HdN Hsweep mu q).
  - unfold mu. apply Forall_app_intro; [exact Hdtr |].
    constructor; [| constructor].
    exists 1%Z, 1%Z. split; [lia | field].
  - unfold q. apply Forall_rev. exact HQr.
  - unfold mu. rewrite length_app.
    rewrite Hdte in Hldt. rewrite length_map in Hldt.
    cbn [length]. lia.
  - unfold mu.
    rewrite app_nth2;
      rewrite Hdte in Hldt; rewrite length_map in Hldt; [| lia].
    rewrite Hldt, Nat.sub_diag. reflexivity.
  - intro y.
    assert (Hpe : forall (cs : list R) (x : R), pe cs x = pevalR cs x).
    { intros cs x. unfold pe. apply Fcomb_powers_pevalR. }
    rewrite !Hpe.
    apply RtoC_inj.
    rewrite RtoC_mul.
    assert (HL : RtoC (pevalR (map IZR Fz) y)
                 = cpeval (map castZ Fz) (RtoC y)).
    { rewrite castZ_as_RtoC, cpeval_map_RtoC_global, CevalR_RtoC.
      reflexivity. }
    rewrite HL, (Hid (RtoC y)).
    assert (Hmu : RtoC (pevalR mu y) = (Cpow (RtoC y) d + cpeval dt (RtoC y))%C).
    { unfold mu.
      rewrite pevalR_app, RtoC_add, RtoC_mul.
      rewrite Hdte in Hldt. rewrite length_map in Hldt.
      rewrite Hldt.
      cbn [pevalR].
      rewrite Cpow_RtoC.
      rewrite Hdte, cpeval_map_RtoC_global, CevalR_RtoC.
      assert (H1R : RtoC (1 + y * 0)%R = C1).
      { unfold RtoC, C1. f_equal. ring. }
      rewrite H1R. ring. }
    assert (Hq : RtoC (pevalR q y) = cpeval_lf Q (RtoC y)).
    { unfold q.
      rewrite HQe.
      rewrite cpeval_lf_rev_c.
      rewrite <- map_rev.
      rewrite cpeval_map_RtoC_global, CevalR_RtoC.
      rewrite pevalR_rev, rev_involutive.
      reflexivity. }
    rewrite Hmu, Hq.
    ring.
Qed.


(** THE MIRROR: excluding a degree excludes its complement, through the monic division cofactor. *)
Lemma CQ_excl_mirror : forall (Fz : list Z) (N d : nat),
  length Fz = Datatypes.S N -> nth N Fz 0%Z = 1%Z ->
  (1 <= d)%nat -> (d <= N - 1)%nat ->
  CQ_excl Fz (N - d) ->
  CQ_excl Fz d.
Proof.
  intros Fz N d HlF HmF Hd1 HdN Hexcl dt Q Hdt Hldt HQ Hid.
  set (Mlf := C1 :: rev dt).
  assert (HlM : length Mlf = Datatypes.S d)
    by (unfold Mlf; cbn [length]; rewrite length_rev, Hldt; reflexivity).
  assert (HevM : forall z, cpeval_lf Mlf z = (Cpow z d + cpeval dt z)%C).
  { intro z. unfold Mlf. cbn [cpeval_lf].
    rewrite length_rev, Hldt.
    rewrite cpeval_lf_rev_c, rev_involutive. ring. }
  set (Flf := rev (map castZ Fz)).
  assert (HevF : forall z, cpeval_lf Flf z = cpeval (map castZ Fz) z).
  { intro z. unfold Flf.
    rewrite cpeval_lf_rev_c, rev_involutive. reflexivity. }
  assert (HlF2 : length Flf = Datatypes.S N)
    by (unfold Flf; rewrite length_rev, length_map, HlF; reflexivity).
  assert (HhdF : hd C0 Flf = C1).
  { unfold Flf.
    rewrite hd_rev_nth.
    2:{ intro E. apply (f_equal (@length C)) in E.
        rewrite length_map, HlF in E. cbn [length] in E. lia. }
    rewrite length_map, HlF.
    replace (Datatypes.S N - 1)%nat with N by lia.
    rewrite (nth_indep _ C0 (castZ 0%Z))
      by (rewrite length_map, HlF; lia).
    rewrite (map_nth castZ Fz 0%Z N).
    rewrite HmF. reflexivity. }
  assert (HFnz : ~ (forall z, cpeval_lf Flf z = C0)).
  { apply cmonic_lf_nonzero; [exact HhdF | rewrite HlF2; lia]. }
  assert (HevNQ : forall z, cpeval_lf (clnorm Q) z = cpeval_lf Q z)
    by (intro z; apply clnorm_eval).
  destruct (clnorm_head Q) as [HN | HhdNq0].
  { exfalso. apply HFnz.
    intro z.
    rewrite (HevF z), (Hid z).
    rewrite <- HevM.
    rewrite <- (HevNQ z), HN.
    cbn [cpeval_lf]. ring. }
  destruct (clnorm Q) as [|nh ntail] eqn:ENq;
    [cbn [hd] in HhdNq0; congruence |].
  cbn [hd] in HhdNq0.
  assert (HevN2 : forall z, cpeval_lf (nh :: ntail) z = cpeval_lf Q z)
    by exact HevNQ.
  assert (HidF : forall z,
    cpeval_lf Flf z = (cpeval_lf (nh :: ntail) z * cpeval_lf Mlf z)%C).
  { intro z.
    rewrite (HevF z), (Hid z), HevM, HevN2. ring. }
  assert (Hheadprod : hd C0 (cpmul_lf (nh :: ntail) Mlf) <> C0).
  { rewrite cpmul_lf_head;
      [| cbn [length]; lia | rewrite HlM; lia].
    cbn [hd].
    unfold Mlf. cbn [hd].
    intro E.
    apply HhdNq0.
    transitivity ((nh * C1)%C); [ring | rewrite E; ring]. }
  assert (Hlists : Flf = cpmul_lf (nh :: ntail) Mlf).
  { apply lf_eq_of_eval; [rewrite HhdF; exact C1_neq_C0 | exact Hheadprod |].
    intro z. rewrite (HidF z), cpmul_lf_eval. reflexivity. }
  assert (Hlnt : length ntail = (N - d)%nat).
  { assert (Hlprod : length (cpmul_lf (nh :: ntail) Mlf)
                     = (length (nh :: ntail) + length Mlf - 1)%nat).
    { unfold cpmul_lf.
      rewrite length_rev.
      rewrite cpmul_length by (rewrite length_rev; cbn [length];
        rewrite ?HlM; lia).
      rewrite !length_rev. reflexivity. }
    rewrite Hlists, Hlprod, HlM in HlF2.
    cbn [length] in HlF2. lia. }
  assert (Hmonic : nh = C1).
  { assert (Hh : hd C0 Flf = (hd C0 (nh :: ntail) * hd C0 Mlf)%C).
    { rewrite Hlists.
      apply cpmul_lf_head; [cbn [length]; lia | rewrite HlM; lia]. }
    rewrite HhdF in Hh.
    cbn [hd] in Hh.
    unfold Mlf in Hh. cbn [hd] in Hh.
    transitivity ((nh * C1)%C); [ring |].
    rewrite <- Hh. reflexivity. }
  subst nh.
  assert (HFq : Forall CQ (C1 :: ntail)).
  { rewrite <- ENq. apply clnorm_Forall. exact HQ. }
  apply (Hexcl (rev ntail) Mlf).
  - apply Forall_rev. exact (Forall_inv_tail HFq).
  - rewrite length_rev. exact Hlnt.
  - unfold Mlf.
    constructor.
    + apply (Csubfield_1 CQ CQ_subfield).
    + apply Forall_rev. exact Hdt.
  - intro z.
    rewrite <- (HevF z), (HidF z).
    assert (Hnq : cpeval_lf (C1 :: ntail) z
                  = (Cpow z (N - d) + cpeval (rev ntail) z)%C).
    { cbn [cpeval_lf].
      rewrite Hlnt.
      rewrite cpeval_lf_rev_c. ring. }
    rewrite Hnq. ring.
Qed.


(* factor certificates modulo a prime -- certify the factorization into irreducibles, so any monic divisor is a subset product and the needed degrees die by subset-sum arithmetic. *)

Local Open Scope Z_scope.

(** divisibility of constant-first integer polynomials modulo m *)
Definition zdivp (m : Z) (a b : list Z) : Prop :=
  exists q : list Z, Zlcong m (Zpmul a q) b.

Lemma Zlcong_refl : forall m u, Zlcong m u u.
Proof.
  intros m u k.
  replace (nth k u 0 - nth k u 0) with 0 by ring.
  apply Z.divide_0_r.
Qed.

Lemma Zlcong_sym_l : forall m u v, Zlcong m u v -> Zlcong m v u.
Proof.
  intros m u v H k.
  replace (nth k v 0 - nth k u 0) with (- (nth k u 0 - nth k v 0)) by ring.
  apply Z.divide_opp_r. apply H.
Qed.

Lemma zdivp_cong_r : forall m a b b',
  Zlcong m b b' -> zdivp m a b -> zdivp m a b'.
Proof.
  intros m a b b' Hbb [q Hq].
  exists q.
  apply (Zlcong_trans m _ b); [exact Hq | exact Hbb].
Qed.

Lemma Zlcong_pmul_r : forall m u v v',
  Zlcong m v v' -> Zlcong m (Zpmul u v) (Zpmul u v').
Proof.
  intros m u v v' Hc k.
  rewrite !nth_Zpmul.
  rewrite (Zconv_comm u v), (Zconv_comm u v').
  pose proof (Zlcong_pmul_l m v v' u Hc k) as H.
  rewrite !nth_Zpmul in H.
  exact H.
Qed.

(* The quotient-ring layer: Zpadd and Zpmul under Zlcong form a commutative setoid ring, so congruence-level identities close by ring. *)

From Stdlib Require Import Setoid.

Lemma Zlcong_padd : forall m u u' v v',
  Zlcong m u u' -> Zlcong m v v' ->
  Zlcong m (Zpadd u v) (Zpadd u' v').
Proof.
  intros m u u' v v' H1 H2 k.
  rewrite !nth_Zpadd.
  replace (nth k u 0 + nth k v 0 - (nth k u' 0 + nth k v' 0))
    with ((nth k u 0 - nth k u' 0) + (nth k v 0 - nth k v' 0)) by ring.
  apply Z.divide_add_r; [apply H1 | apply H2].
Qed.

Lemma nth_map_mul : forall (d : Z) (l : list Z) i,
  nth i (map (Z.mul d) l) 0 = d * nth i l 0.
Proof.
  intros d l i.
  destruct (Nat.lt_ge_cases i (length l)) as [Hk | Hk].
  - replace 0 with (d * 0) at 1 by ring.
    apply (map_nth (Z.mul d) l 0 i).
  - rewrite !nth_overflow; [ring | lia | rewrite length_map; lia].
Qed.

Lemma Zlcong_scale : forall m (c : Z) u v,
  Zlcong m u v -> Zlcong m (map (Z.mul c) u) (map (Z.mul c) v).
Proof.
  intros m c u v H k.
  rewrite !nth_map_mul.
  replace (c * nth k u 0 - c * nth k v 0)
    with (c * (nth k u 0 - nth k v 0)) by ring.
  apply Z.divide_mul_r.
  apply H.
Qed.

Definition Zpopp (p : list Z) : list Z := map (Z.mul (-1)) p.
Definition Zpsub (p q : list Z) : list Z := Zpadd p (Zpopp q).

Lemma peval_map_mul : forall (d : Z) (l : list Z) (x : R),
  peval (map (Z.mul d) l) x = (IZR d * peval l x)%R.
Proof.
  intros d l. induction l as [|h l IH]; intro x; cbn [map peval].
  - ring.
  - rewrite IH, mult_IZR. ring.
Qed.

Lemma Zlcong_peval_intro : forall m u v,
  (forall y : R, peval u y = peval v y) -> Zlcong m u v.
Proof.
  intros m u v H.
  apply nth_eq_lcong.
  apply peval_eq_nth.
  exact H.
Qed.

Section ZlcongRing.

Variable m : Z.

Lemma Zlcong_Setoid : Setoid_Theory (list Z) (Zlcong m).
Proof.
  constructor.
  - exact (Zlcong_refl m).
  - exact (Zlcong_sym_l m).
  - exact (Zlcong_trans m).
Qed.

Lemma Zlcong_ring_eq_ext : ring_eq_ext Zpadd Zpmul Zpopp (Zlcong m).
Proof.
  constructor.
  - intros u u' Hu v v' Hv. apply Zlcong_padd; assumption.
  - intros u u' Hu v v' Hv.
    apply (Zlcong_trans m _ (Zpmul u v')).
    + apply Zlcong_pmul_r. exact Hv.
    + apply Zlcong_pmul_l. exact Hu.
  - intros u u' Hu. unfold Zpopp. apply Zlcong_scale. exact Hu.
Qed.

Lemma Zlcong_ring_theory :
  ring_theory nil (1 :: nil) Zpadd Zpmul Zpsub Zpopp (Zlcong m).
Proof.
  constructor; intros;
    apply Zlcong_peval_intro; intro yy; unfold Zpsub, Zpopp;
    repeat first [rewrite peval_Zpadd | rewrite peval_Zpmul
                 | rewrite peval_map_mul];
    cbn [peval]; ring.
Qed.

Add Ring Zlcong_quotient_ring : Zlcong_ring_theory
  (setoid Zlcong_Setoid Zlcong_ring_eq_ext).

Lemma zc_assoc : forall a b c,
  Zlcong m (Zpmul (Zpmul a b) c) (Zpmul a (Zpmul b c)).
Proof. intros a b c. ring. Qed.

Lemma zc_comm : forall a b, Zlcong m (Zpmul a b) (Zpmul b a).
Proof. intros a b. ring. Qed.

Lemma zc_1l : forall a, Zlcong m (Zpmul (1 :: nil) a) a.
Proof. intro a. ring. Qed.

Lemma zc_addmul : forall a q q',
  Zlcong m (Zpadd (Zpmul a q) (Zpmul a q')) (Zpmul a (Zpadd q q')).
Proof. intros a q q'. ring. Qed.

End ZlcongRing.

(** divisibility algebra mod m *)
Lemma zdivp_mul_r : forall m a b c,
  zdivp m a b -> zdivp m a (Zpmul b c).
Proof.
  intros m a b c [q Hq].
  exists (Zpmul q c).
  apply (Zlcong_trans m _ (Zpmul (Zpmul a q) c)).
  - apply Zlcong_sym_l. apply zc_assoc.
  - apply Zlcong_pmul_l. exact Hq.
Qed.

Lemma zdivp_trans : forall m a b c,
  zdivp m a b -> zdivp m b c -> zdivp m a c.
Proof.
  intros m a b c [q Hq] [q' Hq'].
  exists (Zpmul q q').
  apply (Zlcong_trans m _ (Zpmul (Zpmul a q) q')).
  - apply Zlcong_sym_l. apply zc_assoc.
  - apply (Zlcong_trans m _ (Zpmul b q')); [| exact Hq'].
    apply Zlcong_pmul_l. exact Hq.
Qed.

Lemma zdivp_add : forall m a b c,
  zdivp m a b -> zdivp m a c -> zdivp m a (Zpadd b c).
Proof.
  intros m a b c [q Hq] [q' Hq'].
  exists (Zpadd q q').
  apply (Zlcong_trans m _ (Zpadd (Zpmul a q) (Zpmul a q'))).
  - apply Zlcong_sym_l. apply zc_addmul.
  - apply Zlcong_padd; assumption.
Qed.

Lemma zdivp_congdiv : forall m a a' b,
  Zlcong m a a' -> zdivp m a b -> zdivp m a' b.
Proof.
  intros m a a' b Haa [q Hq].
  exists q.
  apply (Zlcong_trans m _ (Zpmul a q)); [| exact Hq].
  apply Zlcong_pmul_l.
  apply Zlcong_sym_l.
  exact Haa.
Qed.

(* The subtractive extended Euclid modulo m, on constant-first lists with a top-index scan. *)

Definition zshift (k : nat) (b : list Z) : list Z := repeat 0 k ++ b.

Lemma peval_zshift : forall k b y,
  peval (zshift k b) y = (y ^ k * peval b y)%R.
Proof.
  induction k as [|k IH]; intros b y; unfold zshift; cbn [repeat app pow].
  - ring.
  - cbn [peval].
    unfold zshift in IH.
    rewrite IH.
    replace (IZR 0) with 0%R by reflexivity.
    ring.
Qed.

Lemma zc_shiftmul : forall m k b,
  Zlcong m (zshift k b) (Zpmul (zshift k (1 :: nil)) b).
Proof.
  intros m k b.
  apply nth_eq_lcong.
  apply peval_eq_nth.
  intro y.
  rewrite peval_Zpmul, !peval_zshift.
  cbn [peval]. ring.
Qed.

Lemma zdivp_shift : forall m g b k,
  zdivp m g b -> zdivp m g (zshift k b).
Proof.
  intros m g b k Hd.
  apply (zdivp_cong_r m g (Zpmul (zshift k (1 :: nil)) b)).
  - apply Zlcong_sym_l. apply zc_shiftmul.
  - apply (zdivp_cong_r m g (Zpmul b (zshift k (1 :: nil)))).
    + apply zc_comm.
    + apply zdivp_mul_r. exact Hd.
Qed.

(** reduction of one leading term: a - c X^k b, entries reduced mod m *)
Definition zred (m c : Z) (k : nat) (a b : list Z) : list Z :=
  map (fun z => z mod m) (Zpadd a (map (Z.mul (- c)) (zshift k b))).

Lemma map_mod_lcong : forall m l, (1 < m) ->
  Zlcong m (map (fun z => z mod m) l) l.
Proof.
  intros m l Hm k.
  destruct (Nat.lt_ge_cases k (length l)) as [Hk | Hk].
  - replace (nth k (map (fun z => z mod m) l) 0)
      with ((nth k l 0) mod m).
    + rewrite Z.mod_eq by lia.
      replace (nth k l 0 - m * (nth k l 0 / m) - nth k l 0)
        with (- (m * (nth k l 0 / m))) by ring.
      apply Z.divide_opp_r.
      apply Z.divide_factor_l.
    + replace 0 with (0 mod m) at 2 by (apply Z.mod_0_l; lia).
      symmetry.
      exact (map_nth (fun z => z mod m) l 0 k).
  - rewrite !nth_overflow; [| lia | rewrite length_map; lia].
    replace (0 - 0) with 0 by ring.
    apply Z.divide_0_r.
Qed.

Lemma zred_lcong : forall m c k a b, (1 < m) ->
  Zlcong m (zred m c k a b)
    (Zpadd a (map (Z.mul (- c)) (zshift k b))).
Proof.
  intros m c k a b Hm.
  unfold zred.
  apply map_mod_lcong.
  exact Hm.
Qed.

Lemma zdivp_scale : forall m g b (c : Z),
  zdivp m g b -> zdivp m g (map (Z.mul c) b).
Proof.
  intros m g b c [q Hq].
  exists (map (Z.mul c) q).
  apply (Zlcong_trans m _ (map (Z.mul c) (Zpmul g q))).
  - apply nth_eq_lcong.
    intro i.
    apply peval_eq_nth.
    intro y.
    rewrite peval_Zpmul, !peval_map_mul, peval_Zpmul. ring.
  - apply Zlcong_scale. exact Hq.
Qed.

(** the divisor of two terms divides their reduction, and conversely *)
Lemma zdivp_zred : forall m g c k a b, (1 < m) ->
  zdivp m g a -> zdivp m g b -> zdivp m g (zred m c k a b).
Proof.
  intros m g c k a b Hm Ha Hb.
  apply (zdivp_cong_r m g (Zpadd a (map (Z.mul (- c)) (zshift k b)))).
  - apply Zlcong_sym_l. apply zred_lcong. exact Hm.
  - apply zdivp_add; [exact Ha |].
    apply zdivp_scale.
    apply zdivp_shift.
    exact Hb.
Qed.

Lemma zdivp_zred_back : forall m g c k a b, (1 < m) ->
  zdivp m g (zred m c k a b) -> zdivp m g b -> zdivp m g a.
Proof.
  intros m g c k a b Hm Hr Hb.
  assert (Ha' : Zlcong m a
    (Zpadd (zred m c k a b) (map (Z.mul c) (zshift k b)))).
  { apply (Zlcong_trans m _
      (Zpadd (Zpadd a (map (Z.mul (- c)) (zshift k b)))
             (map (Z.mul c) (zshift k b)))).
    - apply nth_eq_lcong.
      intro i.
      rewrite !nth_Zpadd.
      rewrite !nth_map_mul. ring.
    - apply Zlcong_padd.
      + apply Zlcong_sym_l. apply zred_lcong. exact Hm.
      + apply Zlcong_refl. }
  apply (zdivp_cong_r m g
           (Zpadd (zred m c k a b) (map (Z.mul c) (zshift k b))) a
           (Zlcong_sym_l m _ _ Ha')).
  apply zdivp_add; [exact Hr |].
  apply zdivp_scale.
  apply zdivp_shift.
  exact Hb.
Qed.

(** the top nonvanishing index modulo m *)
Fixpoint ztop (m : Z) (l : list Z) : option nat :=
  match l with
  | nil => None
  | a :: t => match ztop m t with
              | Some i => Some (Datatypes.S i)
              | None => if (a mod m =? 0) then None else Some O
              end
  end.

Lemma ztop_none : forall m l, (1 < m) -> ztop m l = None ->
  forall i, (m | nth i l 0).
Proof.
  intros m l Hm.
  induction l as [|a t IH]; intros Hz i.
  - rewrite nth_overflow by (cbn [length]; lia).
    apply Z.divide_0_r.
  - cbn [ztop] in Hz.
    destruct (ztop m t) as [j |] eqn:Et; [discriminate |].
    destruct (a mod m =? 0) eqn:Ea; [| discriminate].
    destruct i as [|i]; cbn [nth].
    + apply Z.mod_divide; [lia |].
      apply Z.eqb_eq. exact Ea.
    + apply IH. reflexivity.
Qed.

Lemma ztop_some_top : forall m l d, (1 < m) -> ztop m l = Some d ->
  ~ (m | nth d l 0).
Proof.
  intros m l.
  induction l as [|a t IH]; intros d Hm Hz.
  - discriminate.
  - cbn [ztop] in Hz.
    destruct (ztop m t) as [j |] eqn:Et.
    + injection Hz as <-.
      cbn [nth].
      apply IH; [exact Hm | reflexivity].
    + destruct (a mod m =? 0) eqn:Ea; [discriminate |].
      injection Hz as <-.
      cbn [nth].
      intro Hd.
      apply Z.mod_divide in Hd; [| lia].
      rewrite Hd in Ea.
      discriminate.
Qed.

Lemma ztop_some_high : forall m l d, (1 < m) -> ztop m l = Some d ->
  forall i, (d < i)%nat -> (m | nth i l 0).
Proof.
  intros m l.
  induction l as [|a t IH]; intros d Hm Hz i Hi.
  - discriminate.
  - cbn [ztop] in Hz.
    destruct (ztop m t) as [j |] eqn:Et.
    + injection Hz as <-.
      destruct i as [|i]; [lia |].
      cbn [nth].
      apply (IH j Hm eq_refl). lia.
    + destruct (a mod m =? 0) eqn:Ea; [discriminate |].
      injection Hz as <-.
      destruct i as [|i]; [lia |].
      cbn [nth].
      apply (ztop_none m t Hm Et).
Qed.

(** modular inverse by scan, certified per modulus by a table check *)
Definition zinv (m a : Z) : Z :=
  hd 0 (filter (fun b => ((a * b) mod m =? 1))
          (map Z.of_nat (seq 0 (Z.to_nat m)))).

Definition invtableb (m : Z) : bool :=
  forallb (fun a =>
    ((Z.of_nat a * zinv m (Z.of_nat a)) mod m =? 1))
    (seq 1 (Z.to_nat m - 1)).

Lemma invtable_7 : invtableb 7 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma invtable_17 : invtableb 17 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zinv_sound : forall m a, (1 < m) -> invtableb m = true ->
  ~ (m | a) -> ((a * zinv m (a mod m)) mod m = 1).
Proof.
  intros m a Hm Htbl Hnd.
  assert (Hr : (0 < a mod m < m)).
  { pose proof (Z.mod_pos_bound a m ltac:(lia)) as Hb.
    assert (Hne : a mod m <> 0).
    { intro E. apply Hnd.
      apply Z.mod_divide; [lia | exact E]. }
    lia. }
  assert (Hin : In (Z.to_nat (a mod m)) (seq 1 (Z.to_nat m - 1)))
    by (apply in_seq; lia).
  pose proof (proj1 (forallb_forall _ _) Htbl _ Hin) as Hok.
  cbv beta in Hok.
  apply Z.eqb_eq in Hok.
  rewrite Z2Nat.id in Hok by lia.
  rewrite <- Hok.
  rewrite <- Z.mul_mod_idemp_l by lia.
  reflexivity.
Qed.

(** nth through shifts and reductions *)
Lemma nth_zshift : forall k b i,
  nth i (zshift k b) 0 = if (i <? k)%nat then 0 else nth (i - k) b 0.
Proof.
  intros k b i.
  unfold zshift.
  destruct (Nat.ltb_spec i k) as [Hi | Hi].
  - rewrite app_nth1 by (rewrite repeat_length; lia).
    apply nth_repeat_lt. lia.
  - rewrite app_nth2 by (rewrite repeat_length; lia).
    rewrite repeat_length. reflexivity.
Qed.

Lemma nth_mapmod : forall m l i, (1 < m) ->
  nth i (map (fun z => z mod m) l) 0 = (nth i l 0) mod m.
Proof.
  intros m l i Hm.
  destruct (Nat.lt_ge_cases i (length l)) as [Hk | Hk].
  - replace 0 with (0 mod m) at 1 by (apply Z.mod_0_l; lia).
    apply (map_nth (fun z => z mod m) l 0 i).
  - rewrite !nth_overflow; [| lia | rewrite length_map; lia].
    symmetry. apply Z.mod_0_l. lia.
Qed.

Lemma nth_zred : forall m c k a b i, (1 < m) ->
  nth i (zred m c k a b) 0
  = ((nth i a 0 + - c * nth i (zshift k b) 0) mod m).
Proof.
  intros m c k a b i Hm.
  unfold zred.
  rewrite nth_mapmod by exact Hm.
  rewrite nth_Zpadd.
  rewrite nth_map_mul.
  reflexivity.
Qed.

(** the reduction kills the leading term *)
Lemma zred_top_drop : forall m r0 r1 d0 d1, (1 < m) -> invtableb m = true ->
  ztop m r0 = Some d0 -> ztop m r1 = Some d1 -> (d1 <= d0)%nat ->
  forall i, (d0 <= i)%nat ->
  (m | nth i (zred m (nth d0 r0 0 * zinv m ((nth d1 r1 0) mod m))
                (d0 - d1) r0 r1) 0).
Proof.
  intros m r0 r1 d0 d1 Hm Htbl Ht0 Ht1 Hle i Hi.
  set (c := nth d0 r0 0 * zinv m ((nth d1 r1 0) mod m)) in *.
  assert (HX : (m | nth i r0 0 + - c * nth i (zshift (d0 - d1) r1) 0)).
  { rewrite nth_zshift.
    destruct (Nat.eq_dec i d0) as [-> | Hne].
    - destruct (Nat.ltb_spec d0 (d0 - d1)) as [Hb | Hb]; [lia |].
      replace (d0 - (d0 - d1))%nat with d1 by lia.
      assert (Hinv : ((nth d1 r1 0 * zinv m ((nth d1 r1 0) mod m)) mod m
                      = 1)).
      { apply zinv_sound; [exact Hm | exact Htbl |].
        apply (ztop_some_top m r1 d1 Hm Ht1). }
      assert (Hdiv1 : (m | nth d1 r1 0 * zinv m ((nth d1 r1 0) mod m) - 1)).
      { rewrite Z.mod_eq in Hinv by lia.
        exists ((nth d1 r1 0 * zinv m ((nth d1 r1 0) mod m)) / m).
        lia. }
      replace (nth d0 r0 0 + - c * nth d1 r1 0)
        with (- (nth d0 r0 0
                 * (nth d1 r1 0 * zinv m ((nth d1 r1 0) mod m) - 1)))
        by (unfold c; ring).
      apply Z.divide_opp_r.
      apply Z.divide_mul_r.
      exact Hdiv1.
    - assert (Hgt : (d0 < i)%nat) by lia.
      apply Z.divide_add_r.
      + apply (ztop_some_high m r0 d0 Hm Ht0 i Hgt).
      + destruct (Nat.ltb_spec i (d0 - d1)) as [Hb | Hb].
        * replace (- c * 0) with 0 by ring.
          apply Z.divide_0_r.
        * apply Z.divide_mul_r.
          apply (ztop_some_high m r1 d1 Hm Ht1).
          lia. }
  rewrite nth_zred by exact Hm.
  apply Z.mod_divide in HX; [| lia].
  rewrite HX.
  apply Z.divide_0_r.
Qed.

(** vanishing above a bound places the top strictly below it *)
Lemma ztop_below : forall m l d, (1 < m) ->
  (forall i, (d <= i)%nat -> (m | nth i l 0)) ->
  match ztop m l with
  | None => True
  | Some d' => (d' < d)%nat
  end.
Proof.
  intros m l d Hm Hvan.
  destruct (ztop m l) as [d' |] eqn:Et; [| exact I].
  destruct (Nat.lt_ge_cases d' d) as [Hlt | Hge]; [exact Hlt | exfalso].
  apply (ztop_some_top m l d' Hm Et).
  apply Hvan. lia.
Qed.

Lemma zdivp_refl : forall m a, zdivp m a a.
Proof.
  intros m a.
  exists (1 :: nil).
  apply (Zlcong_trans m _ (Zpmul (1 :: nil) a)); [apply zc_comm |].
  apply zc_1l.
Qed.

Lemma zdivp_zero : forall m g r, (1 < m) ->
  (forall i, (m | nth i r 0)) -> zdivp m g r.
Proof.
  intros m g r Hm Hvan.
  exists nil.
  intro k.
  assert (Hnil : nth k (Zpmul g nil) 0 = nth k (@nil Z) 0).
  { apply peval_eq_nth.
    intro y.
    rewrite peval_Zpmul. cbn [peval]. ring. }
  rewrite Hnil.
  destruct k; cbn [nth];
    (replace (0 - nth 0 r 0) with (- nth 0 r 0) by ring ||
     idtac);
    [replace (0 - nth 0 r 0) with (- nth 0 r 0) by ring |
     replace (0 - nth (Datatypes.S k) r 0)
       with (- nth (Datatypes.S k) r 0) by ring];
    apply Z.divide_opp_r; apply Hvan.
Qed.

Lemma Zlcong_shift : forall m k u v,
  Zlcong m u v -> Zlcong m (zshift k u) (zshift k v).
Proof.
  intros m k u v H i.
  rewrite !nth_zshift.
  destruct (Nat.ltb_spec i k).
  - replace (0 - 0) with 0 by ring. apply Z.divide_0_r.
  - apply H.
Qed.

(** transporting the combination invariant through one reduction *)
Lemma zred_comb_invariant : forall m (A B r0 r1 u0 v0 u1 v1 : list Z)
                                   (c : Z) (k : nat),
  (1 < m) ->
  Zlcong m r0 (Zpadd (Zpmul u0 A) (Zpmul v0 B)) ->
  Zlcong m r1 (Zpadd (Zpmul u1 A) (Zpmul v1 B)) ->
  Zlcong m (zred m c k r0 r1)
    (Zpadd (Zpmul (zred m c k u0 u1) A) (Zpmul (zred m c k v0 v1) B)).
Proof.
  intros m A B r0 r1 u0 v0 u1 v1 c k Hm H0 H1.
  apply (Zlcong_trans m _
           (Zpadd r0 (map (Z.mul (- c)) (zshift k r1)))).
  { apply zred_lcong. exact Hm. }
  apply (Zlcong_trans m _
           (Zpadd (Zpadd (Zpmul u0 A) (Zpmul v0 B))
                  (map (Z.mul (- c))
                     (zshift k (Zpadd (Zpmul u1 A) (Zpmul v1 B)))))).
  { apply Zlcong_padd; [exact H0 |].
    apply Zlcong_scale.
    apply Zlcong_shift.
    exact H1. }
  apply (Zlcong_trans m _
           (Zpadd (Zpmul (Zpadd u0 (map (Z.mul (- c)) (zshift k u1))) A)
                  (Zpmul (Zpadd v0 (map (Z.mul (- c)) (zshift k v1))) B))).
  { apply nth_eq_lcong.
    apply peval_eq_nth.
    intro y.
    repeat first [rewrite peval_Zpadd | rewrite peval_Zpmul
                 | rewrite peval_map_mul | rewrite peval_zshift].
    ring. }
  apply Zlcong_padd.
  - apply Zlcong_pmul_l.
    apply Zlcong_sym_l.
    apply zred_lcong.
    exact Hm.
  - apply Zlcong_pmul_l.
    apply Zlcong_sym_l.
    apply zred_lcong.
    exact Hm.
Qed.

(** THE LOOP. *)
Fixpoint zgcd_loop (m : Z) (fuel : nat)
    (r0 r1 u0 v0 u1 v1 : list Z) : list Z * list Z * list Z :=
  match fuel with
  | O => (r0, u0, v0)
  | Datatypes.S f =>
    match ztop m r1 with
    | None => (r0, u0, v0)
    | Some d1 =>
      match ztop m r0 with
      | None => (r1, u1, v1)
      | Some d0 =>
        if (d1 <=? d0)%nat then
          let c := nth d0 r0 0 * zinv m ((nth d1 r1 0) mod m) in
          zgcd_loop m f (zred m c (d0 - d1) r0 r1) r1
                       (zred m c (d0 - d1) u0 u1)
                       (zred m c (d0 - d1) v0 v1) u1 v1
        else
          let c := nth d1 r1 0 * zinv m ((nth d0 r0 0) mod m) in
          zgcd_loop m f r0 (zred m c (d1 - d0) r1 r0) u0 v0
                       (zred m c (d1 - d0) u1 u0)
                       (zred m c (d1 - d0) v1 v0)
      end
    end
  end.

Definition zms (m : Z) (r0 r1 : list Z) : nat :=
  (match ztop m r0 with None => O | Some d => Datatypes.S d end)
  + (match ztop m r1 with None => O | Some d => Datatypes.S d end).

Lemma zgcd_loop_correct : forall (m : Z) (A B : list Z), (1 < m) ->
  invtableb m = true ->
  forall n : nat, forall fuel r0 r1 u0 v0 u1 v1,
  (zms m r0 r1 <= n)%nat -> (n < fuel)%nat ->
  Zlcong m r0 (Zpadd (Zpmul u0 A) (Zpmul v0 B)) ->
  Zlcong m r1 (Zpadd (Zpmul u1 A) (Zpmul v1 B)) ->
  let g := fst (fst (zgcd_loop m fuel r0 r1 u0 v0 u1 v1)) in
  let ug := snd (fst (zgcd_loop m fuel r0 r1 u0 v0 u1 v1)) in
  let vg := snd (zgcd_loop m fuel r0 r1 u0 v0 u1 v1) in
  Zlcong m g (Zpadd (Zpmul ug A) (Zpmul vg B)) /\
  zdivp m g r0 /\ zdivp m g r1.
Proof.
  intros m A B Hm Htbl n.
  induction n as [n IH] using (well_founded_induction lt_wf).
  intros fuel r0 r1 u0 v0 u1 v1 Hms Hfuel H0 H1.
  destruct fuel as [|f]; [lia |].
  cbn [zgcd_loop].
  destruct (ztop m r1) as [d1 |] eqn:Et1.
  2:{ cbn [fst snd].
      repeat split.
      - exact H0.
      - apply zdivp_refl.
      - apply zdivp_zero; [exact Hm |].
        apply (ztop_none m r1 Hm Et1). }
  destruct (ztop m r0) as [d0 |] eqn:Et0.
  2:{ cbn [fst snd].
      repeat split.
      - exact H1.
      - apply zdivp_zero; [exact Hm |].
        apply (ztop_none m r0 Hm Et0).
      - apply zdivp_refl. }
  destruct (Nat.leb_spec d1 d0) as [Hle | Hgt].
  - set (c := nth d0 r0 0 * zinv m ((nth d1 r1 0) mod m)).
    set (r0' := zred m c (d0 - d1) r0 r1).
    assert (Hdrop : forall i, (d0 <= i)%nat -> (m | nth i r0' 0))
      by (apply zred_top_drop; assumption).
    unfold zms in Hms.
    rewrite Et0, Et1 in Hms.
    assert (Hms' : (zms m r0' r1 <= n - 1)%nat).
    { unfold zms.
      pose proof (ztop_below m r0' d0 Hm Hdrop) as Hb.
      destruct (ztop m r0') as [d' |]; rewrite Et1; lia. }
    assert (Hinv0' : Zlcong m r0'
      (Zpadd (Zpmul (zred m c (d0 - d1) u0 u1) A)
             (Zpmul (zred m c (d0 - d1) v0 v1) B)))
      by (apply zred_comb_invariant; assumption).
    destruct (IH (n - 1)%nat ltac:(lia) f r0' r1
                (zred m c (d0 - d1) u0 u1) (zred m c (d0 - d1) v0 v1)
                u1 v1 Hms' ltac:(lia) Hinv0' H1)
      as [Hc1 [Hd0' Hd1']].
    repeat split.
    + exact Hc1.
    + apply (zdivp_zred_back m _ c (d0 - d1) r0 r1 Hm Hd0' Hd1').
    + exact Hd1'.
  - set (c := nth d1 r1 0 * zinv m ((nth d0 r0 0) mod m)).
    set (r1' := zred m c (d1 - d0) r1 r0).
    assert (Hdrop : forall i, (d1 <= i)%nat -> (m | nth i r1' 0))
      by (apply zred_top_drop; try assumption; lia).
    unfold zms in Hms.
    rewrite Et0, Et1 in Hms.
    assert (Hms' : (zms m r0 r1' <= n - 1)%nat).
    { unfold zms.
      pose proof (ztop_below m r1' d1 Hm Hdrop) as Hb.
      destruct (ztop m r1') as [d' |]; rewrite Et0; lia. }
    assert (Hinv1' : Zlcong m r1'
      (Zpadd (Zpmul (zred m c (d1 - d0) u1 u0) A)
             (Zpmul (zred m c (d1 - d0) v1 v0) B)))
      by (apply zred_comb_invariant; assumption).
    destruct (IH (n - 1)%nat ltac:(lia) f r0 r1' u0 v0
                (zred m c (d1 - d0) u1 u0) (zred m c (d1 - d0) v1 v0)
                Hms' ltac:(lia) H0 Hinv1')
      as [Hc1 [Hd0' Hd1']].
    repeat split.
    + exact Hc1.
    + exact Hd0'.
    + apply (zdivp_zred_back m _ c (d1 - d0) r1 r0 Hm Hd1' Hd0').
Qed.

(** the top coefficient of a product *)
Lemma zconv_top_mod : forall m (a b : list Z) (da db : nat), (1 < m) ->
  (forall i, (da < i)%nat -> (m | nth i a 0)) ->
  (forall j, (db < j)%nat -> (m | nth j b 0)) ->
  (m | Zconv a b (da + db) - nth da a 0 * nth db b 0).
Proof.
  intros m a b da db Hm Ha Hb.
  revert da Ha.
  induction a as [|x a IH]; intros da Ha.
  - cbn [Zconv].
    rewrite nth_overflow by (cbn [length]; lia).
    replace (0 - 0 * nth db b 0) with 0 by ring.
    apply Z.divide_0_r.
  - destruct da as [|da].
    + cbn [Zconv nth Nat.add].
      destruct db as [|db].
      * replace (x * nth 0 b 0 + 0 - x * nth 0 b 0) with 0 by ring.
        apply Z.divide_0_r.
      * cbn [Zconv].
        replace (x * nth (Datatypes.S db) b 0 + Zconv a b db
                 - x * nth (Datatypes.S db) b 0)
          with (Zconv a b db) by ring.
        (* every entry of a is congruent to zero *)
        assert (Hall : forall i, (m | nth i a 0)).
        { intro i.
          pose proof (Ha (Datatypes.S i) ltac:(lia)) as H.
          cbn [nth] in H. exact H. }
        clear -Hall.
        revert db.
        induction a as [|y a IH2]; intro db; cbn [Zconv].
        { apply Z.divide_0_r. }
        assert (Hy : (m | y)) by (exact (Hall 0%nat)).
        assert (Hall' : forall i, (m | nth i a 0))
          by (intro i; exact (Hall (Datatypes.S i))).
        destruct db as [|db].
        { replace (y * nth 0 b 0 + 0) with (y * nth 0 b 0) by ring.
          apply Z.divide_mul_l. exact Hy. }
        apply Z.divide_add_r.
        { apply Z.divide_mul_l. exact Hy. }
        apply IH2. exact Hall'.
    + cbn [Zconv nth].
      replace (Datatypes.S da + db)%nat with (Datatypes.S (da + db)) by lia.
      assert (Hx : (m | x * nth (Datatypes.S (da + db)) b 0)).
      { apply Z.divide_mul_r. apply Hb. lia. }
      replace (x * nth (Datatypes.S (da + db)) b 0 + Zconv a b (da + db)
               - nth da a 0 * nth db b 0)
        with (x * nth (Datatypes.S (da + db)) b 0
              + (Zconv a b (da + db) - nth da a 0 * nth db b 0)) by ring.
      apply Z.divide_add_r; [exact Hx |].
      apply IH.
      intros i Hi.
      pose proof (Ha (Datatypes.S i) ltac:(lia)) as H.
      cbn [nth] in H. exact H.
Qed.

(* Monic polynomials modulo m: irreducibility, Euclid's lemma, and the classification of monic divisors of a product of irreducibles. *)

Definition zmonic (m : Z) (d : nat) (g : list Z) : Prop :=
  (m | nth d g 0 - 1) /\ (forall i, (d < i)%nat -> (m | nth i g 0)).

Lemma zmonic_top : forall m d g, (1 < m) -> zmonic m d g ->
  ztop m g = Some d.
Proof.
  intros m d g Hm [Htop Hhigh].
  assert (Hnd : ~ (m | nth d g 0)).
  { intro Hd.
    assert (H1 : (m | 1)).
    { replace 1 with (nth d g 0 - (nth d g 0 - 1)) by ring.
      apply Z.divide_sub_r; assumption. }
    apply Z.divide_1_r in H1. lia. }
  destruct (ztop m g) as [d' |] eqn:Et.
  - destruct (Nat.lt_trichotomy d' d) as [Hlt | [-> | Hgt]].
    + exfalso. apply Hnd.
      apply (ztop_some_high m g d' Hm Et). exact Hlt.
    + reflexivity.
    + exfalso.
      apply (ztop_some_top m g d' Hm Et).
      apply Hhigh. exact Hgt.
  - exfalso. apply Hnd.
    apply (ztop_none m g Hm Et).
Qed.

(** A monic multiple of a monic list has the summed degree; a divisor of a lower-degree monic is impossible. *)
Lemma zdivp_monic_degree_le : forall m dl ddl k dk, (1 < m) ->
  zmonic m ddl dl -> zmonic m dk k ->
  zdivp m dl k -> (ddl <= dk)%nat.
Proof.
  intros m dl ddl k dk Hm Hml Hmk [q Hq].
  destruct (Nat.le_gt_cases ddl dk) as [Hle | Hgt]; [exact Hle | exfalso].
  destruct (ztop m q) as [dq |] eqn:Etq.
  - assert (Htopprod : (m | Zconv dl q (ddl + dq)
                         - nth ddl dl 0 * nth dq q 0)).
    { apply zconv_top_mod; [exact Hm | apply (proj2 Hml) |].
      apply (ztop_some_high m q dq Hm Etq). }
    assert (Hkvan : (m | nth (ddl + dq)%nat k 0)).
    { apply (proj2 Hmk). lia. }
    assert (Hprodk : (m | nth (ddl + dq)%nat (Zpmul dl q) 0
                       - nth (ddl + dq)%nat k 0))
      by (apply Hq).
    rewrite nth_Zpmul in Hprodk.
    assert (Hlead : (m | nth ddl dl 0 * nth dq q 0)).
    { replace (nth ddl dl 0 * nth dq q 0)
        with (nth (ddl + dq)%nat k 0
              + (Zconv dl q (ddl + dq) - nth (ddl + dq)%nat k 0)
              - (Zconv dl q (ddl + dq) - nth ddl dl 0 * nth dq q 0))
        by ring.
      apply Z.divide_sub_r; [| exact Htopprod].
      apply Z.divide_add_r; [exact Hkvan | exact Hprodk]. }
    (* the leading product is a unit times the top of q *)
    assert (Hq_top : ~ (m | nth dq q 0))
      by (apply (ztop_some_top m q dq Hm Etq)).
    apply Hq_top.
    assert (Hdl1 : (m | nth ddl dl 0 - 1)) by (apply (proj1 Hml)).
    replace (nth dq q 0)
      with (nth ddl dl 0 * nth dq q 0
            - (nth ddl dl 0 - 1) * nth dq q 0) by ring.
    apply Z.divide_sub_r; [exact Hlead |].
    apply Z.divide_mul_l. exact Hdl1.
  - (* q vanishes, so k vanishes, contradicting monicity *)
    assert (Hkz : forall i, (m | nth i k 0)).
    { intro i.
      pose proof (Hq i) as Hi.
      rewrite nth_Zpmul in Hi.
      assert (Hcz : (m | Zconv dl q i)).
      { rewrite <- nth_Zpmul.
        assert (Hz : zdivp m dl q -> True) by (intro; exact I).
        clear Hz.
        assert (Hqz : forall j, (m | nth j q 0))
          by (apply (ztop_none m q Hm Etq)).
        clear -Hqz.
        revert i.
        induction dl as [|x dl IH]; intro i; cbn [Zpmul].
        { destruct i; cbn [nth]; apply Z.divide_0_r. }
        rewrite nth_Zpadd.
        apply Z.divide_add_r.
        - rewrite nth_map_mul.
          apply Z.divide_mul_r. apply Hqz.
        - destruct i as [|i]; cbn [nth].
          + apply Z.divide_0_r.
          + rewrite nth_Zpmul.
            pose proof (IH i) as H.
            rewrite nth_Zpmul in H.
            exact H. }
      replace (nth i k 0)
        with (Zconv dl q i - (Zconv dl q i - nth i k 0)) by ring.
      apply Z.divide_sub_r; [exact Hcz | exact Hi]. }
    assert (Hnd : ~ (m | nth dk k 0)).
    { intro Hd.
      assert (H1 : (m | 1)).
      { replace 1 with (nth dk k 0 - (nth dk k 0 - 1)) by ring.
        apply Z.divide_sub_r; [exact Hd | apply (proj1 Hmk)]. }
      apply Z.divide_1_r in H1. lia. }
    apply Hnd. apply Hkz.
Qed.

Lemma zmonic_not_vanish : forall m d g, (1 < m) -> zmonic m d g ->
  ~ (forall i, (m | nth i g 0)).
Proof.
  intros m d g Hm [Htop _] Hvan.
  assert (H1 : (m | 1)).
  { replace 1 with (nth d g 0 - (nth d g 0 - 1)) by ring.
    apply Z.divide_sub_r; [apply Hvan | exact Htop]. }
  apply Z.divide_1_r in H1. lia.
Qed.

Lemma zscale_one_cong : forall m (c : Z) (l : list Z),
  (m | c - 1) -> Zlcong m (map (Z.mul c) l) l.
Proof.
  intros m c l Hc k.
  rewrite nth_map_mul.
  replace (c * nth k l 0 - nth k l 0)
    with ((c - 1) * nth k l 0) by ring.
  apply Z.divide_mul_l. exact Hc.
Qed.

Lemma zdivp_monicize : forall m gd dg x, (1 < m) -> invtableb m = true ->
  ztop m gd = Some dg ->
  zdivp m gd x ->
  zdivp m (map (Z.mul (zinv m ((nth dg gd 0) mod m))) gd) x.
Proof.
  intros m gd dg x Hm Htbl Ht [q Hq].
  set (iv := zinv m ((nth dg gd 0) mod m)).
  exists (map (Z.mul (nth dg gd 0)) q).
  apply (Zlcong_trans m _ (map (Z.mul (iv * nth dg gd 0)) (Zpmul gd q))).
  { apply nth_eq_lcong.
    intro i.
    apply peval_eq_nth.
    intro y.
    rewrite peval_Zpmul, !peval_map_mul, peval_Zpmul, mult_IZR. ring. }
  apply (Zlcong_trans m _ (Zpmul gd q)).
  { apply zscale_one_cong.
    assert (Hinv : ((nth dg gd 0 * iv) mod m = 1)).
    { unfold iv.
      apply zinv_sound; [exact Hm | exact Htbl |].
      apply (ztop_some_top m gd dg Hm Ht). }
    rewrite Z.mod_eq in Hinv by lia.
    exists ((nth dg gd 0 * iv) / m).
    lia. }
  exact Hq.
Qed.

Lemma zmonic_monicize : forall m gd dg, (1 < m) -> invtableb m = true ->
  ztop m gd = Some dg ->
  zmonic m dg (map (Z.mul (zinv m ((nth dg gd 0) mod m))) gd).
Proof.
  intros m gd dg Hm Htbl Ht.
  set (iv := zinv m ((nth dg gd 0) mod m)).
  split.
  - rewrite nth_map_mul.
    assert (Hinv : ((nth dg gd 0 * iv) mod m = 1)).
    { unfold iv.
      apply zinv_sound; [exact Hm | exact Htbl |].
      apply (ztop_some_top m gd dg Hm Ht). }
    rewrite Z.mod_eq in Hinv by lia.
    exists ((nth dg gd 0 * iv) / m).
    lia.
  - intros i Hi.
    rewrite nth_map_mul.
    apply Z.divide_mul_r.
    apply (ztop_some_high m gd dg Hm Ht i Hi).
Qed.

(** monic lists of equal degree dividing one another are congruent *)
Lemma zdivp_monic_same_deg : forall m d a b, (1 < m) ->
  zmonic m d a -> zmonic m d b -> zdivp m b a ->
  Zlcong m a b.
Proof.
  intros m d a b Hm Hma Hmb [q Hq].
  set (asub := Zpadd a (map (Z.mul (-1)) b)).
  set (Rr := firstn d (map (fun z => z mod m) asub)).
  assert (HRlow : forall k, (d <= k)%nat -> nth k Rr 0 = 0).
  { intros k Hk.
    unfold Rr.
    apply nth_overflow.
    rewrite firstn_length. lia. }
  assert (Hasub_high : forall k, (d <= k)%nat -> (m | nth k asub 0)).
  { intros k Hk.
    unfold asub.
    rewrite nth_Zpadd, nth_map_mul.
    destruct (Nat.eq_dec k d) as [-> | Hne].
    - replace (nth d a 0 + -1 * nth d b 0)
        with ((nth d a 0 - 1) - (nth d b 0 - 1)) by ring.
      apply Z.divide_sub_r; [apply (proj1 Hma) | apply (proj1 Hmb)].
    - assert (Hgt : (d < k)%nat) by lia.
      replace (nth k a 0 + -1 * nth k b 0)
        with (nth k a 0 - nth k b 0) by ring.
      apply Z.divide_sub_r;
        [apply (proj2 Hma); exact Hgt | apply (proj2 Hmb); exact Hgt]. }
  assert (HRr_cong : Zlcong m Rr asub).
  { intro k.
    destruct (Nat.lt_ge_cases k d) as [Hk | Hk].
    - unfold Rr.
      rewrite nth_firstn_lt by exact Hk.
      rewrite nth_mapmod by exact Hm.
      rewrite Z.mod_eq by lia.
      replace (nth k asub 0 - m * (nth k asub 0 / m) - nth k asub 0)
        with (- (m * (nth k asub 0 / m))) by ring.
      apply Z.divide_opp_r.
      apply Z.divide_factor_l.
    - rewrite (HRlow k Hk).
      replace (0 - nth k asub 0) with (- nth k asub 0) by ring.
      apply Z.divide_opp_r.
      apply Hasub_high.
      exact Hk. }
  assert (Hsplit : Zlcong m a (Zpadd (Zpmul b (1 :: nil)) Rr)).
  { apply (Zlcong_trans m _ (Zpadd b asub)).
    - apply nth_eq_lcong.
      intro i.
      unfold asub.
      rewrite !nth_Zpadd, nth_map_mul.
      ring.
    - apply Zlcong_padd.
      + apply (Zlcong_trans m _ (Zpmul (1 :: nil) b));
          [apply Zlcong_sym_l; apply zc_1l | apply zc_comm].
      + apply Zlcong_sym_l. exact HRr_cong. }
  assert (Hmrz : forall k, (m | nth k Rr 0)).
  { apply (monic_mod_remainder_zero m d b q (1 :: nil) Rr Hm).
    - apply (proj2 Hmb).
    - apply (proj1 Hmb).
    - exact HRlow.
    - apply (Zlcong_trans m _ a); [exact Hq | exact Hsplit]. }
  apply (Zlcong_trans m _ (Zpadd (Zpmul b (1 :: nil)) Rr)); [exact Hsplit |].
  apply (Zlcong_trans m _ (Zpadd b Rr)).
  { apply Zlcong_padd; [| apply Zlcong_refl].
    apply (Zlcong_trans m _ (Zpmul (1 :: nil) b));
      [apply zc_comm | apply zc_1l]. }
  intro k.
  rewrite nth_Zpadd.
  replace (nth k b 0 + nth k Rr 0 - nth k b 0)
    with (nth k Rr 0) by ring.
  apply Hmrz.
Qed.

(** a monic list annihilates only vanishing multipliers *)
Lemma zmul_monic_zero : forall m d g z, (1 < m) ->
  zmonic m d g ->
  (forall i, (m | nth i (Zpmul g z) 0)) ->
  forall i, (m | nth i z 0).
Proof.
  intros m d g z Hm Hmg Hvan.
  destruct (ztop m z) as [dz |] eqn:Et.
  - exfalso.
    pose proof (Hvan (d + dz)%nat) as Hp.
    rewrite nth_Zpmul in Hp.
    pose proof (zconv_top_mod m g z d dz Hm (proj2 Hmg)
                  (ztop_some_high m z dz Hm Et)) as Htop.
    assert (Hlead : (m | nth d g 0 * nth dz z 0)).
    { replace (nth d g 0 * nth dz z 0)
        with (Zconv g z (d + dz)
              - (Zconv g z (d + dz) - nth d g 0 * nth dz z 0)) by ring.
      apply Z.divide_sub_r; [exact Hp | exact Htop]. }
    apply (ztop_some_top m z dz Hm Et).
    replace (nth dz z 0)
      with (nth d g 0 * nth dz z 0 - (nth d g 0 - 1) * nth dz z 0) by ring.
    apply Z.divide_sub_r; [exact Hlead |].
    apply Z.divide_mul_l.
    apply (proj1 Hmg).
  - apply (ztop_none m z Hm Et).
Qed.

(** monic cancellation *)
Lemma zmonic_cancel : forall m d g x y, (1 < m) ->
  zmonic m d g ->
  Zlcong m (Zpmul g x) (Zpmul g y) ->
  Zlcong m x y.
Proof.
  intros m d g x y Hm Hmg Hc.
  set (dxy := Zpadd x (map (Z.mul (-1)) y)).
  assert (Hzero : forall i, (m | nth i (Zpmul g dxy) 0)).
  { intro i.
    assert (HE : nth i (Zpmul g dxy) 0
                 = nth i (Zpadd (Zpmul g x) (map (Z.mul (-1)) (Zpmul g y))) 0).
    { apply peval_eq_nth.
      intro yv.
      unfold dxy.
      rewrite peval_Zpmul, peval_Zpadd, peval_map_mul, peval_Zpadd,
              peval_Zpmul, peval_map_mul, peval_Zpmul.
      ring. }
    rewrite HE.
    rewrite nth_Zpadd, nth_map_mul.
    replace (nth i (Zpmul g x) 0 + -1 * nth i (Zpmul g y) 0)
      with (nth i (Zpmul g x) 0 - nth i (Zpmul g y) 0) by ring.
    apply Hc. }
  pose proof (zmul_monic_zero m d g dxy Hm Hmg Hzero) as Hdz.
  intro k.
  pose proof (Hdz k) as Hk.
  unfold dxy in Hk.
  rewrite nth_Zpadd, nth_map_mul in Hk.
  replace (nth k x 0 - nth k y 0)
    with (nth k x 0 + -1 * nth k y 0) by ring.
  exact Hk.
Qed.

(** the quotient by a monic divisor of a monic list is monic *)
Lemma zquot_monic : forall m d g ddl dl q, (1 < m) ->
  zmonic m d g -> zmonic m ddl dl -> (d <= ddl)%nat ->
  Zlcong m (Zpmul g q) dl ->
  zmonic m (ddl - d)%nat q.
Proof.
  intros m d g ddl dl q Hm Hmg Hmdl Hle Hc.
  assert (Hhigh : forall n i, ((ddl - d) < i)%nat ->
    (length q <= i + n)%nat -> (m | nth i q 0)).
  { induction n as [|n IHn]; intros i Hi Hlen.
    - rewrite nth_overflow by lia.
      apply Z.divide_0_r.
    - destruct (Nat.le_gt_cases (length q) i) as [Hov | Hin].
      + rewrite nth_overflow by lia.
        apply Z.divide_0_r.
      + assert (Hqvan : forall l, (i < l)%nat -> (m | nth l q 0)).
        { intros l Hl.
          apply IHn; lia. }
        pose proof (zconv_top_mod m g q d i Hm (proj2 Hmg) Hqvan) as Htop.
        assert (Hdl : (m | nth (d + i)%nat dl 0))
          by (apply (proj2 Hmdl); lia).
        pose proof (Hc (d + i)%nat) as Hci.
        rewrite nth_Zpmul in Hci.
        assert (Hlead : (m | nth d g 0 * nth i q 0)).
        { replace (nth d g 0 * nth i q 0)
            with (Zconv g q (d + i)
                  - (Zconv g q (d + i) - nth d g 0 * nth i q 0)) by ring.
          apply Z.divide_sub_r; [| exact Htop].
          replace (Zconv g q (d + i))
            with (nth (d + i)%nat dl 0
                  + (Zconv g q (d + i) - nth (d + i)%nat dl 0)) by ring.
          apply Z.divide_add_r; [exact Hdl | exact Hci]. }
        replace (nth i q 0)
          with (nth d g 0 * nth i q 0 - (nth d g 0 - 1) * nth i q 0)
          by ring.
        apply Z.divide_sub_r; [exact Hlead |].
        apply Z.divide_mul_l.
        apply (proj1 Hmg). }
  split.
  - (* the top coefficient is one *)
    assert (Hqvan : forall l, ((ddl - d) < l)%nat -> (m | nth l q 0))
      by (intros l Hl; apply (Hhigh (length q) l Hl); lia).
    pose proof (zconv_top_mod m g q d (ddl - d)%nat Hm (proj2 Hmg) Hqvan)
      as Htop.
    replace (d + (ddl - d))%nat with ddl in Htop by lia.
    pose proof (Hc ddl) as Hcd.
    rewrite nth_Zpmul in Hcd.
    assert (Hlead : (m | nth d g 0 * nth (ddl - d)%nat q 0 - 1)).
    { replace (nth d g 0 * nth (ddl - d)%nat q 0 - 1)
        with ((nth ddl dl 0 - 1)
              + (Zconv g q ddl - nth ddl dl 0)
              - (Zconv g q ddl - nth d g 0 * nth (ddl - d)%nat q 0))
        by ring.
      apply Z.divide_sub_r; [| exact Htop].
      apply Z.divide_add_r; [apply (proj1 Hmdl) | exact Hcd]. }
    replace (nth (ddl - d)%nat q 0 - 1)
      with ((nth d g 0 * nth (ddl - d)%nat q 0 - 1)
            - (nth d g 0 - 1) * nth (ddl - d)%nat q 0) by ring.
    apply Z.divide_sub_r; [exact Hlead |].
    apply Z.divide_mul_l.
    apply (proj1 Hmg).
  - intros i Hi.
    apply (Hhigh (length q) i Hi). lia.
Qed.

(** irreducibility: monic with no proper monic divisor *)
Definition zirred (m : Z) (d : nat) (g : list Z) : Prop :=
  zmonic m d g /\ (1 <= d)%nat /\
  forall (de : nat) (e : list Z), (1 <= de)%nat -> (de < d)%nat ->
    zmonic m de e -> zdivp m e g -> False.

(** THE DICHOTOMY: an irreducible either divides a monic list or admits a Bezout coprimality certificate against it. *)
Lemma zirred_dichotomy : forall m d g ddl dl, (1 < m) ->
  invtableb m = true ->
  zirred m d g -> zmonic m ddl dl ->
  zdivp m g dl \/
  exists u v e, zmonic m 0 e /\
    Zlcong m (Zpadd (Zpmul u g) (Zpmul v dl)) e.
Proof.
  intros m d g ddl dl Hm Htbl [Hmg [Hd1 Hirr]] Hmdl.
  set (fuel := (Datatypes.S (zms m g dl))).
  set (res := zgcd_loop m fuel g dl (1 :: nil) nil nil (1 :: nil)).
  assert (Hinv0 : Zlcong m g (Zpadd (Zpmul (1 :: nil) g) (Zpmul nil dl))).
  { apply nth_eq_lcong.
    intro i.
    apply peval_eq_nth.
    intro y.
    rewrite peval_Zpadd, !peval_Zpmul.
    cbn [peval]. ring. }
  assert (Hinv1 : Zlcong m dl (Zpadd (Zpmul nil g) (Zpmul (1 :: nil) dl))).
  { apply nth_eq_lcong.
    intro i.
    apply peval_eq_nth.
    intro y.
    rewrite peval_Zpadd, !peval_Zpmul.
    cbn [peval]. ring. }
  destruct (zgcd_loop_correct m g dl Hm Htbl (zms m g dl) fuel
              g dl (1 :: nil) nil nil (1 :: nil)
              (Nat.le_refl _) ltac:(unfold fuel; lia) Hinv0 Hinv1)
    as [Hbez [Hdg Hddl]].
  set (gd := fst (fst res)) in *.
  set (ug := snd (fst res)) in *.
  set (vg := snd res) in *.
  fold res gd ug vg in Hbez, Hdg, Hddl.
  destruct (ztop m gd) as [dgd |] eqn:Etg.
  2:{ exfalso.
      apply (zmonic_not_vanish m d g Hm Hmg).
      intro i.
      destruct Hdg as [qg Hqg].
      pose proof (Hqg i) as Hi.
      rewrite nth_Zpmul in Hi.
      assert (Hcz : (m | Zconv gd qg i)).
      { rewrite <- nth_Zpmul.
        assert (Hgz : forall j, (m | nth j gd 0))
          by (apply (ztop_none m gd Hm Etg)).
        clear -Hgz.
        rewrite nth_Zpmul.
        revert i.
        induction gd as [|x t IH]; intro i; cbn [Zconv].
        { apply Z.divide_0_r. }
        assert (Hx : (m | x)) by (exact (Hgz 0%nat)).
        assert (Ht : forall j, (m | nth j t 0))
          by (intro j; exact (Hgz (Datatypes.S j))).
        destruct i as [|i].
        - replace (x * nth 0 qg 0 + 0) with (x * nth 0 qg 0) by ring.
          apply Z.divide_mul_l. exact Hx.
        - apply Z.divide_add_r.
          + apply Z.divide_mul_l. exact Hx.
          + apply IH. exact Ht. }
      replace (nth i g 0)
        with (Zconv gd qg i - (Zconv gd qg i - nth i g 0)) by ring.
      apply Z.divide_sub_r; [exact Hcz | exact Hi]. }
  set (iv := zinv m ((nth dgd gd 0) mod m)).
  set (gmon := map (Z.mul iv) gd).
  assert (Hmon : zmonic m dgd gmon)
    by (apply zmonic_monicize; assumption).
  assert (Hdg' : zdivp m gmon g)
    by (apply zdivp_monicize; assumption).
  assert (Hddl' : zdivp m gmon dl)
    by (apply zdivp_monicize; assumption).
  assert (Hdgd_le : (dgd <= d)%nat)
    by (apply (zdivp_monic_degree_le m gmon dgd g d Hm Hmon Hmg Hdg')).
  destruct (Nat.eq_dec dgd 0%nat) as [-> | Hne0].
  - (* coprime: normalize the Bezout combination *)
    right.
    exists (map (Z.mul iv) ug), (map (Z.mul iv) vg), gmon.
    split; [exact Hmon |].
    apply (Zlcong_trans m _ (map (Z.mul iv) (Zpadd (Zpmul ug g) (Zpmul vg dl)))).
    { apply nth_eq_lcong.
      intro i.
      apply peval_eq_nth.
      intro y.
      rewrite peval_Zpadd, !peval_Zpmul, !peval_map_mul, peval_Zpadd,
              !peval_Zpmul.
      ring. }
    unfold gmon.
    apply Zlcong_scale.
    apply Zlcong_sym_l.
    exact Hbez.
  - destruct (Nat.eq_dec dgd d) as [-> | Hlt].
    + (* full degree: the gcd is the irreducible itself *)
      left.
      apply (zdivp_congdiv m gmon g dl); [| exact Hddl'].
      apply Zlcong_sym_l.
      apply (zdivp_monic_same_deg m d g gmon Hm Hmg Hmon Hdg').
    + exfalso.
      apply (Hirr dgd gmon ltac:(lia) ltac:(lia) Hmon Hdg').
Qed.

(** EUCLID'S LEMMA. *)
Lemma zeuclid : forall m d g ddl dl q w, (1 < m) ->
  invtableb m = true ->
  zirred m d g -> zmonic m ddl dl ->
  Zlcong m (Zpmul dl q) (Zpmul g w) ->
  zdivp m g dl \/ zdivp m dl w.
Proof.
  intros m d g ddl dl q w Hm Htbl Hirr Hmdl Hc.
  destruct (zirred_dichotomy m d g ddl dl Hm Htbl Hirr Hmdl)
    as [Hdiv | [u [v [e [Hme Hbez]]]]].
  - left. exact Hdiv.
  - right.
    exists (Zpadd (Zpmul u q) (Zpmul v w)).
    (* w = w e = w (u g + v dl) = u (g w) + v (dl w) = dl (u q + v w) *)
    apply (Zlcong_trans m _ (Zpadd (Zpmul u (Zpmul dl q))
                                   (Zpmul v (Zpmul dl w)))).
    { apply nth_eq_lcong.
      intro i.
      apply peval_eq_nth.
      intro y.
      rewrite ?peval_Zpadd, ?peval_Zpmul, ?peval_Zpadd, ?peval_Zpmul.
      ring. }
    apply (Zlcong_trans m _ (Zpadd (Zpmul u (Zpmul g w))
                                   (Zpmul v (Zpmul dl w)))).
    { apply Zlcong_padd; [| apply Zlcong_refl].
      apply Zlcong_pmul_r.
      exact Hc. }
    apply (Zlcong_trans m _ (Zpmul (Zpadd (Zpmul u g) (Zpmul v dl)) w)).
    { apply nth_eq_lcong.
      intro i.
      apply peval_eq_nth.
      intro y.
      repeat first [rewrite peval_Zpadd | rewrite peval_Zpmul].
      ring. }
    apply (Zlcong_trans m _ (Zpmul e w)).
    { apply Zlcong_pmul_l. exact Hbez. }
    apply (Zlcong_trans m _ (Zpmul (1 :: nil) w)); [| apply zc_1l].
    apply Zlcong_pmul_l.
    intro k.
    destruct k as [|k].
    + cbn [nth]. apply (proj1 Hme).
    + cbn [nth].
      pose proof ((proj2 Hme) (Datatypes.S k) ltac:(lia)) as Hk.
      replace (match k with O | _ => 0 end) with 0
        by (destruct k; reflexivity).
      replace (nth (Datatypes.S k) e 0 - 0)
        with (nth (Datatypes.S k) e 0) by ring.
      exact Hk.
Qed.

(* The classification: a monic divisor of a product of irreducibles has degree a subset sum of the factor degrees. *)

Fixpoint zprodl (fs : list (list Z)) : list Z :=
  match fs with
  | nil => 1 :: nil
  | g :: fs' => Zpmul g (zprodl fs')
  end.

Lemma zmonic_one : forall m, zmonic m 0 (1 :: nil).
Proof.
  intro m.
  split.
  - cbn [nth].
    replace (1 - 1) with 0 by ring.
    apply Z.divide_0_r.
  - intros i Hi.
    destruct i as [|i]; [lia |].
    cbn [nth].
    destruct i; apply Z.divide_0_r.
Qed.

Lemma zdivisor_degree_subset :
  forall (m : Z) (fs : list (list Z)) (ds : list nat) (dl : list Z)
         (ddl : nat),
  (1 < m) -> invtableb m = true ->
  length ds = length fs ->
  (forall i, (i < length fs)%nat -> zirred m (nth i ds 0%nat) (nth i fs nil)) ->
  zmonic m ddl dl ->
  zdivp m dl (zprodl fs) ->
  exists mask : list bool, length mask = length ds /\
    ddl = fold_right Nat.add 0%nat
            (map (fun p : bool * nat => if fst p then snd p else 0%nat)
               (combine mask ds)).
Proof.
  intros m fs.
  induction fs as [|g fs' IH]; intros ds dl ddl Hm Htbl Hlds Hirrs Hmdl Hdiv.
  - destruct ds; [| cbn [length] in Hlds; lia].
    assert (Hle : (ddl <= 0)%nat).
    { apply (zdivp_monic_degree_le m dl ddl (1 :: nil) 0 Hm Hmdl
               (zmonic_one m) Hdiv). }
    exists nil.
    split; [reflexivity |].
    cbn [combine map fold_right]. lia.
  - destruct ds as [|d ds']; [cbn [length] in Hlds; lia |].
    cbn [length] in Hlds.
    assert (Hirr_g : zirred m d g)
      by (exact (Hirrs 0%nat ltac:(cbn [length]; lia))).
    assert (Hirrs' : forall i, (i < length fs')%nat ->
      zirred m (nth i ds' 0%nat) (nth i fs' nil)).
    { intros i Hi.
      exact (Hirrs (Datatypes.S i) ltac:(cbn [length]; lia)). }
    destruct Hdiv as [q Hq].
    cbn [zprodl] in Hq.
    destruct (zeuclid m d g ddl dl q (zprodl fs') Hm Htbl Hirr_g Hmdl Hq)
      as [Hgdl | HdlP].
    + (* the factor divides: peel it *)
      destruct Hgdl as [e He].
      assert (Hd_le : (d <= ddl)%nat).
      { apply (zdivp_monic_degree_le m g d dl ddl Hm
                 (proj1 Hirr_g) Hmdl).
        exists e. exact He. }
      assert (Hme : zmonic m (ddl - d)%nat e)
        by (apply (zquot_monic m d g ddl dl e Hm (proj1 Hirr_g) Hmdl Hd_le He)).
      assert (HeP : zdivp m e (zprodl fs')).
      { exists q.
        apply (zmonic_cancel m d g _ _ Hm (proj1 Hirr_g)).
        apply (Zlcong_trans m _ (Zpmul (Zpmul g e) q)).
        { apply Zlcong_sym_l. apply zc_assoc. }
        apply (Zlcong_trans m _ (Zpmul dl q)); [| exact Hq].
        apply Zlcong_pmul_l.
        exact He. }
      destruct (IH ds' e (ddl - d)%nat Hm Htbl ltac:(lia) Hirrs' Hme HeP)
        as [mask' [Hlm' Hsum']].
      exists (true :: mask').
      split; [cbn [length]; lia |].
      cbn [combine map fold_right fst snd].
      lia.
    + (* the divisor passes to the tail product *)
      destruct (IH ds' dl ddl Hm Htbl ltac:(lia) Hirrs' Hmdl HdlP)
        as [mask' [Hlm' Hsum']].
      exists (false :: mask').
      split; [cbn [length]; lia |].
      cbn [combine map fold_right fst snd].
      lia.
Qed.

(* Irreducibility from small sweeps, and the rational-level exclusion by factorization certificates. *)

Lemma zmonic_length_min : forall m d e, (1 < m) -> zmonic m d e ->
  (d < length e)%nat.
Proof.
  intros m d e Hm [Htop _].
  destruct (Nat.lt_ge_cases d (length e)) as [Hlt | Hge]; [exact Hlt |].
  exfalso.
  rewrite nth_overflow in Htop by lia.
  replace (0 - 1) with (-1) in Htop by ring.
  apply Z.divide_opp_r in Htop.
  apply Z.divide_1_r in Htop.
  lia.
Qed.

Lemma zirred_of_sweeps : forall m d g, (1 < m) -> invtableb m = true ->
  zmonic m d g -> (1 <= d)%nat ->
  forallb (fun de => forallb (refute_factor m g) (monic_candidates m de))
    (seq 1 (d - 1)) = true ->
  zirred m d g.
Proof.
  intros m d g Hm Htbl Hmg Hd1 Hsweep.
  split; [exact Hmg |].
  split; [exact Hd1 |].
  intros de e Hde1 Hded Hme [q Hq].
  assert (Hlen_e : (de < length e)%nat)
    by (apply (zmonic_length_min m de e Hm Hme)).
  set (e3 := firstn de e ++ 1 :: nil).
  assert (Hle3 : length e3 = Datatypes.S de).
  { unfold e3.
    rewrite length_app, firstn_length.
    cbn [length]. lia. }
  assert (Htop3 : nth de e3 0 = 1).
  { unfold e3.
    rewrite app_nth2; rewrite firstn_length;
      replace (Nat.min de (length e)) with de by lia; [| lia].
    rewrite Nat.sub_diag. reflexivity. }
  assert (Hcong3 : Zlcong m e e3).
  { intro k.
    destruct (Nat.lt_trichotomy k de) as [Hk | [-> | Hk]].
    - unfold e3.
      rewrite app_nth1
        by (rewrite firstn_length; lia).
      rewrite nth_firstn_lt by exact Hk.
      replace (nth k e 0 - nth k e 0) with 0 by ring.
      apply Z.divide_0_r.
    - rewrite Htop3.
      apply (proj1 Hme).
    - rewrite (nth_overflow e3) by (rewrite Hle3; lia).
      replace (nth k e 0 - 0) with (nth k e 0) by ring.
      apply ((proj2 Hme) k Hk). }
  set (dl := map (fun z => z mod m) e3).
  assert (Hdl_in : In dl (monic_candidates m de)).
  { apply reduction_in_candidates; [lia | exact Hle3 | exact Htop3]. }
  assert (Hdl_len : length dl = Datatypes.S de)
    by (unfold dl; rewrite length_map; exact Hle3).
  assert (Hdl_top : nth de dl 0 = 1).
  { unfold dl.
    rewrite nth_mapmod by exact Hm.
    rewrite Htop3.
    apply Z.mod_1_l. lia. }
  assert (Hcong_dl : Zlcong m e dl).
  { apply (Zlcong_trans m _ e3); [exact Hcong3 |].
    apply Zlcong_sym_l.
    unfold dl.
    apply map_mod_lcong.
    exact Hm. }
  assert (Hin_de : In de (seq 1 (d - 1))) by (apply in_seq; lia).
  pose proof (proj1 (forallb_forall _ _) Hsweep de Hin_de) as Hrow.
  cbv beta in Hrow.
  pose proof (proj1 (forallb_forall _ _) Hrow dl Hdl_in) as Href.
  apply (refute_factor_sound_cong m g dl de e q Hm Hdl_len Hdl_top
           Hcong_dl Hq Href).
Qed.

(** boolean congruence check over a window, with soundness *)
Definition zlcongb (m : Z) (u v : list Z) (n : nat) : bool :=
  forallb (fun k => ((nth k u 0 - nth k v 0) mod m =? 0)) (seq 0 n).

Lemma zlcongb_sound : forall m u v n, (1 < m) ->
  (length u <= n)%nat -> (length v <= n)%nat ->
  zlcongb m u v n = true -> Zlcong m u v.
Proof.
  intros m u v n Hm Hu Hv Hb k.
  destruct (Nat.lt_ge_cases k n) as [Hk | Hk].
  - pose proof (proj1 (forallb_forall _ _) Hb k
                  ltac:(apply in_seq; lia)) as Hok.
    cbv beta in Hok.
    apply Z.eqb_eq in Hok.
    apply Z.mod_divide; [lia | exact Hok].
  - rewrite !nth_overflow by lia.
    replace (0 - 0) with 0 by ring.
    apply Z.divide_0_r.
Qed.

(** THE RATIONAL-LEVEL EXCLUSION BY FACTOR CERTIFICATES. *)
Lemma no_rational_factor_by_classification :
  forall (Fz : list Z) (N : nat) (m : Z) (fs : list (list Z))
         (ds : list nat) (d : nat),
  (1 < m) -> invtableb m = true ->
  length Fz = Datatypes.S N -> nth N Fz 0 = 1 -> Zcontent Fz = 1 ->
  (d <= N)%nat ->
  length ds = length fs ->
  (forall i, (i < length fs)%nat ->
     zirred m (nth i ds 0%nat) (nth i fs nil)) ->
  Zlcong m Fz (zprodl fs) ->
  (forall mask : list bool, length mask = length ds ->
     d <> fold_right Nat.add 0%nat
            (map (fun p : bool * nat => if fst p then snd p else 0%nat)
               (combine mask ds))) ->
  forall mu q, Forall is_rational mu -> Forall is_rational q ->
    length mu = Datatypes.S d -> nth d mu 0%R = 1%R ->
    (forall y, pe (map IZR Fz) y = (pe mu y * pe q y)%R) -> False.
Proof.
  intros Fz N m fs ds d Hm Htbl HlF HmF HcF HdN Hlds Hirrs Hprod Hexcl
         mu q Hmurat Hqrat Hmulen Hmumon Hfact.
  destruct (monic_gauss_factor_gen Fz N mu q d HlF HmF HcF Hmurat Hqrat
              Hmulen Hmumon HdN Hfact)
    as [muZ [qZ [Hmu [HmuZlen [HmuZmon [Hq Hpev]]]]]].
  assert (Hnth : forall k, nth k (Zpmul muZ qZ) 0 = nth k Fz 0)
    by (apply peval_eq_nth; exact Hpev).
  assert (HmuZ_monic : zmonic m d muZ).
  { split.
    - rewrite HmuZmon.
      replace (1 - 1) with 0 by ring.
      apply Z.divide_0_r.
    - intros i Hi.
      rewrite nth_overflow by lia.
      apply Z.divide_0_r. }
  assert (Hdiv : zdivp m muZ (zprodl fs)).
  { apply (zdivp_cong_r m muZ Fz); [exact Hprod |].
    exists qZ.
    apply nth_eq_lcong.
    exact Hnth. }
  destruct (zdivisor_degree_subset m fs ds muZ d Hm Htbl Hlds Hirrs
              HmuZ_monic Hdiv) as [mask [Hlm Hsum]].
  exact (Hexcl mask Hlm Hsum).
Qed.
Definition wS17_0 : list Z :=
  (2%Z :: 12%Z :: 2%Z :: 2%Z :: 2%Z :: 1%Z :: nil).

Definition wS17_1 : list Z :=
  (15%Z :: 5%Z :: 14%Z :: 14%Z :: 5%Z :: 1%Z :: nil).

Definition wS17_2 : list Z :=
  (4%Z :: 15%Z :: 16%Z :: 14%Z :: 6%Z :: 1%Z :: nil).

Definition wS7_0 : list Z :=
  (4%Z :: 2%Z :: 5%Z :: 1%Z :: nil).

Definition wS7_1 : list Z :=
  (2%Z :: 2%Z :: 1%Z :: 5%Z :: 0%Z :: 2%Z :: 1%Z :: nil).

Definition wS7_2 : list Z :=
  (1%Z :: 2%Z :: 3%Z :: 5%Z :: 6%Z :: 5%Z :: 1%Z :: nil).

Definition wF7_0 : list Z :=
  (3%Z :: 1%Z :: 4%Z :: 0%Z :: 3%Z :: 4%Z :: 1%Z :: nil).


(** the factorization certificates, checked by vm *)
Lemma wS17_prod : zlcongb 17 witS15z
  (zprodl (wS17_0 :: wS17_1 :: wS17_2 :: nil)) 17 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma wS7_prod : zlcongb 7 witS15z
  (zprodl (wS7_0 :: wS7_1 :: wS7_2 :: nil)) 17 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma wF7_prod : zlcongb 7 witFz (zprodl (wF7_0 :: nil)) 8 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma wS17_irred_sweeps :
  forallb (fun g =>
    forallb (fun de => forallb (refute_factor 17 g) (monic_candidates 17 de))
      (seq 1 4))
    (wS17_0 :: wS17_1 :: wS17_2 :: nil) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma wS7_irred_sweeps :
  forallb (fun gd =>
    forallb (fun de => forallb (refute_factor 7 (snd gd))
               (monic_candidates 7 de))
      (seq 1 (fst gd - 1)))
    ((3%nat, wS7_0) :: (6%nat, wS7_1) :: (6%nat, wS7_2) :: nil) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma wF7_irred_sweep :
  forallb (fun de => forallb (refute_factor 7 wF7_0) (monic_candidates 7 de))
    (seq 1 5) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zmonic_concrete : forall m d (g : list Z),
  nth d g 0 = 1 -> length g = Datatypes.S d -> zmonic m d g.
Proof.
  intros m d g Htop Hlen.
  split.
  - rewrite Htop.
    replace (1 - 1) with 0 by ring.
    apply Z.divide_0_r.
  - intros i Hi.
    rewrite nth_overflow by lia.
    apply Z.divide_0_r.
Qed.

(** the assembled irreducibility facts *)
Lemma wS17_irred : forall i, (i < 3)%nat ->
  zirred 17 (nth i (5%nat :: 5%nat :: 5%nat :: nil) 0%nat)
    (nth i (wS17_0 :: wS17_1 :: wS17_2 :: nil) nil).
Proof.
  intros i Hi.
  assert (Hg : In (nth i (wS17_0 :: wS17_1 :: wS17_2 :: nil) nil)
                  (wS17_0 :: wS17_1 :: wS17_2 :: nil))
    by (apply nth_In; cbn [length]; lia).
  pose proof (proj1 (forallb_forall _ _) wS17_irred_sweeps _ Hg) as Hsw.
  cbv beta in Hsw.
  destruct i as [|[|[|?]]]; try lia; cbn [nth] in *;
    (apply zirred_of_sweeps; try lia;
     [exact invtable_17 | apply zmonic_concrete; reflexivity | exact Hsw]).
Qed.

Lemma wS7_irred : forall i, (i < 3)%nat ->
  zirred 7 (nth i (3%nat :: 6%nat :: 6%nat :: nil) 0%nat)
    (nth i (wS7_0 :: wS7_1 :: wS7_2 :: nil) nil).
Proof.
  intros i Hi.
  assert (Hg : In (nth i ((3%nat, wS7_0) :: (6%nat, wS7_1)
                          :: (6%nat, wS7_2) :: nil) (0%nat, nil))
                  ((3%nat, wS7_0) :: (6%nat, wS7_1) :: (6%nat, wS7_2) :: nil))
    by (apply nth_In; cbn [length]; lia).
  pose proof (proj1 (forallb_forall _ _) wS7_irred_sweeps _ Hg) as Hsw.
  cbv beta in Hsw.
  destruct i as [|[|[|?]]]; try lia; cbn [nth] in *; cbn [fst snd] in Hsw.
  - apply zirred_of_sweeps; try lia;
      [exact invtable_7 | apply zmonic_concrete; reflexivity | exact Hsw].
  - apply zirred_of_sweeps; try lia;
      [exact invtable_7 | apply zmonic_concrete; reflexivity | exact Hsw].
  - apply zirred_of_sweeps; try lia;
      [exact invtable_7 | apply zmonic_concrete; reflexivity | exact Hsw].
Qed.

Lemma wF7_irred : zirred 7 6 wF7_0.
Proof.
  apply zirred_of_sweeps; try lia.
  - exact invtable_7.
  - apply zmonic_concrete; reflexivity.
  - exact wF7_irred_sweep.
Qed.

(** THE RATIONAL EXCLUSIONS. *)
Lemma witS15_excl_rational : forall d, (1 <= d)%nat -> (d <= 7)%nat ->
  forall mu q, Forall is_rational mu -> Forall is_rational q ->
    length mu = Datatypes.S d -> nth d mu 0%R = 1%R ->
    (forall y, pe (map IZR witS15z) y = (pe mu y * pe q y)%R) -> False.
Proof.
  intros d Hd1 Hd7.
  destruct (Nat.eq_dec d 5%nat) as [-> | Hne5].
  - (* degree five dies modulo seven *)
    apply (no_rational_factor_by_classification witS15z 15 7
             (wS7_0 :: wS7_1 :: wS7_2 :: nil)
             (3%nat :: 6%nat :: 6%nat :: nil) 5
             ltac:(lia) invtable_7
             ltac:(reflexivity) ltac:(reflexivity)
             ltac:(vm_compute; reflexivity)
             ltac:(lia) ltac:(reflexivity)
             ltac:(intros i Hi; cbn [length] in Hi;
                   exact (wS7_irred i Hi))
             ltac:(apply (zlcongb_sound 7 _ _ 17); [lia | | | exact wS7_prod];
                   vm_compute; lia)).
    intros mask Hlm.
    destruct mask as [|b1 [|b2 [|b3 [|? ?]]]]; cbn [length] in Hlm; try lia.
    destruct b1; destruct b2; destruct b3;
      cbn [combine map fold_right fst snd]; lia.
  - (* the other degrees die modulo seventeen *)
    apply (no_rational_factor_by_classification witS15z 15 17
             (wS17_0 :: wS17_1 :: wS17_2 :: nil)
             (5%nat :: 5%nat :: 5%nat :: nil) d
             ltac:(lia) invtable_17
             ltac:(reflexivity) ltac:(reflexivity)
             ltac:(vm_compute; reflexivity)
             ltac:(lia) ltac:(reflexivity)
             ltac:(intros i Hi; cbn [length] in Hi;
                   exact (wS17_irred i Hi))
             ltac:(apply (zlcongb_sound 17 _ _ 17); [lia | | | exact wS17_prod];
                   vm_compute; lia)).
    intros mask Hlm.
    destruct mask as [|b1 [|b2 [|b3 [|? ?]]]]; cbn [length] in Hlm; try lia.
    destruct b1; destruct b2; destruct b3;
      cbn [combine map fold_right fst snd]; lia.
Qed.

Lemma witF_excl_rational : forall d, (1 <= d)%nat -> (d <= 5)%nat ->
  forall mu q, Forall is_rational mu -> Forall is_rational q ->
    length mu = Datatypes.S d -> nth d mu 0%R = 1%R ->
    (forall y, pe (map IZR witFz) y = (pe mu y * pe q y)%R) -> False.
Proof.
  intros d Hd1 Hd5.
  apply (no_rational_factor_by_classification witFz 6 7
           (wF7_0 :: nil) (6%nat :: nil) d
           ltac:(lia) invtable_7
           ltac:(reflexivity) ltac:(reflexivity)
           ltac:(vm_compute; reflexivity)
           ltac:(lia) ltac:(reflexivity)
           ltac:(intros i Hi; cbn [length] in Hi;
                 destruct i as [|?]; [exact wF7_irred | lia])
           ltac:(apply (zlcongb_sound 7 _ _ 8); [lia | | | exact wF7_prod];
                 vm_compute; lia)).
  intros mask Hlm.
  destruct mask as [|b1 [|? ?]]; cbn [length] in Hlm; try lia.
  destruct b1; cbn [combine map fold_right fst snd]; lia.
Qed.

Close Scope Z_scope.


Section CLinAlg.

Variable Q : C -> Prop.
Hypothesis HQ : is_Csubfield Q.

Fixpoint CFcomb (cs vs : list C) : C :=
  match cs, vs with
  | c :: cs', v :: vs' => (c * v + CFcomb cs' vs')%C
  | _, _ => C0
  end.

Lemma CFcomb_nil_r : forall cs, CFcomb cs nil = C0.
Proof. destruct cs; reflexivity. Qed.

Lemma CFcomb_zeros : forall vs cs,
  Forall (fun c => c = C0) cs -> CFcomb cs vs = C0.
Proof.
  induction vs as [|v vs IH]; intros cs Hz; [apply CFcomb_nil_r |].
  destruct cs as [|c cs]; [reflexivity |].
  cbn [CFcomb].
  rewrite (Forall_inv Hz).
  rewrite (IH cs (Forall_inv_tail Hz)).
  ring.
Qed.

Lemma CFcomb_app : forall cs1 vs1 cs2 vs2, length cs1 = length vs1 ->
  CFcomb (cs1 ++ cs2) (vs1 ++ vs2) = (CFcomb cs1 vs1 + CFcomb cs2 vs2)%C.
Proof.
  induction cs1 as [|c cs1 IH]; intros vs1 cs2 vs2 Hlen.
  - destruct vs1; cbn [length] in Hlen; [| lia].
    cbn [app CFcomb]. ring.
  - destruct vs1 as [|v vs1]; cbn [length] in Hlen; [lia |].
    cbn [app CFcomb].
    rewrite IH by lia. ring.
Qed.

Lemma CFcomb_middle : forall cL vL x y cR vR, length cL = length vL ->
  CFcomb (cL ++ x :: cR) (vL ++ y :: vR)
  = (CFcomb cL vL + x * y + CFcomb cR vR)%C.
Proof.
  intros cL vL x y cR vR H.
  rewrite CFcomb_app by assumption.
  cbn [CFcomb]. ring.
Qed.

Lemma CFcomb_in_field : forall (K : C -> Prop) cs vs, is_Csubfield K ->
  Forall K cs -> Forall K vs -> K (CFcomb cs vs).
Proof.
  intros K cs vs HK.
  revert vs. induction cs as [|c cs IH]; intros vs Hcs Hvs.
  - cbn [CFcomb]. apply (Csubfield_0 K HK).
  - destruct vs as [|v vs]; cbn [CFcomb]; [apply (Csubfield_0 K HK) |].
    apply Csubfield_add; [exact HK | |].
    + apply Csubfield_mul;
        [exact HK | exact (Forall_inv Hcs) | exact (Forall_inv Hvs)].
    + apply IH; [exact (Forall_inv_tail Hcs) | exact (Forall_inv_tail Hvs)].
Qed.

Definition Cspan (vs : list C) (y : C) : Prop :=
  exists cs, length cs = length vs /\ Forall Q cs /\ CFcomb cs vs = y.

Definition Cindep (vs : list C) : Prop :=
  forall cs, length cs = length vs -> Forall Q cs ->
    CFcomb cs vs = C0 -> Forall (fun c => c = C0) cs.

Definition Cspanning (B : list C) (S : C -> Prop) : Prop :=
  forall y, S y -> Cspan B y.

Definition Cbasis (B : list C) (S : C -> Prop) : Prop :=
  Forall S B /\ Cindep B /\ Cspanning B S.

Lemma Cspan_zero : forall vs, Cspan vs C0.
Proof.
  intro vs.
  exists (repeat C0 (length vs)).
  repeat split.
  - apply repeat_length.
  - apply Forall_forall. intros x Hx.
    apply repeat_spec in Hx. subst x. apply (Csubfield_0 Q HQ).
  - apply CFcomb_zeros.
    apply Forall_forall. intros x Hx.
    apply repeat_spec in Hx. exact Hx.
Qed.


Definition zipC (cs ds : list C) : list C :=
  map (fun p : C * C => (fst p + snd p)%C) (combine cs ds).

Lemma zipC_length : forall cs ds, length cs = length ds ->
  length (zipC cs ds) = length cs.
Proof.
  intros cs ds H. unfold zipC.
  rewrite length_map, length_combine. lia.
Qed.

Lemma zipC_Forall : forall cs ds, Forall Q cs -> Forall Q ds ->
  Forall Q (zipC cs ds).
Proof.
  intros cs ds Hc Hd. unfold zipC.
  apply Forall_map_intro.
  intros p Hp.
  destruct p as [a b].
  apply Csubfield_add; [exact HQ | |].
  - exact (proj1 (Forall_forall Q cs) Hc a (in_combine_l cs ds a b Hp)).
  - exact (proj1 (Forall_forall Q ds) Hd b (in_combine_r cs ds a b Hp)).
Qed.

Lemma CFcomb_zipC : forall vs cs ds,
  length cs = length vs -> length ds = length vs ->
  CFcomb (zipC cs ds) vs = (CFcomb cs vs + CFcomb ds vs)%C.
Proof.
  induction vs as [|v vs IH]; intros cs ds Hc Hd.
  - rewrite !CFcomb_nil_r. ring.
  - destruct cs as [|c cs]; [cbn [length] in Hc; lia |].
    destruct ds as [|d ds]; [cbn [length] in Hd; lia |].
    cbn [length] in Hc, Hd.
    cbn [zipC combine map CFcomb fst snd].
    unfold zipC in IH.
    rewrite IH by lia. ring.
Qed.

Lemma Cspan_add : forall vs x y, Cspan vs x -> Cspan vs y -> Cspan vs (x + y)%C.
Proof.
  intros vs x y [cs [Hl [Hf He]]] [ds [Hl' [Hf' He']]].
  exists (zipC cs ds).
  repeat split.
  - rewrite zipC_length by lia. exact Hl.
  - apply zipC_Forall; assumption.
  - rewrite CFcomb_zipC by assumption.
    rewrite He, He'. reflexivity.
Qed.

Lemma CFcomb_scale : forall vs a cs,
  CFcomb (map (Cmul a) cs) vs = (a * CFcomb cs vs)%C.
Proof.
  induction vs as [|v vs IH]; intros a cs.
  - rewrite !CFcomb_nil_r. ring.
  - destruct cs as [|c cs]; cbn [map CFcomb]; [ring |].
    rewrite IH. ring.
Qed.

Lemma Cspan_scale : forall vs a y, Q a -> Cspan vs y -> Cspan vs (a * y)%C.
Proof.
  intros vs a y Ha [cs [Hl [Hf He]]].
  exists (map (Cmul a) cs).
  repeat split.
  - rewrite length_map. exact Hl.
  - apply Forall_map_intro. intros c Hc.
    apply Csubfield_mul;
      [exact HQ | exact Ha | exact (proj1 (Forall_forall Q cs) Hf c Hc)].
  - rewrite CFcomb_scale, He. reflexivity.
Qed.

Lemma Cspan_opp : forall vs y, Cspan vs y -> Cspan vs (- y)%C.
Proof.
  intros vs y Hy.
  assert (Hm : ((- C1) * y = - y)%C) by ring.
  rewrite <- Hm.
  apply Cspan_scale; [| exact Hy].
  apply Csubfield_opp; [exact HQ | apply (Csubfield_1 Q HQ)].
Qed.

Lemma Cspan_sub : forall vs x y, Cspan vs x -> Cspan vs y -> Cspan vs (x - y)%C.
Proof.
  intros vs x y Hx Hy.
  assert (Hs : (x - y = x + (- y))%C) by ring.
  rewrite Hs.
  apply Cspan_add; [exact Hx | apply Cspan_opp; exact Hy].
Qed.

Fixpoint Ce_i (n i : nat) : list C :=
  match n with
  | O => nil
  | Datatypes.S n' => match i with
                      | O => C1 :: repeat C0 n'
                      | Datatypes.S i' => C0 :: Ce_i n' i'
                      end
  end.

Lemma Ce_i_length : forall n i, length (Ce_i n i) = n.
Proof.
  induction n as [|n IH]; intro i; [reflexivity |].
  destruct i; cbn [Ce_i length].
  - rewrite repeat_length. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma Ce_i_Forall : forall n i, Forall Q (Ce_i n i).
Proof.
  induction n as [|n IH]; intro i; [constructor |].
  destruct i; cbn [Ce_i].
  - constructor; [apply (Csubfield_1 Q HQ) |].
    apply Forall_forall. intros x Hx.
    apply repeat_spec in Hx. subst x. apply (Csubfield_0 Q HQ).
  - constructor; [apply (Csubfield_0 Q HQ) | apply IH].
Qed.

Lemma CFcomb_Ce_i : forall vs i, (i < length vs)%nat ->
  CFcomb (Ce_i (length vs) i) vs = nth i vs C0.
Proof.
  induction vs as [|v vs IH]; intros i Hi; [cbn [length] in Hi; lia |].
  cbn [length] in *.
  destruct i; cbn [Ce_i CFcomb nth].
  - rewrite CFcomb_zeros.
    + ring.
    + apply Forall_forall. intros x Hx. apply repeat_spec in Hx. exact Hx.
  - rewrite IH by lia. ring.
Qed.

Lemma Cspan_in : forall vs v, In v vs -> Cspan vs v.
Proof.
  intros vs v Hv.
  destruct (In_nth vs v C0 Hv) as [i [Hi Hnth]].
  exists (Ce_i (length vs) i).
  repeat split; [apply Ce_i_length | apply Ce_i_Forall |].
  rewrite CFcomb_Ce_i by exact Hi. exact Hnth.
Qed.

Lemma Cspan_trans : forall ws vs y,
  (forall v, In v vs -> Cspan ws v) -> Cspan vs y -> Cspan ws y.
Proof.
  intros ws vs.
  induction vs as [|v vs IH]; intros y Hall [cs [Hl [Hf He]]].
  - rewrite CFcomb_nil_r in He. subst y. apply Cspan_zero.
  - destruct cs as [|c cs]; [cbn [length] in Hl; lia |].
    cbn [length] in Hl. cbn [CFcomb] in He.
    subst y.
    apply Cspan_add.
    + apply Cspan_scale; [exact (Forall_inv Hf) |].
      apply Hall. left. reflexivity.
    + apply (IH (CFcomb cs vs) (fun w Hw => Hall w (or_intror Hw))).
      exists cs.
      repeat split; [lia | exact (Forall_inv_tail Hf)].
Qed.

Lemma Cspan_reps : forall (us vs : list C),
  Forall (Cspan vs) us ->
  exists css : list (list C),
    length css = length us /\
    forall i, (i < length us)%nat ->
      length (nth i css nil) = length vs /\
      Forall Q (nth i css nil) /\
      CFcomb (nth i css nil) vs = nth i us C0.
Proof.
  intros us vs H.
  induction H as [|u us [cs [Hl [Hf He]]] Hall IH].
  - exists nil. split; [reflexivity | intros i Hi; cbn [length] in Hi; lia].
  - destruct IH as [css [Hlc Hspec]].
    exists (cs :: css).
    split; [cbn [length]; lia |].
    intros i Hi.
    destruct i; cbn [nth].
    + repeat split; assumption.
    + apply Hspec. cbn [length] in Hi. lia.
Qed.

Lemma list_split_nth : forall (l : list C) (k : nat),
  (k < length l)%nat ->
  l = firstn k l ++ nth k l C0 :: skipn (Datatypes.S k) l.
Proof.
  induction l as [|a l IH]; intros k Hk; [cbn [length] in Hk; lia |].
  destruct k.
  - reflexivity.
  - cbn [length] in Hk.
    cbn [firstn nth skipn app].
    f_equal.
    apply IH. lia.
Qed.

Lemma CFcomb_shift : forall (u0 w : C) (es us ds : list C),
  length us = length ds ->
  CFcomb es (map (fun p : C * C => (fst p - (snd p * w) * u0)%C)
               (combine us ds))
  = (CFcomb es us - (CFcomb es ds * w) * u0)%C.
Proof.
  intros u0 w es.
  induction es as [|e es IH]; intros us ds Hlen.
  - cbn [CFcomb]. ring.
  - destruct us as [|u us]; destruct ds as [|d ds];
      cbn [length] in Hlen; try lia.
    + cbn [combine map CFcomb]. ring.
    + cbn [combine map CFcomb fst snd].
      rewrite IH by lia. ring.
Qed.

Lemma nth_skipn_my : forall (l : list C) (k j : nat),
  nth j (skipn k l) C0 = nth (k + j) l C0.
Proof.
  induction l as [|a l IH]; intros k j.
  - rewrite skipn_nil. destruct k; destruct j; reflexivity.
  - destruct k; [reflexivity |].
    cbn [skipn nth]. apply IH.
Qed.

Lemma In_firstn : forall (l : list C) k x, In x (firstn k l) -> In x l.
Proof.
  induction l as [|a l IH]; intros k x Hx.
  - rewrite firstn_nil in Hx. contradiction.
  - destruct k; [contradiction |].
    cbn [firstn In] in Hx.
    destruct Hx as [-> | Hx]; [left; reflexivity | right; exact (IH k x Hx)].
Qed.

Lemma In_skipn : forall (l : list C) k x, In x (skipn k l) -> In x l.
Proof.
  induction l as [|a l IH]; intros k x Hx.
  - rewrite skipn_nil in Hx. contradiction.
  - destruct k; [exact Hx |].
    cbn [skipn] in Hx.
    right. exact (IH k x Hx).
Qed.

(** THE STEINITZ EXCHANGE. *)
Lemma Csteinitz : forall vs us,
  Cindep us -> Forall (Cspan vs) us -> (length us <= length vs)%nat.
Proof.
  induction vs as [|v vs IH]; intros us Hind Hsp.
  - destruct us as [|u us]; [cbn [length]; lia | exfalso].
    assert (Hu0 : u = C0).
    { pose proof (Forall_inv Hsp) as [cs [Hl [Hf He]]].
      rewrite CFcomb_nil_r in He. symmetry. exact He. }
    assert (He1 : CFcomb (Ce_i (length (u :: us)) 0) (u :: us) = C0).
    { rewrite CFcomb_Ce_i by (cbn [length]; lia).
      cbn [nth]. exact Hu0. }
    pose proof (Hind _ (Ce_i_length _ _) (Ce_i_Forall _ _) He1) as Hz.
    cbn [length Ce_i] in Hz.
    pose proof (Forall_inv Hz) as HC1.
    exact (C1_neq_C0 HC1).
  - destruct (Cspan_reps us (v :: vs) Hsp) as [css [Hlc Hspec]].
    set (hds := map (fun cs => hd C0 cs) css).
    assert (Hlh : length hds = length us)
      by (unfold hds; rewrite length_map; exact Hlc).
    assert (HhdsQ : Forall Q hds).
    { apply Forall_forall. intros x Hx.
      unfold hds in Hx. apply in_map_iff in Hx.
      destruct Hx as [cs0 [Hcs0 Hin0]].
      destruct (In_nth css cs0 nil Hin0) as [i [Hi Hnth0]].
      rewrite Hlc in Hi.
      destruct (Hspec i Hi) as [_ [Hfi _]].
      rewrite <- Hcs0, <- Hnth0.
      destruct (nth i css nil);
        [apply (Csubfield_0 Q HQ) | exact (Forall_inv Hfi)]. }
    assert (Hhds_nth : forall i, nth i hds C0 = hd C0 (nth i css nil)).
    { intro i. unfold hds.
      replace C0 with (hd C0 (@nil C)) at 1 by reflexivity.
      exact (map_nth (fun cs => hd C0 cs) css nil i). }
    assert (Htails : forall i, (i < length us)%nat ->
      nth i us C0 = (nth i hds C0 * v
                     + CFcomb (tl (nth i css nil)) vs)%C).
    { intros i Hi.
      destruct (Hspec i Hi) as [Hli [Hfi Hei]].
      rewrite Hhds_nth.
      destruct (nth i css nil) as [|c0 ct] eqn:Ecs;
        [cbn [length] in Hli; lia |].
      cbn [hd tl].
      cbn [CFcomb] in Hei.
      rewrite <- Hei. reflexivity. }
    assert (Htail_span : forall i, (i < length us)%nat ->
      Cspan vs (CFcomb (tl (nth i css nil)) vs)).
    { intros i Hi.
      destruct (Hspec i Hi) as [Hli [Hfi _]].
      exists (tl (nth i css nil)).
      repeat split.
      - destruct (nth i css nil); cbn [length] in Hli |- *;
          cbn [tl length]; lia.
      - destruct (nth i css nil); cbn [tl];
          [constructor | exact (Forall_inv_tail Hfi)]. }
    assert (HhQ : forall i, Q (nth i hds C0)).
    { intro i.
      destruct (Nat.lt_ge_cases i (length hds)) as [Hi | Hi].
      - exact (proj1 (Forall_forall Q hds) HhdsQ _ (nth_In hds C0 Hi)).
      - rewrite nth_overflow by lia. apply (Csubfield_0 Q HQ). }
    destruct (classic (Forall (fun c => c = C0) hds)) as [Hallz | Hnz].
    + assert (Hsp' : Forall (Cspan vs) us).
      { apply Forall_forall. intros u Hu.
        destruct (In_nth us u C0 Hu) as [i [Hi Hnth]].
        assert (Hhz : nth i hds C0 = C0).
        { apply (proj1 (Forall_forall _ hds) Hallz).
          apply nth_In. lia. }
        assert (Hval : u = CFcomb (tl (nth i css nil)) vs).
        { rewrite <- Hnth, (Htails i Hi), Hhz. ring. }
        rewrite Hval.
        apply Htail_span. exact Hi. }
      pose proof (IH us Hind Hsp') as Hle.
      cbn [length]. lia.
    + destruct (not_Forall_ex C _ hds Hnz) as [h [Hh_in Hh_ne]].
      destruct (In_nth hds h C0 Hh_in) as [k [Hk Hnth_h]].
      rewrite Hlh in Hk.
      set (c := nth k hds C0).
      assert (Hc_ne : c <> C0)
        by (unfold c; rewrite Hnth_h; exact Hh_ne).
      assert (HcQ : Q c) by apply HhQ.
      set (u0 := nth k us C0).
      set (w := Cinv c).
      assert (HwQ : Q w)
        by (unfold w; apply Csubfield_inv; assumption).
      assert (Hcw : (c * w)%C = C1).
      { unfold w.
        transitivity ((Cinv c * c)%C); [ring |].
        apply Cinv_l. exact Hc_ne. }
      set (P := firstn k us).
      set (S' := skipn (Datatypes.S k) us).
      set (dP := firstn k hds).
      set (dS := skipn (Datatypes.S k) hds).
      assert (HlP : length P = k)
        by (unfold P; rewrite firstn_length; lia).
      assert (HlS : length S' = (length us - Datatypes.S k)%nat)
        by (unfold S'; rewrite skipn_length; lia).
      assert (HldP : length dP = k)
        by (unfold dP; rewrite firstn_length; lia).
      assert (HldS : length dS = (length us - Datatypes.S k)%nat)
        by (unfold dS; rewrite skipn_length; lia).
      assert (HdPQ : Forall Q dP).
      { apply Forall_forall. intros x Hx.
        apply (proj1 (Forall_forall Q hds) HhdsQ).
        apply (In_firstn hds k x Hx). }
      assert (HdSQ : Forall Q dS).
      { apply Forall_forall. intros x Hx.
        apply (proj1 (Forall_forall Q hds) HhdsQ).
        apply (In_skipn hds (Datatypes.S k) x Hx). }
      set (shift := fun p : C * C => (fst p - (snd p * w) * u0)%C).
      set (Us := map shift (combine P dP) ++ map shift (combine S' dS)).
      assert (HlUs : length Us = (length us - 1)%nat).
      { unfold Us.
        rewrite length_app, !length_map, !length_combine. lia. }
      assert (Hsplit_us : us = P ++ u0 :: S')
        by (unfold P, u0, S'; apply list_split_nth; exact Hk).
      assert (HUs_span : Forall (Cspan vs) Us).
      { apply Forall_forall.
        intros x Hx.
        unfold Us in Hx.
        apply in_app_or in Hx.
        assert (Hgen : forall (off : nat) (L D : list C),
          (forall j, (j < length L)%nat ->
             nth j L C0 = nth (off + j) us C0 /\
             nth j D C0 = nth (off + j) hds C0) ->
          length L = length D ->
          (forall j, (j < length L)%nat -> (off + j < length us)%nat) ->
          In x (map shift (combine L D)) -> Cspan vs x).
        { intros off L D Hcorr Hld Hbound Hin.
          apply in_map_iff in Hin.
          destruct Hin as [[a b] [Hab Hin]].
          destruct (In_nth (combine L D) (a, b) (C0, C0) Hin)
            as [j [Hj Hnthj]].
          rewrite length_combine in Hj.
          rewrite combine_nth in Hnthj by lia.
          injection Hnthj as Ha Hb.
          destruct (Hcorr j ltac:(lia)) as [HL HD].
          subst x a b.
          unfold shift. cbn [fst snd].
          rewrite HL, HD.
          set (i := (off + j)%nat).
          assert (Hi : (i < length us)%nat)
            by (unfold i; apply Hbound; lia).
          assert (Hu0v : u0 = (c * v + CFcomb (tl (nth k css nil)) vs)%C)
            by (unfold u0, c; apply (Htails k Hk)).
          assert (Hexp : (nth i us C0 - (nth i hds C0 * w) * u0)%C
            = (CFcomb (tl (nth i css nil)) vs
               - (nth i hds C0 * w) * CFcomb (tl (nth k css nil)) vs)%C).
          { rewrite (Htails i Hi), Hu0v.
            transitivity
              ((nth i hds C0 * (C1 - c * w) * v
                + CFcomb (tl (nth i css nil)) vs
                - (nth i hds C0 * w) * CFcomb (tl (nth k css nil)) vs)%C);
              [ring |].
            rewrite Hcw. ring. }
          rewrite Hexp.
          apply Cspan_sub.
          - apply Htail_span. exact Hi.
          - apply Cspan_scale.
            + apply Csubfield_mul; [exact HQ | apply HhQ | exact HwQ].
            + apply Htail_span. exact Hk. }
        destruct Hx as [Hx | Hx].
        - apply (Hgen 0%nat P dP); [| lia | | exact Hx].
          + intros j Hj.
            rewrite HlP in Hj.
            split.
            * unfold P. cbn [Nat.add].
              rewrite nth_firstn_lt by exact Hj. reflexivity.
            * unfold dP. cbn [Nat.add].
              rewrite nth_firstn_lt by exact Hj. reflexivity.
          + intros j Hj. rewrite HlP in Hj. lia.
        - apply (Hgen (Datatypes.S k) S' dS); [| lia | | exact Hx].
          + intros j Hj.
            split.
            * unfold S'. rewrite nth_skipn_my. reflexivity.
            * unfold dS. rewrite nth_skipn_my. reflexivity.
          + intros j Hj. rewrite HlS in Hj. lia. }
      assert (HUs_ind : Cindep Us).
      { intros es Hle Hfe Hee.
        set (e1 := firstn (length P) es).
        set (e2 := skipn (length P) es).
        assert (Hsplit_e : es = e1 ++ e2)
          by (unfold e1, e2; symmetry; apply firstn_skipn).
        assert (Hle1 : length e1 = length P).
        { unfold e1. rewrite firstn_length.
          rewrite Hle, HlUs. lia. }
        assert (Hle2 : length e2 = length S').
        { unfold e2. rewrite skipn_length.
          rewrite Hle, HlUs. lia. }
        assert (Hfe1 : Forall Q e1).
        { rewrite Hsplit_e in Hfe.
          apply Forall_app in Hfe. exact (proj1 Hfe). }
        assert (Hfe2 : Forall Q e2).
        { rewrite Hsplit_e in Hfe.
          apply Forall_app in Hfe. exact (proj2 Hfe). }
        rewrite Hsplit_e in Hee.
        unfold Us in Hee.
        rewrite CFcomb_app in Hee
          by (rewrite length_map, length_combine; lia).
        unfold shift in Hee.
        rewrite (CFcomb_shift u0 w e1 P dP) in Hee by lia.
        rewrite (CFcomb_shift u0 w e2 S' dS) in Hee by lia.
        set (x0 := (- ((CFcomb e1 dP + CFcomb e2 dS) * w))%C).
        assert (Hx0Q : Q x0).
        { unfold x0.
          apply Csubfield_opp; [exact HQ |].
          apply Csubfield_mul; [exact HQ | | exact HwQ].
          apply Csubfield_add; [exact HQ | |].
          - apply CFcomb_in_field; [exact HQ | exact Hfe1 | exact HdPQ].
          - apply CFcomb_in_field; [exact HQ | exact Hfe2 | exact HdSQ]. }
        assert (Hcomb : CFcomb (e1 ++ x0 :: e2) us = C0).
        { rewrite Hsplit_us.
          rewrite CFcomb_middle by lia.
          unfold x0.
          transitivity
            ((CFcomb e1 P - (CFcomb e1 dP * w) * u0)
             + (CFcomb e2 S' - (CFcomb e2 dS * w) * u0))%C;
            [ring | rewrite Hee; reflexivity]. }
        assert (Hlz : length (e1 ++ x0 :: e2) = length us).
        { rewrite length_app. cbn [length].
          rewrite Hsplit_us, length_app. cbn [length]. lia. }
        assert (Hfz : Forall Q (e1 ++ x0 :: e2)).
        { apply Forall_app_intro_c; [exact Hfe1 |].
          constructor; [exact Hx0Q | exact Hfe2]. }
        pose proof (Hind _ Hlz Hfz Hcomb) as Hz.
        apply Forall_app in Hz.
        destruct Hz as [Hz1 Hz2].
        rewrite Hsplit_e.
        apply Forall_app_intro_c;
          [exact Hz1 | exact (Forall_inv_tail Hz2)]. }
      pose proof (IH Us HUs_ind HUs_span) as Hle.
      rewrite HlUs in Hle.
      cbn [length]. lia.
Qed.


Lemma Cindep_le_span : forall B G (S : C -> Prop),
  Cindep B -> Forall S B -> Cspanning G S -> (length B <= length G)%nat.
Proof.
  intros B G S Hind HBS Hsp.
  apply (Csteinitz G B Hind).
  apply Forall_forall. intros b Hb.
  apply Hsp.
  exact (proj1 (Forall_forall S B) HBS b Hb).
Qed.

Lemma Cbasis_card_unique : forall B1 B2 (S : C -> Prop),
  Cbasis B1 S -> Cbasis B2 S -> length B1 = length B2.
Proof.
  intros B1 B2 S [HS1 [Hli1 Hsp1]] [HS2 [Hli2 Hsp2]].
  assert (H12 : (length B1 <= length B2)%nat)
    by (apply (Cindep_le_span B1 B2 S); assumption).
  assert (H21 : (length B2 <= length B1)%nat)
    by (apply (Cindep_le_span B2 B1 S); assumption).
  lia.
Qed.

(** BASIS EXTRACTION from a finite spanning list, classically. *)
Lemma Cbasis_extract : forall (G : list C) (S : C -> Prop),
  Forall S G -> Cspanning G S ->
  exists B, incl B G /\ Cbasis B S.
Proof.
  intro G.
  remember (length G) as n eqn:Hn.
  revert G Hn.
  induction n as [n IHn] using (well_founded_induction lt_wf);
    intros G Hn S HGS Hsp.
  destruct (classic (Cindep G)) as [Hind | Hnind].
  { exists G.
    split; [apply incl_refl |].
    repeat split; assumption. }
  apply not_all_ex_not in Hnind.
  destruct Hnind as [cs Hcs].
  apply imply_to_and in Hcs. destruct Hcs as [Hlcs Hcs].
  apply imply_to_and in Hcs. destruct Hcs as [Hfcs Hcs].
  apply imply_to_and in Hcs. destruct Hcs as [Hccs Hcs].
  destruct (not_Forall_ex C _ cs Hcs) as [x [Hx_in Hx_ne]].
  destruct (In_nth cs x C0 Hx_in) as [k [Hk Hnth_x]].
  set (ck := nth k cs C0).
  assert (Hck_ne : ck <> C0) by (unfold ck; rewrite Hnth_x; exact Hx_ne).
  assert (HckQ : Q ck).
  { unfold ck.
    apply (proj1 (Forall_forall Q cs) Hfcs).
    apply nth_In. exact Hk. }
  rewrite Hlcs in Hk.
  set (gk := nth k G C0).
  set (P := firstn k G).
  set (S' := skipn (Datatypes.S k) G).
  set (e1 := firstn k cs).
  set (e2 := skipn (Datatypes.S k) cs).
  assert (Hsplit_G : G = P ++ gk :: S')
    by (unfold P, gk, S'; apply list_split_nth; exact Hk).
  assert (Hsplit_cs : cs = e1 ++ ck :: e2)
    by (unfold e1, ck, e2; apply list_split_nth; lia).
  assert (Hle1 : length e1 = length P).
  { unfold e1, P. rewrite !firstn_length. lia. }
  assert (Hle2 : length e2 = length S').
  { unfold e2, S'. rewrite !skipn_length. lia. }
  assert (Hfe1 : Forall Q e1).
  { apply Forall_forall. intros z Hz.
    apply (proj1 (Forall_forall Q cs) Hfcs).
    apply (In_firstn cs k z Hz). }
  assert (Hfe2 : Forall Q e2).
  { apply Forall_forall. intros z Hz.
    apply (proj1 (Forall_forall Q cs) Hfcs).
    apply (In_skipn cs (Datatypes.S k) z Hz). }
  assert (Hgk_span : Cspan (P ++ S') gk).
  { rewrite Hsplit_cs, Hsplit_G in Hccs.
    rewrite CFcomb_middle in Hccs by exact Hle1.
    exists (map (Cmul (- (Cinv ck))%C) (e1 ++ e2)).
    repeat split.
    - rewrite length_map, !length_app. lia.
    - apply Forall_map_intro. intros z Hz.
      apply Csubfield_mul; [exact HQ | |].
      + apply Csubfield_opp; [exact HQ |].
        apply Csubfield_inv; assumption.
      + apply in_app_or in Hz.
        destruct Hz as [Hz | Hz];
          [exact (proj1 (Forall_forall Q e1) Hfe1 z Hz)
          | exact (proj1 (Forall_forall Q e2) Hfe2 z Hz)].
    - rewrite CFcomb_scale.
      rewrite CFcomb_app by exact Hle1.
      assert (Hsum : (CFcomb e1 P + CFcomb e2 S')%C = (- (ck * gk))%C).
      { transitivity ((CFcomb e1 P + ck * gk + CFcomb e2 S') - ck * gk)%C;
          [ring | rewrite Hccs; ring]. }
      rewrite Hsum.
      transitivity ((Cinv ck * ck) * gk)%C; [ring |].
      rewrite Cinv_l by exact Hck_ne. ring. }
  assert (HG'S : Forall S (P ++ S')).
  { rewrite Hsplit_G in HGS.
    apply Forall_app in HGS.
    destruct HGS as [H1 H2].
    apply Forall_app_intro_c; [exact H1 | exact (Forall_inv_tail H2)]. }
  assert (Hsp' : Cspanning (P ++ S') S).
  { intros y Hy.
    apply (Cspan_trans (P ++ S') G y); [| apply Hsp; exact Hy].
    intros v Hv.
    rewrite Hsplit_G in Hv.
    apply in_app_or in Hv.
    destruct Hv as [Hv | [<- | Hv]].
    - apply Cspan_in. apply in_or_app. left. exact Hv.
    - exact Hgk_span.
    - apply Cspan_in. apply in_or_app. right. exact Hv. }
  assert (Hlen' : (length (P ++ S') < n)%nat).
  { rewrite length_app.
    unfold P, S'.
    rewrite firstn_length, skipn_length.
    lia. }
  destruct (IHn (length (P ++ S')) Hlen' (P ++ S') eq_refl S HG'S Hsp')
    as [B [Hincl HB]].
  exists B.
  split; [| exact HB].
  intros b Hb.
  rewrite Hsplit_G.
  pose proof (Hincl b Hb) as Hb'.
  apply in_app_or in Hb'.
  apply in_or_app.
  destruct Hb' as [Hb' | Hb']; [left; exact Hb' | right; right; exact Hb'].
Qed.

End CLinAlg.

(* The tower law: a Q-basis of K and a K-basis of L multiply to a Q-basis of L, so dimensions multiply. *)

Lemma CFcomb_mulr : forall cs vs b,
  CFcomb cs (map (fun v => (v * b)%C) vs) = (CFcomb cs vs * b)%C.
Proof.
  induction cs as [|c cs IH]; intros vs b.
  - cbn [CFcomb]. ring.
  - destruct vs as [|v vs]; cbn [map CFcomb]; [ring |].
    rewrite IH. ring.
Qed.

Section CTower.

Variables (Q K L : C -> Prop).
Hypothesis HQ : is_Csubfield Q.
Hypothesis HK : is_Csubfield K.
Hypothesis HL : is_Csubfield L.
Hypothesis HQK : forall x, Q x -> K x.
Hypothesis HKL : forall x, K x -> L x.

Variable Bf : list C.
Hypothesis HBf : Cbasis Q Bf K.

Definition prodRow (be : C) : list C := map (fun bf => (bf * be)%C) Bf.
Definition prodOf (bs : list C) : list C := flat_map prodRow bs.

Lemma prodOf_length : forall bs,
  length (prodOf bs) = (length Bf * length bs)%nat.
Proof.
  induction bs as [|be bs IH]; cbn [prodOf flat_map length].
  - lia.
  - rewrite length_app.
    unfold prodRow at 1. rewrite length_map.
    unfold prodOf in IH. rewrite IH. lia.
Qed.

Fixpoint kappa (bs es : list C) : list C :=
  match bs with
  | nil => nil
  | _ :: bs' => CFcomb (firstn (length Bf) es) Bf
                :: kappa bs' (skipn (length Bf) es)
  end.

Lemma kappa_length : forall bs es, length (kappa bs es) = length bs.
Proof.
  induction bs as [|be bs IH]; intro es; cbn [kappa length];
    [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma kappa_ForallK : forall bs es, Forall Q es -> Forall K (kappa bs es).
Proof.
  induction bs as [|be bs IH]; intros es Hes; cbn [kappa]; [constructor |].
  constructor.
  - apply CFcomb_in_field; [exact HK | |].
    + apply Forall_forall. intros z Hz.
      apply HQK.
      apply (proj1 (Forall_forall Q es) Hes).
      apply (In_firstn es (length Bf) z Hz).
    + exact (proj1 HBf).
  - apply IH.
    apply Forall_forall. intros z Hz.
    apply (proj1 (Forall_forall Q es) Hes).
    apply (In_skipn es (length Bf) z Hz).
Qed.

Lemma prod_comb : forall bs es,
  length es = (length Bf * length bs)%nat ->
  CFcomb es (prodOf bs) = CFcomb (kappa bs es) bs.
Proof.
  induction bs as [|be bs IH]; intros es Hlen.
  - cbn [prodOf flat_map kappa CFcomb].
    rewrite CFcomb_nil_r. reflexivity.
  - cbn [prodOf flat_map kappa CFcomb].
    cbn [length] in Hlen.
    set (e1 := firstn (length Bf) es).
    set (e2 := skipn (length Bf) es).
    assert (Hsplit : es = e1 ++ e2)
      by (unfold e1, e2; symmetry; apply firstn_skipn).
    assert (Hl1 : length e1 = length Bf)
      by (unfold e1; rewrite firstn_length; lia).
    assert (Hl2 : length e2 = (length Bf * length bs)%nat)
      by (unfold e2; rewrite skipn_length; lia).
    rewrite Hsplit at 1.
    unfold prodOf in IH |- *.
    rewrite CFcomb_app
      by (rewrite Hl1; unfold prodRow; rewrite length_map; reflexivity).
    unfold prodRow at 1.
    rewrite CFcomb_mulr.
    rewrite (IH e2 Hl2).
    reflexivity.
Qed.

Lemma kappa_zero_es : forall bs es,
  length es = (length Bf * length bs)%nat ->
  Forall Q es ->
  Forall (fun c => c = C0) (kappa bs es) ->
  Forall (fun c => c = C0) es.
Proof.
  induction bs as [|be bs IH]; intros es Hlen Hes Hz.
  - cbn [length] in Hlen.
    destruct es; [constructor | cbn [length] in Hlen; lia].
  - cbn [kappa] in Hz.
    cbn [length] in Hlen.
    set (e1 := firstn (length Bf) es).
    set (e2 := skipn (length Bf) es).
    assert (Hsplit : es = e1 ++ e2)
      by (unfold e1, e2; symmetry; apply firstn_skipn).
    assert (Hl1 : length e1 = length Bf)
      by (unfold e1; rewrite firstn_length; lia).
    assert (Hl2 : length e2 = (length Bf * length bs)%nat)
      by (unfold e2; rewrite skipn_length; lia).
    assert (Hf1 : Forall Q e1).
    { apply Forall_forall. intros z Hz'.
      apply (proj1 (Forall_forall Q es) Hes).
      apply (In_firstn es (length Bf) z Hz'). }
    assert (Hf2 : Forall Q e2).
    { apply Forall_forall. intros z Hz'.
      apply (proj1 (Forall_forall Q es) Hes).
      apply (In_skipn es (length Bf) z Hz'). }
    rewrite Hsplit.
    apply Forall_app_intro_c.
    + apply (proj1 (proj2 HBf)); [exact Hl1 | exact Hf1 |].
      exact (Forall_inv Hz).
    + apply (IH e2 Hl2 Hf2).
      exact (Forall_inv_tail Hz).
Qed.

Lemma concat_comb : forall bs ks css,
  length ks = length bs ->
  length css = length ks ->
  (forall i, (i < length ks)%nat ->
     length (nth i css nil) = length Bf /\
     CFcomb (nth i css nil) Bf = nth i ks C0) ->
  CFcomb (concat css) (prodOf bs) = CFcomb ks bs.
Proof.
  induction bs as [|be bs IH]; intros ks css Hlk Hlc Hspec.
  - destruct ks; [| cbn [length] in Hlk; lia].
    destruct css; [| cbn [length] in Hlc; lia].
    reflexivity.
  - destruct ks as [|k0 ks]; [cbn [length] in Hlk; lia |].
    destruct css as [|cs0 css]; [cbn [length] in Hlc; lia |].
    cbn [length] in Hlk, Hlc.
    cbn [concat prodOf flat_map CFcomb].
    destruct (Hspec 0%nat ltac:(cbn [length]; lia)) as [Hl0 He0].
    cbn [nth] in Hl0, He0.
    unfold prodOf in IH |- *.
    rewrite CFcomb_app
      by (rewrite Hl0; unfold prodRow; rewrite length_map; reflexivity).
    unfold prodRow at 1.
    rewrite CFcomb_mulr, He0.
    rewrite (IH ks css ltac:(lia) ltac:(lia)).
    + reflexivity.
    + intros i Hi.
      exact (Hspec (Datatypes.S i) ltac:(cbn [length]; lia)).
Qed.

Lemma concat_length_blocks : forall css (n : nat),
  Forall (fun cs : list C => length cs = n) css ->
  length (concat css) = (n * length css)%nat.
Proof.
  induction css as [|cs css IH]; intros n Hall; cbn [concat length].
  - lia.
  - rewrite length_app.
    rewrite (IH n (Forall_inv_tail Hall)).
    rewrite (Forall_inv Hall). lia.
Qed.

Theorem prodOf_basis : forall Be, Cbasis K Be L -> Cbasis Q (prodOf Be) L.
Proof.
  intros Be [HBeL [HBei HBes]].
  repeat split.
  - apply Forall_forall. intros x Hx.
    unfold prodOf in Hx.
    apply in_flat_map in Hx.
    destruct Hx as [be [Hbe Hx]].
    unfold prodRow in Hx.
    apply in_map_iff in Hx.
    destruct Hx as [bf [Hbf Hbf_in]].
    rewrite <- Hbf.
    apply Csubfield_mul; [exact HL | |].
    + apply HKL.
      exact (proj1 (Forall_forall K Bf) (proj1 HBf) bf Hbf_in).
    + exact (proj1 (Forall_forall L Be) HBeL be Hbe).
  - intros es Hlen Hfe He.
    rewrite prodOf_length in Hlen.
    rewrite (prod_comb Be es Hlen) in He.
    apply (kappa_zero_es Be es Hlen Hfe).
    apply (HBei (kappa Be es));
      [rewrite kappa_length; reflexivity
      | apply kappa_ForallK; exact Hfe
      | exact He].
  - intros y Hy.
    destruct (HBes y Hy) as [ks [Hlk [Hfk Hek]]].
    assert (Hks_span : Forall (Cspan Q Bf) ks).
    { apply Forall_forall. intros k Hk.
      apply (proj2 (proj2 HBf)).
      exact (proj1 (Forall_forall K ks) Hfk k Hk). }
    destruct (Cspan_reps Q ks Bf Hks_span) as [css [Hlc Hspec]].
    exists (concat css).
    repeat split.
    + rewrite prodOf_length.
      rewrite (concat_length_blocks css (length Bf)).
      * lia.
      * apply Forall_forall. intros cs Hcs.
        destruct (In_nth css cs nil Hcs) as [i [Hi Hnth]].
        rewrite Hlc in Hi.
        rewrite <- Hnth.
        exact (proj1 (Hspec i Hi)).
    + apply Forall_forall. intros z Hz.
      apply in_concat in Hz.
      destruct Hz as [cs [Hcs Hz]].
      destruct (In_nth css cs nil Hcs) as [i [Hi Hnth]].
      rewrite Hlc in Hi.
      destruct (Hspec i Hi) as [_ [Hfi _]].
      rewrite <- Hnth in Hz.
      exact (proj1 (Forall_forall Q _) Hfi z Hz).
    + rewrite (concat_comb Be ks css Hlk Hlc).
      * exact Hek.
      * intros i Hi.
        destruct (Hspec i Hi) as [H1 [H2 H3]].
        split; [exact H1 | exact H3].
Qed.

Theorem Ctower_card : forall Be BL,
  Cbasis K Be L -> Cbasis Q BL L ->
  length BL = (length Bf * length Be)%nat.
Proof.
  intros Be BL HBe HBL.
  rewrite <- (prodOf_length Be).
  apply (Cbasis_card_unique Q HQ BL (prodOf Be) L HBL).
  apply prodOf_basis. exact HBe.
Qed.

End CTower.

(* Power bases: the first j powers of an adjoined element form a basis of the one-step extension, tying chain degrees to dimensions. *)

Definition CQpows (z : C) (n : nat) : list C := map (Cpow z) (seq 0 n).

Lemma CQpows_length : forall z n, length (CQpows z n) = n.
Proof.
  intros z n. unfold CQpows. rewrite length_map, length_seq. reflexivity.
Qed.

Lemma CFcomb_scaler_vs : forall cs vs z,
  CFcomb cs (map (Cmul z) vs) = (z * CFcomb cs vs)%C.
Proof.
  induction cs as [|c cs IH]; intros vs z.
  - cbn [CFcomb]. ring.
  - destruct vs as [|v vs]; cbn [map CFcomb]; [ring |].
    rewrite IH. ring.
Qed.

Lemma CFcomb_pows : forall (z : C) (cs : list C) (n : nat),
  length cs = n -> CFcomb cs (CQpows z n) = cpeval cs z.
Proof.
  intros z cs.
  revert z.
  induction cs as [|c cs IH]; intros z n Hlen.
  - destruct n; cbn [CQpows seq map CFcomb cpeval]; reflexivity.
  - destruct n as [|n']; [cbn [length] in Hlen; lia |].
    cbn [length] in Hlen.
    unfold CQpows.
    cbn [seq map CFcomb Cpow cpeval].
    assert (Hshift : map (Cpow z) (seq 1 n')
                     = map (Cmul z) (map (Cpow z) (seq 0 n'))).
    { rewrite <- seq_shift.
      rewrite !map_map.
      apply map_ext.
      intro k. reflexivity. }
    rewrite Hshift.
    rewrite CFcomb_scaler_vs.
    unfold CQpows in IH.
    rewrite (IH z n') by lia.
    ring.
Qed.

Lemma CQpows_nth : forall z n k, (k < n)%nat ->
  nth k (CQpows z n) C0 = Cpow z k.
Proof.
  intros z n k Hk.
  unfold CQpows.
  rewrite (nth_indep _ C0 (Cpow z 0%nat))
    by (rewrite length_map, length_seq; exact Hk).
  rewrite (map_nth (Cpow z) (seq 0 n) 0%nat k).
  rewrite seq_nth by exact Hk.
  reflexivity.
Qed.

Lemma CPolyF_powers_basis : forall (K : C -> Prop) (r : C) (j : nat)
                                   (dt : list C),
  is_Csubfield K -> (1 <= j)%nat ->
  length dt = j -> Forall K dt ->
  (cpeval dt r + Cpow r j)%C = C0 ->
  Cindep_pows K r j ->
  Cbasis K (CQpows r j) (CPolyF K j r).
Proof.
  intros K r j dt HK Hj Hldt HKdt Hrel Hind.
  repeat split.
  - apply Forall_forall. intros x Hx.
    destruct (In_nth (CQpows r j) x C0 Hx) as [k [Hk Hnth]].
    rewrite CQpows_length in Hk.
    exists (Ce_i j k).
    repeat split.
    + apply Ce_i_length.
    + apply Ce_i_Forall. exact HK.
    + rewrite <- (CFcomb_pows r (Ce_i j k) j (Ce_i_length j k)).
      replace j with (length (CQpows r j)) at 1 by apply CQpows_length.
      rewrite CFcomb_Ce_i by (rewrite CQpows_length; exact Hk).
      symmetry. exact Hnth.
  - intros cs Hlen Hf He.
    rewrite CQpows_length in Hlen.
    apply (Hind cs Hlen Hf).
    rewrite <- (CFcomb_pows r cs j Hlen).
    exact He.
  - intros y [cs [Hlcs [Hfcs Hy]]].
    exists cs.
    repeat split.
    + rewrite CQpows_length. exact Hlcs.
    + exact Hfcs.
    + rewrite (CFcomb_pows r cs j Hlcs).
      symmetry. exact Hy.
Qed.

(** THE DIVISIBILITY OF DIMENSIONS: a fifteen-dimensional subfield inside a two-step chain forces the second degree to five. *)
Lemma dim_divide_15 :
  forall (K1 L KP : C -> Prop) (r1 r2 t2 : C) (j2 : nat),
  is_Csubfield K1 -> is_Csubfield L -> is_Csubfield KP ->
  (forall x, CQ x -> K1 x) -> (forall x, K1 x -> L x) ->
  (forall x, CQ x -> KP x) -> (forall x, KP x -> L x) ->
  Cbasis CQ (CQpows r1 6) K1 ->
  Cbasis K1 (CQpows r2 j2) L ->
  Cbasis CQ (CQpows t2 15) KP ->
  Nat.divide 15 (6 * j2)%nat.
Proof.
  intros K1 L KP r1 r2 t2 j2
         HK1 HL HKP HQK1 HK1L HQKP HKPL Hb1 Hb2 HbP.
  set (BL := prodOf (CQpows r1 6) (CQpows r2 j2)).
  assert (HBL : Cbasis CQ BL L).
  { apply (prodOf_basis CQ K1 L HK1 HL HQK1 HK1L
             (CQpows r1 6) Hb1 (CQpows r2 j2) Hb2). }
  assert (HlBL : length BL = (6 * j2)%nat).
  { unfold BL.
    rewrite prodOf_length.
    rewrite !CQpows_length. reflexivity. }
  assert (HBLspan : Cspanning KP BL L).
  { intros y Hy.
    destruct HBL as [_ [_ Hsp]].
    destruct (Hsp y Hy) as [cs [Hlc [Hfc Hec]]].
    exists cs.
    repeat split; [exact Hlc | | exact Hec].
    apply Forall_forall. intros z Hz.
    apply HQKP.
    exact (proj1 (Forall_forall CQ cs) Hfc z Hz). }
  assert (HBLinL : Forall L BL) by (exact (proj1 HBL)).
  destruct (Cbasis_extract KP HKP BL L HBLinL HBLspan) as [Be [Hincl HBe]].
  assert (Hcount : length BL = (15 * length Be)%nat).
  { pose proof (Ctower_card CQ KP L CQ_subfield HKP HL HQKP HKPL
                  (CQpows t2 15) HbP Be BL HBe HBL) as Hc.
    rewrite CQpows_length in Hc. exact Hc. }
  rewrite HlBL in Hcount.
  exists (length Be). lia.
Qed.


(* the degree pinning -- relation degrees pinned to six for witness roots and fifteen for the squared difference, and the chain built with second degree five. *)


(** local vm facts, merged into the sweeps batch at assembly *)
Lemma witF_len : length witFz = 7%nat.
Proof. reflexivity. Qed.

Lemma witF_mon : nth 6 witFz 0%Z = 1%Z.
Proof. reflexivity. Qed.

Lemma witF_content : Zcontent witFz = 1%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma witS15_len : length witS15z = 16%nat.
Proof. reflexivity. Qed.

Lemma witS15_mon : nth 15 witS15z 0%Z = 1%Z.
Proof. reflexivity. Qed.

Lemma witS15_content : Zcontent witS15z = 1%Z.
Proof. vm_compute. reflexivity. Qed.







Lemma Forall_CQ_castZ : forall (l : list Z), Forall CQ (map castZ l).
Proof.
  intro l.
  apply Forall_map_intro.
  intros n _.
  unfold castZ.
  apply CQ_IZR.
Qed.

(** a rational-level exclusion transports to the CQ level *)
Lemma CQ_excl_of_rational : forall (Fz : list Z) (d : nat),
  (forall mu q, Forall is_rational mu -> Forall is_rational q ->
     length mu = Datatypes.S d -> nth d mu 0%R = 1%R ->
     (forall y, pe (map IZR Fz) y = (pe mu y * pe q y)%R) -> False) ->
  CQ_excl Fz d.
Proof.
  intros Fz d Hrat dt Q Hdt Hldt HQ Hid.
  destruct (CQ_list_preimage dt Hdt) as [dtr [Hdtr Hdte]].
  destruct (CQ_list_preimage Q HQ) as [Qr [HQr HQe]].
  set (mu := dtr ++ (1 :: nil)%R).
  set (q := rev Qr).
  apply (Hrat mu q).
  - unfold mu. apply Forall_app_intro; [exact Hdtr |].
    constructor; [| constructor].
    exists 1%Z, 1%Z. split; [lia | field].
  - unfold q. apply Forall_rev. exact HQr.
  - unfold mu. rewrite length_app.
    rewrite Hdte in Hldt. rewrite length_map in Hldt.
    cbn [length]. lia.
  - unfold mu.
    rewrite app_nth2;
      rewrite Hdte in Hldt; rewrite length_map in Hldt; [| lia].
    rewrite Hldt, Nat.sub_diag. reflexivity.
  - intro y.
    assert (Hpe : forall (cs : list R) (x : R), pe cs x = pevalR cs x).
    { intros cs x. unfold pe. apply Fcomb_powers_pevalR. }
    rewrite !Hpe.
    apply RtoC_inj.
    rewrite RtoC_mul.
    assert (HL : RtoC (pevalR (map IZR Fz) y)
                 = cpeval (map castZ Fz) (RtoC y)).
    { rewrite castZ_as_RtoC, cpeval_map_RtoC_global, CevalR_RtoC.
      reflexivity. }
    rewrite HL, (Hid (RtoC y)).
    assert (Hmu : RtoC (pevalR mu y) = (Cpow (RtoC y) d + cpeval dt (RtoC y))%C).
    { unfold mu.
      rewrite pevalR_app, RtoC_add, RtoC_mul.
      rewrite Hdte in Hldt. rewrite length_map in Hldt.
      rewrite Hldt.
      cbn [pevalR].
      rewrite Cpow_RtoC.
      rewrite Hdte, cpeval_map_RtoC_global, CevalR_RtoC.
      assert (H1R : RtoC (1 + y * 0)%R = C1).
      { unfold RtoC, C1. f_equal. ring. }
      rewrite H1R. ring. }
    assert (Hq : RtoC (pevalR q y) = cpeval_lf Q (RtoC y)).
    { unfold q.
      rewrite HQe.
      rewrite cpeval_lf_rev_c.
      rewrite <- map_rev.
      rewrite cpeval_map_RtoC_global, CevalR_RtoC.
      rewrite pevalR_rev, rev_involutive.
      reflexivity. }
    rewrite Hmu, Hq.
    ring.
Qed.

(** the low-degree exclusions for the witness sextic *)
Lemma witF_excl : forall d, (1 <= d)%nat -> (d <= 5)%nat -> CQ_excl witFz d.
Proof.
  intros d Hd1 Hd5.
  apply CQ_excl_of_rational.
  apply witF_excl_rational; assumption.
Qed.

(** the exclusions for the resolvent quotient, low degrees *)
Lemma witS15_excl_low : forall d, (1 <= d)%nat -> (d <= 7)%nat ->
  CQ_excl witS15z d.
Proof.
  intros d Hd1 Hd7.
  apply CQ_excl_of_rational.
  apply witS15_excl_rational; assumption.
Qed.

(** every proper degree is excluded *)
Lemma witS15_excl : forall d, (1 <= d)%nat -> (d <= 14)%nat ->
  CQ_excl witS15z d.
Proof.
  intros d Hd1 Hd14.
  destruct (Nat.le_gt_cases d 7%nat) as [Hle | Hgt].
  - apply witS15_excl_low; assumption.
  - apply (CQ_excl_mirror witS15z 15 d witS15_len witS15_mon Hd1
             ltac:(lia)).
    apply witS15_excl_low; lia.
Qed.

(** THE RELATION-DEGREE PINNING: any CQ-relation of a root of a swept monic integer polynomial has the full degree. *)
Lemma relation_degree_pinned : forall (Fz : list Z) (N : nat) (r : C) (j : nat)
                                      (dt : list C),
  length Fz = Datatypes.S N -> nth N Fz 0%Z = 1%Z ->
  cpeval (map castZ Fz) r = C0 ->
  (forall d, (1 <= d)%nat -> (d <= N - 1)%nat -> CQ_excl Fz d) ->
  (1 <= j)%nat -> (j <= N)%nat ->
  length dt = j -> Forall CQ dt ->
  (cpeval dt r + Cpow r j)%C = C0 ->
  Cindep_pows CQ r j ->
  j = N.
Proof.
  intros Fz N r j dt HlF HmF Hroot Hexcl Hj1 HjN Hldt Hfdt Hrel Hind.
  destruct (Nat.eq_dec j N) as [E | Hne]; [exact E | exfalso].
  destruct (cminpoly_divides CQ r j dt CQ_subfield Hj1 Hldt Hfdt Hrel Hind
              (map castZ Fz) (Forall_CQ_castZ Fz) Hroot) as [HQdiv Hdiv].
  apply (Hexcl j Hj1 ltac:(lia) dt
           (fst (cpdiv_lf (length (rev (map castZ Fz))) (rev (map castZ Fz))
                   (rev dt))) Hfdt Hldt HQdiv).
  intro z.
  rewrite (Hdiv z). ring.
Qed.

(** THE GREEDY CHAIN CONSTRUCTION: adjoin a list of roots one at a time, minimizing each degree. *)
Lemma build_chain : forall (B : C -> Prop) (rho : list C),
  is_Csubfield B ->
  length rho = 6%nat ->
  (forall r, In r rho -> cpeval (map castZ witFz) r = C0) ->
  (forall z, CQ z -> B z) ->
  forall (todo : list C), incl todo rho ->
  exists rs js K, RootChain B rho rs js K /\ incl todo rs.
Proof.
  intros B rho HB Hlrho Hroots HQB todo.
  induction todo as [|r todo IH]; intro Hincl.
  - exists nil, nil, B.
    split; [constructor | intros x Hx; contradiction].
  - destruct IH as [rs [js [K [Hch Hin]]]];
      [intros x Hx; apply Hincl; right; exact Hx |].
    assert (HKsub : is_Csubfield K)
      by (apply (RootChain_subfield B rho rs js K HB Hch)).
    assert (Hr_rho : In r rho) by (apply Hincl; left; reflexivity).
    destruct (cpowers_max_prefix K r 6 HKsub ltac:(lia))
      as [j [Hj [Hind Hcase]]].
    assert (Hrel : exists dt, length dt = j /\ Forall K dt /\
      (cpeval dt r + Cpow r j)%C = C0).
    { destruct Hcase as [-> | Hex]; [| exact Hex].
      exists (map castZ (firstn 6 witFz)).
      refine (conj _ (conj _ _)).
      - rewrite length_map, firstn_length, witF_len. lia.
      - apply Forall_forall. intros z Hz.
        apply (RootChain_incl B rho rs js K HB Hch).
        apply HQB.
        apply in_map_iff in Hz.
        destruct Hz as [n [Hzn _]].
        rewrite <- Hzn. unfold castZ. apply CQ_IZR.
      - assert (Hsplit6 : cpeval (map castZ witFz) r
                          = (cpeval (map castZ (firstn 6 witFz)) r
                             + Cpow r 6)%C).
        { assert (HFz_split : witFz = firstn 6 witFz ++ (1 :: nil)%Z).
          { vm_compute. reflexivity. }
          rewrite HFz_split at 1.
          rewrite map_app, cpeval_app.
          rewrite length_map, firstn_length, witF_len.
          cbn [map cpeval Nat.min].
          assert (Hc1 : castZ 1%Z = C1) by reflexivity.
          rewrite Hc1. ring. }
        rewrite <- Hsplit6.
        apply Hroots. exact Hr_rho. }
    destruct Hrel as [dt [Hldt [HKdt Hreldt]]].
    exists (rs ++ r :: nil), (js ++ j :: nil), (CPolyF K j r).
    split.
    + apply (RC_step B rho rs js K r j dt); try assumption.
      * lia.
      * rewrite Hlrho. lia.
    + intros x Hx.
      destruct Hx as [<- | Hx].
      * apply in_or_app. right. left. reflexivity.
      * apply in_or_app. left. apply Hin. exact Hx.
Qed.

(** chains over an extension prepend onto chains reaching it *)
Lemma RootChain_append : forall (K0 : C -> Prop) (rho rs1 : list C)
                                (js1 : list nat) (K : C -> Prop)
                                (rs2 : list C) (js2 : list nat)
                                (K' : C -> Prop),
  RootChain K0 rho rs1 js1 K ->
  RootChain K rho rs2 js2 K' ->
  RootChain K0 rho (rs1 ++ rs2) (js1 ++ js2) K'.
Proof.
  intros K0 rho rs1 js1 K rs2 js2 K' H1 H2.
  induction H2 as [| rs js K2 r j dt H2 IH Hin Hj1 Hjn Hldt HKdt Hrel Hind].
  - rewrite !app_nil_r. exact H1.
  - rewrite !app_assoc.
    apply (RC_step K0 rho (rs1 ++ rs) (js1 ++ js) K2 r j dt); assumption.
Qed.

(** the six-term tail of the witness sextic as a CQ relation *)
Lemma witF_tail_relation : forall (K : C -> Prop) (r : C),
  is_Csubfield K -> (forall z, CQ z -> K z) ->
  cpeval (map castZ witFz) r = C0 ->
  length (map castZ (firstn 6 witFz)) = 6%nat /\
  Forall K (map castZ (firstn 6 witFz)) /\
  (cpeval (map castZ (firstn 6 witFz)) r + Cpow r 6)%C = C0.
Proof.
  intros K r HK HQK Hroot.
  refine (conj _ (conj _ _)).
  - rewrite length_map, firstn_length, witF_len. reflexivity.
  - apply Forall_forall. intros z Hz.
    apply HQK.
    apply in_map_iff in Hz.
    destruct Hz as [n [Hzn _]].
    rewrite <- Hzn. unfold castZ. apply CQ_IZR.
  - assert (HFz_split : witFz = firstn 6 witFz ++ (1 :: nil)%Z).
    { vm_compute. reflexivity. }
    rewrite <- Hroot.
    rewrite HFz_split at 2.
    rewrite map_app, cpeval_app.
    rewrite length_map, firstn_length, witF_len.
    cbn [map cpeval Nat.min].
    assert (Hc1 : castZ 1%Z = C1) by reflexivity.
    rewrite Hc1. ring.
Qed.

(** The chain over CQ with the two designated roots adjoined first and the first degree pinned to six. *)
Lemma witness_chain_shape :
  forall (rho : list C) (r1 r2 : C),
  length rho = 6%nat ->
  (forall r, In r rho -> cpeval (map castZ witFz) r = C0) ->
  In r1 rho -> In r2 rho ->
  exists (j2 : nat) (dt1 dt2 : list C) (rs : list C) (js : list nat)
         (K : C -> Prop),
    length dt1 = 6%nat /\ Forall CQ dt1 /\
    (cpeval dt1 r1 + Cpow r1 6)%C = C0 /\ Cindep_pows CQ r1 6 /\
    (1 <= j2)%nat /\ (j2 <= 6)%nat /\
    length dt2 = j2 /\ Forall (CPolyF CQ 6 r1) dt2 /\
    (cpeval dt2 r2 + Cpow r2 j2)%C = C0 /\
    Cindep_pows (CPolyF CQ 6 r1) r2 j2 /\
    RootChain (CPolyF (CPolyF CQ 6 r1) j2 r2) rho rs js K /\
    RootChain CQ rho (r1 :: r2 :: rs) (6%nat :: j2 :: js) K /\
    incl rho (r1 :: r2 :: rs).
Proof.
  intros rho r1 r2 Hlrho Hroots Hr1 Hr2.
  (* pin the first degree *)
  destruct (cpowers_max_prefix CQ r1 6 CQ_subfield ltac:(lia))
    as [j1 [Hj1b [Hind1 Hcase1]]].
  destruct (witF_tail_relation CQ r1 CQ_subfield (fun z Hz => Hz)
              (Hroots r1 Hr1)) as [Hl0 [Hf0 Hrel0]].
  assert (Hrel1 : exists dt, length dt = j1 /\ Forall CQ dt /\
    (cpeval dt r1 + Cpow r1 j1)%C = C0).
  { destruct Hcase1 as [-> | Hex]; [| exact Hex].
    exists (map castZ (firstn 6 witFz)).
    repeat split; assumption. }
  destruct Hrel1 as [dtc [Hldtc [Hfdtc Hreldtc]]].
  assert (Hj1_6 : j1 = 6%nat).
  { apply (relation_degree_pinned witFz 6 r1 j1 dtc witF_len witF_mon
             (Hroots r1 Hr1)); try assumption; try lia.
    intros d Hd1 Hd5.
    apply witF_excl; [exact Hd1 | lia]. }
  subst j1.
  rewrite Hj1_6 in Hreldtc, Hind1.
  set (K1 := CPolyF CQ 6 r1).
  assert (Hch1 : RootChain CQ rho (r1 :: nil) (6%nat :: nil) K1).
  { replace (r1 :: nil) with (nil ++ r1 :: nil) by reflexivity.
    replace (6%nat :: nil) with (nil ++ 6%nat :: nil) by reflexivity.
    apply (RC_step CQ rho nil nil CQ r1 6%nat dtc).
    - constructor.
    - exact Hr1.
    - lia.
    - rewrite Hlrho. lia.
    - exact Hj1_6.
    - exact Hfdtc.
    - exact Hreldtc.
    - exact Hind1. }
  assert (HK1sub : is_Csubfield K1)
    by (apply (RootChain_subfield CQ rho _ _ K1 CQ_subfield Hch1)).
  assert (HQK1 : forall z, CQ z -> K1 z)
    by (apply (RootChain_incl CQ rho _ _ K1 CQ_subfield Hch1)).
  (* the second step *)
  destruct (cpowers_max_prefix K1 r2 6 HK1sub ltac:(lia))
    as [j2 [Hj2b [Hind2 Hcase2]]].
  destruct (witF_tail_relation K1 r2 HK1sub HQK1 (Hroots r2 Hr2))
    as [Hl2 [Hf2 Hrel2]].
  assert (Hrel2' : exists dt, length dt = j2 /\ Forall K1 dt /\
    (cpeval dt r2 + Cpow r2 j2)%C = C0).
  { destruct Hcase2 as [-> | Hex]; [| exact Hex].
    exists (map castZ (firstn 6 witFz)).
    repeat split; assumption. }
  destruct Hrel2' as [dt2 [Hldt2 [Hfdt2 Hreldt2]]].
  set (L := CPolyF K1 j2 r2).
  assert (Hch2 : RootChain CQ rho (r1 :: r2 :: nil) (6%nat :: j2 :: nil) L).
  { replace (r1 :: r2 :: nil) with ((r1 :: nil) ++ r2 :: nil) by reflexivity.
    replace (6%nat :: j2 :: nil) with ((6%nat :: nil) ++ j2 :: nil)
      by reflexivity.
    apply (RC_step CQ rho (r1 :: nil) (6%nat :: nil) K1 r2 j2 dt2).
    - exact Hch1.
    - exact Hr2.
    - lia.
    - rewrite Hlrho. lia.
    - exact Hldt2.
    - exact Hfdt2.
    - exact Hreldt2.
    - exact Hind2. }
  assert (HLsub : is_Csubfield L)
    by (apply (RootChain_subfield CQ rho _ _ L CQ_subfield Hch2)).
  assert (HQL : forall z, CQ z -> L z)
    by (apply (RootChain_incl CQ rho _ _ L CQ_subfield Hch2)).
  (* the remaining roots *)
  destruct (build_chain L rho HLsub Hlrho Hroots HQL rho (incl_refl rho))
    as [rs3 [js3 [K [Hch3 Hin3]]]].
  exists j2, (map castZ (firstn 6 witFz)), dt2, rs3, js3, K.
  repeat split; try assumption; try lia.
  - pose proof (RootChain_append CQ rho (r1 :: r2 :: nil)
                  (6%nat :: j2 :: nil) L rs3 js3 K Hch2 Hch3) as Happ.
    cbn [app] in Happ.
    exact Happ.
  - intros x Hx.
    right. right.
    apply Hin3. exact Hx.
Qed.

(** the fifteen-term tail of the resolvent quotient as a CQ relation *)
Lemma witS15_tail_relation : forall (r : C),
  cpeval (map castZ witS15z) r = C0 ->
  length (map castZ (firstn 15 witS15z)) = 15%nat /\
  Forall CQ (map castZ (firstn 15 witS15z)) /\
  (cpeval (map castZ (firstn 15 witS15z)) r + Cpow r 15)%C = C0.
Proof.
  intros r Hroot.
  refine (conj _ (conj _ _)).
  - rewrite length_map, firstn_length, witS15_len. reflexivity.
  - apply Forall_CQ_castZ.
  - assert (HFz_split : witS15z = firstn 15 witS15z ++ (1 :: nil)%Z).
    { vm_compute. reflexivity. }
    rewrite <- Hroot.
    rewrite HFz_split at 2.
    rewrite map_app, cpeval_app.
    rewrite length_map, firstn_length, witS15_len.
    cbn [map cpeval Nat.min].
    assert (Hc1 : castZ 1%Z = C1) by reflexivity.
    rewrite Hc1. ring.
Qed.

(** THE SECOND DEGREE IS FIVE. *)
Lemma witness_j2_five :
  forall (rho : list C) (r1 r2 : C) (j2 : nat) (dt1 dt2 : list C),
  (forall r, In r rho -> cpeval (map castZ witFz) r = C0) ->
  In r1 rho -> In r2 rho -> r1 <> r2 ->
  length dt1 = 6%nat -> Forall CQ dt1 ->
  (cpeval dt1 r1 + Cpow r1 6)%C = C0 -> Cindep_pows CQ r1 6 ->
  (1 <= j2)%nat -> (j2 <= 6)%nat ->
  length dt2 = j2 -> Forall (CPolyF CQ 6 r1) dt2 ->
  (cpeval dt2 r2 + Cpow r2 j2)%C = C0 ->
  Cindep_pows (CPolyF CQ 6 r1) r2 j2 ->
  j2 = 5%nat.
Proof.
  intros rho r1 r2 j2 dt1 dt2 Hroots Hr1 Hr2 Hne
         Hl1 Hf1 Hrel1 Hi1 Hj21 Hj26 Hl2 Hf2 Hrel2 Hi2.
  set (K1 := CPolyF CQ 6 r1).
  set (L := CPolyF K1 j2 r2).
  set (t2 := ((r1 - r2) * (r1 - r2))%C).
  assert (Ht2root : cpeval (map castZ witS15z) t2 = C0)
    by (apply theta_sq_roots_S15;
        [apply Hroots; exact Hr1 | apply Hroots; exact Hr2 | exact Hne]).
  (* pin the resolvent degree to fifteen *)
  destruct (cpowers_max_prefix CQ t2 15 CQ_subfield ltac:(lia))
    as [jt [Hjtb [Hindt Hcaset]]].
  destruct (witS15_tail_relation t2 Ht2root) as [HlS [HfS HrelS]].
  assert (Hrelt : exists dt, length dt = jt /\ Forall CQ dt /\
    (cpeval dt t2 + Cpow t2 jt)%C = C0).
  { destruct Hcaset as [-> | Hex]; [| exact Hex].
    exists (map castZ (firstn 15 witS15z)).
    repeat split; assumption. }
  destruct Hrelt as [dtt [Hldtt [Hfdtt Hreldtt]]].
  assert (Hjt15 : jt = 15%nat).
  { apply (relation_degree_pinned witS15z 15 t2 jt dtt witS15_len witS15_mon
             Ht2root); try assumption; try lia.
    intros d Hd1 Hd14.
    apply witS15_excl; [exact Hd1 | lia]. }
  subst jt.
  rewrite Hjt15 in Hreldtt, Hindt.
  set (KP := CPolyF CQ 15 t2).
  (* fields and inclusions *)
  assert (HK1sub : is_Csubfield K1)
    by (apply (CPolyF_Csubfield CQ r1 6 dt1 CQ_subfield ltac:(lia) Hl1 Hf1
                 Hrel1)).
  assert (HLsub : is_Csubfield L)
    by (apply (CPolyF_Csubfield K1 r2 j2 dt2 HK1sub Hj21 Hl2 Hf2 Hrel2)).
  assert (HKPsub : is_Csubfield KP)
    by (apply (CPolyF_Csubfield CQ t2 15 dtt CQ_subfield ltac:(lia) Hjt15
                 Hfdtt Hreldtt)).
  assert (HQK1 : forall x, CQ x -> K1 x)
    by (apply (CPolyF_contains CQ r1 6 dt1 CQ_subfield ltac:(lia) Hl1 Hf1
                 Hrel1)).
  assert (HK1L : forall x, K1 x -> L x)
    by (apply (CPolyF_contains K1 r2 j2 dt2 HK1sub Hj21 Hl2 Hf2 Hrel2)).
  assert (HQKP : forall x, CQ x -> KP x)
    by (apply (CPolyF_contains CQ t2 15 dtt CQ_subfield ltac:(lia) Hjt15
                 Hfdtt Hreldtt)).
  assert (Hr1L : L r1).
  { apply HK1L.
    apply (CPolyF_r_mem CQ r1 6 dt1 CQ_subfield ltac:(lia) Hl1 Hf1 Hrel1). }
  assert (Hr2L : L r2)
    by (apply (CPolyF_r_mem K1 r2 j2 dt2 HK1sub Hj21 Hl2 Hf2 Hrel2)).
  assert (Ht2L : L t2).
  { unfold t2.
    apply Csubfield_mul; [exact HLsub | |];
      apply Csubfield_sub; assumption. }
  assert (HKPL : forall x, KP x -> L x).
  { intros x [cs [Hlcs [Hfcs Hxe]]].
    rewrite Hxe.
    apply cpeval_in_K; [exact HLsub | | exact Ht2L].
    apply Forall_forall. intros z Hz.
    apply HK1L. apply HQK1.
    exact (proj1 (Forall_forall CQ cs) Hfcs z Hz). }
  (* the three power bases *)
  assert (Hb1 : Cbasis CQ (CQpows r1 6) K1)
    by (apply (CPolyF_powers_basis CQ r1 6 dt1 CQ_subfield ltac:(lia) Hl1 Hf1
                 Hrel1 Hi1)).
  assert (Hb2 : Cbasis K1 (CQpows r2 j2) L)
    by (apply (CPolyF_powers_basis K1 r2 j2 dt2 HK1sub Hj21 Hl2 Hf2 Hrel2
                 Hi2)).
  assert (HbP : Cbasis CQ (CQpows t2 15) KP)
    by (apply (CPolyF_powers_basis CQ t2 15 dtt CQ_subfield ltac:(lia) Hjt15
                 Hfdtt Hreldtt Hindt)).
  (* the divisibility *)
  pose proof (dim_divide_15 K1 L KP r1 r2 t2 j2
                HK1sub HLsub HKPsub HQK1 HK1L HQKP HKPL Hb1 Hb2 HbP) as Hdiv.
  destruct Hdiv as [m Hm].
  lia.
Qed.


(* the roots of the witness sextic -- four bracketed reals, a negative-discriminant conjugate pair, and conjugation as their transposition. *)

Definition witD : Z := 16777216%Z.

(** the scaled seven-coefficient bridge *)
Lemma peval7_scale : forall (c0 c1 c2 c3 c4 c5 c6 dz a : Z),
  IZR dz <> 0 ->
  (pevalR (map IZR (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: nil))
     (IZR a / IZR dz) * (IZR dz * (IZR dz * (IZR dz * (IZR dz * (IZR dz * IZR dz))))))%R
  = IZR (c0 * (dz * (dz * (dz * (dz * (dz * dz)))))
         + a * (c1 * (dz * (dz * (dz * (dz * dz))))
                + a * (c2 * (dz * (dz * (dz * dz)))
                       + a * (c3 * (dz * (dz * dz))
                              + a * (c4 * (dz * dz)
                                     + a * (c5 * dz + a * c6))))))%Z.
Proof.
  intros c0 c1 c2 c3 c4 c5 c6 dz a Hdz.
  cbn [map pevalR].
  repeat first [rewrite plus_IZR | rewrite mult_IZR].
  field.
  exact Hdz.
Qed.

(** sign transfer through the scaling *)
Lemma scaled_sign_pos : forall (c0 c1 c2 c3 c4 c5 c6 dz a : Z),
  (0 < dz)%Z ->
  (0 <? c0 * (dz * (dz * (dz * (dz * (dz * dz)))))
        + a * (c1 * (dz * (dz * (dz * (dz * dz))))
               + a * (c2 * (dz * (dz * (dz * dz)))
                      + a * (c3 * (dz * (dz * dz))
                             + a * (c4 * (dz * dz)
                                    + a * (c5 * dz + a * c6))))))%Z = true ->
  0 < pevalR (map IZR (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: nil))
        (IZR a / IZR dz).
Proof.
  intros c0 c1 c2 c3 c4 c5 c6 dz a Hdz Hlt.
  apply Z.ltb_lt in Hlt.
  assert (HdzR : 0 < IZR dz) by (exact (IZR_lt 0 dz Hdz)).
  assert (HdzR6 : 0 < IZR dz * (IZR dz * (IZR dz * (IZR dz * (IZR dz * IZR dz)))))
    by (repeat apply Rmult_lt_0_compat; exact HdzR).
  assert (Hval : 0 < IZR (c0 * (dz * (dz * (dz * (dz * (dz * dz)))))
         + a * (c1 * (dz * (dz * (dz * (dz * dz))))
                + a * (c2 * (dz * (dz * (dz * dz)))
                       + a * (c3 * (dz * (dz * dz))
                              + a * (c4 * (dz * dz)
                                     + a * (c5 * dz + a * c6))))))%Z)
    by (exact (IZR_lt _ _ Hlt)).
  rewrite <- (peval7_scale c0 c1 c2 c3 c4 c5 c6 dz a ltac:(lra)) in Hval.
  nra.
Qed.

Lemma scaled_sign_neg : forall (c0 c1 c2 c3 c4 c5 c6 dz a : Z),
  (0 < dz)%Z ->
  (c0 * (dz * (dz * (dz * (dz * (dz * dz)))))
   + a * (c1 * (dz * (dz * (dz * (dz * dz))))
          + a * (c2 * (dz * (dz * (dz * dz)))
                 + a * (c3 * (dz * (dz * dz))
                        + a * (c4 * (dz * dz)
                               + a * (c5 * dz + a * c6))))) <? 0)%Z = true ->
  pevalR (map IZR (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: nil))
    (IZR a / IZR dz) < 0.
Proof.
  intros c0 c1 c2 c3 c4 c5 c6 dz a Hdz Hlt.
  apply Z.ltb_lt in Hlt.
  assert (HdzR : 0 < IZR dz) by (exact (IZR_lt 0 dz Hdz)).
  assert (HdzR6 : 0 < IZR dz * (IZR dz * (IZR dz * (IZR dz * (IZR dz * IZR dz)))))
    by (repeat apply Rmult_lt_0_compat; exact HdzR).
  assert (Hval : IZR (c0 * (dz * (dz * (dz * (dz * (dz * dz)))))
         + a * (c1 * (dz * (dz * (dz * (dz * dz))))
                + a * (c2 * (dz * (dz * (dz * dz)))
                       + a * (c3 * (dz * (dz * dz))
                              + a * (c4 * (dz * dz)
                                     + a * (c5 * dz + a * c6))))))%Z < 0)
    by (exact (IZR_lt _ _ Hlt)).
  rewrite <- (peval7_scale c0 c1 c2 c3 c4 c5 c6 dz a ltac:(lra)) in Hval.
  nra.
Qed.

(** the intermediate value theorem on a dyadic bracket, both orientations *)
Lemma bracket_root_asc : forall (l : list R) (x y : R),
  x < y -> pevalR l x < 0 -> 0 < pevalR l y ->
  exists r, x <= r <= y /\ pevalR l r = 0.
Proof.
  intros l x y Hxy Hneg Hpos.
  set (g := fun t => peval_lf (rev l) t).
  assert (Hgx : g x < 0) by (unfold g; rewrite <- pevalR_rev; exact Hneg).
  assert (Hgy : 0 < g y) by (unfold g; rewrite <- pevalR_rev; exact Hpos).
  assert (Hcont : continuity g) by (unfold g; apply peval_lf_continuity).
  destruct (IVT g x y Hcont Hxy Hgx Hgy) as [r [Hr Hgr]].
  exists r.
  split; [exact Hr |].
  rewrite pevalR_rev. exact Hgr.
Qed.

Lemma bracket_root_desc : forall (l : list R) (x y : R),
  x < y -> 0 < pevalR l x -> pevalR l y < 0 ->
  exists r, x <= r <= y /\ pevalR l r = 0.
Proof.
  intros l x y Hxy Hpos Hneg.
  set (g := fun t => - peval_lf (rev l) t).
  assert (Hgx : g x < 0)
    by (unfold g; rewrite <- pevalR_rev; lra).
  assert (Hgy : 0 < g y)
    by (unfold g; rewrite <- pevalR_rev; lra).
  assert (Hcont : continuity g).
  { unfold g.
    apply continuity_opp.
    apply peval_lf_continuity. }
  destruct (IVT g x y Hcont Hxy Hgx Hgy) as [r [Hr Hgr]].
  exists r.
  split; [exact Hr |].
  rewrite pevalR_rev.
  unfold g in Hgr. lra.
Qed.

(** the four bracketed real roots *)
Definition wbr : list (Z * Z) :=
  ((-633045697807735)%Z, (-633045697807732)%Z)
  :: ((-84410879089805)%Z, (-84410879089802)%Z)
  :: (104252567179735%Z, 104252567179738%Z)
  :: (428820087806213%Z, 428820087806216%Z)
  :: nil.

Definition witFR : list R := map IZR witFz.

Lemma witFR_expose :
  witFR = map IZR
    (2795309191751463646995099641203274900592260
     :: (-250439519908253635661434543391737596)
     :: (-71579381792837368681196275607)
     :: 12528974921812564304936
     :: (-1034347114106394)
     :: 347428 :: 1 :: nil)%Z.
Proof. reflexivity. Qed.

Lemma witD_pos : (0 < witD)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma witD_R_pos : 0 < IZR witD.
Proof. apply IZR_lt. exact witD_pos. Qed.

Lemma dy_lt : forall a b : Z, (a < b)%Z ->
  IZR a / IZR witD < IZR b / IZR witD.
Proof.
  intros a b Hab.
  unfold Rdiv.
  apply Rmult_lt_compat_r.
  - apply Rinv_0_lt_compat. exact witD_R_pos.
  - apply IZR_lt. exact Hab.
Qed.

(** each bracketed root, with its interval and the complex root form *)
Lemma wroot_exists_desc : forall (a b : Z), (a < b)%Z ->
  0 < pevalR witFR (IZR a / IZR witD) ->
  pevalR witFR (IZR b / IZR witD) < 0 ->
  exists r, IZR a / IZR witD <= r <= IZR b / IZR witD /\
    cpeval (map castZ witFz) (RtoC r) = C0.
Proof.
  intros a b Hab Hpos Hneg.
  destruct (bracket_root_desc witFR (IZR a / IZR witD) (IZR b / IZR witD)
              (dy_lt a b Hab) Hpos Hneg) as [r [Hr He]].
  exists r.
  split; [exact Hr |].
  rewrite castZ_as_RtoC, cpeval_map_RtoC_global, CevalR_RtoC.
  unfold witFR in He.
  rewrite He.
  reflexivity.
Qed.

Lemma wroot_exists_asc : forall (a b : Z), (a < b)%Z ->
  pevalR witFR (IZR a / IZR witD) < 0 ->
  0 < pevalR witFR (IZR b / IZR witD) ->
  exists r, IZR a / IZR witD <= r <= IZR b / IZR witD /\
    cpeval (map castZ witFz) (RtoC r) = C0.
Proof.
  intros a b Hab Hneg Hpos.
  destruct (bracket_root_asc witFR (IZR a / IZR witD) (IZR b / IZR witD)
              (dy_lt a b Hab) Hneg Hpos) as [r [Hr He]].
  exists r.
  split; [exact Hr |].
  rewrite castZ_as_RtoC, cpeval_map_RtoC_global, CevalR_RtoC.
  unfold witFR in He.
  rewrite He.
  reflexivity.
Qed.

(** sign facts at the eight dyadic endpoints *)
Lemma wsign_a1 : 0 < pevalR witFR (IZR (-633045697807735) / IZR witD).
Proof.
  rewrite witFR_expose.
  apply scaled_sign_pos; [exact witD_pos | vm_compute; reflexivity].
Qed.

Lemma wsign_b1 : pevalR witFR (IZR (-633045697807732) / IZR witD) < 0.
Proof.
  rewrite witFR_expose.
  apply scaled_sign_neg; [exact witD_pos | vm_compute; reflexivity].
Qed.

Lemma wsign_a2 : pevalR witFR (IZR (-84410879089805) / IZR witD) < 0.
Proof.
  rewrite witFR_expose.
  apply scaled_sign_neg; [exact witD_pos | vm_compute; reflexivity].
Qed.

Lemma wsign_b2 : 0 < pevalR witFR (IZR (-84410879089802) / IZR witD).
Proof.
  rewrite witFR_expose.
  apply scaled_sign_pos; [exact witD_pos | vm_compute; reflexivity].
Qed.

Lemma wsign_a3 : 0 < pevalR witFR (IZR 104252567179735 / IZR witD).
Proof.
  rewrite witFR_expose.
  apply scaled_sign_pos; [exact witD_pos | vm_compute; reflexivity].
Qed.

Lemma wsign_b3 : pevalR witFR (IZR 104252567179738 / IZR witD) < 0.
Proof.
  rewrite witFR_expose.
  apply scaled_sign_neg; [exact witD_pos | vm_compute; reflexivity].
Qed.

Lemma wsign_a4 : pevalR witFR (IZR 428820087806213 / IZR witD) < 0.
Proof.
  rewrite witFR_expose.
  apply scaled_sign_neg; [exact witD_pos | vm_compute; reflexivity].
Qed.

Lemma wsign_b4 : 0 < pevalR witFR (IZR 428820087806216 / IZR witD).
Proof.
  rewrite witFR_expose.
  apply scaled_sign_pos; [exact witD_pos | vm_compute; reflexivity].
Qed.

(** THE FOUR REAL ROOTS with brackets. *)
Lemma four_real_roots :
  exists r1 r2 r3 r4 : R,
    (IZR (-633045697807735) / IZR witD <= r1 <= IZR (-633045697807732) / IZR witD) /\
    (IZR (-84410879089805) / IZR witD <= r2 <= IZR (-84410879089802) / IZR witD) /\
    (IZR 104252567179735 / IZR witD <= r3 <= IZR 104252567179738 / IZR witD) /\
    (IZR 428820087806213 / IZR witD <= r4 <= IZR 428820087806216 / IZR witD) /\
    cpeval (map castZ witFz) (RtoC r1) = C0 /\
    cpeval (map castZ witFz) (RtoC r2) = C0 /\
    cpeval (map castZ witFz) (RtoC r3) = C0 /\
    cpeval (map castZ witFz) (RtoC r4) = C0 /\
    r1 < r2 /\ r2 < r3 /\ r3 < r4.
Proof.
  destruct (wroot_exists_desc (-633045697807735) (-633045697807732)
              ltac:(lia) wsign_a1 wsign_b1) as [r1 [Hbr1 He1]].
  destruct (wroot_exists_asc (-84410879089805) (-84410879089802)
              ltac:(lia) wsign_a2 wsign_b2) as [r2 [Hbr2 He2]].
  destruct (wroot_exists_desc 104252567179735 104252567179738
              ltac:(lia) wsign_a3 wsign_b3) as [r3 [Hbr3 He3]].
  destruct (wroot_exists_asc 428820087806213 428820087806216
              ltac:(lia) wsign_a4 wsign_b4) as [r4 [Hbr4 He4]].
  exists r1, r2, r3, r4.
  assert (Hsep1 : IZR (-633045697807732) / IZR witD
                  < IZR (-84410879089805) / IZR witD)
    by (apply dy_lt; lia).
  assert (Hsep2 : IZR (-84410879089802) / IZR witD
                  < IZR 104252567179735 / IZR witD)
    by (apply dy_lt; lia).
  assert (Hsep3 : IZR 104252567179738 / IZR witD
                  < IZR 428820087806213 / IZR witD)
    by (apply dy_lt; lia).
  repeat split; try tauto; try lra.
Qed.

(* The real-coefficient subfield, the quadratic cofactor, and its negative discriminant. *)

Definition CR (z : C) : Prop := snd z = 0%R.

Lemma CR_subfield : is_Csubfield CR.
Proof.
  repeat split.
  - intros x y Hx Hy.
    unfold CR, Cadd in *. cbn. rewrite Hx, Hy. ring.
  - intros x y Hx Hy.
    unfold CR, Csub, Cadd, Copp in *. cbn. rewrite Hx, Hy. ring.
  - intros x y Hx Hy.
    unfold CR, Cmul in *. cbn. rewrite Hx, Hy. ring.
  - intros x Hx Hne.
    unfold CR, Cinv in *. cbn.
    rewrite Hx.
    assert (Hf : fst x <> 0%R).
    { intro E. apply Hne.
      unfold C0.
      rewrite (surjective_pairing x), E, Hx. reflexivity. }
    field. nra.
Qed.

Lemma CR_RtoC : forall x : R, CR (RtoC x).
Proof. intro x. reflexivity. Qed.

Lemma CR_form : forall z, CR z -> z = RtoC (fst z).
Proof.
  intros z Hz.
  unfold RtoC.
  rewrite (surjective_pairing z), Hz.
  reflexivity.
Qed.

Lemma CR_castZ : forall n : Z, CR (castZ n).
Proof. intro n. reflexivity. Qed.

(** peeling one real root off a monic real-coefficient list *)
Lemma peel_root : forall (A : list C) (r : R),
  (2 <= length A)%nat -> hd C0 A = C1 -> Forall CR A ->
  cpeval_lf A (RtoC r) = C0 ->
  exists A', length A' = (length A - 1)%nat /\ hd C0 A' = C1 /\
    Forall CR A' /\
    forall z, cpeval_lf A z = (cpeval_lf A' z * (z - RtoC r))%C.
Proof.
  intros A r Hlen Hhd Hfa Hroot.
  set (A' := fst (cpdiv_lf (length A) A (Copp (RtoC r) :: nil))).
  destruct (cpdiv_head_monic A (RtoC r) Hhd Hlen) as [Hhd' Hlen'].
  exists A'.
  repeat split.
  - exact Hlen'.
  - exact Hhd'.
  - unfold A'.
    apply (proj1 (cpdiv_lf_Forall CR (length A) A (Copp (RtoC r) :: nil)
                    CR_subfield Hfa
                    ltac:(constructor;
                          [unfold CR, Copp, RtoC; cbn; ring | constructor]))).
  - intro z.
    exact (cp_root_factor A (RtoC r) Hroot z).
Qed.

(** complex conjugation *)
Definition Cconj (z : C) : C := (fst z, (- snd z)%R).

Lemma Cconj_RtoC : forall x : R, Cconj (RtoC x) = RtoC x.
Proof.
  intro x. unfold Cconj, RtoC. apply injective_projections; cbn; ring.
Qed.

Lemma Cconj_CR : forall z, CR z -> Cconj z = z.
Proof.
  intros z Hz.
  unfold Cconj.
  apply injective_projections; cbn.
  - reflexivity.
  - unfold CR in Hz. rewrite Hz. ring.
Qed.

Lemma Cconj_add : forall x y, Cconj (x + y)%C = (Cconj x + Cconj y)%C.
Proof.
  intros x y. unfold Cconj, Cadd. apply injective_projections; cbn; ring.
Qed.

Lemma Cconj_mul : forall x y, Cconj (x * y)%C = (Cconj x * Cconj y)%C.
Proof.
  intros x y. unfold Cconj, Cmul. apply injective_projections; cbn; ring.
Qed.

Lemma Cconj_invol : forall z, Cconj (Cconj z) = z.
Proof.
  intro z. unfold Cconj.
  rewrite (surjective_pairing z) at 3.
  apply injective_projections; cbn; ring.
Qed.

Lemma Cconj_eval : forall (cs : list C) (z : C),
  Forall CR cs ->
  cpeval cs (Cconj z) = Cconj (cpeval cs z).
Proof.
  induction cs as [|c cs IH]; intros z Hf; cbn [cpeval].
  - unfold Cconj, C0. apply injective_projections; cbn; ring.
  - rewrite Cconj_add, Cconj_mul.
    rewrite (Cconj_CR c (Forall_inv Hf)).
    rewrite (IH z (Forall_inv_tail Hf)).
    reflexivity.
Qed.

Lemma Cconj_neq_of_im : forall z, snd z <> 0%R -> Cconj z <> z.
Proof.
  intros z Hz E.
  apply Hz.
  apply (f_equal snd) in E.
  unfold Cconj in E. cbn in E. lra.
Qed.

Lemma RtoC_neq : forall x y : R, x <> y -> RtoC x <> RtoC y.
Proof.
  intros x y Hxy E.
  apply Hxy.
  exact (f_equal fst E).
Qed.

Lemma nonreal_neq_real : forall (z : C) (x : R), snd z <> 0%R -> z <> RtoC x.
Proof.
  intros z x Hz E.
  apply Hz.
  rewrite E. reflexivity.
Qed.

(** THE QUARTIC-COFACTOR EXTRACTION: peeling four distinct real roots off the witness sextic leaves a monic real quadratic pinned by its two Vieta equations. *)
Lemma witF_quartic_cofactor : forall r1 r2 r3 r4 : R,
  cpeval (map castZ witFz) (RtoC r1) = C0 ->
  cpeval (map castZ witFz) (RtoC r2) = C0 ->
  cpeval (map castZ witFz) (RtoC r3) = C0 ->
  cpeval (map castZ witFz) (RtoC r4) = C0 ->
  r1 < r2 -> r2 < r3 -> r3 < r4 ->
  exists pr qr : R,
    (forall z, cpeval (map castZ witFz) z
       = (cpeval_lf (C1 :: RtoC pr :: RtoC qr :: nil) z
          * ((z - RtoC r1) * ((z - RtoC r2) * ((z - RtoC r3) * (z - RtoC r4)))))%C) /\
    pr = (IZR 347428 + (r1 + r2 + r3 + r4))%R /\
    (qr * (r1 * r2 * r3 * r4))%R = IZR 2795309191751463646995099641203274900592260.
Proof.
  intros r1 r2 r3 r4 He1 He2 He3 He4 H12 H23 H34.
  set (FClf := rev (map castZ witFz)).
  assert (HevF : forall z, cpeval_lf FClf z = cpeval (map castZ witFz) z).
  { intro z. unfold FClf.
    rewrite cpeval_lf_rev_c, rev_involutive. reflexivity. }
  assert (HlF : length FClf = 7%nat) by reflexivity.
  assert (HhdF : hd C0 FClf = C1) by reflexivity.
  assert (HfF : Forall CR FClf).
  { unfold FClf. apply Forall_rev.
    apply Forall_map_intro. intros n _. apply CR_castZ. }
  (* peel the four real roots *)
  destruct (peel_root FClf r1 ltac:(rewrite HlF; lia) HhdF HfF
              ltac:(rewrite HevF; exact He1))
    as [A1 [HlA1 [HhA1 [HfA1 Hid1]]]].
  rewrite HlF in HlA1.
  assert (HA1r2 : cpeval_lf A1 (RtoC r2) = C0).
  { pose proof (Hid1 (RtoC r2)) as H.
    rewrite HevF, He2 in H.
    destruct (Cmul_integral _ _ (eq_sym H)) as [E | E]; [exact E | exfalso].
    assert (Hne : (RtoC r2 - RtoC r1)%C <> C0).
    { intro E'.
      apply (RtoC_neq r2 r1 ltac:(lra)).
      transitivity ((RtoC r2 - RtoC r1) + RtoC r1)%C; [ring | rewrite E'; ring]. }
    exact (Hne E). }
  destruct (peel_root A1 r2 ltac:(lia) HhA1 HfA1 HA1r2)
    as [A2 [HlA2 [HhA2 [HfA2 Hid2]]]].
  rewrite HlA1 in HlA2.
  assert (HA2r3 : cpeval_lf A2 (RtoC r3) = C0).
  { pose proof (Hid1 (RtoC r3)) as H.
    rewrite HevF, He3 in H.
    rewrite (Hid2 (RtoC r3)) in H.
    assert (Hne1 : (RtoC r3 - RtoC r1)%C <> C0).
    { intro E'.
      apply (RtoC_neq r3 r1 ltac:(lra)).
      transitivity ((RtoC r3 - RtoC r1) + RtoC r1)%C; [ring | rewrite E'; ring]. }
    assert (Hne2 : (RtoC r3 - RtoC r2)%C <> C0).
    { intro E'.
      apply (RtoC_neq r3 r2 ltac:(lra)).
      transitivity ((RtoC r3 - RtoC r2) + RtoC r2)%C; [ring | rewrite E'; ring]. }
    destruct (Cmul_integral _ _ (eq_sym H)) as [E | E].
    - destruct (Cmul_integral _ _ E) as [E2 | E2];
        [exact E2 | exfalso; exact (Hne2 E2)].
    - exfalso. exact (Hne1 E). }
  destruct (peel_root A2 r3 ltac:(lia) HhA2 HfA2 HA2r3)
    as [A3 [HlA3 [HhA3 [HfA3 Hid3]]]].
  rewrite HlA2 in HlA3.
  assert (HA3r4 : cpeval_lf A3 (RtoC r4) = C0).
  { pose proof (Hid1 (RtoC r4)) as H.
    rewrite HevF, He4 in H.
    rewrite (Hid2 (RtoC r4)), (Hid3 (RtoC r4)) in H.
    assert (Hne1 : (RtoC r4 - RtoC r1)%C <> C0).
    { intro E'.
      apply (RtoC_neq r4 r1 ltac:(lra)).
      transitivity ((RtoC r4 - RtoC r1) + RtoC r1)%C; [ring | rewrite E'; ring]. }
    assert (Hne2 : (RtoC r4 - RtoC r2)%C <> C0).
    { intro E'.
      apply (RtoC_neq r4 r2 ltac:(lra)).
      transitivity ((RtoC r4 - RtoC r2) + RtoC r2)%C; [ring | rewrite E'; ring]. }
    assert (Hne3 : (RtoC r4 - RtoC r3)%C <> C0).
    { intro E'.
      apply (RtoC_neq r4 r3 ltac:(lra)).
      transitivity ((RtoC r4 - RtoC r3) + RtoC r3)%C; [ring | rewrite E'; ring]. }
    destruct (Cmul_integral _ _ (eq_sym H)) as [E | E];
      [| exfalso; exact (Hne1 E)].
    destruct (Cmul_integral _ _ E) as [E2 | E2];
      [| exfalso; exact (Hne2 E2)].
    destruct (Cmul_integral _ _ E2) as [E3 | E3];
      [exact E3 | exfalso; exact (Hne3 E3)]. }
  destruct (peel_root A3 r4 ltac:(lia) HhA3 HfA3 HA3r4)
    as [A4 [HlA4 [HhA4 [HfA4 Hid4]]]].
  rewrite HlA3 in HlA4.
  (* the quadratic cofactor *)
  destruct A4 as [|h [|pc [|qc [|x rest]]]];
    try (cbn [length] in HlA4; lia).
  cbn [hd] in HhA4. subst h.
  assert (Hpr : pc = RtoC (fst pc))
    by (apply CR_form; exact (Forall_inv (Forall_inv_tail HfA4))).
  assert (Hqr : qc = RtoC (fst qc))
    by (apply CR_form;
        exact (Forall_inv (Forall_inv_tail (Forall_inv_tail HfA4)))).
  (* the master factorization through the quadratic *)
  assert (Hmaster : forall z,
    cpeval (map castZ witFz) z
    = (cpeval_lf (C1 :: pc :: qc :: nil) z
       * ((z - RtoC r1) * ((z - RtoC r2) * ((z - RtoC r3) * (z - RtoC r4)))))%C).
  { intro z.
    rewrite <- HevF.
    rewrite (Hid1 z), (Hid2 z), (Hid3 z), (Hid4 z).
    ring. }
  (* the coefficient equations through the explicit quartic product *)
  set (r1C := RtoC r1). set (r2C := RtoC r2).
  set (r3C := RtoC r3). set (r4C := RtoC r4).
  set (P12 := cpmul_lf (C1 :: Copp r1C :: nil) (C1 :: Copp r2C :: nil)).
  set (P34 := cpmul_lf (C1 :: Copp r3C :: nil) (C1 :: Copp r4C :: nil)).
  assert (HP12 : P12 = C1 :: Copp (r1C + r2C) :: (r1C * r2C)%C :: nil).
  { unfold P12, cpmul_lf.
    cbn [rev app cpmul cpadd cpscale map length].
    apply f_equal2; [ring |].
    apply f_equal2; [ring |].
    apply f_equal2; [ring | reflexivity]. }
  assert (HP34 : P34 = C1 :: Copp (r3C + r4C) :: (r3C * r4C)%C :: nil).
  { unfold P34, cpmul_lf.
    cbn [rev app cpmul cpadd cpscale map length].
    apply f_equal2; [ring |].
    apply f_equal2; [ring |].
    apply f_equal2; [ring | reflexivity]. }
  set (S1 := (r1C + r2C + r3C + r4C)%C).
  set (S4 := (r1C * r2C * r3C * r4C)%C).
  set (P4q := cpmul_lf P12 P34).
  assert (HP4form : exists g2 g3,
    P4q = C1 :: Copp S1 :: g2 :: g3 :: S4 :: nil).
  { unfold P4q.
    rewrite HP12, HP34.
    unfold cpmul_lf.
    cbn [rev app cpmul cpadd cpscale map length].
    eexists _, _.
    apply f_equal2; [unfold S1, S4; ring |].
    apply f_equal2; [unfold S1, S4; ring |].
    apply f_equal2; [reflexivity |].
    apply f_equal2; [reflexivity |].
    apply f_equal2; [unfold S1, S4; ring | reflexivity]. }
  destruct HP4form as [g2 [g3 HP4form]].
  assert (HevP4 : forall z, cpeval_lf P4q z
    = ((z - r1C) * ((z - r2C) * ((z - r3C) * (z - r4C))))%C).
  { intro z.
    unfold P4q.
    rewrite cpmul_lf_eval.
    unfold P12, P34.
    rewrite !cpmul_lf_eval.
    assert (Hlin : forall w : C, cpeval_lf (C1 :: Copp w :: nil) z = (z - w)%C).
    { intro w. cbn [cpeval_lf length]. cbn. ring. }
    rewrite !Hlin. ring. }
  assert (Hlist : FClf = cpmul_lf (C1 :: pc :: qc :: nil) P4q).
  { apply lf_eq_of_eval.
    - rewrite HhdF. exact C1_neq_C0.
    - rewrite cpmul_lf_head;
        [| cbn [length]; lia
         | rewrite HP4form; cbn [length]; lia].
      cbn [hd].
      rewrite HP4form. cbn [hd].
      intro E.
      apply C1_neq_C0.
      transitivity ((C1 * C1)%C); [ring | exact E].
    - intro z.
      rewrite cpmul_lf_eval.
      rewrite HevF, (Hmaster z), (HevP4 z).
      reflexivity. }
  (* expose both sides as literal lists and extract the two equations *)
  assert (HFexpose : FClf
    = castZ 1 :: castZ 347428 :: castZ (-1034347114106394)
      :: castZ 12528974921812564304936
      :: castZ (-71579381792837368681196275607)
      :: castZ (-250439519908253635661434543391737596)
      :: castZ 2795309191751463646995099641203274900592260 :: nil).
  { reflexivity. }
  rewrite HP4form in Hlist.
  unfold cpmul_lf in Hlist.
  cbn [rev app cpmul cpadd cpscale map length] in Hlist.
  rewrite HFexpose in Hlist.
  pose proof (f_equal (fun l => nth 1 l C0) Hlist) as Ep.
  pose proof (f_equal (fun l => nth 6 l C0) Hlist) as Eq.
  cbn [nth] in Ep, Eq.
  assert (Hp_val : pc = (castZ 347428 + S1)%C).
  { transitivity ((pc * C1 + C1 * - S1) + S1)%C; [ring |].
    rewrite <- Ep. ring. }
  assert (Hq_val : (qc * S4)%C
                   = castZ 2795309191751463646995099641203274900592260).
  { transitivity ((qc * S4 + C0)%C); [ring |].
    rewrite <- Eq. reflexivity. }
  assert (HS1R : S1 = RtoC (r1 + r2 + r3 + r4)%R).
  { unfold S1, r1C, r2C, r3C, r4C.
    rewrite !RtoC_add. reflexivity. }
  assert (HS4R : S4 = RtoC (r1 * r2 * r3 * r4)%R).
  { unfold S4, r1C, r2C, r3C, r4C.
    rewrite !RtoC_mul. reflexivity. }
  assert (Hpr_val : fst pc = (IZR 347428 + (r1 + r2 + r3 + r4))%R).
  { apply RtoC_inj.
    rewrite <- Hpr.
    rewrite Hp_val, HS1R.
    unfold castZ.
    rewrite (RtoC_add (IZR 347428) (r1 + r2 + r3 + r4)%R). reflexivity. }
  assert (Hqr_rel : (fst qc * (r1 * r2 * r3 * r4))%R
                    = IZR 2795309191751463646995099641203274900592260).
  { apply RtoC_inj.
    rewrite RtoC_mul.
    rewrite <- Hqr, <- HS4R.
    exact Hq_val. }
  exists (fst pc), (fst qc).
  refine (conj _ (conj Hpr_val Hqr_rel)).
  intro z.
  rewrite (Hmaster z), <- Hpr, <- Hqr.
  reflexivity.
Qed.

(** THE DISCRIMINANT BOUND: on the dyadic brackets the quartic cofactor's discriminant is negative, by the integer keystone comparison. *)
Lemma witF_disc_neg : forall r1 r2 r3 r4 pr qr : R,
  IZR (-633045697807735) / IZR witD <= r1 <= IZR (-633045697807732) / IZR witD ->
  IZR (-84410879089805) / IZR witD <= r2 <= IZR (-84410879089802) / IZR witD ->
  IZR 104252567179735 / IZR witD <= r3 <= IZR 104252567179738 / IZR witD ->
  IZR 428820087806213 / IZR witD <= r4 <= IZR 428820087806216 / IZR witD ->
  pr = (IZR 347428 + (r1 + r2 + r3 + r4))%R ->
  (qr * (r1 * r2 * r3 * r4))%R = IZR 2795309191751463646995099641203274900592260 ->
  (pr * pr < 4 * qr)%R.
Proof.
  intros r1 r2 r3 r4 pr qr Hbr1 Hbr2 Hbr3 Hbr4 Hpr_val Hqr_rel.
  assert (Hinv : 0 < / IZR witD)
    by (apply Rinv_0_lt_compat; exact witD_R_pos).
  assert (HDpos : 0 < IZR witD) by exact witD_R_pos.
  unfold Rdiv in Hbr1, Hbr2, Hbr3, Hbr4.
  assert (Ha1 : IZR (-633045697807735) < 0) by (exact (IZR_lt (-633045697807735) 0 ltac:(lia))).
  assert (Hb1 : IZR (-633045697807732) < 0) by (exact (IZR_lt (-633045697807732) 0 ltac:(lia))).
  assert (Ha2 : IZR (-84410879089805) < 0) by (exact (IZR_lt (-84410879089805) 0 ltac:(lia))).
  assert (Hb2 : IZR (-84410879089802) < 0) by (exact (IZR_lt (-84410879089802) 0 ltac:(lia))).
  assert (Ha3 : 0 < IZR 104252567179735) by (exact (IZR_lt 0 104252567179735 ltac:(lia))).
  assert (Hb3 : 0 < IZR 104252567179738) by (exact (IZR_lt 0 104252567179738 ltac:(lia))).
  assert (Ha4 : 0 < IZR 428820087806213) by (exact (IZR_lt 0 428820087806213 ltac:(lia))).
  assert (Hb4 : 0 < IZR 428820087806216) by (exact (IZR_lt 0 428820087806216 ltac:(lia))).
  assert (Hr1n : r1 < 0) by nra.
  assert (Hr2n : r2 < 0) by nra.
  assert (Hr3p : 0 < r3) by nra.
  assert (Hr4p : 0 < r4) by nra.
  (* pairwise product bounds *)
  assert (Hm12 : (0 < r1 * r2
                  /\ r1 * r2 <= IZR (-633045697807735) * IZR (-84410879089805)
                               * (/ IZR witD * / IZR witD))%R)
    by (split; nra).
  assert (Hm34 : (0 < r3 * r4
                  /\ r3 * r4 <= IZR 104252567179738 * IZR 428820087806216
                               * (/ IZR witD * / IZR witD))%R)
    by (split; nra).
  assert (HPi_pos : 0 < (r1 * r2 * r3 * r4)%R) by nra.
  assert (HPi_up : ((r1 * r2 * r3 * r4)
    <= (IZR (-633045697807735) * IZR (-84410879089805)
        * (IZR 104252567179738 * IZR 428820087806216))
       * (/ IZR witD * / IZR witD * (/ IZR witD * / IZR witD)))%R).
  { destruct Hm12 as [Hm12p Hm12u].
    destruct Hm34 as [Hm34p Hm34u].
    nra. }
  (* the scalar bound on pr *)
  assert (Hunit : (IZR witD * / IZR witD)%R = 1%R)
    by (field; lra).
  assert (Hpr_low : ((IZR 347428 * IZR witD
                      + (IZR (-633045697807735) + IZR (-84410879089805)
                         + IZR 104252567179735 + IZR 428820087806213))
                     * / IZR witD <= pr)%R).
  { rewrite Hpr_val. nra. }
  assert (Hpr_hi : (pr <= (IZR 347428 * IZR witD
                      + (IZR (-633045697807732) + IZR (-84410879089802)
                         + IZR 104252567179738 + IZR 428820087806216))
                     * / IZR witD)%R).
  { rewrite Hpr_val. nra. }
  assert (Hhi_neg : ((IZR 347428 * IZR witD
                      + (IZR (-633045697807732) + IZR (-84410879089802)
                         + IZR 104252567179738 + IZR 428820087806216))
                     * / IZR witD < 0)%R).
  { assert (Hz : (347428 * witD
                  + (-633045697807732 + -84410879089802
                     + 104252567179738 + 428820087806216) < 0)%Z)
      by (vm_compute; reflexivity).
    pose proof (IZR_lt _ 0 Hz) as HzR.
    rewrite plus_IZR, mult_IZR in HzR.
    repeat rewrite plus_IZR in HzR.
    nra. }
  (* the integer keystone comparison *)
  assert (Hkey : ((347428 * witD
                   + (-633045697807735 + -84410879089805
                      + 104252567179735 + 428820087806213))
                  * (347428 * witD
                     + (-633045697807735 + -84410879089805
                        + 104252567179735 + 428820087806213))
                  * ((-633045697807735) * (-84410879089805)
                     * (104252567179738 * 428820087806216))
                  <? 4 * 2795309191751463646995099641203274900592260
                       * (witD * witD * (witD * witD) * (witD * witD)))%Z
                 = true)
    by (vm_compute; reflexivity).
  apply Z.ltb_lt in Hkey.
  (* the discriminant bound *)
  assert (Hc0pos : 0 < IZR 2795309191751463646995099641203274900592260)
    by (exact (IZR_lt 0 2795309191751463646995099641203274900592260
                 ltac:(lia))).
  set (PLn := (IZR 347428 * IZR witD
               + (IZR (-633045697807735) + IZR (-84410879089805)
                  + IZR 104252567179735 + IZR 428820087806213))%R) in *.
  set (CRN := (IZR (-633045697807735) * IZR (-84410879089805)
               * (IZR 104252567179738 * IZR 428820087806216))%R) in *.
  set (IV2 := (/ IZR witD * / IZR witD)%R) in *.
  set (D6 := (IZR witD * IZR witD * (IZR witD * IZR witD)
              * (IZR witD * IZR witD))%R) in *.
  assert (HD6pos : 0 < D6).
  { unfold D6.
    apply Rmult_lt_0_compat;
      [apply Rmult_lt_0_compat;
         [apply Rmult_lt_0_compat; [exact HDpos | exact HDpos]
         | apply Rmult_lt_0_compat; [exact HDpos | exact HDpos]]
      | apply Rmult_lt_0_compat; [exact HDpos | exact HDpos]]. }
  assert (Hunit6 : (D6 * (IV2 * (IV2 * IV2)))%R = 1%R)
    by (unfold D6, IV2; field; lra).
  assert (Hqr_pos : 0 < qr) by nra.
  assert (HQH : (r1 * r2 * r3 * r4 <= CRN * (IV2 * IV2))%R).
  { clear - Hbr1 Hbr2 Hbr3 Hbr4 Hinv HDpos Hr1n Hr2n Hr3p Hr4p
      Ha1 Hb1 Ha2 Hb2 Ha3 Hb3 Ha4 Hb4 Hm12 Hm34.
    destruct Hm12 as [Hm12p Hm12u].
    destruct Hm34 as [Hm34p Hm34u].
    unfold CRN, IV2 in *. nra. }
  assert (HCRNpos : 0 < CRN)
    by (clear - Ha1 Ha2 Hb3 Hb4; unfold CRN; nra).
  assert (HIV2pos : 0 < IV2) by (clear - Hinv; unfold IV2; nra).
  assert (H4 : (4 * IZR 2795309191751463646995099641203274900592260
                <= 4 * qr * (CRN * (IV2 * IV2)))%R) by nra.
  assert (Hpr2 : (pr * pr <= PLn * PLn * IV2)%R).
  { assert (HPL2 : ((PLn * / IZR witD) * (PLn * / IZR witD)
                    = PLn * PLn * IV2)%R)
      by (unfold IV2; ring).
    clear - HPL2 Hpr_low Hpr_hi Hhi_neg.
    rewrite <- HPL2.
    clear HPL2.
    try clear IV2. try clear CRN. try clear D6.
    clearbody PLn.
    assert (Hpa : (pr + PLn * / IZR witD <= 0)%R) by lra.
    assert (Hpm : (0 <= pr - PLn * / IZR witD)%R) by lra.
    assert (Hprod : ((pr - PLn * / IZR witD) * (pr + PLn * / IZR witD)
                     <= (pr - PLn * / IZR witD) * 0)%R)
      by (apply Rmult_le_compat_l; lra).
    assert (Hexp : ((pr - PLn * / IZR witD) * (pr + PLn * / IZR witD)
                    = pr * pr
                      - (PLn * / IZR witD) * (PLn * / IZR witD))%R)
      by ring.
    lra. }
  assert (Hkey2 : (PLn * PLn * CRN
                   < 4 * IZR 2795309191751463646995099641203274900592260
                     * D6)%R).
  { unfold PLn, CRN, D6.
    repeat first [rewrite <- mult_IZR | rewrite <- plus_IZR].
    apply IZR_lt.
    exact Hkey. }
  (* multiply through by the positive unit *)
  assert (Hfacpos : (0 < CRN * (IV2 * IV2) * D6)%R).
  { apply Rmult_lt_0_compat;
      [apply Rmult_lt_0_compat;
         [exact HCRNpos
         | apply Rmult_lt_0_compat; [exact HIV2pos | exact HIV2pos]]
      | exact HD6pos]. }
  assert (Hu : (IV2 * (IV2 * IV2) * D6)%R = 1%R)
    by (rewrite <- Hunit6; ring).
  assert (Hfin : ((pr * pr) * (CRN * (IV2 * IV2) * D6)
                  < (4 * qr) * (CRN * (IV2 * IV2) * D6))%R).
  { apply Rle_lt_trans
      with ((PLn * PLn * IV2) * (CRN * (IV2 * IV2) * D6))%R.
    - apply Rmult_le_compat_r; [lra | exact Hpr2].
    - replace ((PLn * PLn * IV2) * (CRN * (IV2 * IV2) * D6))%R
        with ((PLn * PLn * CRN) * (IV2 * (IV2 * IV2) * D6))%R by ring.
      rewrite Hu.
      apply Rlt_le_trans
        with ((4 * IZR 2795309191751463646995099641203274900592260 * D6))%R.
      + replace ((PLn * PLn * CRN) * 1)%R with (PLn * PLn * CRN)%R by ring.
        exact Hkey2.
      + replace ((4 * qr) * (CRN * (IV2 * IV2) * D6))%R
          with ((4 * qr * (CRN * (IV2 * IV2))) * D6)%R by ring.
        apply Rmult_le_compat_r; [lra | exact H4]. }
  apply (Rmult_lt_reg_r (CRN * (IV2 * IV2) * D6)%R); [exact Hfacpos |].
  exact Hfin.
Qed.

(** THE ROOT LIST: four bracketed reals and a conjugate pair, splitting the witness sextic. *)
Lemma witness_rho_exists :
  exists (r1 r2 r3 r4 : R) (w : C),
    r1 < r2 /\ r2 < r3 /\ r3 < r4 /\
    snd w <> 0%R /\
    (forall r : R, In r (r1 :: r2 :: r3 :: r4 :: nil) ->
       cpeval (map castZ witFz) (RtoC r) = C0) /\
    (forall z, cpeval (map castZ witFz) z
       = (C1 * prod_linear (RtoC r1 :: RtoC r2 :: RtoC r3 :: RtoC r4
                            :: w :: Cconj w :: nil) z)%C) /\
    NoDup (RtoC r1 :: RtoC r2 :: RtoC r3 :: RtoC r4 :: w :: Cconj w :: nil).
Proof.
  destruct four_real_roots
    as [r1 [r2 [r3 [r4 [Hbr1 [Hbr2 [Hbr3 [Hbr4
        [He1 [He2 [He3 [He4 [H12 [H23 H34]]]]]]]]]]]]]].
  destruct (witF_quartic_cofactor r1 r2 r3 r4 He1 He2 He3 He4 H12 H23 H34)
    as [pr [qr [Hmaster [Hpr_val Hqr_rel]]]].
  (* the quadratic splits *)
  destruct (monic_real_step_splits_all 2 (qr :: pr :: nil)
              ltac:(lia) ltac:(lia) ltac:(reflexivity))
    as [ws [Hlws Hws]].
  destruct ws as [|w1 [|w2 [|]]]; try (cbn [length] in Hlws; lia).
  assert (Hquad : forall z, cpeval_lf (C1 :: RtoC pr :: RtoC qr :: nil) z
                            = ((z - w1) * (z - w2))%C).
  { intro z.
    assert (HL : cpeval_lf (C1 :: RtoC pr :: RtoC qr :: nil) z
                 = (cpeval (map RtoC (qr :: pr :: nil)) z + Cpow z 2)%C).
    { cbn [cpeval_lf length map cpeval Cpow]. ring. }
    rewrite HL, (Hws z).
    cbn [prod_linear]. ring. }
  (* the discriminant is negative on the brackets *)
  assert (Hdisc : (pr * pr < 4 * qr)%R)
    by (exact (witF_disc_neg r1 r2 r3 r4 pr qr Hbr1 Hbr2 Hbr3 Hbr4
                 Hpr_val Hqr_rel)).
  (* nonreality of the quadratic roots *)
  assert (Hw1_im : snd w1 <> 0%R).
  { intro Him.
    assert (Hw1r : w1 = RtoC (fst w1)).
    { unfold RtoC.
      rewrite (surjective_pairing w1), Him. reflexivity. }
    assert (Hroot : cpeval_lf (C1 :: RtoC pr :: RtoC qr :: nil) w1 = C0)
      by (rewrite (Hquad w1); ring).
    assert (HrootR : cpeval_lf (C1 :: RtoC pr :: RtoC qr :: nil) (RtoC (fst w1)) = C0)
      by (rewrite <- Hw1r; exact Hroot).
    rewrite cpeval_lf_rev_c in HrootR.
    cbn [rev app] in HrootR.
    cbn [cpeval] in HrootR.
    change C1 with (RtoC 1%R) in HrootR.
    change C0 with (RtoC 0%R) in HrootR.
    repeat first [rewrite <- RtoC_mul in HrootR
                 | rewrite <- RtoC_add in HrootR].
    apply RtoC_inj in HrootR.
    assert (Hd0 : (0 <= (pr + 2 * fst w1) * (pr + 2 * fst w1))%R).
    { pose proof (Rle_0_sqr (pr + 2 * fst w1)%R) as Hsq.
      unfold Rsqr in Hsq. exact Hsq. }
    assert (Hexp2 : ((pr + 2 * fst w1) * (pr + 2 * fst w1)
                     = pr * pr + 4 * (pr * fst w1)
                       + 4 * (fst w1 * fst w1))%R) by ring.
    assert (Hlin : (qr + (fst w1 * fst w1) + (pr * fst w1) = 0)%R)
      by (rewrite <- HrootR; ring).
    lra. }
  (* the conjugate is the other root *)
  assert (Hw2_conj : w2 = Cconj w1).
  { assert (HfaQ : Forall CR (C1 :: RtoC pr :: RtoC qr :: nil)).
    { constructor; [reflexivity |].
      constructor; [apply CR_RtoC |].
      constructor; [apply CR_RtoC | constructor]. }
    assert (Hc1 : cpeval_lf (C1 :: RtoC pr :: RtoC qr :: nil) (Cconj w1) = C0).
    { assert (Hrev : forall u : C, cpeval_lf (C1 :: RtoC pr :: RtoC qr :: nil) u
                     = cpeval (rev (C1 :: RtoC pr :: RtoC qr :: nil)) u)
        by (intro u; rewrite cpeval_lf_rev_c; reflexivity).
      rewrite Hrev.
      rewrite (Cconj_eval (rev (C1 :: RtoC pr :: RtoC qr :: nil)) w1
                 ltac:(apply Forall_rev; exact HfaQ)).
      rewrite <- Hrev.
      assert (Hz : cpeval_lf (C1 :: RtoC pr :: RtoC qr :: nil) w1 = C0)
        by (rewrite (Hquad w1); ring).
      rewrite Hz.
      apply injective_projections; cbn; ring. }
    rewrite (Hquad (Cconj w1)) in Hc1.
    destruct (Cmul_integral _ _ Hc1) as [E | E].
    - exfalso.
      assert (Hcw : Cconj w1 = w1).
      { transitivity ((Cconj w1 - w1) + w1)%C; [ring | rewrite E; ring]. }
      exact (Cconj_neq_of_im w1 Hw1_im Hcw).
    - transitivity ((Cconj w1 - (Cconj w1 - w2))%C); [ring |].
      rewrite E. ring. }
  (* assembly *)
  exists r1, r2, r3, r4, w1.
  split; [exact H12 |].
  split; [exact H23 |].
  split; [exact H34 |].
  split; [exact Hw1_im |].
  split.
  { intros r Hr.
    cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | []]]]]; assumption. }
  split.
  { intro z.
    rewrite (Hmaster z).
    rewrite (Hquad z).
    rewrite <- Hw2_conj.
    cbn [prod_linear].
    ring. }
  (* NoDup of the six roots *)
  assert (Hd12 : RtoC r1 <> RtoC r2) by (apply RtoC_neq; lra).
    assert (Hd13 : RtoC r1 <> RtoC r3) by (apply RtoC_neq; lra).
    assert (Hd14 : RtoC r1 <> RtoC r4) by (apply RtoC_neq; lra).
    assert (Hd23 : RtoC r2 <> RtoC r3) by (apply RtoC_neq; lra).
    assert (Hd24 : RtoC r2 <> RtoC r4) by (apply RtoC_neq; lra).
    assert (Hd34 : RtoC r3 <> RtoC r4) by (apply RtoC_neq; lra).
    assert (Hw1r : forall x : R, w1 <> RtoC x)
      by (intro x; apply nonreal_neq_real; exact Hw1_im).
    assert (Hw2_im : snd (Cconj w1) <> 0%R).
    { unfold Cconj. cbn. lra. }
    assert (Hw2r : forall x : R, Cconj w1 <> RtoC x)
      by (intro x; apply nonreal_neq_real; exact Hw2_im).
    assert (Hw12 : w1 <> Cconj w1).
  { intro E.
    apply (Cconj_neq_of_im w1 Hw1_im).
    symmetry. exact E. }
  constructor.
  { intro Hin. cbn [In] in Hin.
    destruct Hin as [E | [E | [E | [E | [E | []]]]]].
    - exact (Hd12 (eq_sym E)).
    - exact (Hd13 (eq_sym E)).
    - exact (Hd14 (eq_sym E)).
    - exact (Hw1r r1 E).
    - exact (Hw2r r1 E). }
  constructor.
  { intro Hin. cbn [In] in Hin.
    destruct Hin as [E | [E | [E | [E | []]]]].
    - exact (Hd23 (eq_sym E)).
    - exact (Hd24 (eq_sym E)).
    - exact (Hw1r r2 E).
    - exact (Hw2r r2 E). }
  constructor.
  { intro Hin. cbn [In] in Hin.
    destruct Hin as [E | [E | [E | []]]].
    - exact (Hd34 (eq_sym E)).
    - exact (Hw1r r3 E).
    - exact (Hw2r r3 E). }
  constructor.
  { intro Hin. cbn [In] in Hin.
    destruct Hin as [E | [E | []]].
    - exact (Hw1r r4 E).
    - exact (Hw2r r4 E). }
  constructor.
  { intro Hin. cbn [In] in Hin.
    destruct Hin as [E | []].
    exact (Hw12 (eq_sym E)). }
  constructor.
  { intro Hin. exact Hin. }
  constructor.
Qed.


(* two-transitivity of the witness group and the base case -- it contains every transposition, hence all of S6. *)

(** the first-step minimal relation reproduces the monic sextic exactly *)
Lemma step1_minpoly_exact : forall (r1 : C) (dt1 : list C),
  cpeval (map castZ witFz) r1 = C0 ->
  length dt1 = 6%nat -> Forall CQ dt1 ->
  (cpeval dt1 r1 + Cpow r1 6)%C = C0 ->
  Cindep_pows CQ r1 6 ->
  forall z, cpeval (map castZ witFz) z = (Cpow z 6 + cpeval dt1 z)%C.
Proof.
  intros r1 dt1 Hroot Hl Hf Hrel Hind z.
  destruct (cminpoly_divides CQ r1 6 dt1 CQ_subfield ltac:(lia) Hl Hf Hrel Hind
              (map castZ witFz) (Forall_CQ_castZ witFz) Hroot) as [HQdiv Hdiv].
  set (Q := fst (cpdiv_lf (length (rev (map castZ witFz)))
                   (rev (map castZ witFz)) (rev dt1))) in *.
  assert (HlQ : length Q = 1%nat).
  { unfold Q.
    rewrite (cpdiv_lf_qlen _ _ _ (Nat.le_refl _)).
    rewrite !length_rev, length_map, Hl.
    reflexivity. }
  destruct Q as [|q0 [|? ?]]; try (cbn [length] in HlQ; lia).
  assert (Hq0 : q0 = C1).
  { set (Mlf := C1 :: rev dt1).
    assert (HlM : length Mlf = 7%nat)
      by (unfold Mlf; cbn [length]; rewrite length_rev, Hl; reflexivity).
    assert (HevM : forall w, cpeval_lf Mlf w = (Cpow w 6 + cpeval dt1 w)%C).
    { intro w. unfold Mlf. cbn [cpeval_lf].
      rewrite length_rev, Hl.
      rewrite cpeval_lf_rev_c, rev_involutive. ring. }
    assert (Hlists : rev (map castZ witFz) = cpmul_lf (q0 :: nil) Mlf).
    { apply lf_eq_of_eval.
      - assert (Hh : hd C0 (rev (map castZ witFz)) = C1) by reflexivity.
        rewrite Hh. exact C1_neq_C0.
      - rewrite cpmul_lf_head;
          [| cbn [length]; lia | rewrite HlM; lia].
        cbn [hd]. unfold Mlf. cbn [hd].
        intro E.
        assert (Hz : forall w, cpeval (map castZ witFz) w = C0).
        { intro w.
          rewrite (Hdiv w).
          assert (Hq0e : cpeval_lf (q0 :: nil) w = q0)
            by (rewrite cpeval_lf_rev_c; cbn [rev app cpeval]; ring).
          assert (Hq00 : q0 = C0)
            by (transitivity ((q0 * C1)%C); [ring | exact E]).
          rewrite Hq0e, Hq00. ring. }
        pose proof (Hz C0) as H0.
        assert (Hc0 : cpeval (map castZ witFz) C0 = castZ 2795309191751463646995099641203274900592260).
        { cbn [witFz map cpeval]. ring. }
        rewrite Hc0 in H0.
        assert (Hne : castZ 2795309191751463646995099641203274900592260 <> C0).
        { unfold castZ. intro E2.
          assert (Hr : IZR 2795309191751463646995099641203274900592260 = 0%R)
            by (exact (f_equal fst E2)).
          apply eq_IZR in Hr. lia. }
        exact (Hne H0).
      - intro w.
        rewrite cpmul_lf_eval.
        assert (HevF2 : cpeval_lf (rev (map castZ witFz)) w
                        = cpeval (map castZ witFz) w)
          by (rewrite cpeval_lf_rev_c, rev_involutive; reflexivity).
        rewrite HevF2, (Hdiv w), HevM.
        reflexivity. }
    assert (Hhead : hd C0 (rev (map castZ witFz))
                    = hd C0 (cpmul_lf (q0 :: nil) Mlf))
      by (rewrite Hlists; reflexivity).
    rewrite cpmul_lf_head in Hhead;
      [| cbn [length]; lia | rewrite HlM; lia].
    cbn [hd] in Hhead.
    unfold Mlf in Hhead. cbn [hd] in Hhead.
    assert (Hh1 : hd C0 (rev (map castZ witFz)) = C1) by reflexivity.
    rewrite Hh1 in Hhead.
    transitivity ((q0 * C1)%C); [ring | rewrite <- Hhead; reflexivity]. }
  subst q0.
  rewrite (Hdiv z).
  assert (Hq0e : cpeval_lf (C1 :: nil) z = C1)
    by (rewrite cpeval_lf_rev_c; cbn [rev app cpeval]; ring).
  rewrite Hq0e. ring.
Qed.

(** the second-step relation as a coefficient identity against the sextic *)
Lemma step2_coeff_identity : forall (r1 r2 : C) (dt1 dt2 : list C),
  cpeval (map castZ witFz) r1 = C0 ->
  cpeval (map castZ witFz) r2 = C0 ->
  r1 <> r2 ->
  length dt1 = 6%nat -> Forall CQ dt1 ->
  (cpeval dt1 r1 + Cpow r1 6)%C = C0 ->
  length dt2 = 5%nat -> Forall (CPolyF CQ 6 r1) dt2 ->
  (cpeval dt2 r2 + Cpow r2 5)%C = C0 ->
  Cindep_pows (CPolyF CQ 6 r1) r2 5 ->
  map castZ witFz = cpmul (Copp r1 :: C1 :: nil) (dt2 ++ C1 :: nil).
Proof.
  intros r1 r2 dt1 dt2 Hroot1 Hroot2 Hne Hl1 Hf1 Hrel1 Hl2 Hf2 Hrel2 Hind2.
  set (K1 := CPolyF CQ 6 r1) in *.
  assert (HK1sub : is_Csubfield K1)
    by (apply (CPolyF_Csubfield CQ r1 6 dt1 CQ_subfield ltac:(lia) Hl1 Hf1
                 Hrel1)).
  assert (HQK1 : forall x, CQ x -> K1 x)
    by (apply (CPolyF_contains CQ r1 6 dt1 CQ_subfield ltac:(lia) Hl1 Hf1
                 Hrel1)).
  assert (Hr1K1 : K1 r1)
    by (apply (CPolyF_r_mem CQ r1 6 dt1 CQ_subfield ltac:(lia) Hl1 Hf1 Hrel1)).
  set (FClf := rev (map castZ witFz)).
  assert (HevF : forall z, cpeval_lf FClf z = cpeval (map castZ witFz) z).
  { intro z. unfold FClf.
    rewrite cpeval_lf_rev_c, rev_involutive. reflexivity. }
  set (G1 := fst (cpdiv_lf (length FClf) FClf (Copp r1 :: nil))).
  assert (Hfac : forall z, cpeval_lf FClf z = (cpeval_lf G1 z * (z - r1))%C).
  { intro z.
    apply (cp_root_factor FClf r1).
    rewrite HevF. exact Hroot1. }
  assert (HhdF : hd C0 FClf = C1) by reflexivity.
  assert (HlF : length FClf = 7%nat) by reflexivity.
  destruct (cpdiv_head_monic FClf r1 HhdF ltac:(rewrite HlF; lia))
    as [HhdG HlG].
  fold G1 in HhdG, HlG.
  rewrite HlF in HlG.
  assert (HfG : Forall K1 G1).
  { unfold G1.
    apply (proj1 (cpdiv_lf_Forall K1 (length FClf) FClf (Copp r1 :: nil)
                    HK1sub
                    ltac:(unfold FClf; apply Forall_rev;
                          apply Forall_map_intro; intros n _;
                          apply HQK1; unfold castZ; apply CQ_IZR)
                    ltac:(constructor;
                          [apply Csubfield_opp; assumption | constructor]))). }
  assert (HG1r2 : cpeval_lf G1 r2 = C0).
  { pose proof (Hfac r2) as H.
    rewrite HevF, Hroot2 in H.
    destruct (Cmul_integral _ _ (eq_sym H)) as [E | E]; [exact E | exfalso].
    apply Hne.
    symmetry.
    transitivity ((r2 - r1) + r1)%C; [ring | rewrite E; ring]. }
  (* the quotient of G1 by the second minimal relation is the constant one *)
  destruct (cminpoly_divides K1 r2 5 dt2 HK1sub ltac:(lia) Hl2 Hf2 Hrel2 Hind2
              (rev G1)
              ltac:(apply Forall_rev; exact HfG)
              ltac:(rewrite <- cpeval_lf_rev_c; exact HG1r2))
    as [HQdiv Hdiv].
  set (Q := fst (cpdiv_lf (length (rev (rev G1))) (rev (rev G1)) (rev dt2)))
    in *.
  assert (HlQ : length Q = 1%nat).
  { unfold Q.
    rewrite (cpdiv_lf_qlen _ _ _ (Nat.le_refl _)).
    rewrite !length_rev, HlG, Hl2.
    reflexivity. }
  destruct Q as [|q0 [|? ?]]; try (cbn [length] in HlQ; lia).
  set (Mlf := C1 :: rev dt2).
  assert (HlM : length Mlf = 6%nat)
    by (unfold Mlf; cbn [length]; rewrite length_rev, Hl2; reflexivity).
  assert (HevM : forall w, cpeval_lf Mlf w = (Cpow w 5 + cpeval dt2 w)%C).
  { intro w. unfold Mlf. cbn [cpeval_lf].
    rewrite length_rev, Hl2.
    rewrite cpeval_lf_rev_c, rev_involutive.
    ring. }
  assert (HevG : forall w, cpeval (rev G1) w = cpeval_lf G1 w)
    by (intro w; rewrite <- cpeval_lf_rev_c; reflexivity).
  assert (Hq0 : q0 = C1).
  { assert (Hlists : G1 = cpmul_lf (q0 :: nil) Mlf).
    { apply lf_eq_of_eval.
      - rewrite HhdG. exact C1_neq_C0.
      - rewrite cpmul_lf_head;
          [| cbn [length]; lia | rewrite HlM; lia].
        cbn [hd]. unfold Mlf. cbn [hd].
        intro E.
        assert (Hq00 : q0 = C0)
          by (transitivity ((q0 * C1)%C); [ring | exact E]).
        assert (Hz : cpeval (map castZ witFz) C0 = C0).
        { rewrite <- HevF, (Hfac C0).
          pose proof (Hdiv C0) as Hd0.
          rewrite HevG in Hd0.
          rewrite Hd0.
          assert (Hq0e : cpeval_lf (q0 :: nil) C0 = q0)
            by (rewrite cpeval_lf_rev_c; cbn [rev app cpeval]; ring).
          rewrite Hq0e, Hq00. ring. }
        assert (Hc0 : cpeval (map castZ witFz) C0
                      = castZ 2795309191751463646995099641203274900592260)
          by (cbn [witFz map cpeval]; ring).
        rewrite Hc0 in Hz.
        unfold castZ in Hz.
        assert (Hr : IZR 2795309191751463646995099641203274900592260 = 0%R)
          by (exact (f_equal fst Hz)).
        apply eq_IZR in Hr. lia.
      - intro w.
        rewrite cpmul_lf_eval.
        pose proof (Hdiv w) as Hd.
        rewrite HevG in Hd.
        rewrite Hd, HevM.
        reflexivity. }
    assert (Hhead : hd C0 G1 = hd C0 (cpmul_lf (q0 :: nil) Mlf))
      by (rewrite <- Hlists; reflexivity).
    rewrite cpmul_lf_head in Hhead;
      [| cbn [length]; lia | rewrite HlM; lia].
    cbn [hd] in Hhead.
    unfold Mlf in Hhead. cbn [hd] in Hhead.
    rewrite HhdG in Hhead.
    transitivity ((q0 * C1)%C); [ring | rewrite <- Hhead; reflexivity]. }
  subst q0.
  (* assemble the coefficient identity *)
  apply cpeval_ext_coeffs.
  - rewrite cpmul_length;
      [| cbn [length]; lia | rewrite length_app, Hl2; cbn [length]; lia].
    assert (H7 : length witFz = 7%nat) by reflexivity.
    rewrite length_map, H7, length_app, Hl2.
    cbn [length]. lia.
  - intro z.
    rewrite cpeval_cpmul.
    assert (Hlin : cpeval (Copp r1 :: C1 :: nil) z = (z - r1)%C)
      by (cbn [cpeval]; ring).
    assert (Happ : cpeval (dt2 ++ C1 :: nil) z = (cpeval dt2 z + Cpow z 5)%C).
    { rewrite cpeval_app, Hl2. cbn [cpeval]. ring. }
    rewrite Hlin, Happ.
    rewrite <- HevF, (Hfac z).
    pose proof (Hdiv z) as Hd.
    rewrite HevG in Hd.
    rewrite Hd.
    assert (Hq0e : cpeval_lf (C1 :: nil) z = C1)
      by (rewrite cpeval_lf_rev_c; cbn [rev app cpeval]; ring).
    rewrite Hq0e. ring.
Qed.

(** THE DOUBLE EXTENSION: an embedding of the two-step field sending the two designated roots to any ordered pair of distinct roots. *)
Lemma two_point_extension :
  forall (r1 r2 : C) (dt1 dt2 : list C) (wk wl : C),
  cpeval (map castZ witFz) r1 = C0 ->
  cpeval (map castZ witFz) r2 = C0 ->
  r1 <> r2 ->
  length dt1 = 6%nat -> Forall CQ dt1 ->
  (cpeval dt1 r1 + Cpow r1 6)%C = C0 -> Cindep_pows CQ r1 6 ->
  length dt2 = 5%nat -> Forall (CPolyF CQ 6 r1) dt2 ->
  (cpeval dt2 r2 + Cpow r2 5)%C = C0 ->
  Cindep_pows (CPolyF CQ 6 r1) r2 5 ->
  cpeval (map castZ witFz) wk = C0 ->
  cpeval (map castZ witFz) wl = C0 ->
  wk <> wl ->
  exists tau : C -> C,
    CCembeds (CPolyF (CPolyF CQ 6 r1) 5 r2) tau /\
    (forall x, CQ x -> tau x = x) /\
    tau r1 = wk /\ tau r2 = wl.
Proof.
  intros r1 r2 dt1 dt2 wk wl Hroot1 Hroot2 Hne
         Hl1 Hf1 Hrel1 Hind1 Hl2 Hf2 Hrel2 Hind2 Hwk Hwl Hnekl.
  set (K1 := CPolyF CQ 6 r1) in *.
  assert (HK1sub : is_Csubfield K1)
    by (apply (CPolyF_Csubfield CQ r1 6 dt1 CQ_subfield ltac:(lia) Hl1 Hf1
                 Hrel1)).
  assert (HQK1 : forall x, CQ x -> K1 x)
    by (apply (CPolyF_contains CQ r1 6 dt1 CQ_subfield ltac:(lia) Hl1 Hf1
                 Hrel1)).
  assert (Hr1K1 : K1 r1)
    by (apply (CPolyF_r_mem CQ r1 6 dt1 CQ_subfield ltac:(lia) Hl1 Hf1 Hrel1)).
  (* step one: send r1 to wk over the rationals *)
  assert (Hid : CCembeds CQ (fun z => z)) by (apply CCembeds_id).
  assert (Hexact1 := step1_minpoly_exact r1 dt1 Hroot1 Hl1 Hf1 Hrel1 Hind1).
  assert (Hwrel1 : (CCevalMap (fun z => z) dt1 wk + Cpow wk 6)%C = C0).
  { rewrite CCevalMap_id.
    transitivity ((Cpow wk 6 + cpeval dt1 wk)%C); [ring |].
    rewrite <- (Hexact1 wk). exact Hwk. }
  destruct (CCembeds_extend_step CQ r1 6 dt1 (fun z => z) wk CQ_subfield
              ltac:(lia) Hl1 Hf1 Hrel1 Hind1 Hid Hwrel1)
    as [s1 [Hs1emb [Hs1fix Hs1r1]]].
  fold K1 in Hs1emb.
  (* step two: transport the coefficient identity and send r2 to wl *)
  pose proof (step2_coeff_identity r1 r2 dt1 dt2 Hroot1 Hroot2 Hne
                Hl1 Hf1 Hrel1 Hl2 Hf2 Hrel2 Hind2) as Hcoeff.
  assert (Hs1opp : s1 (Copp r1) = Copp wk).
  { assert (H0 : s1 C0 = C0) by (exact (proj1 Hs1emb)).
    assert (Hadd : s1 (r1 + Copp r1)%C = (s1 r1 + s1 (Copp r1))%C).
    { apply (proj1 (proj2 (proj2 Hs1emb)));
        [exact Hr1K1 | apply Csubfield_opp; assumption]. }
    assert (Hz : (r1 + Copp r1)%C = C0) by ring.
    rewrite Hz, H0 in Hadd.
    rewrite Hs1r1 in Hadd.
    transitivity ((wk + s1 (Copp r1)) - wk)%C; [ring | rewrite <- Hadd; ring]. }
  assert (Himg : (CCevalMap s1 dt2 wl + Cpow wl 5)%C = C0).
  { assert (Htrans : CCevalMap s1 (map castZ witFz) wl
                     = (CCevalMap s1 (Copp r1 :: C1 :: nil) wl
                        * CCevalMap s1 (dt2 ++ C1 :: nil) wl)%C).
    { rewrite Hcoeff at 1.
      apply (CCevalMap_cpmul K1 s1 Hs1emb HK1sub).
      - constructor; [apply Csubfield_opp; assumption |].
        constructor; [apply (Csubfield_1 K1 HK1sub) | constructor].
      - apply Forall_app_intro_c; [exact Hf2 |].
        constructor; [apply (Csubfield_1 K1 HK1sub) | constructor]. }
    assert (Hfixed : CCevalMap s1 (map castZ witFz) wl
                     = cpeval (map castZ witFz) wl).
    { rewrite (CCevalMap_ext_on s1 (fun c => c));
        [apply CCevalMap_id |].
      apply Forall_map_intro. intros n _.
      apply Hs1fix. unfold castZ. apply CQ_IZR. }
    rewrite Hfixed, Hwl in Htrans.
    assert (Hlin : CCevalMap s1 (Copp r1 :: C1 :: nil) wl = (wl - wk)%C).
    { cbn [CCevalMap].
      rewrite Hs1opp, (proj1 (proj2 Hs1emb)).
      ring. }
    assert (Happ : CCevalMap s1 (dt2 ++ C1 :: nil) wl
                   = (CCevalMap s1 dt2 wl + Cpow wl 5)%C).
    { rewrite CCevalMap_app, Hl2.
      cbn [CCevalMap].
      rewrite (proj1 (proj2 Hs1emb)).
      ring. }
    rewrite Hlin, Happ in Htrans.
    assert (Hnekl' : (wl - wk)%C <> C0).
    { intro E. apply Hnekl.
      transitivity ((wl - wk) + wk)%C; [rewrite E |]; ring. }
    destruct (Cmul_integral _ _ (eq_sym Htrans)) as [E | E];
      [exfalso; exact (Hnekl' E) | exact E]. }
  destruct (CCembeds_extend_step K1 r2 5 dt2 s1 wl HK1sub
              ltac:(lia) Hl2 Hf2 Hrel2 Hind2 Hs1emb Himg)
    as [s2 [Hs2emb [Hs2fix Hs2r2]]].
  exists s2.
  split; [exact Hs2emb |].
  split.
  { intros x Hx.
    rewrite (Hs2fix x (HQK1 x Hx)).
    apply Hs1fix. exact Hx. }
  split.
  { rewrite (Hs2fix r1 Hr1K1). exact Hs1r1. }
  exact Hs2r2.
Qed.

(** entries of a nonzero-length chain multiply to a positive count *)
Lemma prodl_pos_of_ge1 : forall js : list nat,
  Forall (fun j => (1 <= j)%nat) js -> (1 <= prodl js)%nat.
Proof.
  induction js as [|j js IH]; intro Hall; cbn [prodl fold_right].
  - lia.
  - pose proof (Forall_inv Hall) as Hj.
    pose proof (IH (Forall_inv_tail Hall)) as Hrest.
    pose proof (Nat.mul_le_mono 1 j 1 (prodl js) Hj Hrest) as H1.
    unfold prodl in H1.
    lia.
Qed.

Lemma RootChain_js_ge1 : forall K0 rho rs js K,
  RootChain K0 rho rs js K -> Forall (fun j => (1 <= j)%nat) js.
Proof.
  intros K0 rho rs js K Hch.
  induction Hch as [| rs js K r j dt Hch IH Hin Hj1 Hjn Hldt HKdt Hrel Hind];
    [constructor |].
  rewrite Forall_app.
  split; [exact IH |].
  constructor; [exact Hj1 | constructor].
Qed.

(** conjugating a transposition relabels its two points *)
Lemma conj_transp_vm :
  forallb (fun p =>
    forallb (fun i =>
      forallb (fun j =>
        eqb_listnat (conj_of p (transp i j))
          (transp (nth i p 0%nat) (nth j p 0%nat)))
        (seq 0 6))
      (seq 0 6))
    S6list = true.
Proof. vm_compute. reflexivity. Qed.

Lemma conj_transp : forall p i j,
  In p S6list -> (i < 6)%nat -> (j < 6)%nat ->
  conj_of p (transp i j) = transp (nth i p 0%nat) (nth j p 0%nat).
Proof.
  intros p i j Hp Hi Hj.
  pose proof (proj1 (forallb_forall _ S6list) conj_transp_vm p Hp) as H1.
  cbv beta in H1.
  pose proof (proj1 (forallb_forall _ (seq 0 6)) H1 i
                ltac:(apply in_seq; lia)) as H2.
  cbv beta in H2.
  pose proof (proj1 (forallb_forall _ (seq 0 6)) H2 j
                ltac:(apply in_seq; lia)) as H3.
  apply eqb_listnat_spec in H3.
  exact H3.
Qed.

(** THE BASE CASE: the witness permutation group contains every transposition and hence all of the symmetric group. *)
Theorem base_case_S6 :
  forall (rho : list C) (dt1 dt2 : list C) (rs3 : list C) (js3 : list nat)
         (K : C -> Prop) (Perm : list (list nat)) (N : nat),
  NoDup rho -> length rho = 6%nat ->
  (forall r, In r rho -> cpeval (map castZ witFz) r = C0) ->
  (forall z, cpeval (map castZ witFz) z = (C1 * prod_linear rho z)%C) ->
  length dt1 = 6%nat -> Forall CQ dt1 ->
  (cpeval dt1 (nth 4 rho C0) + Cpow (nth 4 rho C0) 6)%C = C0 ->
  Cindep_pows CQ (nth 4 rho C0) 6 ->
  length dt2 = 5%nat -> Forall (CPolyF CQ 6 (nth 4 rho C0)) dt2 ->
  (cpeval dt2 (nth 5 rho C0) + Cpow (nth 5 rho C0) 5)%C = C0 ->
  Cindep_pows (CPolyF CQ 6 (nth 4 rho C0)) (nth 5 rho C0) 5 ->
  RootChain (CPolyF (CPolyF CQ 6 (nth 4 rho C0)) 5 (nth 5 rho C0))
    rho rs3 js3 K ->
  pgroup Perm ->
  (forall tau, CCembeds K tau -> (forall x, CQ x -> tau x = x) ->
     exists m, (m < N)%nat /\
       forall i, (i < 6)%nat ->
         tau (nth i rho C0) = nth (nth i (nth m Perm pid6) 0%nat) rho C0) ->
  length Perm = N ->
  In (transp 4 5) Perm ->
  incl S6list Perm.
Proof.
  intros rho dt1 dt2 rs3 js3 K Perm N
         Hnd Hlen Hroots Hsplit Hl1 Hf1 Hrel1 Hi1 Hl2 Hf2 Hrel2 Hi2
         Hch3 HPg Hcomp HlP Ht45.
  set (r1 := nth 4 rho C0) in *.
  set (r2 := nth 5 rho C0) in *.
  set (K1 := CPolyF CQ 6 r1) in *.
  set (L := CPolyF K1 5 r2) in *.
  assert (Hr1_in : In r1 rho) by (apply nth_In; lia).
  assert (Hr2_in : In r2 rho) by (apply nth_In; lia).
  assert (Hne12 : r1 <> r2).
  { intro E.
    pose proof (proj1 (NoDup_nth rho C0) Hnd 4%nat 5%nat
                  ltac:(lia) ltac:(lia) E) as Hc.
    lia. }
  assert (HK1sub : is_Csubfield K1)
    by (apply (CPolyF_Csubfield CQ r1 6 dt1 CQ_subfield); try assumption; lia).
  assert (HLsub : is_Csubfield L)
    by (apply (CPolyF_Csubfield K1 r2 5 dt2 HK1sub); try assumption; lia).
  assert (HQK1 : forall x, CQ x -> K1 x)
    by (apply (CPolyF_contains CQ r1 6 dt1 CQ_subfield); try assumption; lia).
  assert (HK1L : forall x, K1 x -> L x)
    by (apply (CPolyF_contains K1 r2 5 dt2 HK1sub); try assumption; lia).
  assert (Hr1L : L r1).
  { apply HK1L.
    apply (CPolyF_r_mem CQ r1 6 dt1 CQ_subfield); try assumption; lia. }
  assert (Hr2L : L r2)
    by (apply (CPolyF_r_mem K1 r2 5 dt2 HK1sub); try assumption; lia).
  assert (HQL : forall x, CQ x -> L x)
    by (intros x Hx; apply HK1L; apply HQK1; exact Hx).
  assert (Hpair : forall k l, (k < 6)%nat -> (l < 6)%nat -> k <> l ->
    exists pm, In pm Perm /\
      nth 4 pm 0%nat = k /\ nth 5 pm 0%nat = l).
  { intros k l Hk Hl Hkl.
    set (wk := nth k rho C0).
    set (wl := nth l rho C0).
    assert (Hwk_ne : wk <> wl).
    { intro E.
      pose proof (proj1 (NoDup_nth rho C0) Hnd k l
                    ltac:(lia) ltac:(lia) E) as Hc.
      lia. }
    destruct (two_point_extension r1 r2 dt1 dt2 wk wl
                (Hroots r1 Hr1_in) (Hroots r2 Hr2_in) Hne12
                Hl1 Hf1 Hrel1 Hi1 Hl2 Hf2 Hrel2 Hi2
                (Hroots wk ltac:(apply nth_In; lia))
                (Hroots wl ltac:(apply nth_In; lia))
                Hwk_ne)
      as [s2 [Hs2emb [Hs2fix [Hs2r1 Hs2r2]]]].
    fold K1 in Hs2emb. fold L in Hs2emb.
    assert (HFcfL : Forall L (map castZ witFz)).
    { apply Forall_map_intro. intros n _.
      apply HQL. unfold castZ. apply CQ_IZR. }
    assert (Hs2Fcf : Forall (fun c => s2 c = c) (map castZ witFz)).
    { apply Forall_map_intro. intros n _.
      apply Hs2fix. unfold castZ. apply CQ_IZR. }
    destruct (RootChain_embeddings_over L rho (map castZ witFz) C1 s2
                HLsub Hnd C1_neq_C0 Hsplit HFcfL
                ltac:(rewrite length_map, Hlen; reflexivity)
                Hs2emb Hs2Fcf rs3 js3 K Hch3)
      as [sigmas' [Hlsig' [Hwf' [Hcomp' _]]]].
    assert (Hpos : (1 <= prodl js3)%nat).
    { apply prodl_pos_of_ge1.
      apply (RootChain_js_ge1 L rho rs3 js3 K Hch3). }
    set (tau := nth 0 sigmas' (fun z => z)).
    destruct (Hwf' 0%nat ltac:(lia)) as [Htau_emb Htau_agr].
    assert (Htau_fix : forall x, CQ x -> tau x = x).
    { intros x Hx.
      unfold tau.
      rewrite (Htau_agr x (HQL x Hx)).
      apply Hs2fix. exact Hx. }
    destruct (Hcomp tau Htau_emb Htau_fix) as [m [Hm Hvals]].
    set (pm := nth m Perm pid6).
    assert (Hpm_in : In pm Perm)
      by (apply nth_In; rewrite HlP; exact Hm).
    assert (Hpm_S6 : In pm S6list) by (exact (pg_S6 Perm HPg pm Hpm_in)).
    exists pm.
    split; [exact Hpm_in |].
    assert (Hv4 : tau r1 = wk).
    { unfold tau.
      rewrite (Htau_agr r1 Hr1L).
      exact Hs2r1. }
    assert (Hv5 : tau r2 = wl).
    { unfold tau.
      rewrite (Htau_agr r2 Hr2L).
      exact Hs2r2. }
    split.
    - pose proof (Hvals 4%nat ltac:(lia)) as H4.
      fold r1 pm in H4.
      rewrite Hv4 in H4.
      apply (proj1 (NoDup_nth rho C0) Hnd);
        [rewrite Hlen; exact (S6_entries_lt pm Hpm_S6 4%nat ltac:(lia))
        | rewrite Hlen; exact Hk
        | symmetry; exact H4].
    - pose proof (Hvals 5%nat ltac:(lia)) as H5.
      fold r2 pm in H5.
      rewrite Hv5 in H5.
      apply (proj1 (NoDup_nth rho C0) Hnd);
        [rewrite Hlen; exact (S6_entries_lt pm Hpm_S6 5%nat ltac:(lia))
        | rewrite Hlen; exact Hl
        | symmetry; exact H5]. }
  (* every transposition lies in the group *)
  assert (Htl : forall t, In t tlist -> In t Perm).
  { intros t Ht.
    unfold tlist in Ht.
    apply in_flat_map in Ht.
    destruct Ht as [i [Hi Ht]].
    apply in_map_iff in Ht.
    destruct Ht as [j [Htj Hj]].
    apply in_seq in Hi.
    apply in_seq in Hj.
    assert (Hij : i <> j) by lia.
    destruct (Hpair i j ltac:(lia) ltac:(lia) Hij)
      as [pm [Hpm [H4 H5]]].
    assert (Hconj : conj_of pm (transp 4 5) = transp i j).
    { rewrite (conj_transp pm 4 5 (pg_S6 Perm HPg pm Hpm)
                 ltac:(lia) ltac:(lia)).
      rewrite H4, H5. reflexivity. }
    rewrite <- Htj, <- Hconj.
    unfold conj_of.
    apply (pg_comp Perm HPg); [exact Hpm |].
    apply (pg_comp Perm HPg); [exact Ht45 |].
    apply pgroup_inv; [exact HPg | exact Hpm]. }
  (* closure *)
  set (CL := fst (gen_closure 7 tlist (gc_seed (pid6 :: tlist)))).
  assert (HCL : Forall (fun q => In q Perm) CL).
  { unfold CL.
    apply gen_closure_in.
    - intros g c Hg Hc. exact (pg_comp Perm HPg g c Hg Hc).
    - apply Forall_forall. exact Htl.
    - rewrite gc_seed_fst.
      constructor; [exact (pg_id Perm HPg) |].
      apply Forall_forall. exact Htl. }
  intros p Hp.
  pose proof (proj1 (forallb_forall _ S6list) transpositions_generate_S6 p Hp)
    as Hmb.
  cbv beta in Hmb.
  exact (proj1 (Forall_forall _ CL) HCL p
           (proj1 (memb_spec p (fst (gen_closure 7 tlist
                                       (gc_seed (pid6 :: tlist))))) Hmb)).
Qed.



(** conjugation as an embedding, and small conveniences *)
Lemma Cconj_embeds : forall (K : C -> Prop), CCembeds K Cconj.
Proof.
  intro K.
  split.
  { unfold Cconj, C0. apply injective_projections; cbn; ring. }
  split.
  { unfold Cconj, C1. apply injective_projections; cbn; ring. }
  split.
  - intros x y _ _. apply Cconj_add.
  - intros x y _ _. apply Cconj_mul.
Qed.

Lemma Cconj_fixes_CQ : forall z, CQ z -> Cconj z = z.
Proof.
  intros z [q [Hq Hz]].
  rewrite Hz. apply Cconj_RtoC.
Qed.

Lemma transp45_val : transp 4 5 = (0 :: 1 :: 2 :: 3 :: 5 :: 4 :: nil)%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma FcfB_g : forall (B : C -> Prop),
  (forall z, CQ z -> B z) -> Forall B (map castZ witFz).
Proof.
  intros B HQB.
  apply Forall_map_intro. intros n _.
  apply HQB. unfold castZ. apply CQ_IZR.
Qed.

Fixpoint Btow (L : list okstep) : C -> Prop :=
  match L with
  | nil => CQ
  | OKQuad s :: L' => CPolyF (Btow L') 2 (RtoC s)
  | OKPrime d c r :: L' => CPolyF (Btow L') d (RtoC r)
  end.

Lemma fsum_cpeval : forall (d : nat) (c : nat -> R) (t : R),
  RtoC (fsum d (fun i => c i * t ^ i))
  = cpeval (map (fun i => RtoC (c i)) (seq 0 d)) (RtoC t).
Proof.
  induction d as [|d IH]; intros c t.
  - reflexivity.
  - cbn [fsum].
    rewrite seq_S, map_app, cpeval_app.
    rewrite length_map, length_seq.
    cbn [map cpeval].
    rewrite RtoC_add, RtoC_mul, <- Cpow_RtoC.
    rewrite (IH c t).
    replace (0 + d)%nat with d by lia.
    ring.
Qed.

Definition stepdeg (st : okstep) : nat :=
  match st with OKQuad _ => 2%nat | OKPrime d _ _ => d end.

Definition stepelt (st : okstep) : C :=
  match st with OKQuad s => RtoC s | OKPrime _ _ r => RtoC r end.

Definition stepdt (st : okstep) : list C :=
  match st with
  | OKQuad s => RtoC (- (s * s)) :: C0 :: nil
  | OKPrime d c _ => map (fun i => RtoC (c i)) (seq 0 d)
  end.

Lemma okstep_facts : forall (st : okstep) (L' : list okstep),
  okwf 2 (st :: L') ->
  is_Csubfield (Btow L') ->
  (forall x : R, oktower L' x -> Btow L' (RtoC x)) ->
  (2 <= stepdeg st)%nat /\ (stepdeg st <= 5)%nat /\
  length (stepdt st) = stepdeg st /\
  Forall (Btow L') (stepdt st) /\
  (cpeval (stepdt st) (stepelt st) + Cpow (stepelt st) (stepdeg st))%C = C0 /\
  okwf 2 L'.
Proof.
  intros st L' W HB' HCB'.
  destruct st as [s | d c r]; cbn [okwf] in W;
    cbn [stepdeg stepelt stepdt].
  - destruct W as [Wss W'].
    refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))));
      try lia; try exact W'; try reflexivity.
    + constructor.
      * apply HCB'.
        apply subfield_opp;
          [apply (oktower_subfield 2 L' W') | exact Wss].
      * constructor; [| constructor].
        assert (H0 : RtoC 0 = C0) by reflexivity.
        rewrite <- H0.
        apply HCB'.
        apply (oktower_contains_rational 2 L' W').
        exists 0%Z, 1%Z. split; [lia | cbn; field].
    + cbn [cpeval Cpow].
      assert (Hm : RtoC (- (s * s)) = (C0 - RtoC s * RtoC s)%C).
      { assert (Hz : (- (s * s))%R = (0 - s * s)%R) by ring.
        rewrite Hz, RtoC_sub_c, RtoC_mul. reflexivity. }
      rewrite Hm. ring.
  - destruct W as [Hd2 [Hd5 [Hmem [Hrel W']]]].
    refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))));
      try lia; try exact W'.
    + rewrite length_map, length_seq. reflexivity.
    + apply Forall_map_intro. intros i Hi.
      apply in_seq in Hi.
      apply HCB'. apply Hmem. lia.
    + rewrite <- fsum_cpeval.
      rewrite Cpow_RtoC.
      rewrite <- RtoC_add.
      rewrite Hrel.
      reflexivity.
Qed.

Lemma Btow_facts : forall (L : list okstep),
  okwf 2 L ->
  is_Csubfield (Btow L) /\
  (forall z, CQ z -> Btow L z) /\
  (forall x : R, oktower L x -> Btow L (RtoC x)).
Proof.
  induction L as [|st L' IH]; intro W.
  - refine (conj _ (conj _ _)).
    + exact CQ_subfield.
    + intros z Hz. exact Hz.
    + intros x Hx. exists x. split; [exact Hx | reflexivity].
  - assert (W' : okwf 2 L').
    { destruct st as [s | d c r]; cbn [okwf] in W; tauto. }
    destruct (IH W') as [HB' [HQB' HCB']].
    destruct (okstep_facts st L' W HB' HCB')
      as [Hd2 [Hd5 [Hldt [Hfdt [Hrel _]]]]].
    assert (HBtow_eq : Btow (st :: L')
                       = CPolyF (Btow L') (stepdeg st) (stepelt st)).
    { destruct st as [s | d c r]; reflexivity. }
    assert (HBsub : is_Csubfield (Btow (st :: L'))).
    { rewrite HBtow_eq.
      apply (CPolyF_Csubfield (Btow L') (stepelt st) (stepdeg st)
               (stepdt st) HB' ltac:(lia) Hldt Hfdt Hrel). }
    assert (Hcont : forall z, Btow L' z -> Btow (st :: L') z).
    { rewrite HBtow_eq.
      apply (CPolyF_contains (Btow L') (stepelt st) (stepdeg st)
               (stepdt st) HB' ltac:(lia) Hldt Hfdt Hrel). }
    refine (conj _ (conj _ _)).
    + exact HBsub.
    + intros z Hz. apply Hcont. apply HQB'. exact Hz.
    + intros x Hx.
      destruct st as [s | d c r]; cbn [Btow oktower] in *.
      * destruct Hx as [p [q [Hp [Hq Hx]]]].
        exists (RtoC p :: RtoC q :: nil).
        refine (conj _ (conj _ _)); [reflexivity | |].
        -- constructor; [exact (HCB' p Hp) |].
           constructor; [exact (HCB' q Hq) | constructor].
        -- rewrite Hx.
           cbn [cpeval].
           rewrite RtoC_add, RtoC_mul.
           ring.
      * destruct Hx as [cf [Hcf Hx]].
        exists (map (fun i => RtoC (cf i)) (seq 0 d)).
        refine (conj _ (conj _ _)).
        -- rewrite length_map, length_seq. reflexivity.
        -- apply Forall_map_intro. intros i Hi.
           apply in_seq in Hi.
           apply HCB'. apply Hcf. lia.
        -- rewrite Hx.
           rewrite fsum_cpeval. reflexivity.
Qed.

Section WitnessKeystone.

Variable rho : list C.
Variable wroot : C.
Hypothesis Hnd : NoDup rho.
Hypothesis Hlen6 : length rho = 6%nat.
Hypothesis Hsplit : forall z,
  cpeval (map castZ witFz) z = (C1 * prod_linear rho z)%C.
Hypothesis Hw4 : nth 4 rho C0 = wroot.
Hypothesis Hw5 : nth 5 rho C0 = Cconj wroot.
Hypothesis Hreals03 : forall i, (i < 4)%nat ->
  exists xr : R, nth i rho C0 = RtoC xr.

Lemma Hroots_all : forall r, In r rho -> cpeval (map castZ witFz) r = C0.
Proof.
  intros r Hr.
  rewrite (Hsplit r).
  rewrite (prod_linear_root rho r Hr r eq_refl).
  ring.
Qed.

Definition levelpack (B : C -> Prop) (rs : list C) (js : list nat)
           (K : C -> Prop) (sigmas : list (C -> C))
           (Perm : list (list nat)) : Prop :=
  RootChain B rho rs js K /\ incl rho rs /\
  length sigmas = prodl js /\
  (forall i, (i < prodl js)%nat ->
     CCembeds K (nth i sigmas (fun z => z)) /\
     (forall x, B x -> nth i sigmas (fun z => z) x = x)) /\
  pgroup Perm /\ length Perm = prodl js /\
  (forall m, (m < prodl js)%nat -> forall i, (i < 6)%nat ->
     (nth i (nth m Perm pid6) 0%nat < 6)%nat /\
     nth (nth i (nth m Perm pid6) 0%nat) rho C0
     = nth m sigmas (fun z => z) (nth i rho C0)) /\
  (forall tau, CCembeds K tau -> (forall x, B x -> tau x = x) ->
     exists m, (m < prodl js)%nat /\
       forall i, (i < 6)%nat ->
         tau (nth i rho C0) = nth (nth i (nth m Perm pid6) 0%nat) rho C0).

Lemma level_package : forall (B : C -> Prop),
  is_Csubfield B -> (forall z, CQ z -> B z) ->
  exists rs js K sigmas Perm, levelpack B rs js K sigmas Perm.
Proof.
  intros B HB HQB.
  destruct (build_chain B rho HB Hlen6 Hroots_all HQB rho (incl_refl rho))
    as [rs [js [K [Hch Hin]]]].
  destruct (RootChain_embeddings B rho (map castZ witFz) C1 HB Hnd C1_neq_C0
              Hsplit (FcfB_g B HQB)
              ltac:(rewrite length_map, Hlen6; reflexivity)
              rs js K Hch)
    as [sigmas [Hlsig [Hwf [Hcomp Hdist]]]].
  destruct (perm_group_of_embeddings B K rho (map castZ witFz) C1 rs js
              sigmas (prodl js)
              HB Hnd Hlen6 C1_neq_C0 Hsplit
              ltac:(apply Forall_map_intro; intros n _; unfold castZ;
                    apply CQ_IZR)
              HQB Hch Hin Hlsig Hwf Hcomp Hdist)
    as [Perm [HlP [HPg [Hspec Hpcomp]]]].
  exists rs, js, K, sigmas, Perm.
  unfold levelpack.
  exact (conj Hch (conj Hin (conj Hlsig (conj Hwf
           (conj HPg (conj HlP (conj Hspec Hpcomp))))))).
Qed.

Lemma level_incl :
  forall (B B' : C -> Prop) rs js K rs' js' K' sigmas sigmas' Perm Perm',
  is_Csubfield B -> is_Csubfield B' ->
  (forall z, B z -> B' z) ->
  levelpack B rs js K sigmas Perm ->
  levelpack B' rs' js' K' sigmas' Perm' ->
  incl Perm' Perm.
Proof.
  intros B B' rs js K rs' js' K' sigmas sigmas' Perm Perm'
         HB HB' HBB'
         [Hch [Hin [Hlsig [Hwf [HPg [HlP [Hspec Hpcomp]]]]]]]
         [Hch' [Hin' [Hlsig' [Hwf' [HPg' [HlP' [Hspec' Hpcomp']]]]]]].
  assert (HKK' : forall x, K x -> K' x).
  { apply (RootChain_contained B rho rs js K K' HB Hch
             (RootChain_subfield B' rho rs' js' K' HB' Hch')).
    - intros x Hx.
      apply (RootChain_incl B' rho rs' js' K' HB' Hch').
      apply HBB'. exact Hx.
    - intros r Hr.
      apply (RootChain_roots_in B' rho rs' js' K' HB' Hch').
      apply Hin'.
      apply (RootChain_rs_in_rho B rho rs js K Hch).
      exact Hr. }
  intros p' Hp'.
  destruct (In_nth Perm' p' pid6 Hp') as [m [Hm Hnthm]].
  rewrite HlP' in Hm.
  destruct (Hwf' m Hm) as [Hsg_emb Hsg_fix].
  assert (Hsg_K : CCembeds K (nth m sigmas' (fun z => z)))
    by (apply (CCembeds_mono K K' _ HKK' Hsg_emb)).
  assert (Hsg_fixB : forall x, B x -> nth m sigmas' (fun z => z) x = x)
    by (intros x Hx; apply Hsg_fix; apply HBB'; exact Hx).
  destruct (Hpcomp _ Hsg_K Hsg_fixB) as [m2 [Hm2 Hvals]].
  set (pm := nth m2 Perm pid6).
  assert (Hpm_in : In pm Perm)
    by (apply nth_In; rewrite HlP; exact Hm2).
  assert (Hpm_S6 : In pm S6list) by (exact (pg_S6 Perm HPg pm Hpm_in)).
  assert (Hp'_S6 : In p' S6list).
  { rewrite <- Hnthm.
    apply (pg_S6 Perm' HPg').
    apply nth_In. rewrite HlP'. exact Hm. }
  assert (Hpeq : p' = pm).
  { apply (nth_ext p' pm 0%nat 0%nat).
    - rewrite (S6_length6 p' Hp'_S6), (S6_length6 pm Hpm_S6).
      reflexivity.
    - intros i Hi.
      rewrite (S6_length6 p' Hp'_S6) in Hi.
      assert (Hvi : nth (nth i p' 0%nat) rho C0
                    = nth (nth i pm 0%nat) rho C0).
      { destruct (Hspec' m Hm i Hi) as [Hb' He'].
        rewrite Hnthm in He'.
        rewrite He'.
        symmetry.
        pose proof (Hvals i Hi) as Hv.
        fold pm in Hv.
        rewrite <- Hv.
        reflexivity. }
      apply (proj1 (NoDup_nth rho C0) Hnd).
      + rewrite Hlen6.
        rewrite <- Hnthm.
        exact (proj1 (Hspec' m Hm i Hi)).
      + rewrite Hlen6.
        exact (S6_entries_lt pm Hpm_S6 i Hi).
      + exact Hvi. }
  rewrite Hpeq. exact Hpm_in.
Qed.

Lemma level_step_bound :
  forall (B : C -> Prop) (st : okstep) rs js K sigmas Perm
         rs' js' K' sigmas' Perm',
  is_Csubfield B -> (forall z, CQ z -> B z) ->
  (2 <= stepdeg st)%nat -> (stepdeg st <= 5)%nat ->
  length (stepdt st) = stepdeg st ->
  Forall B (stepdt st) ->
  (cpeval (stepdt st) (stepelt st) + Cpow (stepelt st) (stepdeg st))%C = C0 ->
  levelpack B rs js K sigmas Perm ->
  levelpack (CPolyF B (stepdeg st) (stepelt st)) rs' js' K' sigmas' Perm' ->
  (length Perm <= 5 * length Perm')%nat.
Proof.
  intros B st rs js K sigmas Perm rs' js' K' sigmas' Perm'
         HB HQB Hd2 Hd5 Hldt Hfdt Hrel
         [Hch [Hin [_ [_ [_ [HlP [_ _]]]]]]]
         [Hch' [Hin' [_ [_ [_ [HlP' [_ _]]]]]]].
  rewrite HlP, HlP'.
  assert (Hrt : exists rt : list R,
    length rt = stepdeg st /\ map RtoC rt = stepdt st).
  { destruct st as [s | d c r]; cbn [stepdeg stepdt].
    - exists ((- (s * s))%R :: 0%R :: nil).
      split; [reflexivity | reflexivity].
    - exists (map c (seq 0 d)).
      split.
      + rewrite length_map, length_seq. reflexivity.
      + rewrite map_map. reflexivity. }
  destruct Hrt as [rt [Hlrt Hmrt]].
  assert (Hstep_le : (prodl js <= stepdeg st * prodl js')%nat).
  { apply (tower_step_descent B rho (map castZ witFz) C1 rt (stepdeg st)
             (stepelt st) rs js K rs' js' K' HB Hnd C1_neq_C0 Hsplit
             (FcfB_g B HQB)
             ltac:(rewrite length_map, Hlen6; reflexivity)
             ltac:(apply Forall_map_intro; intros n _; unfold castZ;
                   apply CQ_IZR)
             HQB Hd2 Hd5 Hlrt
             ltac:(rewrite Hmrt; exact Hfdt)
             ltac:(rewrite Hmrt; exact Hrel)
             Hch Hin Hch' Hin'). }
  apply (Nat.le_trans _ (stepdeg st * prodl js')%nat); [exact Hstep_le |].
  apply Nat.mul_le_mono_r. exact Hd5.
Qed.

Lemma witness_base_pack :
  exists rsW jsW KW sigW PermW,
    levelpack CQ rsW jsW KW sigW PermW /\ incl S6list PermW.
Proof.
  set (r1W := nth 4 rho C0).
  set (r2W := nth 5 rho C0).
  assert (Hr1_in : In r1W rho) by (apply nth_In; lia).
  assert (Hr2_in : In r2W rho) by (apply nth_In; lia).
  destruct (witness_chain_shape rho r1W r2W Hlen6 Hroots_all Hr1_in Hr2_in)
    as [j2 [dt1 [dt2 [rs3 [js3 [KW [Hl1 [Hf1 [Hrel1 [Hi1
        [Hj21 [Hj26 [Hl2 [Hf2 [Hrel2 [Hi2 [Hch3 [Hch Hincl]]]]]]]]]]]]]]]]]].
  assert (Hne12 : r1W <> r2W).
  { intro E.
    pose proof (proj1 (NoDup_nth rho C0) Hnd 4%nat 5%nat
                  ltac:(lia) ltac:(lia) E) as Hc.
    lia. }
  assert (Hj2_5 : j2 = 5%nat).
  { apply (witness_j2_five rho r1W r2W j2 dt1 dt2 Hroots_all
             Hr1_in Hr2_in Hne12 Hl1 Hf1 Hrel1 Hi1 Hj21 Hj26 Hl2 Hf2
             Hrel2 Hi2). }
  subst j2.
  rewrite Hj2_5 in Hch, Hch3, Hrel2, Hi2.
  destruct (RootChain_embeddings CQ rho (map castZ witFz) C1 CQ_subfield
              Hnd C1_neq_C0 Hsplit (FcfB_g CQ (fun z Hz => Hz))
              ltac:(rewrite length_map, Hlen6; reflexivity)
              _ _ KW Hch)
    as [sigW [HlsigW [HwfW [HcompW HdistW]]]].
  destruct (perm_group_of_embeddings CQ KW rho (map castZ witFz) C1
              _ _ sigW (prodl (6%nat :: 5%nat :: js3))
              CQ_subfield Hnd Hlen6 C1_neq_C0 Hsplit
              ltac:(apply Forall_map_intro; intros n _; unfold castZ;
                    apply CQ_IZR)
              (fun z Hz => Hz) Hch Hincl
              HlsigW HwfW HcompW HdistW)
    as [PermW [HlPW [HPgW [HspecW HpcompW]]]].
  (* the conjugation permutation *)
  destruct (HpcompW Cconj (Cconj_embeds KW)
              (fun z Hz => Cconj_fixes_CQ z Hz)) as [mc [Hmc Hcvals]].
  set (pmc := nth mc PermW pid6).
  assert (Hpmc_in : In pmc PermW)
    by (apply nth_In; rewrite HlPW; exact Hmc).
  assert (Hpmc_S6 : In pmc S6list)
    by (exact (pg_S6 PermW HPgW pmc Hpmc_in)).
  assert (Hidx : forall i k, (i < 6)%nat -> (k < 6)%nat ->
    Cconj (nth i rho C0) = nth k rho C0 -> nth i pmc 0%nat = k).
  { intros i k Hi Hk He.
    pose proof (Hcvals i Hi) as Hv.
    fold pmc in Hv.
    rewrite He in Hv.
    apply (proj1 (NoDup_nth rho C0) Hnd);
      [rewrite Hlen6; exact (S6_entries_lt pmc Hpmc_S6 i Hi)
      | rewrite Hlen6; exact Hk
      | symmetry; exact Hv]. }
  assert (Hpmc_eq : pmc = transp 4 5).
  { rewrite transp45_val.
    apply (nth_ext pmc _ 0%nat 0%nat).
    - rewrite (S6_length6 pmc Hpmc_S6). reflexivity.
    - intros i Hi.
      rewrite (S6_length6 pmc Hpmc_S6) in Hi.
      destruct i as [|[|[|[|[|[|?]]]]]]; try lia.
      + destruct (Hreals03 0%nat ltac:(lia)) as [xr Hxr].
        cbn [nth].
        apply (Hidx 0%nat 0%nat ltac:(lia) ltac:(lia)).
        rewrite Hxr. apply Cconj_RtoC.
      + destruct (Hreals03 1%nat ltac:(lia)) as [xr Hxr].
        cbn [nth].
        apply (Hidx 1%nat 1%nat ltac:(lia) ltac:(lia)).
        rewrite Hxr. apply Cconj_RtoC.
      + destruct (Hreals03 2%nat ltac:(lia)) as [xr Hxr].
        cbn [nth].
        apply (Hidx 2%nat 2%nat ltac:(lia) ltac:(lia)).
        rewrite Hxr. apply Cconj_RtoC.
      + destruct (Hreals03 3%nat ltac:(lia)) as [xr Hxr].
        cbn [nth].
        apply (Hidx 3%nat 3%nat ltac:(lia) ltac:(lia)).
        rewrite Hxr. apply Cconj_RtoC.
      + cbn [nth].
        apply (Hidx 4%nat 5%nat ltac:(lia) ltac:(lia)).
        rewrite Hw4, Hw5. reflexivity.
      + cbn [nth].
        apply (Hidx 5%nat 4%nat ltac:(lia) ltac:(lia)).
        rewrite Hw4, Hw5. apply Cconj_invol. }
  assert (Ht45 : In (transp 4 5) PermW)
    by (rewrite <- Hpmc_eq; exact Hpmc_in).
  (* the base case *)
  assert (HS6 : incl S6list PermW).
  { apply (base_case_S6 rho dt1 dt2 rs3 js3 KW PermW
             (prodl (6%nat :: 5%nat :: js3))
             Hnd Hlen6 Hroots_all Hsplit Hl1 Hf1 Hrel1 Hi1 Hj2_5 Hf2 Hrel2
             Hi2 Hch3 HPgW HpcompW HlPW Ht45). }
  exists (r1W :: r2W :: rs3), (6%nat :: 5%nat :: js3), KW, sigW, PermW.
  unfold levelpack.
  exact (conj (conj Hch (conj Hincl (conj HlsigW (conj HwfW
                (conj HPgW (conj HlPW (conj HspecW HpcompW)))))))
              HS6).
Qed.

Lemma tower_descent : forall (L : list okstep),
  okwf 2 L ->
  exists rs js K sigmas Perm,
    levelpack (Btow L) rs js K sigmas Perm /\
    incl A6list Perm.
Proof.
  induction L as [|st L' IH]; intro W.
  - destruct (level_package CQ CQ_subfield (fun z Hz => Hz))
      as [rs [js [K [sigmas [Perm Hpk]]]]].
    exists rs, js, K, sigmas, Perm.
    split; [exact Hpk |].
    destruct witness_base_pack
      as [rsW [jsW [KW [sigW [PermW [HpkW HS6W]]]]]].
    intros p Hp.
    apply (level_incl CQ CQ rs js K rsW jsW KW sigmas sigW Perm PermW
             CQ_subfield CQ_subfield (fun z Hz => Hz) Hpk HpkW).
    apply HS6W.
    apply A6_sub_S6.
    exact Hp.
  - assert (W' : okwf 2 L').
    { destruct st as [s | d c r]; cbn [okwf] in W; tauto. }
    destruct (IH W') as [rs' [js' [K' [sigmas' [Perm' [Hpk' HA6']]]]]].
    destruct (Btow_facts L' W') as [HB' [HQB' HCB']].
    destruct (Btow_facts (st :: L') W) as [HB [HQB HCB]].
    destruct (level_package (Btow (st :: L')) HB HQB)
      as [rs [js [K [sigmas [Perm Hpk]]]]].
    exists rs, js, K, sigmas, Perm.
    split; [exact Hpk |].
    destruct (okstep_facts st L' W HB' HCB')
      as [Hd2 [Hd5 [Hldt [Hfdt [Hrel _]]]]].
    assert (HBtow_eq : Btow (st :: L')
                       = CPolyF (Btow L') (stepdeg st) (stepelt st)).
    { destruct st as [s | d c r]; reflexivity. }
    assert (Hincl : incl Perm Perm').
    { apply (level_incl (Btow L') (Btow (st :: L'))
               rs' js' K' rs js K sigmas' sigmas Perm' Perm
               HB' HB); [| exact Hpk' | exact Hpk].
      rewrite HBtow_eq.
      apply (CPolyF_contains (Btow L') (stepelt st) (stepdeg st)
               (stepdt st) HB' ltac:(lia) Hldt Hfdt Hrel). }
    assert (Hidx : (length Perm' <= 5 * length Perm)%nat).
    { apply (level_step_bound (Btow L') st rs' js' K' sigmas' Perm'
               rs js K sigmas Perm HB' HQB' Hd2 Hd5 Hldt Hfdt Hrel Hpk').
      rewrite <- HBtow_eq. exact Hpk. }
    destruct Hpk' as [_ [_ [_ [_ [HPg' [_ [_ _]]]]]]].
    destruct Hpk as [_ [_ [_ [_ [HPg [_ [_ _]]]]]]].
    pose proof (between_A6_S6 Perm' HPg' HA6') as Hcase'.
    exact (sandwich_contains A6list S6list A6_sub_S6 Perm
             (chain_step_perm Perm' Perm HPg' HPg Hincl Hidx Hcase')).
Qed.

Lemma witness_root_blocked : forall x : R,
  pevalR (map IZR witFz) x = 0 -> ~ OrigamiNum2 x.
Proof.
  intros x Hx HON2.
  assert (HxC : cpeval (map castZ witFz) (RtoC x) = C0).
  { rewrite castZ_as_RtoC, cpeval_map_RtoC_global, CevalR_RtoC.
    rewrite Hx. reflexivity. }
  assert (Hx_in : In (RtoC x) rho).
  { apply prod_linear_zero_in.
    pose proof (Hsplit (RtoC x)) as Hs.
    rewrite HxC in Hs.
    assert (Hs2 : prod_linear rho (RtoC x)
                  = (C1 * prod_linear rho (RtoC x))%C) by ring.
    rewrite Hs2, <- Hs. reflexivity. }
  destruct (In_nth rho (RtoC x) C0 Hx_in) as [ix [Hix Hnthix]].
  rewrite Hlen6 in Hix.
  apply Origami2_in_ONK_2 in HON2.
  destruct (ONK_in_oktower 2 ltac:(lia) x HON2) as [L [W T]].
  destruct (tower_descent L W)
    as [rs [js [K [sigmas [Perm [Hpk HA6]]]]]].
  destruct (Btow_facts L W) as [HBL [HQBL HCBL]].
  assert (HxB : Btow L (RtoC x)) by (apply HCBL; exact T).
  destruct Hpk as [Hch [Hin [Hlsig [Hwf [HPg [HlP [Hspec Hpcomp]]]]]]].
  assert (Hfix : forall pm, In pm Perm -> nth ix pm 0%nat = ix).
  { intros pm Hpm.
    destruct (In_nth Perm pm pid6 Hpm) as [m [Hm Hnthm]].
    rewrite HlP in Hm.
    destruct (Hspec m Hm ix Hix) as [Hb He].
    rewrite Hnthm in Hb, He.
    destruct (Hwf m Hm) as [_ Hfixm].
    rewrite Hnthix in He.
    rewrite (Hfixm (RtoC x) HxB) in He.
    rewrite <- Hnthix in He.
    apply (proj1 (NoDup_nth rho C0) Hnd);
      [rewrite Hlen6; exact Hb | rewrite Hlen6; exact Hix | exact He]. }
  set (p0 := (1 :: 2 :: 0 :: 4 :: 5 :: 3 :: nil)%nat).
  assert (Hp0_A6 : In p0 A6list)
    by (apply memb_spec; vm_compute; reflexivity).
  assert (Hp0_moves : nth ix p0 0%nat <> ix).
  { unfold p0.
    destruct ix as [|[|[|[|[|[|?]]]]]]; cbn [nth]; lia. }
  apply Hp0_moves.
  apply Hfix.
  apply HA6.
  exact Hp0_A6.
Qed.

End WitnessKeystone.

(** THE KEYSTONE, fully assembled. *)
Theorem witness_sextic_outside_ON2 :
  (exists x : R, pevalR (map IZR witFz) x = 0) /\
  (forall x : R, pevalR (map IZR witFz) x = 0 -> ~ OrigamiNum2 x).
Proof.
  destruct witness_rho_exists
    as [r1 [r2 [r3 [r4 [w [H12 [H23 [H34 [Hwim [Hreals [Hsplit Hnd]]]]]]]]]]].
  set (rho := RtoC r1 :: RtoC r2 :: RtoC r3 :: RtoC r4
              :: w :: Cconj w :: nil) in *.
  assert (Hlen6 : length rho = 6%nat) by reflexivity.
  split.
  { exists r1.
    apply RtoC_inj.
    rewrite <- CevalR_RtoC, <- cpeval_map_RtoC_global, <- castZ_as_RtoC.
    apply Hreals. left. reflexivity. }
  intros x Hx.
  apply (witness_root_blocked rho w Hnd Hlen6 Hsplit
           ltac:(reflexivity) ltac:(reflexivity)
           ltac:(intros i Hi;
                 destruct i as [|[|[|[|?]]]]; try lia;
                 [exists r1 | exists r2 | exists r3 | exists r4];
                 reflexivity)
           x Hx).
Qed.

