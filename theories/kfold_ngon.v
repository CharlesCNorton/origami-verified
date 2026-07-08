(* Companion to "Regular Polygons by k-Fold Origami: An Exact Characterization"
   (C. C. Norton): each numbered result restated under the paper's names and
   discharged by the development, supporting lemmas type-checked by Check, the
   axiom footprint of the main theorem printed at the end. *)

From Stdlib Require Import Reals List ZArith Lia.
From Stdlib Require Znumtheory.
Import ListNotations.
Require Import foundations cyclotomic geometry frontier.
Open Scope R_scope.

(* ===== Section 2.  The hierarchy of k-fold origami numbers ===== *)

(** Definition 2.1: the class [OrigamiNumK] with root constructor [ONK_proot]. *)
Notation kfold_number := OrigamiNumK (only parsing).
Check OrigamiNumK.
Check ONK_proot.

(** Proposition 2.2: the bottom three levels are the classical fold classes. *)
Theorem prop_2_2_single_fold : forall x, kfold_number 1 x <-> OrigamiNum x.
Proof. exact OrigamiNumK_1_iff. Qed.

Theorem prop_2_2_two_fold : forall x, kfold_number 2 x <-> OrigamiNum2 x.
Proof. exact OrigamiNumK_2_iff. Qed.

Theorem prop_2_2_three_fold : forall x, kfold_number 3 x <-> OrigamiNum3 x.
Proof. exact OrigamiNumK_3_iff. Qed.

(* ===== Section 3.  The geometric substrate ===== *)

(** Theorem 3.1: k coupled creases over a monic degree-(2k+1) polynomial produce a real root. *)
Theorem thm_3_1_coupled_lill_solves :
  forall k (a : nat -> R) gs, (1 <= k)%nat -> a (2 * k + 1)%nat = 1 ->
  general_lill k a gs ->
  exists t, fsum (S (2 * k + 1)) (fun i => a i * t ^ i) = 0.
Proof. exact general_lill_solves. Qed.

(** Theorem 3.2: in the Bring-Jerrard family with q <> 0, every real root arises from an explicit crease configuration of normal (1, -t). *)
Theorem thm_3_2_bring_jerrard_realizable :
  forall k p q t, (1 <= k)%nat ->
  t ^ (2 * k + 1) + p * t + q = 0 -> q <> 0 ->
  k_fold_lill k p q
    (fun i => {| A := 1; B := - t; C := - (1 + (-1) ^ i * t ^ (2 * i + 2)) |}).
Proof. exact k_fold_lill_realizable. Qed.

(** Section 3: Beloch-pencil presentation with quintic and septic instances. *)
Check k_fold_lill_solves.
Check twofold_reflects_quintic.
Check three_fold_lill_septic.

(** Section 3 axiom bridge: the on_line and line_perp alignments of [k_fold_lill] and [general_lill] are the Huzita O1 and O4 fold relations. *)
Theorem fold_O1_line_through : forall p1 p2,
  fold_line (fold_O1 p1 p2) = line_through p1 p2.
Proof. reflexivity. Qed.

Theorem fold_O4_perp_incident : forall p l,
  line_perp (fold_line (fold_O4 p l)) l /\ on_line p (fold_line (fold_O4 p l)).
Proof.
  intros p l. rewrite fold_line_O4.
  split; [ apply perp_through_perp | apply perp_through_incident ].
Qed.

(* ===== Section 4.  The main theorem ===== *)

(** Theorem 4.1: the regular n-gon is k-fold constructible iff every prime factor of phi(n) is at most 2k+1. *)
Theorem thm_4_1_kfold_ngon :
  forall k, (1 <= k)%nat -> forall n, (3 <= n)%nat ->
  (kfold_number k (cos (2 * PI / INR n)) <-> smooth_upto (2 * k + 1) (euler_phi n)).
Proof. exact ngon_k_fold_iff. Qed.

(** Theorem 4.1 sufficiency: smooth totient gives constructible cos and sin. *)
Theorem thm_4_1_sufficiency :
  forall k, (1 <= k)%nat -> forall n, (1 <= n)%nat ->
  smooth_upto (2 * k + 1) (euler_phi n) ->
  kfold_number k (cos (2 * PI / INR n)) /\ kfold_number k (sin (2 * PI / INR n)).
Proof. exact cos_sin_smoothK. Qed.

(** Theorem 4.1 necessity: a prime factor of phi(n) above 2k+1 rules out k-fold constructibility. *)
Theorem thm_4_1_necessity :
  forall k, (1 <= k)%nat -> forall n m, (3 <= n)%nat ->
  (euler_phi n = 2 * m)%nat -> ~ smooth_upto (2 * k + 1) m ->
  ~ kfold_number k (cos (2 * PI / INR n)).
Proof. exact cos_2pi_n_not_k_fold. Qed.

(** Theorem 4.2: the exact cosine degree [Q(2cos 2pi/n) : Q] = phi(n)/2. *)
Theorem thm_4_2_cosine_degree :
  forall n k, (3 <= n)%nat -> (euler_phi n = 2 * k)%nat ->
  basis is_rational (powers (2 * cos (2 * PI / INR n)) k)
                    (Qx (2 * cos (2 * PI / INR n))).
Proof. exact cos_2pi_n_degree_exactly. Qed.

(** Theorem 4.3: every k-fold origami number has degree over Q with all prime factors at most 2k+1. *)
Theorem thm_4_3_smooth_degree_bound :
  forall k, (1 <= k)%nat -> forall x, kfold_number k x ->
  exists d, basis is_rational (powers x d) (Qx x) /\ smooth_upto (2 * k + 1) d.
Proof. exact OrigamiNumK_field_degree_smooth. Qed.

(* ===== Section 4.3.  Corollaries ===== *)

(** Corollary 4.7: every regular polygon is constructible at some fold level. *)
Theorem cor_4_7_exhaustion : forall n, (3 <= n)%nat ->
  exists k, (1 <= k)%nat /\ kfold_number k (cos (2 * PI / INR n)).
Proof.
  intros n Hn.
  exists (euler_phi n).
  assert (Hpos : (1 <= euler_phi n)%nat) by (apply euler_phi_pos; lia).
  split; [exact Hpos |].
  apply (proj2 (ngon_k_fold_iff (euler_phi n) Hpos n Hn)).
  apply smooth_upto_of_le; lia.
Qed.

(** Corollary 4.5: k is the minimal fold budget of the n-gon iff 2k+1 is the smoothness threshold of phi(n), smooth at 2k+1 and not below. *)
Theorem cor_4_5_minimal_budget : forall n k, (3 <= n)%nat -> (1 <= k)%nat ->
  ( kfold_number k (cos (2 * PI / INR n)) /\
    (forall j, (1 <= j < k)%nat -> ~ kfold_number j (cos (2 * PI / INR n))) )
  <->
  ( smooth_upto (2 * k + 1) (euler_phi n) /\
    (forall j, (1 <= j < k)%nat -> ~ smooth_upto (2 * j + 1) (euler_phi n)) ).
Proof.
  intros n k Hn Hk. split; intros [H1 H2]; split.
  - apply (ngon_k_fold_iff k Hk n Hn); exact H1.
  - intros j Hj Hs. apply (H2 j Hj).
    apply (proj2 (ngon_k_fold_iff j ltac:(lia) n Hn)); exact Hs.
  - apply (proj2 (ngon_k_fold_iff k Hk n Hn)); exact H1.
  - intros j Hj HO. apply (H2 j Hj).
    apply (ngon_k_fold_iff j ltac:(lia) n Hn); exact HO.
Qed.

(** Corollary 4.6 smoothness helpers for the first-polygon budgets. *)
Lemma dvd_le_q : forall q d, (1 <= d)%nat -> Nat.divide q d -> (q <= d)%nat.
Proof. intros q d Hd H. apply Nat.divide_pos_le; [lia | exact H]. Qed.

Lemma prime_Z_23 : Znumtheory.prime (Z.of_nat 23).
Proof.
  change (Z.of_nat 23) with 23%Z. apply Znumtheory.prime_intro; [lia |].
  intros n Hn. apply Znumtheory.Zgcd_1_rel_prime.
  assert (Hc : (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7
                \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13
                \/ n = 14 \/ n = 15 \/ n = 16 \/ n = 17 \/ n = 18 \/ n = 19
                \/ n = 20 \/ n = 21 \/ n = 22)%Z) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]]]]]]]]; reflexivity.
Qed.

Lemma smooth_5_10 : smooth_upto 5 10.
Proof.
  intros q Hq Hd. change 10%nat with (2 * 5)%nat in Hd.
  destruct (nat_prime_mult q 2 5 Hq Hd) as [H|H]; apply dvd_le_q in H; lia.
Qed.

Lemma smooth_7_28 : smooth_upto 7 28.
Proof.
  intros q Hq Hd. change 28%nat with (2 * (2 * 7))%nat in Hd.
  destruct (nat_prime_mult q 2 (2 * 7) Hq Hd) as [H|H]; [apply dvd_le_q in H; lia |].
  destruct (nat_prime_mult q 2 7 Hq H) as [H2|H7]; apply dvd_le_q in H2 || apply dvd_le_q in H7; lia.
Qed.

Lemma smooth_11_22 : smooth_upto 11 22.
Proof.
  intros q Hq Hd. change 22%nat with (2 * 11)%nat in Hd.
  destruct (nat_prime_mult q 2 11 Hq Hd) as [H|H]; apply dvd_le_q in H; lia.
Qed.

Lemma smooth_23_46 : smooth_upto 23 46.
Proof.
  intros q Hq Hd. change 46%nat with (2 * 23)%nat in Hd.
  destruct (nat_prime_mult q 2 23 Hq Hd) as [H|H]; apply dvd_le_q in H; lia.
Qed.

Lemma smooth_11_198 : smooth_upto 11 198.
Proof.
  intros q Hq Hd. change 198%nat with (2 * (9 * 11))%nat in Hd.
  destruct (nat_prime_mult q 2 (9 * 11) Hq Hd) as [H|H]; [apply dvd_le_q in H; lia |].
  destruct (nat_prime_mult q 9 11 Hq H) as [H9|H11]; apply dvd_le_q in H9 || apply dvd_le_q in H11; lia.
Qed.

Lemma smooth_3_2 : smooth_upto 3 2.
Proof. intros q Hq Hd. apply dvd_le_q in Hd; lia. Qed.

Lemma smooth_3_4 : smooth_upto 3 4.
Proof.
  intros q Hq Hd. change 4%nat with (2 * 2)%nat in Hd.
  destruct (nat_prime_mult q 2 2 Hq Hd) as [H|H]; apply dvd_le_q in H; lia.
Qed.

Lemma smooth_3_6 : smooth_upto 3 6.
Proof.
  intros q Hq Hd. change 6%nat with (2 * 3)%nat in Hd.
  destruct (nat_prime_mult q 2 3 Hq Hd) as [H|H]; apply dvd_le_q in H; lia.
Qed.

(** 11-gon: two folds, not one. *)
Theorem cor_4_6_hendecagon :
  kfold_number 2 (cos (2 * PI / INR 11)) /\ ~ kfold_number 1 (cos (2 * PI / INR 11)).
Proof.
  split.
  - apply (proj2 (ngon_k_fold_iff 2 ltac:(lia) 11 ltac:(lia))). exact smooth_5_10.
  - intro H.
    pose proof (proj1 (ngon_k_fold_iff 1 ltac:(lia) 11 ltac:(lia)) H) as Hs.
    assert (H5 : (5 <= 3)%nat) by (apply Hs; [exact prime_Z_5 | exists 2%nat; reflexivity]).
    lia.
Qed.

(** 29-gon: three folds, not two. *)
Theorem cor_4_6_29gon :
  kfold_number 3 (cos (2 * PI / INR 29)) /\ ~ kfold_number 2 (cos (2 * PI / INR 29)).
Proof.
  split.
  - apply (proj2 (ngon_k_fold_iff 3 ltac:(lia) 29 ltac:(lia))). exact smooth_7_28.
  - intro H.
    pose proof (proj1 (ngon_k_fold_iff 2 ltac:(lia) 29 ltac:(lia)) H) as Hs.
    assert (H7 : (7 <= 5)%nat) by (apply Hs; [exact prime_Z_7 | exists 4%nat; reflexivity]).
    lia.
Qed.

(** 23-gon: five folds, not four. *)
Theorem cor_4_6_23gon :
  kfold_number 5 (cos (2 * PI / INR 23)) /\ ~ kfold_number 4 (cos (2 * PI / INR 23)).
Proof.
  split.
  - apply (proj2 (ngon_k_fold_iff 5 ltac:(lia) 23 ltac:(lia))). exact smooth_11_22.
  - intro H.
    pose proof (proj1 (ngon_k_fold_iff 4 ltac:(lia) 23 ltac:(lia)) H) as Hs.
    assert (H11 : (11 <= 9)%nat) by (apply Hs; [exact prime_Z_11 | exists 2%nat; reflexivity]).
    lia.
Qed.

(** 47-gon: eleven folds, not ten. *)
Theorem cor_4_6_47gon :
  kfold_number 11 (cos (2 * PI / INR 47)) /\ ~ kfold_number 10 (cos (2 * PI / INR 47)).
Proof.
  split.
  - apply (proj2 (ngon_k_fold_iff 11 ltac:(lia) 47 ltac:(lia))). exact smooth_23_46.
  - intro H.
    pose proof (proj1 (ngon_k_fold_iff 10 ltac:(lia) 47 ltac:(lia)) H) as Hs.
    assert (H23 : (23 <= 21)%nat) by (apply Hs; [exact prime_Z_23 | exists 2%nat; reflexivity]).
    lia.
Qed.

(** 199-gon: five folds, not four. *)
Theorem cor_4_6_199gon :
  kfold_number 5 (cos (2 * PI / INR 199)) /\ ~ kfold_number 4 (cos (2 * PI / INR 199)).
Proof.
  split.
  - apply (proj2 (ngon_k_fold_iff 5 ltac:(lia) 199 ltac:(lia))). exact smooth_11_198.
  - intro H.
    pose proof (proj1 (ngon_k_fold_iff 4 ltac:(lia) 199 ltac:(lia)) H) as Hs.
    assert (H11 : (11 <= 9)%nat) by (apply Hs; [exact prime_Z_11 | exists 18%nat; reflexivity]).
    lia.
Qed.

(** 11-gon is the first requiring two folds: every smaller polygon is single-fold constructible. *)
Theorem cor_4_6_first_two_fold :
  kfold_number 2 (cos (2 * PI / INR 11)) /\
  ~ kfold_number 1 (cos (2 * PI / INR 11)) /\
  (forall n, (3 <= n < 11)%nat -> kfold_number 1 (cos (2 * PI / INR n))).
Proof.
  destruct cor_4_6_hendecagon as [H2 H1].
  split; [exact H2 |]. split; [exact H1 |].
  intros n Hn.
  apply (proj2 (ngon_k_fold_iff 1 ltac:(lia) n ltac:(lia))).
  assert (Hc : (n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9
                \/ n = 10)%nat) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]].
  - exact smooth_3_2.
  - exact smooth_3_2.
  - exact smooth_3_4.
  - exact smooth_3_2.
  - exact smooth_3_6.
  - exact smooth_3_4.
  - exact smooth_3_6.
  - exact smooth_3_4.
Qed.

(** 29-gon is the first requiring exactly three folds; smaller polygons are two-fold constructible or beyond three, via Proposition 2.2. *)
Theorem cor_4_6_first_exactly_three :
  kfold_number 3 (cos (2 * PI / INR 29)) /\
  ~ kfold_number 2 (cos (2 * PI / INR 29)) /\
  (forall m, (3 <= m < 29)%nat ->
     kfold_number 2 (cos (2 * PI / INR m)) \/ ~ kfold_number 3 (cos (2 * PI / INR m))).
Proof.
  destruct ngon_29_first_exactly_three_fold as [H3 [H2 Hsmall]].
  split; [apply (proj2 (OrigamiNumK_3_iff _)); exact H3 |].
  split; [intro H; apply H2; apply (proj1 (OrigamiNumK_2_iff _)); exact H |].
  intros m Hm. destruct (Hsmall m Hm) as [HO2 | HnO3].
  - left. apply (proj2 (OrigamiNumK_2_iff _)); exact HO2.
  - right. intro H. apply HnO3. apply (proj1 (OrigamiNumK_3_iff _)); exact H.
Qed.

(** 23-gon is the first requiring five folds: every smaller polygon is four-fold
    constructible, and four folds reach nothing beyond three (Remark 2.4). *)
Lemma smooth_9_le : forall m, (1 <= m <= 9)%nat -> smooth_upto 9 m.
Proof. intros m H. apply smooth_upto_of_le; lia. Qed.

Lemma smooth_9_2 : smooth_upto 9 2. Proof. apply smooth_9_le; lia. Qed.
Lemma smooth_9_4 : smooth_upto 9 4. Proof. apply smooth_9_le; lia. Qed.
Lemma smooth_9_6 : smooth_upto 9 6. Proof. apply smooth_9_le; lia. Qed.
Lemma smooth_9_8 : smooth_upto 9 8. Proof. apply smooth_9_le; lia. Qed.

Lemma smooth_9_10 : smooth_upto 9 10.
Proof. change 10%nat with (2 * 5)%nat. apply smooth_upto_mul; apply smooth_9_le; lia. Qed.

Lemma smooth_9_12 : smooth_upto 9 12.
Proof. change 12%nat with (2 * 6)%nat. apply smooth_upto_mul; apply smooth_9_le; lia. Qed.

Lemma smooth_9_16 : smooth_upto 9 16.
Proof. change 16%nat with (2 * 8)%nat. apply smooth_upto_mul; apply smooth_9_le; lia. Qed.

Lemma smooth_9_18 : smooth_upto 9 18.
Proof. change 18%nat with (2 * 9)%nat. apply smooth_upto_mul; apply smooth_9_le; lia. Qed.

Theorem cor_4_6_first_five :
  kfold_number 5 (cos (2 * PI / INR 23)) /\
  ~ kfold_number 4 (cos (2 * PI / INR 23)) /\
  (forall n, (3 <= n < 23)%nat -> kfold_number 4 (cos (2 * PI / INR n))).
Proof.
  destruct cor_4_6_23gon as [H5 H4].
  split; [exact H5 |]. split; [exact H4 |].
  intros n Hn.
  apply (proj2 (ngon_k_fold_iff 4 ltac:(lia) n ltac:(lia))).
  assert (Hc : (n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9
                \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15
                \/ n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/ n = 21
                \/ n = 22)%nat) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]]]]]].
  - exact smooth_9_2.
  - exact smooth_9_2.
  - exact smooth_9_4.
  - exact smooth_9_2.
  - exact smooth_9_6.
  - exact smooth_9_4.
  - exact smooth_9_6.
  - exact smooth_9_4.
  - exact smooth_9_10.
  - exact smooth_9_4.
  - exact smooth_9_12.
  - exact smooth_9_6.
  - exact smooth_9_8.
  - exact smooth_9_8.
  - exact smooth_9_16.
  - exact smooth_9_6.
  - exact smooth_9_18.
  - exact smooth_9_8.
  - exact smooth_9_12.
  - exact smooth_9_10.
Qed.

(** Section 4.1 sufficiency lemmas: primitive root, Chebyshev rung, composite step, Newton-Vieta rungs. *)
Check primitive_root_gen.
Check cos_2pi_qe_ONK.
Check cos_sin_ONK_mul.
Check sin_ONK_of_cos.
Check esym_K.
Check step_prime_K.
Check tower_cos_prime_rungs.

(** Section 4.3 necessity lemmas: tower assembly and step basis. *)
Check ONK_in_oktower.
Check powers_max_prefix.
Check PolyF_step_basis.
Check oktower_dim.
Check tower_law_div.

(* ===== Axiom footprint ===== *)

Print Assumptions thm_4_1_kfold_ngon.
