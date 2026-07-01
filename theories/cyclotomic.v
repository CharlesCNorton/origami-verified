(* cyclotomic.v -- roots of unity, the cyclotomic polynomial Phi_n over Z and C,
   Dedekind irreducibility, Chebyshev/Dickson, and the cos-degree theory
   [Q(2cos(2pi/n)):Q] = phi(n)/2.  Depends on foundations. *)
From Stdlib Require Import Reals Lra Field R_sqr Psatz Nsatz Ring Ranalysis1 RingMicromega List ProofIrrelevance ClassicalDescription PeanoNat ZArith Classical ClassicalEpsilon Permutation Bool Arith.Wf_nat.
From Stdlib Require Znumtheory.
Import ListNotations.
Require Import foundations.
Import Cardano_C.
Open Scope R_scope.
Definition cos_2pi_11 : R := cos (2 * PI / 11).
Definition sin_2pi_11 : R := sin (2 * PI / 11).

(** Minimal polynomial of cos(2π/11) over Q has degree 5.
    Derived from: 2cos(2π/11) satisfies y^5 + y^4 - 4y^3 - 3y^2 + 3y + 1 = 0.
    Substituting y = 2x gives: 32x^5 + 16x^4 - 32x^3 - 12x^2 + 6x + 1 = 0.
    Monic form: x^5 + (1/2)x^4 - x^3 - (3/8)x^2 + (3/16)x + (1/32) = 0. *)
Definition cos_2pi_11_minpoly (x : R) : R :=
  x^5 + (/2) * x^4 - x^3 - (3/8) * x^2 + (3/16) * x + (/32).
Fixpoint chebyshev_T (n : nat) (x : R) : R :=
  match n with
  | O => 1
  | S O => x
  | S (S m as p) => 2 * x * chebyshev_T p x - chebyshev_T m x
  end.

Lemma chebyshev_rec : forall n x,
  chebyshev_T (S (S n)) x = 2 * x * chebyshev_T (S n) x - chebyshev_T n x.
Proof. reflexivity. Qed.
Lemma chebyshev_cos : forall n θ, chebyshev_T n (cos θ) = cos (INR n * θ).
Proof.
  induction n using (well_founded_induction lt_wf).
  destruct n as [|[|n]].
  - intros. simpl. rewrite Rmult_0_l. symmetry. apply cos_0.
  - intros. simpl. ring_simplify (1 * θ). reflexivity.
  - intros θ. rewrite chebyshev_rec.
    rewrite H by lia. rewrite H by lia.
    repeat rewrite S_INR.
    replace (INR n * θ) with ((INR n + 1) * θ - θ) by ring.
    replace ((INR n + 1 + 1) * θ) with ((INR n + 1) * θ + θ) by ring.
    apply cos_2x_minus.
Qed.

Lemma chebyshev_11_cos_2pi_11 : chebyshev_T 11 cos_2pi_11 = 1.
Proof.
  unfold cos_2pi_11.
  rewrite chebyshev_cos.
  replace (INR 11 * (2 * PI / 11)) with (2 * PI).
  - apply cos_2PI.
  - simpl. field.
Qed.

Definition double_cos_2pi_11 : R := 2 * cos_2pi_11.

Definition minpoly_2cos (y : R) : R :=
  y^5 + y^4 - 4*y^3 - 3*y^2 + 3*y + 1.

Lemma chebyshev_T_11_explicit : forall x,
  chebyshev_T 11 x = 1024*x^11 - 2816*x^9 + 2816*x^7 - 1232*x^5 + 220*x^3 - 11*x.
Proof.
  intros. unfold chebyshev_T. ring.
Qed.

Definition poly_deg11 (y : R) : R :=
  y^11 - 11*y^9 + 44*y^7 - 77*y^5 + 55*y^3 - 11*y - 2.

Lemma double_cos_root_deg11 : poly_deg11 double_cos_2pi_11 = 0.
Proof.
  unfold poly_deg11, double_cos_2pi_11.
  pose proof chebyshev_11_cos_2pi_11 as H.
  rewrite chebyshev_T_11_explicit in H.
  lra.
Qed.

Lemma poly_deg11_factors : forall y,
  poly_deg11 y = (y - 2) * (minpoly_2cos y)^2.
Proof.
  intros. unfold poly_deg11, minpoly_2cos. ring.
Qed.

Lemma double_cos_2pi_11_neq_2 : double_cos_2pi_11 <> 2.
Proof.
  unfold double_cos_2pi_11, cos_2pi_11.
  assert (Hpi: 0 < PI) by apply PI_RGT_0.
  assert (H1: 0 < 2 * PI / 11).
  { apply Rmult_lt_0_compat. lra. apply Rinv_0_lt_compat. lra. }
  assert (H2: 2 * PI / 11 < PI).
  { apply Rmult_lt_reg_r with 11. lra.
    unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by lra.
    rewrite Rmult_1_r. lra. }
  assert (Hcos: cos (2 * PI / 11) < cos 0).
  { apply cos_decreasing_1; lra. }
  rewrite cos_0 in Hcos. lra.
Qed.

Lemma minpoly_2cos_root : minpoly_2cos double_cos_2pi_11 = 0.
Proof.
  pose proof double_cos_root_deg11 as Hroot.
  pose proof double_cos_2pi_11_neq_2 as Hne2.
  rewrite poly_deg11_factors in Hroot.
  apply Rmult_integral in Hroot.
  destruct Hroot as [Hroot | Hroot].
  - exfalso. lra.
  - replace (minpoly_2cos double_cos_2pi_11 ^ 2) with
      (Rsqr (minpoly_2cos double_cos_2pi_11)) in Hroot by (unfold Rsqr; ring).
    apply Rsqr_0_uniq in Hroot. exact Hroot.
Qed.

(** Cyclotomic and Chebyshev theory for the hendecagon.

    Φ₁₁(x) = x¹⁰ + x⁹ + ... + x + 1 has degree φ(11) = 10.
    Roots: primitive 11th roots of unity ζ = e^(2πi/11).

    [ℚ(2cos(2π/11)) : ℚ] = 5 because:
    - ζ + ζ⁻¹ = 2cos(2π/11)
    - The map ζ ↦ ζ + ζ⁻¹ is 2-to-1 on primitive roots
    - So φ(11)/2 = 5

    5 ∉ {2^a × 3^b} implies cos(2π/11) ∉ OrigamiNum.
    5 ∈ {2^a × 3^b × 5^c} implies cos(2π/11) ∈ OrigamiNum2. *)

(** The 11th cyclotomic polynomial *)
Definition cyclotomic_11 (x : R) : R :=
  x^10 + x^9 + x^8 + x^7 + x^6 + x^5 + x^4 + x^3 + x^2 + x + 1.

(** x¹¹ - 1 = (x - 1) × Φ₁₁(x) *)
Lemma x11_minus_1_factors : forall x,
  x^11 - 1 = (x - 1) * cyclotomic_11 x.
Proof.
  intros. unfold cyclotomic_11. ring.
Qed.

(** Chebyshev T_n satisfies: T_n(x) - 1 has roots cos(2πk/n) for k = 1, ..., n-1
    when x = cos(θ) and T_n(cos θ) = cos(nθ) = 1 means nθ = 2πk *)

(** T₁₁(x) - 1 factorization over reals using cos(2πk/11) *)
Definition cos_2pi_k_11 (k : nat) : R := cos (2 * PI * INR k / 11).

Lemma cos_2pi_k_11_root : forall k,
  (1 <= k <= 10)%nat -> chebyshev_T 11 (cos_2pi_k_11 k) = 1.
Proof.
  intros k Hk.
  unfold cos_2pi_k_11.
  rewrite chebyshev_cos.
  replace (INR 11 * (2 * PI * INR k / 11)) with (2 * PI * INR k) by (simpl; field).
  replace (2 * PI * INR k) with (0 + 2 * INR k * PI) by ring.
  rewrite cos_period. apply cos_0.
Qed.

(** cos(2πk/11) = cos(2π(11-k)/11) for symmetry *)
Lemma cos_symmetry_11 : forall k,
  (1 <= k <= 5)%nat -> cos_2pi_k_11 k = cos_2pi_k_11 (11 - k).
Proof.
  intros k Hk.
  unfold cos_2pi_k_11.
  replace (2 * PI * INR (11 - k) / 11) with (2 * PI - 2 * PI * INR k / 11)
    by (rewrite minus_INR by lia; simpl; field).
  rewrite cos_minus.
  rewrite cos_2PI, sin_2PI.
  ring.
Qed.

(** The five distinct values cos(2πk/11) for k = 1,2,3,4,5 *)
Definition c1 : R := cos_2pi_k_11 1.
Definition c2 : R := cos_2pi_k_11 2.
Definition c3 : R := cos_2pi_k_11 3.
Definition c4 : R := cos_2pi_k_11 4.
Definition c5 : R := cos_2pi_k_11 5.

Lemma c1_eq_cos_2pi_11 : c1 = cos_2pi_11.
Proof.
  unfold c1, cos_2pi_k_11, cos_2pi_11.
  f_equal. simpl. field.
Qed.

(** All five are roots of T₁₁(x) - 1 *)
Lemma c1_root : chebyshev_T 11 c1 = 1.
Proof. apply cos_2pi_k_11_root. lia. Qed.

Lemma c2_root : chebyshev_T 11 c2 = 1.
Proof. apply cos_2pi_k_11_root. lia. Qed.

Lemma c3_root : chebyshev_T 11 c3 = 1.
Proof. apply cos_2pi_k_11_root. lia. Qed.

Lemma c4_root : chebyshev_T 11 c4 = 1.
Proof. apply cos_2pi_k_11_root. lia. Qed.

Lemma c5_root : chebyshev_T 11 c5 = 1.
Proof. apply cos_2pi_k_11_root. lia. Qed.

(** The polynomial T₁₁(x) - 1 divided by (x - 1) gives degree 10 *)
Definition chebyshev_11_minus_1 (x : R) : R := chebyshev_T 11 x - 1.

Lemma chebyshev_11_minus_1_explicit : forall x,
  chebyshev_11_minus_1 x = 1024*x^11 - 2816*x^9 + 2816*x^7 - 1232*x^5 + 220*x^3 - 11*x - 1.
Proof.
  intros. unfold chebyshev_11_minus_1.
  rewrite chebyshev_T_11_explicit. ring.
Qed.

(** x = 1 is a root of T₁₁(x) - 1 *)
Lemma chebyshev_11_at_1 : chebyshev_T 11 1 = 1.
Proof.
  rewrite chebyshev_T_11_explicit. ring.
Qed.

(** Factor out (x - 1) from T₁₁(x) - 1 *)
Lemma chebyshev_11_minus_1_factors : forall x,
  chebyshev_11_minus_1 x = (x - 1) * chebyshev_11_quotient x.
Proof.
  intros. unfold chebyshev_11_minus_1, chebyshev_11_quotient.
  rewrite chebyshev_T_11_explicit. ring.
Qed.

(** 2cos(2π/11) satisfies the degree-5 minimal polynomial *)
Theorem double_cos_2pi_11_minimal_poly : minpoly_2cos (2 * cos_2pi_11) = 0.
Proof.
  replace (2 * cos_2pi_11) with double_cos_2pi_11 by reflexivity.
  exact minpoly_2cos_root.
Qed.

(** The minimal polynomial is monic and degree 5 *)
Lemma minpoly_2cos_is_monic : forall y,
  minpoly_2cos y = y^5 + (y^4 - 4*y^3 - 3*y^2 + 3*y + 1).
Proof.
  intros. unfold minpoly_2cos. ring.
Qed.


(** ** Algebraic Degree Theory for cos(2π/11)

    The field extension [ℚ(cos(2π/11)) : ℚ] = 5 because:
    1. cos(2π/11) = (ζ + ζ⁻¹)/2 where ζ = e^(2πi/11)
    2. ℚ(ζ) has degree φ(11) = 10 over ℚ
    3. ζ + ζ⁻¹ generates the maximal real subfield of ℚ(ζ)
    4. [ℚ(ζ) : ℚ(ζ + ζ⁻¹)] = 2 (ζ satisfies x² - (ζ+ζ⁻¹)x + 1 = 0)
    5. Therefore [ℚ(ζ + ζ⁻¹) : ℚ] = 10/2 = 5

    Since minpoly_2cos has exactly 5 roots (the 2cos(2πk/11) for k=1..5)
    and is degree 5, it must be irreducible over ℚ. *)

(** The five roots are distinct *)
Lemma cos_2pi_k_11_distinct : forall j k,
  (1 <= j)%nat -> (j < k)%nat -> (k <= 5)%nat ->
  cos_2pi_k_11 j <> cos_2pi_k_11 k.
Proof.
  intros j k Hj Hjk Hk.
  unfold cos_2pi_k_11.
  assert (Hpi : 0 < PI) by apply PI_RGT_0.
  intro Heq.
  assert (Hj_bound : INR j < INR 6) by (apply lt_INR; lia).
  assert (Hk_bound : INR k < INR 6) by (apply lt_INR; lia).
  simpl in Hj_bound, Hk_bound.
  assert (Hj_le5 : INR j <= INR 5) by (apply le_INR; lia).
  assert (Hk_le5 : INR k <= INR 5) by (apply le_INR; lia).
  simpl in Hj_le5, Hk_le5.
  assert (Hj_angle : 0 < 2 * PI * INR j / 11 < PI).
  { split.
    - apply Rmult_lt_0_compat. apply Rmult_lt_0_compat. lra.
      apply lt_0_INR. lia. apply Rinv_0_lt_compat. lra.
    - unfold Rdiv.
      apply Rmult_lt_reg_r with 11. lra.
      rewrite Rmult_assoc. rewrite Rinv_l by lra. rewrite Rmult_1_r.
      nra. }
  assert (Hk_angle : 0 < 2 * PI * INR k / 11 < PI).
  { split.
    - apply Rmult_lt_0_compat. apply Rmult_lt_0_compat. lra.
      apply lt_0_INR. lia. apply Rinv_0_lt_compat. lra.
    - unfold Rdiv.
      apply Rmult_lt_reg_r with 11. lra.
      rewrite Rmult_assoc. rewrite Rinv_l by lra. rewrite Rmult_1_r.
      nra. }
  assert (Hjk_angle : 2 * PI * INR j / 11 < 2 * PI * INR k / 11).
  { apply Rmult_lt_compat_r. apply Rinv_0_lt_compat. lra.
    apply Rmult_lt_compat_l. lra. apply lt_INR. lia. }
  assert (Hcos_strict : cos (2 * PI * INR k / 11) < cos (2 * PI * INR j / 11)).
  { apply cos_decreasing_1; lra. }
  lra.
Qed.

(** minpoly_2cos has no rational roots - by the Rational Root Theorem,
    any rational root p/q (in lowest terms) of y^5+y^4-4y^3-3y^2+3y+1
    must have p | 1 and q | 1, so p/q ∈ {-1, 1}. Direct evaluation shows
    neither is a root: 1+1-4-3+3+1 = -1 ≠ 0 and -1+1+4-3-3+1 = -1 ≠ 0. *)
Lemma minpoly_2cos_at_1 : minpoly_2cos 1 <> 0.
Proof. unfold minpoly_2cos. lra. Qed.

Lemma minpoly_2cos_at_neg1 : minpoly_2cos (-1) <> 0.
Proof. unfold minpoly_2cos. lra. Qed.

(** [ℚ(cos(2π/11)) : ℚ] = 5.
    minpoly_2cos(2x) = 0 is degree 5 with no rational roots.
    All 5 roots are real and distinct, so irreducible over ℚ. *)
Theorem cos_2pi_11_degree_5 :
  minpoly_2cos (2 * cos_2pi_11) = 0 /\
  minpoly_2cos_degree = 5%nat /\
  minpoly_2cos 1 <> 0 /\ minpoly_2cos (-1) <> 0.
Proof.
  split. exact double_cos_2pi_11_minimal_poly.
  split. reflexivity.
  split. exact minpoly_2cos_at_1.
  exact minpoly_2cos_at_neg1.
Qed.

(** Constructibility classification for cos(2π/11).
    deg = 5, and 5 ∉ {2^a × 3^b}, so cos(2π/11) ∉ OrigamiNum.
    But 5 = 5^1 ∈ {2^a × 3^b × 5^c}, so cos(2π/11) ∈ OrigamiNum2. *)
Lemma cos_2pi_11_satisfies_quintic :
  let x := cos_2pi_11 in
  let y := 2 * x in
  y^5 + y^4 - 4*y^3 - 3*y^2 + 3*y + 1 = 0.
Proof.
  simpl. exact double_cos_2pi_11_minimal_poly.
Qed.

Theorem cos_2pi_11_in_OrigamiNum2 : OrigamiNum2 cos_2pi_11.
Proof.
  set (y := 2 * cos_2pi_11).
  assert (Hy : y^5 + 1*y^4 + (-4)*y^3 + (-3)*y^2 + 3*y + 1 = 0).
  { unfold y.
    replace (1 * (2 * cos_2pi_11)^4) with ((2 * cos_2pi_11)^4) by ring.
    replace ((-4) * (2 * cos_2pi_11)^3) with (- 4 * (2 * cos_2pi_11)^3) by ring.
    replace ((-3) * (2 * cos_2pi_11)^2) with (- 3 * (2 * cos_2pi_11)^2) by ring.
    pose proof double_cos_2pi_11_minimal_poly as H.
    unfold minpoly_2cos in H. lra. }
  assert (Hy_ON2 : OrigamiNum2 y).
  { apply (ON2_quint 1 (-4) (-3) 3 1 y).
    - apply ON2_1.
    - replace (-4) with (0 - 4) by ring. apply ON2_sub. apply ON2_0.
      replace 4 with (1+1+1+1) by ring. repeat apply ON2_add; apply ON2_1.
    - replace (-3) with (0 - 3) by ring. apply ON2_sub. apply ON2_0.
      replace 3 with (1+1+1) by ring. repeat apply ON2_add; apply ON2_1.
    - replace 3 with (1+1+1) by ring. repeat apply ON2_add; apply ON2_1.
    - apply ON2_1.
    - exact Hy. }
  replace cos_2pi_11 with (y / 2).
  - unfold Rdiv. apply ON2_mul.
    + exact Hy_ON2.
    + apply ON2_inv.
      * replace 2 with (1+1) by ring. apply ON2_add; apply ON2_1.
      * lra.
  - unfold y. field.
Qed.

(** cos(2π/11) ∈ OrigamiNum2 (equivalent statement) *)
Theorem hendecagon_2fold_constructible_proved : OrigamiNum2 cos_2pi_11.
Proof. exact cos_2pi_11_in_OrigamiNum2. Qed.

(** Hendecagon vertex coordinates. *)

(** sin(2π/11) ∈ OrigamiNum2 via sin²θ + cos²θ = 1 *)
Lemma sin_2pi_11_squared : sin_2pi_11 ^ 2 = 1 - cos_2pi_11 ^ 2.
Proof.
  unfold sin_2pi_11, cos_2pi_11.
  pose proof (sin2_cos2 (2 * PI / 11)) as H.
  unfold Rsqr in H. lra.
Qed.

Lemma sin_2pi_11_pos : 0 < sin_2pi_11.
Proof.
  unfold sin_2pi_11.
  apply sin_gt_0.
  - assert (Hpi : 0 < PI) by apply PI_RGT_0.
    lra.
  - assert (Hpi : 0 < PI) by apply PI_RGT_0.
    apply Rmult_lt_reg_r with 11. lra.
    unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by lra.
    rewrite Rmult_1_r. lra.
Qed.

Lemma sin_2pi_11_nonneg : 0 <= 1 - cos_2pi_11 ^ 2.
Proof.
  pose proof (COS_bound (2 * PI / 11)) as Hbound.
  unfold cos_2pi_11. nra.
Qed.

Theorem sin_2pi_11_in_OrigamiNum2 : OrigamiNum2 sin_2pi_11.
Proof.
  rewrite <- sqrt_pow2.
  - rewrite sin_2pi_11_squared.
    apply ON2_sqrt.
    + apply ON2_sub.
      * apply ON2_1.
      * replace (cos_2pi_11 ^ 2) with (cos_2pi_11 * cos_2pi_11) by ring.
        apply ON2_mul; exact cos_2pi_11_in_OrigamiNum2.
    + exact sin_2pi_11_nonneg.
  - left. exact sin_2pi_11_pos.
Qed.

(** k-th vertex of the regular 11-gon *)
Theorem hendecagon_vertex_1 : hendecagon_vertex 1 = (cos_2pi_11, sin_2pi_11).
Proof.
  unfold hendecagon_vertex, cos_2pi_11, sin_2pi_11.
  simpl INR.
  replace (2 * PI * 1 / 11) with (2 * PI / 11) by field.
  reflexivity.
Qed.
Definition cos_2pi_7 : R := cos (2 * PI / 7).

(** T_7(x) = 64x⁷ - 112x⁵ + 56x³ - 7x *)
Lemma chebyshev_T_7_explicit : forall x,
  chebyshev_T 7 x = 64*x^7 - 112*x^5 + 56*x^3 - 7*x.
Proof.
  intros. unfold chebyshev_T. ring.
Qed.

(** T_7(cos(2π/7)) = cos(7 · 2π/7) = cos(2π) = 1 *)
Lemma chebyshev_7_cos_2pi_7 : chebyshev_T 7 cos_2pi_7 = 1.
Proof.
  unfold cos_2pi_7.
  rewrite chebyshev_cos.
  replace (INR 7 * (2 * PI / 7)) with (2 * PI) by (simpl; field).
  apply cos_2PI.
Qed.

(** Key factorization: T_7(x) - 1 = (x - 1) · (heptagon_poly x)² *)
Lemma chebyshev_7_factorization : forall x,
  chebyshev_T 7 x - 1 = (x - 1) * (heptagon_poly x)^2.
Proof.
  intros x.
  rewrite chebyshev_T_7_explicit.
  unfold heptagon_poly.
  ring.
Qed.

(** cos(2π/7) ≠ 1 *)
Lemma cos_2pi_7_neq_1 : cos_2pi_7 <> 1.
Proof.
  unfold cos_2pi_7.
  assert (Hpi : 0 < PI) by apply PI_RGT_0.
  assert (H1 : 0 < 2 * PI / 7) by lra.
  assert (H2 : 2 * PI / 7 < PI) by lra.
  assert (Hcos : cos (2 * PI / 7) < cos 0).
  { apply cos_decreasing_1; lra. }
  rewrite cos_0 in Hcos. lra.
Qed.

(** cos(2π/7) is a root of 8c³ + 4c² - 4c - 1 *)
Theorem cos_2pi_7_satisfies_heptagon_poly : heptagon_poly cos_2pi_7 = 0.
Proof.
  assert (HT7 : chebyshev_T 7 cos_2pi_7 = 1) by exact chebyshev_7_cos_2pi_7.
  assert (Hfact : chebyshev_T 7 cos_2pi_7 - 1 = (cos_2pi_7 - 1) * (heptagon_poly cos_2pi_7)^2)
    by apply chebyshev_7_factorization.
  rewrite HT7 in Hfact.
  assert (Hzero : (cos_2pi_7 - 1) * (heptagon_poly cos_2pi_7)^2 = 0) by lra.
  assert (Hne1 : cos_2pi_7 - 1 <> 0).
  { assert (H := cos_2pi_7_neq_1). lra. }
  apply Rmult_integral in Hzero.
  destruct Hzero as [Hcontra | Hsq].
  - exfalso. exact (Hne1 Hcontra).
  - apply Rsqr_0_uniq.
    replace (Rsqr (heptagon_poly cos_2pi_7)) with ((heptagon_poly cos_2pi_7)^2)
      by (unfold Rsqr; ring).
    exact Hsq.
Qed.

(** Reformulation in the form used by heptagon_constructible *)
Lemma cos_2pi_7_cubic_form :
  8*(cos_2pi_7*cos_2pi_7*cos_2pi_7) + 4*(cos_2pi_7*cos_2pi_7) - 4*cos_2pi_7 - 1 = 0.
Proof.
  pose proof cos_2pi_7_satisfies_heptagon_poly as H.
  unfold heptagon_poly in H.
  replace (cos_2pi_7^3) with (cos_2pi_7*cos_2pi_7*cos_2pi_7) in H by ring.
  replace (cos_2pi_7^2) with (cos_2pi_7*cos_2pi_7) in H by ring.
  lra.
Qed.

(** cos(2π/7) ∈ OrigamiNum *)
Theorem cos_2pi_7_is_origami_constructible : OrigamiNum cos_2pi_7.
Proof.
  apply heptagon_constructible.
  exact cos_2pi_7_cubic_form.
Qed.

(** sin(2π/7) *)
Definition sin_2pi_7 : R := sin (2 * PI / 7).

(** sin²(2π/7) = 1 - cos²(2π/7) *)
Lemma sin_2pi_7_squared : sin_2pi_7^2 = 1 - cos_2pi_7^2.
Proof.
  unfold sin_2pi_7, cos_2pi_7.
  pose proof (sin2_cos2 (2 * PI / 7)) as H.
  unfold Rsqr in H. lra.
Qed.

(** 0 < sin(2π/7) *)
Lemma sin_2pi_7_pos : 0 < sin_2pi_7.
Proof.
  unfold sin_2pi_7.
  apply sin_gt_0.
  - assert (Hpi : 0 < PI) by apply PI_RGT_0. lra.
  - assert (Hpi : 0 < PI) by apply PI_RGT_0. lra.
Qed.

(** sin(2π/7) ∈ OrigamiNum *)
Theorem sin_2pi_7_is_origami_constructible : OrigamiNum sin_2pi_7.
Proof.
  rewrite <- sqrt_pow2.
  - rewrite sin_2pi_7_squared.
    apply ON_sqrt.
    + apply ON_sub.
      * apply ON_1.
      * replace (cos_2pi_7^2) with (cos_2pi_7 * cos_2pi_7) by ring.
        apply ON_mul; exact cos_2pi_7_is_origami_constructible.
    + pose proof (COS_bound (2 * PI / 7)) as H.
      unfold cos_2pi_7 in *. nra.
  - left. exact sin_2pi_7_pos.
Qed.

(** The first vertex of the regular heptagon *)
Theorem cos_2pi_11_in_OrigamiNum2_verified : OrigamiNum2 cos_2pi_11.
Proof. exact cos_2pi_11_in_OrigamiNum2. Qed.

(** 11-gon boundary: cos(2π/11) ∈ OrigamiNum2 ∧ φ(11)=10 ∉ {2^a × 3^b} *)
Theorem hendecagon_boundary :
  OrigamiNum2 cos_2pi_11 /\
  euler_phi 11 = 10%nat /\
  ~ is_2_3_smooth (euler_phi 11).
Proof.
  split. { exact cos_2pi_11_in_OrigamiNum2. }
  split. { exact phi_11. }
  rewrite phi_11. exact ten_not_smooth.
Qed.


(** ═══════════════════════════════════════════════════════════════════════════
    SHOWCASE: Key Results of This Formalization
    ═══════════════════════════════════════════════════════════════════════════

    n-GON CONSTRUCTIBILITY (φ(n) must be 2-3-smooth for origami):
    ┌─────┬────────┬───────────┬─────────┐
    │  n  │  φ(n)  │ Compass   │ Origami │
    ├─────┼────────┼───────────┼─────────┤
    │  7  │   6    │     ✗     │    ✓    │
    │  9  │   6    │     ✗     │    ✓    │
    │ 11  │  10    │     ✗     │    ✗    │  ← requires 2-fold
    │ 13  │  12    │     ✗     │    ✓    │
    │ 19  │  18    │     ✗     │    ✓    │
    └─────┴────────┴───────────┴─────────┘                                    *)

(** I. THE HEPTAGON *)
Section Heptagon_Irreducibility.
Local Open Scope Z_scope.

(** Cleared of denominators (root y = a/b, gcd(a,b)=1, b>0):
    a^3 + a^2 b - 2 a b^2 - b^3 <> 0. *)
Lemma heptagon_min_no_rational_root : forall a b : Z,
  b > 0 -> Z.gcd a b = 1 ->
  a*a*a + a*a*b - 2*a*b*b - b*b*b <> 0.
Proof.
  intros a b Hb Hcop Heq.
  assert (Hgba : Z.gcd b a = 1) by (rewrite Z.gcd_comm; exact Hcop).
  assert (Hrel : Znumtheory.rel_prime b a) by (apply Znumtheory.Zgcd_1_rel_prime; exact Hgba).
  assert (Hbd3 : (b | a * (a * a))).
  { exists (- (a*a) + 2*a*b + b*b). nia. }
  assert (Hbd2 : (b | a * a)) by (apply (Znumtheory.Gauss b a (a*a)); [exact Hbd3 | exact Hrel]).
  assert (Hbd1 : (b | a)) by (apply (Znumtheory.Gauss b a a); [exact Hbd2 | exact Hrel]).
  assert (Hbg : (b | Z.gcd a b)) by (apply Z.gcd_greatest; [exact Hbd1 | apply Z.divide_refl]).
  rewrite Hcop in Hbg. apply Z.divide_1_r in Hbg.
  destruct Hbg as [Hb1|Hb1]; [|lia]. subst b.
  assert (Ha : (a | 1)) by (exists (a*a + a - 2); nia).
  apply Z.divide_1_r in Ha. destruct Ha as [Ha1|Ha1]; subst a; lia.
Qed.

(** The cubic form a^3 + a^2 b - 2 a b^2 - b^3 (cleared y^3+y^2-2y-1 at y=a/b). *)
Definition heptagon_form (a b : Z) : Z := a*a*a + a*a*b - 2*a*b*b - b*b*b.

(** Homogeneity of degree 3 and sign symmetry. *)
Lemma heptagon_form_homog : forall g a b,
  heptagon_form (a*g) (b*g) = g*g*g * heptagon_form a b.
Proof. intros. unfold heptagon_form. ring. Qed.

Lemma heptagon_form_neg : forall a b,
  heptagon_form (-a) (-b) = - heptagon_form a b.
Proof. intros. unfold heptagon_form. ring. Qed.

(** No coprimality assumption: for any denominator b <> 0, y^3+y^2-2y-1 never
    vanishes at y = a/b (reduce by gcd, then the coprime case above). *)
Lemma heptagon_no_rational_root_general : forall a b : Z,
  b <> 0 -> heptagon_form a b <> 0.
Proof.
  intros a b Hb Heq.
  set (g := Z.gcd a b).
  assert (Hg0 : g <> 0).
  { unfold g. intro H. apply Z.gcd_eq_0 in H. destruct H. contradiction. }
  assert (Hgpos : g > 0).
  { assert (0 <= g) by (unfold g; apply Z.gcd_nonneg). lia. }
  assert (Hga : (g | a)) by (unfold g; apply Z.gcd_divide_l).
  assert (Hgb : (g | b)) by (unfold g; apply Z.gcd_divide_r).
  destruct Hga as [a' Ha']. destruct Hgb as [b' Hb'].
  assert (Hcop : Z.gcd a' b' = 1).
  { assert (Hgg : Z.gcd a b = g) by reflexivity.
    rewrite Ha', Hb' in Hgg.
    rewrite Z.gcd_mul_mono_r in Hgg.
    rewrite Z.abs_eq in Hgg by lia. nia. }
  assert (Hb'0 : b' <> 0).
  { intro H. subst b'. rewrite Z.mul_0_l in Hb'. contradiction. }
  assert (Hfab' : heptagon_form a' b' = 0).
  { assert (Hh : heptagon_form a b = g*g*g * heptagon_form a' b').
    { rewrite Ha', Hb'. apply heptagon_form_homog. }
    rewrite Heq in Hh. symmetry in Hh.
    apply Zmult_integral in Hh. destruct Hh as [Hh|Hh]; [exfalso; nia | exact Hh]. }
  destruct (Z_lt_le_dec b' 0) as [Hbneg | Hbpos].
  - assert (Hopp : heptagon_form (-a') (-b') = 0)
      by (rewrite heptagon_form_neg, Hfab'; ring).
    assert (Hcop' : Z.gcd (-a') (-b') = 1).
    { rewrite Z.gcd_opp_l, Z.gcd_opp_r. exact Hcop. }
    apply (heptagon_min_no_rational_root (-a') (-b')); [lia | exact Hcop' | exact Hopp].
  - apply (heptagon_min_no_rational_root a' b'); [lia | exact Hcop | exact Hfab'].
Qed.

End Heptagon_Irreducibility.
(** ═══════════════════════════════════════════════════════════════════════════
    ALGEBRAIC DEGREE OF cos(2 pi / 7)
    2cos(2pi/7) is a root of the monic y^3+y^2-2y-1, which has no rational root.
    Hence any degree-<=2 integer relation forces a rational root (contradiction),
    so cos(2pi/7) and 2cos(2pi/7) have algebraic degree exactly 3 over Q.
    ═══════════════════════════════════════════════════════════════════════════ *)
Section Heptagon_Root_Degree.
Variable d : R.
Hypothesis Hd : d*d*d + d*d - 2*d - 1 = 0.

(** A degree-<=2 integer relation P d + Q = 0 forces a rational root a/b = -Q/P:
    heptagon_form(-Q, P) = P^3 * (cubic at d) + (P d + Q) * (quotient) = 0. *)
Lemma hept_rel_gives_form : forall P Q : Z,
  IZR P * d + IZR Q = 0 -> heptagon_form (-Q) P = 0%Z.
Proof.
  intros P Q Hr.
  apply eq_IZR_R0.
  assert (Hpush : IZR (heptagon_form (-Q) P) =
     IZR P * IZR P * IZR P * (d*d*d + d*d - 2*d - 1)
     + (IZR P * d + IZR Q) * (- (IZR P * d) * (IZR P * d)
          + (IZR Q - IZR P) * (IZR P * d)
          + (2 * (IZR P * IZR P) + IZR P * IZR Q - IZR Q * IZR Q))).
  { unfold heptagon_form.
    rewrite ?minus_IZR, ?plus_IZR, ?mult_IZR, ?opp_IZR, ?IZR_eq_2. ring. }
  rewrite Hpush, Hd, Hr. ring.
Qed.

(** Any degree-<=2 integer relation c0 + c1 d + c2 d^2 = 0 is trivial.
    Divide the cubic by c2 x^2 + c1 x + c0: the linear remainder gives A d + B = 0
    with integers A, B; A <> 0 makes d rational, A = 0 makes the quadratic divide
    the cubic (a rational linear factor) -- both contradict no-rational-root. *)
Lemma hept_deg2_contra : forall c0 c1 c2 : Z,
  IZR c0 + IZR c1 * d + IZR c2 * (d*d) = 0 ->
  c0 = 0%Z /\ c1 = 0%Z /\ c2 = 0%Z.
Proof.
  intros c0 c1 c2 Hrel0.
  set (A := (c1*c1 - c1*c2 - c0*c2 - 2*c2*c2)%Z).
  set (B := (c0*c1 - c0*c2 - c2*c2)%Z).
  assert (HAB : IZR A * d + IZR B = 0).
  { assert (Hid : IZR A * d + IZR B
        = IZR c2 * IZR c2 * (d*d*d + d*d - 2*d - 1)
          - (IZR c0 + IZR c1 * d + IZR c2 * (d*d)) * (IZR c2 * d + IZR c2 - IZR c1)).
    { unfold A, B.
      rewrite ?minus_IZR, ?plus_IZR, ?mult_IZR, ?opp_IZR, ?IZR_eq_2. ring. }
    rewrite Hid, Hd, Hrel0. ring. }
  destruct (Z.eq_dec c2 0) as [Hc2|Hc2].
  - subst c2.
    assert (Hrel1 : IZR c1 * d + IZR c0 = 0).
    { rewrite <- Hrel0. change (IZR 0) with 0. ring. }
    destruct (Z.eq_dec c1 0) as [Hc1|Hc1].
    + subst c1.
      assert (Hc0 : IZR c0 = 0) by (rewrite <- Hrel1; change (IZR 0) with 0; ring).
      apply eq_IZR_R0 in Hc0. subst c0. auto.
    + exfalso.
      apply (heptagon_no_rational_root_general (-c0) c1 Hc1).
      apply (hept_rel_gives_form c1 c0). exact Hrel1.
  - destruct (Z.eq_dec A 0) as [HA|HA].
    + exfalso.
      assert (HB : B = 0%Z).
      { apply eq_IZR_R0. rewrite HA in HAB. change (IZR 0) with 0 in HAB. lra. }
      apply (heptagon_no_rational_root_general (c1 - c2) c2 Hc2).
      assert (Hfid : (heptagon_form (c1 - c2) c2 = (c1 - c2) * A + c2 * B)%Z)
        by (unfold heptagon_form, A, B; ring).
      rewrite Hfid, HA, HB. ring.
    + exfalso.
      apply (heptagon_no_rational_root_general (-B) A HA).
      apply (hept_rel_gives_form A B). exact HAB.
Qed.

Lemma hept_d_alg_deg_le_3 : alg_deg_le d 3.
Proof.
  exists ((-1)%Z :: (-2)%Z :: 1%Z :: 1%Z :: nil).
  split; [apply Exists_cons_hd; lia | split; [simpl; lia|]].
  unfold is_poly_root. simpl. nra.
Qed.

Lemma hept_d_not_alg_deg_le_2 : ~ alg_deg_le d 2.
Proof.
  intros [p [Hnz [Hlen Hroot]]].
  destruct p as [|c0 [|c1 [|c2 [|c3 p']]]]; simpl in Hlen; try lia.
  - inversion Hnz.
  - assert (E : IZR c0 + IZR 0 * d + IZR 0 * (d*d) = 0).
    { transitivity (peval (c0 :: nil) d); [simpl; ring | exact Hroot]. }
    destruct (hept_deg2_contra c0 0 0 E) as [H0 _]. subst c0.
    inversion Hnz as [x l Hx|x l Ht]; [lia | inversion Ht].
  - assert (E : IZR c0 + IZR c1 * d + IZR 0 * (d*d) = 0).
    { transitivity (peval (c0 :: c1 :: nil) d); [simpl; ring | exact Hroot]. }
    destruct (hept_deg2_contra c0 c1 0 E) as [H0 [H1 _]]. subst c0 c1.
    inversion Hnz as [x l Hx|x l Ht]; [lia|].
    inversion Ht as [x2 l2 Hx2|x2 l2 Ht2]; [lia | inversion Ht2].
  - assert (E : IZR c0 + IZR c1 * d + IZR c2 * (d*d) = 0).
    { transitivity (peval (c0 :: c1 :: c2 :: nil) d); [simpl; ring | exact Hroot]. }
    destruct (hept_deg2_contra c0 c1 c2 E) as [H0 [H1 H2]]. subst c0 c1 c2.
    inversion Hnz as [x l Hx|x l Ht]; [lia|].
    inversion Ht as [x2 l2 Hx2|x2 l2 Ht2]; [lia|].
    inversion Ht2 as [x3 l3 Hx3|x3 l3 Ht3]; [lia | inversion Ht3].
Qed.

Theorem hept_d_alg_deg_exactly_3 : alg_deg_le d 3 /\ ~ alg_deg_le d 2.
Proof. split; [exact hept_d_alg_deg_le_3 | exact hept_d_not_alg_deg_le_2]. Qed.

End Heptagon_Root_Degree.
(** 2cos(2pi/7) satisfies the monic minimal cubic y^3 + y^2 - 2y - 1 = 0. *)
Lemma two_cos_2pi_7_min :
  (2*cos_2pi_7)*(2*cos_2pi_7)*(2*cos_2pi_7) + (2*cos_2pi_7)*(2*cos_2pi_7)
    - 2*(2*cos_2pi_7) - 1 = 0.
Proof.
  pose proof cos_2pi_7_satisfies_heptagon_poly as H. unfold heptagon_poly in H. nra.
Qed.

(** 2cos(2pi/7) has algebraic degree exactly 3 over Q. *)
Theorem two_cos_2pi_7_alg_deg_exactly_3 :
  alg_deg_le (2*cos_2pi_7) 3 /\ ~ alg_deg_le (2*cos_2pi_7) 2.
Proof. exact (hept_d_alg_deg_exactly_3 (2*cos_2pi_7) two_cos_2pi_7_min). Qed.

(** Transfer to cos itself: any root of 8x^3+4x^2-4x-1 has degree exactly 3.
    A degree-<=2 relation on x scales (by 4) to one on 2x, where the monic
    argument applies. *)
Section Cos_2pi_7_Degree.
Variable c : R.
Hypothesis Hc : 8*(c*c*c) + 4*(c*c) - 4*c - 1 = 0.

Lemma hept_cos_Hd : (2*c)*(2*c)*(2*c) + (2*c)*(2*c) - 2*(2*c) - 1 = 0.
Proof. nra. Qed.

Lemma hept_cos_alg_deg_le_3 : alg_deg_le c 3.
Proof.
  exists ((-1)%Z :: (-4)%Z :: 4%Z :: 8%Z :: nil).
  split; [apply Exists_cons_hd; lia | split; [simpl; lia|]].
  unfold is_poly_root. simpl. nra.
Qed.

Lemma hept_cos_not_alg_deg_le_2 : ~ alg_deg_le c 2.
Proof.
  intros [p [Hnz [Hlen Hroot]]]. unfold is_poly_root in Hroot.
  destruct p as [|c0 [|c1 [|c2 [|c3 p']]]]; simpl in Hlen; try lia.
  - inversion Hnz.
  - assert (E : IZR (4*c0) + IZR (2*0) * (2*c) + IZR 0 * ((2*c)*(2*c)) = 0).
    { rewrite !mult_IZR, ?IZR_eq_2, ?IZR_eq_4.
      transitivity (4 * peval (c0 :: nil) c); [simpl; ring|].
      replace (peval (c0 :: nil) c) with 0 by (symmetry; exact Hroot). ring. }
    destruct (hept_deg2_contra (2*c) hept_cos_Hd (4*c0) (2*0) 0 E) as [H0 _].
    assert (c0 = 0%Z) by lia. subst c0.
    inversion Hnz as [x l Hx|x l Ht]; [lia | inversion Ht].
  - assert (E : IZR (4*c0) + IZR (2*c1) * (2*c) + IZR 0 * ((2*c)*(2*c)) = 0).
    { rewrite !mult_IZR, ?IZR_eq_2, ?IZR_eq_4.
      transitivity (4 * peval (c0 :: c1 :: nil) c); [simpl; ring|].
      replace (peval (c0 :: c1 :: nil) c) with 0 by (symmetry; exact Hroot). ring. }
    destruct (hept_deg2_contra (2*c) hept_cos_Hd (4*c0) (2*c1) 0 E) as [H0 [H1 _]].
    assert (c0 = 0%Z) by lia. assert (c1 = 0%Z) by lia. subst c0 c1.
    inversion Hnz as [x l Hx|x l Ht]; [lia|].
    inversion Ht as [x2 l2 Hx2|x2 l2 Ht2]; [lia | inversion Ht2].
  - assert (E : IZR (4*c0) + IZR (2*c1) * (2*c) + IZR c2 * ((2*c)*(2*c)) = 0).
    { rewrite !mult_IZR, ?IZR_eq_2, ?IZR_eq_4.
      transitivity (4 * peval (c0 :: c1 :: c2 :: nil) c); [simpl; ring|].
      replace (peval (c0 :: c1 :: c2 :: nil) c) with 0 by (symmetry; exact Hroot). ring. }
    destruct (hept_deg2_contra (2*c) hept_cos_Hd (4*c0) (2*c1) c2 E) as [H0 [H1 H2]].
    assert (c0 = 0%Z) by lia. assert (c1 = 0%Z) by lia. subst c0 c1 c2.
    inversion Hnz as [x l Hx|x l Ht]; [lia|].
    inversion Ht as [x2 l2 Hx2|x2 l2 Ht2]; [lia|].
    inversion Ht2 as [x3 l3 Hx3|x3 l3 Ht3]; [lia | inversion Ht3].
Qed.

Theorem hept_cos_alg_deg_exactly_3 : alg_deg_le c 3 /\ ~ alg_deg_le c 2.
Proof. split; [exact hept_cos_alg_deg_le_3 | exact hept_cos_not_alg_deg_le_2]. Qed.

End Cos_2pi_7_Degree.
(** cos(2pi/7) has algebraic degree exactly 3 over Q -- it is genuinely a cubic
    irrational, sitting at origami degree 3 (not a compass power of two). *)
Theorem cos_2pi_7_alg_deg_exactly_3 :
  alg_deg_le cos_2pi_7 3 /\ ~ alg_deg_le cos_2pi_7 2.
Proof. exact (hept_cos_alg_deg_exactly_3 cos_2pi_7 cos_2pi_7_cubic_form). Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    COMPASS-STRAIGHTEDGE IMPOSSIBILITY VIA REAL QUADRATIC TOWERS
    Euclidean (compass-straightedge) numbers lie in an iterated real quadratic
    extension of Q. A root of a rational cubic with no rational root cannot:
    if it sat in F(sqrt a) with sqrt a not in F, its conjugate is another root and
    Vieta forces the third root into F, descending to a rational root. Hence the
    heptagon is not compass-constructible and Euclid c Origami is strict.
    ═══════════════════════════════════════════════════════════════════════════ *)
Open Scope R_scope.
(* ---------- abstract subfields of R ---------- *)
Lemma heptagon_cubic_no_rat_root : forall r, is_rational r ->
  r*r*r + 1*(r*r) + (-2)*r + (-1) <> 0.
Proof.
  intros r [p [q [Hq Hr]]] Heq. subst r.
  assert (Hqne : IZR q <> 0) by (apply not_0_IZR; lia).
  apply (heptagon_no_rational_root_general p q); [lia |].
  apply eq_IZR_R0.
  assert (Hpush : IZR (heptagon_form p q) =
    (IZR q * IZR q * IZR q) * ((IZR p/IZR q)*(IZR p/IZR q)*(IZR p/IZR q)
      + 1*((IZR p/IZR q)*(IZR p/IZR q)) + (-2)*(IZR p/IZR q) + (-1))).
  { unfold heptagon_form. rewrite ?minus_IZR, ?plus_IZR, ?mult_IZR, ?IZR_eq_2.
    field. exact Hqne. }
  rewrite Hpush, Heq. ring.
Qed.

Theorem not_EuclidNum_two_cos_2pi_7 : ~ EuclidNum (2 * cos_2pi_7).
Proof.
  apply (not_EuclidNum_of_cubic_no_rat_root (-1) (-2) 1
           is_rational_m1 is_rational_m2 is_rational_1 heptagon_cubic_no_rat_root).
  pose proof two_cos_2pi_7_min. lra.
Qed.

(** The regular heptagon is not compass-and-straightedge constructible. *)
Theorem not_EuclidNum_cos_2pi_7 : ~ EuclidNum cos_2pi_7.
Proof.
  intro H. apply not_EuclidNum_two_cos_2pi_7.
  apply EN_mul; [replace 2 with (1+1) by ring; apply EN_add; apply EN_1 | exact H].
Qed.

(** Compass-straightedge is a strict subset of origami, witnessed by cos(2pi/7). *)
Theorem euclid_strict_subset_origami : exists x, OrigamiNum x /\ ~ EuclidNum x.
Proof.
  exists cos_2pi_7. split.
  - exact cos_2pi_7_is_origami_constructible.
  - exact not_EuclidNum_cos_2pi_7.
Qed.


(** ═══════════════════════════════════════════════════════════════════════════
    THE THREE CLASSICAL IMPOSSIBILITIES BY COMPASS AND STRAIGHTEDGE
    Cube duplication (cbrt 2), angle trisection (cos pi/9), and the nonagon
    (cos 2pi/9) each give a monic rational cubic with no rational root, hence no
    Euclidean root by the quadratic-tower descent above.
    ═══════════════════════════════════════════════════════════════════════════ *)
Open Scope R_scope.
(* ---------- monic cubic rational root theorem (integer side) ---------- *)
Definition cos_2pi_9 : R := cos (2*PI/9).
Lemma cos_2pi_9_cubic : 8*(cos_2pi_9*cos_2pi_9*cos_2pi_9) - 6*cos_2pi_9 + 1 = 0.
Proof.
  unfold cos_2pi_9. pose proof (cos_triple (2*PI/9)) as H.
  replace (3*(2*PI/9)) with (2*PI/3) in H by field.
  rewrite cos_2pi_3 in H. nra.
Qed.

(* ---------- impossibilities ---------- *)
(** Doubling the cube is impossible by compass and straightedge. *)
Theorem not_EuclidNum_two_cos_2pi_9 : ~ EuclidNum (2 * cos_2pi_9).
Proof.
  apply (not_EuclidNum_of_cubic_no_rat_root 1 (-3) 0
           (is_rational_IZR 1) (is_rational_IZR (-3)) (is_rational_IZR 0)
           (cubic_no_rat_root_of_int 1 (-3) 0 nonagon_check)).
  pose proof cos_2pi_9_cubic. nra.
Qed.

(** The regular nonagon is not compass-and-straightedge constructible. *)
Theorem not_EuclidNum_cos_2pi_9 : ~ EuclidNum cos_2pi_9.
Proof.
  intro H. apply not_EuclidNum_two_cos_2pi_9.
  apply EN_mul; [replace 2 with (1+1) by ring; apply EN_add; apply EN_1 | exact H].
Qed.
Open Scope R_scope.
(** A verified O5 fold genuinely satisfies the O5 incidence constraint. *)
Close Scope R_scope.
Open Scope R_scope.
Definition minpoly_list : list R := 1 :: 3 :: (-3) :: (-4) :: 1 :: 1 :: nil.

Lemma pe_minpoly_list : forall y, pe minpoly_list y = minpoly_2cos y.
Proof.
  intros y. unfold minpoly_list. rewrite !pe_cons, pe_nil. unfold minpoly_2cos. ring.
Qed.
Close Scope R_scope.
Open Scope R_scope.
Lemma minpoly_list_rational : Forall is_rational minpoly_list.
Proof. unfold minpoly_list. repeat constructor; apply is_rational_IZR. Qed.

(* if delta has degree d <= 4 then its monic minimal polynomial divides minpoly_2cos *)
Lemma minpoly_low_degree_factors : forall delta d,
  lin_indep is_rational (powers delta d) ->
  spans is_rational (powers delta d) (delta ^ d) ->
  pe minpoly_list delta = 0 -> (d <= 4)%nat ->
  exists mu q, length mu = S d /\ nth d mu 0 = 1 /\
               Forall is_rational mu /\ Forall is_rational q /\
               (forall y, pe minpoly_list y = pe mu y * pe q y).
Proof.
  intros delta d Hli Hsp Hroot Hd.
  destruct Hsp as [a [Hla [Hra Hfa]]].
  assert (Hlad : length a = d) by (rewrite Hla; apply powers_length).
  set (mu := map (Rmult (-1)) a ++ (1 :: nil)).
  assert (Hmulen : length mu = S d) by (unfold mu; rewrite length_app, length_map, Hlad; simpl; lia).
  assert (Hmurat : Forall is_rational mu).
  { unfold mu. apply Forall_app. split.
    - apply Forall_rat_map_mult;
        [apply (subfield_opp is_rational 1 is_rational_subfield);
           apply (subfield_1 is_rational is_rational_subfield) | exact Hra].
    - constructor; [apply (subfield_1 is_rational is_rational_subfield) | constructor]. }
  assert (Hmonic : nth d mu 0 = 1).
  { unfold mu. rewrite app_nth2 by (rewrite length_map, Hlad; lia).
    rewrite length_map, Hlad. replace (d - d)%nat with 0%nat by lia. reflexivity. }
  assert (Hmudelta : pe mu delta = 0).
  { unfold mu. rewrite pe_app, pe_scale, length_map, Hlad, pe_cons, pe_nil.
    replace (pe a delta) with (delta ^ d) by (unfold pe; rewrite Hlad; symmetry; exact Hfa). ring. }
  destruct (monic_div_exists mu d Hmulen Hmonic Hmurat (length minpoly_list) minpoly_list
              (le_n _) minpoly_list_rational) as [q [r [Hid [Hrlen [Hqrat Hrrat]]]]].
  assert (Hrdelta : pe r delta = 0).
  { pose proof (Hid delta) as H. rewrite Hroot, Hmudelta in H. lra. }
  assert (Hrzero : Forall (fun c => c = 0) r).
  { set (r' := r ++ repeat 0 (d - length r)).
    assert (Hr'len : length r' = d) by (unfold r'; rewrite length_app, repeat_length; lia).
    assert (Hr'rat : Forall is_rational r').
    { unfold r'. apply Forall_app. split; [exact Hrrat |].
      apply Forall_forall. intros z Hz. apply repeat_spec in Hz. subst z.
      apply (subfield_0 is_rational is_rational_subfield). }
    assert (Hr'fc : Fcomb r' (powers delta d) = 0).
    { replace (Fcomb r' (powers delta d)) with (pe r' delta)
        by (unfold pe; rewrite Hr'len; reflexivity).
      unfold r'. rewrite pe_app.
      rewrite (pe_zeros (repeat 0 (d - length r)) delta)
        by (apply Forall_forall; intros z Hz; apply repeat_spec in Hz; subst z; reflexivity).
      rewrite Hrdelta. ring. }
    pose proof (Hli r' (eq_trans Hr'len (eq_sym (powers_length delta d))) Hr'rat Hr'fc) as Hr'0.
    unfold r' in Hr'0. apply Forall_app in Hr'0. destruct Hr'0; assumption. }
  exists mu, q. repeat split; [exact Hmulen | exact Hmonic | exact Hmurat | exact Hqrat |].
  intros y. rewrite (Hid y), (pe_zeros r y Hrzero). ring.
Qed.

(* minpoly_2cos has no rational root: this rules out a monic rational linear
   factor (degree d = 1, and by the symmetry d <-> 5 - d, degree d = 4). *)
Lemma minpoly_2cos_no_rat_root : forall r, is_rational r -> minpoly_2cos r <> 0.
Proof.
  intros r [p [q [Hq Hr]]] Heq. subst r.
  assert (Hqne : IZR q <> 0) by (apply not_0_IZR; lia).
  assert (Hi3 : IZR 3 = 3) by lra.
  apply (quintic_form_general p q); [lia |].
  apply eq_IZR_R0.
  assert (HZR : IZR (quintic_form p q) =
     IZR p*IZR p*IZR p*IZR p*IZR p + IZR p*IZR p*IZR p*IZR p*IZR q
     - 4*(IZR p*IZR p*IZR p*(IZR q*IZR q)) - 3*(IZR p*IZR p*(IZR q*IZR q*IZR q))
     + 3*(IZR p*(IZR q*IZR q*IZR q*IZR q)) + IZR q*IZR q*IZR q*IZR q*IZR q).
  { unfold quintic_form.
    rewrite ?plus_IZR, ?minus_IZR, ?plus_IZR, ?minus_IZR, ?mult_IZR, ?IZR_eq_4, ?Hi3. ring. }
  assert (HRR :
     IZR p*IZR p*IZR p*IZR p*IZR p + IZR p*IZR p*IZR p*IZR p*IZR q
     - 4*(IZR p*IZR p*IZR p*(IZR q*IZR q)) - 3*(IZR p*IZR p*(IZR q*IZR q*IZR q))
     + 3*(IZR p*(IZR q*IZR q*IZR q*IZR q)) + IZR q*IZR q*IZR q*IZR q*IZR q
     = (IZR q*IZR q*IZR q*IZR q*IZR q) * minpoly_2cos (IZR p / IZR q)).
  { unfold minpoly_2cos. field. exact Hqne. }
  rewrite HZR, HRR, Heq. ring.
Qed.

(* an integer polynomial that vanishes at every real has all coefficients zero:
   the constant term is its value at 0; dividing by the variable and using
   continuity at 0 peels off the next coefficient.  This is the coefficient-
   matching fact behind the monic form of Gauss's lemma. *)
Close Scope R_scope.
Open Scope R_scope.
Definition minpoly_Z : list Z := (1 :: 3 :: (-3) :: (-4) :: 1 :: 1 :: nil)%Z.

Lemma peval_minpoly_Z : forall y, peval minpoly_Z y = minpoly_2cos y.
Proof.
  intro y. unfold minpoly_Z, minpoly_2cos. simpl peval.
  replace (IZR 1) with 1 by lra. replace (IZR 3) with 3 by lra.
  replace (IZR (-3)) with (-3) by lra. replace (IZR (-4)) with (-4) by lra.
  ring.
Qed.

Lemma Zcontent_minpoly_Z : Zcontent minpoly_Z = 1%Z.
Proof. reflexivity. Qed.
Close Scope R_scope.
Open Scope R_scope.
Open Scope Z_scope.
(* Two integer polynomials with equal evaluations agree coefficient by
   coefficient. This turns an evaluation identity into the integer coefficient
   equations consumed by the finite degree checks. *)
Close Scope Z_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope Z_scope.
Lemma high_coeff_zero : forall muZ0 qZ0 Dmu Dq d,
  length muZ0 = S d -> nth d muZ0 0 <> 0 ->
  (forall k, nth k (Zpmul muZ0 qZ0) 0 = (Dmu * Dq) * nth k minpoly_Z 0) ->
  forall j, (5 < d + j)%nat -> nth j qZ0 0 = 0.
Proof.
  intros muZ0 qZ0 Dmu Dq d Hlen Hlead Hprod.
  assert (Hmudeg : forall i, (d < i)%nat -> nth i muZ0 0 = 0).
  { intros i Hi. apply nth_overflow. lia. }
  assert (Hrange : forall n j, (length qZ0 <= j + n)%nat -> (5 < d + j)%nat -> nth j qZ0 0 = 0).
  { induction n as [|n IH]; intros j Hjn Hj.
    - apply nth_overflow. lia.
    - destruct (Nat.le_gt_cases (length qZ0) j) as [Hov | Hlt].
      + apply nth_overflow. exact Hov.
      + assert (Hqdeg : forall j', (j < j')%nat -> nth j' qZ0 0 = 0).
        { intros j' Hj'. apply IH; lia. }
        pose proof (Zconv_top muZ0 qZ0 d j Hmudeg Hqdeg) as Htop.
        rewrite <- nth_Zpmul in Htop. rewrite Hprod in Htop.
        assert (Hhi : nth (d + j) minpoly_Z 0 = 0) by (apply nth_overflow; simpl; lia).
        rewrite Hhi, Z.mul_0_r in Htop. symmetry in Htop.
        apply Z.mul_eq_0 in Htop. destruct Htop as [Hbad | Hgood];
          [ exfalso; apply Hlead; exact Hbad | exact Hgood ]. }
  intros j Hj. apply (Hrange (length qZ0) j); [ lia | exact Hj ].
Qed.
Close Scope Z_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope Z_scope.
Lemma monic_gauss_factor : forall mu q d,
  Forall is_rational mu -> Forall is_rational q ->
  length mu = S d -> nth d mu 0%R = 1%R -> (d <= 5)%nat ->
  (forall y, pe minpoly_list y = (pe mu y * pe q y)%R) ->
  exists muZ qZ : list Z,
    map IZR muZ = mu /\ length muZ = S d /\ nth d muZ 0%Z = 1%Z /\
    map IZR qZ = q /\
    (forall y, peval (Zpmul muZ qZ) y = peval minpoly_Z y).
Proof.
  intros mu q d Hmurat Hqrat Hmulen Hmonic Hd5 Hfact.
  destruct (clear_denoms mu Hmurat) as [Dmu [muZ0 [HDmu [HmuZlen HF2mu]]]].
  destruct (clear_denoms q Hqrat) as [Dq [qZ0 [HDq [HqZlen HF2q]]]].
  assert (HDmu' : 0 < Dmu) by lia.
  assert (HDq' : 0 < Dq) by lia.
  assert (HmuZlenSd : length muZ0 = S d) by (rewrite HmuZlen; exact Hmulen).
  assert (HpevMu : forall y, peval muZ0 y = (IZR Dmu * pe mu y)%R)
    by (intro y; rewrite peval_eq_pe, (Forall2_map_eq _ _ _ HF2mu), pe_scale; reflexivity).
  assert (HpevQ : forall y, peval qZ0 y = (IZR Dq * pe q y)%R)
    by (intro y; rewrite peval_eq_pe, (Forall2_map_eq _ _ _ HF2q), pe_scale; reflexivity).
  assert (Hdlt : (d < length muZ0)%nat) by (rewrite HmuZlen, Hmulen; lia).
  assert (HleadMu : nth d muZ0 0%Z = Dmu).
  { pose proof (Forall2_IZRrel_nth _ _ _ d HF2mu Hdlt) as Hn.
    rewrite Hmonic, Rmult_1_r in Hn. apply eq_IZR. exact Hn. }
  assert (HleadMuNz : nth d muZ0 0%Z <> 0) by (rewrite HleadMu; lia).
  assert (HprodPev : forall y, peval (Zpmul muZ0 qZ0) y = peval (map (Z.mul (Dmu * Dq)) minpoly_Z) y).
  { intro y. rewrite peval_Zpmul, HpevMu, HpevQ, peval_map_Zmul, peval_minpoly_Z.
    rewrite <- pe_minpoly_list, (Hfact y), mult_IZR. ring. }
  assert (Hprodnth : forall k, nth k (Zpmul muZ0 qZ0) 0 = (Dmu * Dq) * nth k minpoly_Z 0)
    by (intro k; rewrite (peval_eq_nth _ _ HprodPev k), nth_map_Zmul; reflexivity).
  pose proof (high_coeff_zero muZ0 qZ0 Dmu Dq d HmuZlenSd HleadMuNz Hprodnth) as Hqhigh.
  assert (Hmudeg : forall i, (d < i)%nat -> nth i muZ0 0 = 0) by (intros i Hi; apply nth_overflow; lia).
  assert (HqdegBound : forall j, ((5 - d) < j)%nat -> nth j qZ0 0%Z = 0) by (intros j Hj; apply Hqhigh; lia).
  assert (Hm5 : nth 5 minpoly_Z 0 = 1) by reflexivity.
  assert (HleadQ : nth (5 - d) qZ0 0%Z = Dq).
  { pose proof (Zconv_top muZ0 qZ0 d (5 - d) Hmudeg HqdegBound) as Htop.
    replace (d + (5 - d))%nat with 5%nat in Htop by lia.
    rewrite <- nth_Zpmul, Hprodnth, HleadMu, Hm5, Z.mul_1_r in Htop.
    assert (Hcancel : Dmu * (Dq - nth (5 - d) qZ0 0) = 0) by (rewrite Z.mul_sub_distr_l; lia).
    apply Z.mul_eq_0 in Hcancel. destruct Hcancel as [Hb | Hg]; lia. }
  assert (HcMuNz : Zcontent muZ0 <> 0).
  { intro H0. rewrite Zcontent_zero_iff in H0.
    pose proof (Forall_eq0_nth _ H0 d) as Hz. rewrite HleadMu in Hz. lia. }
  assert (HcQNz : Zcontent qZ0 <> 0).
  { intro H0. rewrite Zcontent_zero_iff in H0.
    pose proof (Forall_eq0_nth _ H0 (5 - d)) as Hz. rewrite HleadQ in Hz. lia. }
  assert (Hprodcontnz : Zcontent (Zpmul muZ0 qZ0) <> 0).
  { rewrite (peval_eq_content _ _ HprodPev), Zcontent_scale by nia.
    rewrite Zcontent_minpoly_Z. nia. }
  pose proof (Zcontent_mult muZ0 qZ0 HcMuNz HcQNz Hprodcontnz) as Hcmult.
  assert (Hcontprod : Zcontent (Zpmul muZ0 qZ0) = Dmu * Dq).
  { rewrite (peval_eq_content _ _ HprodPev), Zcontent_scale by nia.
    rewrite Zcontent_minpoly_Z. ring. }
  rewrite Hcontprod in Hcmult.
  assert (HcmuDiv : (Zcontent muZ0 | Dmu))
    by (rewrite <- HleadMu; apply (proj1 (divide_content_nth _ _) (Z.divide_refl _))).
  assert (HcqDiv : (Zcontent qZ0 | Dq))
    by (rewrite <- HleadQ; apply (proj1 (divide_content_nth _ _) (Z.divide_refl _))).
  assert (HcmuPos : 0 < Zcontent muZ0) by (pose proof (Zcontent_nonneg muZ0); lia).
  assert (HcqPos : 0 < Zcontent qZ0) by (pose proof (Zcontent_nonneg qZ0); lia).
  assert (HcmuLe : Zcontent muZ0 <= Dmu) by (apply Z.divide_pos_le; [ exact HDmu' | exact HcmuDiv ]).
  assert (HcqLe : Zcontent qZ0 <= Dq) by (apply Z.divide_pos_le; [ exact HDq' | exact HcqDiv ]).
  assert (HcmuEq : Zcontent muZ0 = Dmu) by nia.
  assert (HcqEq : Zcontent qZ0 = Dq) by nia.
  assert (HmuZdiv : Forall (fun z => (Dmu | z)) muZ0)
    by (rewrite <- HcmuEq; apply (proj1 (divide_content_iff _ _) (Z.divide_refl _))).
  assert (HqZdiv : Forall (fun z => (Dq | z)) qZ0)
    by (rewrite <- HcqEq; apply (proj1 (divide_content_iff _ _) (Z.divide_refl _))).
  assert (HmapMu : map IZR (Zprim muZ0) = mu).
  { unfold Zprim. rewrite map_map, HcmuEq. exact (map_div_IZR_eq Dmu muZ0 mu HDmu' HmuZdiv HF2mu). }
  assert (HmapQ : map IZR (Zprim qZ0) = q).
  { unfold Zprim. rewrite map_map, HcqEq. exact (map_div_IZR_eq Dq qZ0 q HDq' HqZdiv HF2q). }
  exists (Zprim muZ0), (Zprim qZ0).
  repeat split.
  - exact HmapMu.
  - unfold Zprim. rewrite length_map, HmuZlen. exact Hmulen.
  - apply eq_IZR.
    pose proof (map_nth IZR (Zprim muZ0) 0%Z d) as Hmn.
    rewrite HmapMu in Hmn. replace (IZR 0%Z) with 0%R in Hmn by (simpl; reflexivity).
    rewrite Hmonic in Hmn. rewrite <- Hmn. simpl. lra.
  - exact HmapQ.
  - intro y. rewrite peval_Zpmul, (peval_eq_pe (Zprim muZ0) y), (peval_eq_pe (Zprim qZ0) y), HmapMu, HmapQ.
    rewrite peval_minpoly_Z, <- pe_minpoly_list, (Hfact y). reflexivity.
Qed.
Close Scope Z_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope R_scope.
(* peval distributes over append, with the second part shifted by the degree. *)
Close Scope R_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope R_scope.
Lemma linear_factor_absurd : forall f g,
  nth 1 f 0%Z = 1%Z -> (forall j, (2 <= j)%nat -> nth j f 0%Z = 0%Z) ->
  (forall y, peval minpoly_Z y = peval f y * peval g y) -> False.
Proof.
  intros f g Hlead Hdeg Hfact.
  destruct f as [|f0 [|f1 rest]].
  - simpl in Hlead. discriminate.
  - simpl in Hlead. discriminate.
  - simpl in Hlead. subst f1.
    set (r := - IZR f0).
    assert (Hfr : peval (f0 :: 1%Z :: rest) r = 0).
    { rewrite (peval_high_zero (f0 :: 1%Z :: rest) 2 Hdeg r). simpl.
      replace (IZR 1) with 1%R by lra. unfold r. ring. }
    assert (Hmpr : minpoly_2cos r = 0).
    { rewrite <- peval_minpoly_Z, (Hfact r), Hfr. ring. }
    apply (minpoly_2cos_no_rat_root r);
      [ unfold r; rewrite <- opp_IZR; apply is_rational_IZR | exact Hmpr ].
Qed.
Close Scope R_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope Z_scope.
(* minpoly_2cos has no monic rational factor of degree 1 to 4.  By monic Gauss
   the factor and cofactor are integer; a degree-1 (or degree-4 via the
   cofactor) factor gives an integer root, excluded by the no-rational-root
   result, while a degree-2 (or degree-3 via the cofactor) factor gives the five
   integer convolution equations excluded by the quadratic check. *)
Lemma minpoly_no_low_factor : forall mu q d,
  Forall is_rational mu -> Forall is_rational q ->
  length mu = S d -> nth d mu 0%R = 1%R -> (1 <= d <= 4)%nat ->
  (forall y, pe minpoly_list y = (pe mu y * pe q y)%R) -> False.
Proof.
  intros mu q d Hmurat Hqrat Hmulen Hmonic Hd Hfact.
  destruct (monic_gauss_factor mu q d Hmurat Hqrat Hmulen Hmonic ltac:(lia) Hfact)
    as [muZ [qZ [HmapMu [HmuZlen [HmuZmonic [HmapQ Hpevalprod]]]]]].
  assert (Hconv : forall k, Zconv muZ qZ k = nth k minpoly_Z 0)
    by (intro k; rewrite <- nth_Zpmul; apply (peval_eq_nth _ _ Hpevalprod k)).
  assert (HprodId : forall k, nth k (Zpmul muZ qZ) 0 = (1 * 1) * nth k minpoly_Z 0)
    by (intro k; rewrite nth_Zpmul, Hconv; ring).
  assert (HmuZmonicNz : nth d muZ 0 <> 0) by (rewrite HmuZmonic; lia).
  pose proof (high_coeff_zero muZ qZ 1 1 d HmuZlen HmuZmonicNz HprodId) as HqZhigh.
  assert (Hmudeg : forall i, (d < i)%nat -> nth i muZ 0 = 0) by (intros i Hi; apply nth_overflow; lia).
  assert (HqdegB : forall j, ((5 - d) < j)%nat -> nth j qZ 0 = 0) by (intros j Hj; apply HqZhigh; lia).
  assert (Hm5 : nth 5 minpoly_Z 0 = 1) by reflexivity.
  assert (HqZlead : nth (5 - d) qZ 0 = 1).
  { pose proof (Zconv_top muZ qZ d (5 - d) Hmudeg HqdegB) as Htop.
    replace (d + (5 - d))%nat with 5%nat in Htop by lia.
    rewrite Hconv, Hm5, HmuZmonic in Htop. lia. }
  assert (Hfactlr : forall y, peval minpoly_Z y = (peval muZ y * peval qZ y)%R)
    by (intro y; rewrite <- Hpevalprod, peval_Zpmul; reflexivity).
  assert (Hfactrl : forall y, peval minpoly_Z y = (peval qZ y * peval muZ y)%R)
    by (intro y; rewrite <- Hpevalprod, peval_Zpmul; ring).
  destruct d as [|[|[|[|[|d']]]]]; try lia.
  - (* d = 1: muZ linear *)
    apply (linear_factor_absurd muZ qZ HmuZmonic).
    + intros j Hj. apply nth_overflow. lia.
    + exact Hfactlr.
  - (* d = 2: muZ quadratic *)
    destruct muZ as [|s [|m [|e [|x tl]]]]; simpl in HmuZlen; try lia.
    simpl in HmuZmonic. subst e.
    pose proof (Hconv 0%nat) as H0. pose proof (Hconv 1%nat) as H1. pose proof (Hconv 2%nat) as H2.
    pose proof (Hconv 3%nat) as H3. pose proof (Hconv 4%nat) as H4.
    cbn [Zconv nth minpoly_Z] in H0, H1, H2, H3, H4.
    assert (Hq3 : nth 3%nat qZ 0 = 1) by exact HqZlead.
    assert (Hq4 : nth 4%nat qZ 0 = 0) by (apply HqdegB; lia).
    rewrite Hq3 in H3. rewrite Hq3, Hq4 in H4.
    apply (minpoly_quad_coeffs_absurd s m (nth 2%nat qZ 0) (nth 1%nat qZ 0) (nth 0%nat qZ 0)); nia.
  - (* d = 3: qZ quadratic, muZ cubic *)
    destruct muZ as [|cc [|bb [|aa [|e [|x tl]]]]]; simpl in HmuZlen; try lia.
    simpl in HmuZmonic. subst e.
    pose proof (Hconv 0%nat) as H0. pose proof (Hconv 1%nat) as H1. pose proof (Hconv 2%nat) as H2.
    pose proof (Hconv 3%nat) as H3. pose proof (Hconv 4%nat) as H4.
    cbn [Zconv nth minpoly_Z] in H0, H1, H2, H3, H4.
    assert (Hq2 : nth 2%nat qZ 0 = 1) by exact HqZlead.
    assert (Hq3 : nth 3%nat qZ 0 = 0) by (apply HqdegB; lia).
    assert (Hq4 : nth 4%nat qZ 0 = 0) by (apply HqdegB; lia).
    rewrite Hq2 in H2, H3, H4. rewrite Hq3 in H3, H4. rewrite Hq4 in H4.
    apply (minpoly_quad_coeffs_absurd (nth 0%nat qZ 0) (nth 1%nat qZ 0) aa bb cc); nia.
  - (* d = 4: qZ linear *)
    apply (linear_factor_absurd qZ muZ HqZlead).
    + intros j Hj. apply HqdegB. lia.
    + exact Hfactrl.
Qed.
Close Scope Z_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope R_scope.
(* #8 resolved: cos(2 pi / 11) is not origami-constructible.  If it were, so
   would 2 cos(2 pi / 11) = delta, whose rational vector space Qx delta has a
   power basis of two-three-smooth dimension d.  The minimal polynomial of delta
   has degree 5, so delta^5 lies in the span of 1, delta, ..., delta^4 and the
   dimension d is at most 5; being two-three-smooth and at most 5 forces d in
   {1,2,3,4}.  But then the minimal polynomial of delta factors with a monic
   rational factor of that degree, contradicting the irreducibility of
   minpoly_2cos.  The hendecagon therefore cannot be constructed by single-fold
   origami. *)
Theorem cos_2pi_11_not_origami : ~ OrigamiNum cos_2pi_11.
Proof.
  intro HO.
  assert (Hdelta : OrigamiNum (2 * cos_2pi_11)).
  { replace (2 * cos_2pi_11) with (cos_2pi_11 + cos_2pi_11) by ring. apply ON_add; exact HO. }
  set (delta := 2 * cos_2pi_11) in *.
  destruct (origami_field_degree_smooth delta Hdelta) as [d [Hbasis Hsmooth]].
  destruct Hbasis as [HQxB [Hli Hspanning]].
  assert (Hroot : pe minpoly_list delta = 0).
  { rewrite pe_minpoly_list. exact double_cos_2pi_11_minimal_poly. }
  assert (Hspan5 : spans is_rational (powers delta 5) (delta ^ 5)).
  { exists (IZR (-1) :: IZR (-3) :: IZR 3 :: IZR 4 :: IZR (-1) :: nil).
    split; [rewrite powers_length; reflexivity |].
    split; [repeat constructor; apply is_rational_IZR |].
    pose proof double_cos_2pi_11_minimal_poly as H. unfold minpoly_2cos in H.
    fold delta in H. unfold powers. cbn [seq map Fcomb]. nra. }
  assert (Hspanning5 : spanning is_rational (powers delta 5) (Qx delta))
    by (intros v Hv; apply (Qx_spanned_by_powers delta 5 v Hspan5 Hv)).
  assert (Hd5 : (d <= 5)%nat).
  { pose proof (indep_le_span is_rational (powers delta d) (powers delta 5) (Qx delta)
                  is_rational_subfield Hli HQxB Hspanning5) as Hle.
    rewrite !powers_length in Hle. exact Hle. }
  assert (Hd14 : (1 <= d <= 4)%nat).
  { assert (Hne0 : d <> 0%nat).
    { intro Hd0. subst d. destruct Hsmooth as [a [b Hab]].
      pose proof (Nat.pow_nonzero 2 a ltac:(lia)). pose proof (Nat.pow_nonzero 3 b ltac:(lia)). nia. }
    assert (Hne5 : d <> 5%nat) by (intro H5; subst d; apply five_not_2_3_smooth; exact Hsmooth).
    lia. }
  assert (HspanD : spans is_rational (powers delta d) (delta ^ d))
    by (apply Hspanning; apply (subring_pow (Qx delta) delta d (Qx_subring delta) (Qx_x delta))).
  destruct (minpoly_low_degree_factors delta d Hli HspanD Hroot ltac:(lia))
    as [mu [q [Hmulen [Hmonic [Hmurat [Hqrat Hfact]]]]]].
  exact (minpoly_no_low_factor mu q d Hmurat Hqrat Hmulen Hmonic Hd14 Hfact).
Qed.

(* Truncating a power family for the exact-degree argument. *)
Close Scope R_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope R_scope.
Theorem cos_2pi_11_degree_exactly_5 :
  basis is_rational (powers (2 * cos_2pi_11) 5) (Qx (2 * cos_2pi_11)).
Proof.
  set (delta := 2 * cos_2pi_11).
  assert (Hroot : pe minpoly_list delta = 0)
    by (rewrite pe_minpoly_list; exact double_cos_2pi_11_minimal_poly).
  assert (Hdep6 : ~ lin_indep is_rational (powers delta 6)).
  { intro Hli.
    assert (Hlen : length minpoly_list = length (powers delta 6))
      by (rewrite powers_length; reflexivity).
    assert (Hfc : Fcomb minpoly_list (powers delta 6) = 0) by (unfold pe in Hroot; exact Hroot).
    pose proof (Hli minpoly_list Hlen minpoly_list_rational Hfc) as Hall.
    pose proof (Forall_inv Hall) as Hhd. lra. }
  destruct (nat_boundary (fun k => lin_indep is_rational (powers delta k)) 5
              (lin_indep_nil is_rational) Hdep6) as [d [Hindd Hdepd]].
  assert (Hd5 : d = 5%nat).
  { assert (Hle5 : (d <= 5)%nat).
    { destruct (le_lt_dec d 5) as [Hok | Hgt]; [exact Hok | exfalso].
      apply Hdep6. apply (lin_indep_powers_le delta 6 d ltac:(lia) Hindd). }
    assert (Hge5 : (5 <= d)%nat).
    { destruct (le_lt_dec 5 d) as [Hok | Hlt]; [exact Hok | exfalso].
      assert (Hd1 : (1 <= d)%nat).
      { destruct d as [|d']; [| lia]. exfalso. apply Hdepd.
        intros cs Hlen Hrat Hfc.
        destruct cs as [|c0 cs']; simpl in Hlen; [lia|].
        destruct cs' as [|c1 cs'']; simpl in Hlen; [| lia].
        assert (Hc0 : c0 = 0). { cbn in Hfc. lra. }
        subst c0. constructor; [reflexivity | constructor]. }
      assert (Hd4 : (d <= 4)%nat) by lia.
      pose proof (Qx_powers_basis delta d Hindd Hdepd) as Hb.
      destruct Hb as [HBd [Hlid Hspd]].
      assert (HspanD : spans is_rational (powers delta d) (delta ^ d))
        by (apply Hspd; apply (subring_pow (Qx delta) delta d (Qx_subring delta) (Qx_x delta))).
      destruct (minpoly_low_degree_factors delta d Hlid HspanD Hroot Hd4)
        as [mu [q [Hmulen [Hmonic [Hmurat [Hqrat Hfact]]]]]].
      exact (minpoly_no_low_factor mu q d Hmurat Hqrat Hmulen Hmonic (conj Hd1 Hd4) Hfact). }
    lia. }
  subst d. exact (Qx_powers_basis delta 5 Hindd Hdepd).
Qed.

(* monic minimal polynomial of 2 cos(2 pi / 7): y^3 + y^2 - 2 y - 1. *)
Definition minpoly_7_list : list R := (-1) :: (-2) :: 1 :: 1 :: nil.

Lemma minpoly_7_list_rational : Forall is_rational minpoly_7_list.
Proof.
  unfold minpoly_7_list. repeat constructor;
    [ apply (is_rational_IZR (-1)) | apply (is_rational_IZR (-2))
    | apply (is_rational_IZR 1) | apply (is_rational_IZR 1) ].
Qed.

Lemma pe_minpoly_7_list : forall y, pe minpoly_7_list y = y*y*y + 1*(y*y) + (-2)*y + (-1).
Proof.
  intro y. unfold minpoly_7_list. rewrite !pe_cons, pe_nil. ring.
Qed.

Lemma double_cos_2pi_7_root : pe minpoly_7_list (2 * cos_2pi_7) = 0.
Proof.
  rewrite pe_minpoly_7_list. pose proof cos_2pi_7_cubic_form. nra.
Qed.

(* closure of the rationals under ring operations, for ad hoc membership goals *)
Ltac rclose := repeat first
  [ assumption | exact is_rational_subfield
  | apply (subfield_add is_rational) | apply (subfield_sub is_rational)
  | apply (subfield_mul is_rational) | apply (subfield_opp is_rational) ].

(* #9 resolved: the algebraic degree of 2 cos(2 pi / 7) is exactly 3, exhibited
   as a power basis of Qx of length 3.  The minimal polynomial gives a degree-4
   dependency, so the boundary degree is at most 3; a degree-1 dependency makes
   the angle a rational root, and a degree-2 dependency yields, via the cubic
   relation and independence of {1, delta}, an explicit rational root
   (c1 - c2)/c2 -- both excluded by the no-rational-root result, so the boundary
   is exactly 3. *)
Theorem cos_2pi_7_degree_exactly_3 :
  basis is_rational (powers (2 * cos_2pi_7) 3) (Qx (2 * cos_2pi_7)).
Proof.
  set (delta := 2 * cos_2pi_7).
  assert (Hcubic : pe minpoly_7_list delta = 0) by exact double_cos_2pi_7_root.
  assert (HcubicR : delta*delta*delta + 1*(delta*delta) + (-2)*delta + (-1) = 0)
    by (rewrite pe_minpoly_7_list in Hcubic; exact Hcubic).
  clearbody delta.
  assert (Hdep4 : ~ lin_indep is_rational (powers delta 4)).
  { intro Hli.
    assert (Hlen : length minpoly_7_list = length (powers delta 4)) by (rewrite powers_length; reflexivity).
    assert (Hfc : Fcomb minpoly_7_list (powers delta 4) = 0) by (unfold pe in Hcubic; exact Hcubic).
    pose proof (Forall_inv (Hli minpoly_7_list Hlen minpoly_7_list_rational Hfc)) as Hhd.
    simpl in Hhd. lra. }
  destruct (nat_boundary (fun k => lin_indep is_rational (powers delta k)) 3
              (lin_indep_nil is_rational) Hdep4) as [d [Hindd Hdepd]].
  assert (Hd3 : d = 3%nat).
  { assert (Hle3 : (d <= 3)%nat).
    { destruct (le_lt_dec d 3) as [Hok|Hgt]; [exact Hok | exfalso].
      apply Hdep4. apply (lin_indep_powers_le delta 4 d ltac:(lia) Hindd). }
    assert (Hge3 : (3 <= d)%nat).
    { destruct (le_lt_dec 3 d) as [Hok|Hlt]; [exact Hok | exfalso].
      apply not_all_ex_not in Hdepd. destruct Hdepd as [cs Hcs].
      apply imply_to_and in Hcs. destruct Hcs as [Hcslen Hcs].
      apply imply_to_and in Hcs. destruct Hcs as [Hcsrat Hcs].
      apply imply_to_and in Hcs. destruct Hcs as [Hcsfc Hcsnz].
      rewrite powers_length in Hcslen.
      destruct d as [|[|[|d']]]; [ | | | lia ].
      - (* d = 0 *)
        destruct cs as [|c0 [|? ?]]; simpl in Hcslen; try lia.
        apply Hcsnz. constructor; [ cbn in Hcsfc; lra | constructor ].
      - (* d = 1 *)
        destruct cs as [|c0 [|c1 [|? ?]]]; simpl in Hcslen; try lia.
        pose proof (Forall_inv Hcsrat) as Hc0r. pose proof (Forall_inv (Forall_inv_tail Hcsrat)) as Hc1r.
        cbn in Hcsfc.
        destruct (Req_dec c1 0) as [Hc1z | Hc1nz].
        + subst c1. apply Hcsnz. constructor; [ lra | constructor; [ reflexivity | constructor ] ].
        + assert (Hde : delta = - c0 / c1).
          { apply (Rmult_eq_reg_l c1); [ | exact Hc1nz ]. field_simplify; [ lra | exact Hc1nz ]. }
          assert (Hrat : is_rational delta).
          { rewrite Hde. apply subfield_div;
              [ apply is_rational_subfield
              | apply subfield_opp; [ apply is_rational_subfield | exact Hc0r ]
              | exact Hc1r | exact Hc1nz ]. }
          apply (heptagon_cubic_no_rat_root delta Hrat). exact HcubicR.
      - (* d = 2 *)
        destruct cs as [|c0 [|c1 [|c2 [|? ?]]]]; simpl in Hcslen; try lia.
        pose proof (Forall_inv Hcsrat) as Hc0r.
        pose proof (Forall_inv (Forall_inv_tail Hcsrat)) as Hc1r.
        pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail Hcsrat))) as Hc2r.
        cbn in Hcsfc.
        destruct (Req_dec c2 0) as [Hc2z | Hc2nz].
        + (* c2 = 0: reduces to a linear relation *)
          subst c2. destruct (Req_dec c1 0) as [Hc1z | Hc1nz].
          * subst c1. apply Hcsnz. constructor; [ lra | constructor; [ reflexivity | constructor; [ reflexivity | constructor ] ] ].
          * assert (Hde : delta = - c0 / c1).
            { apply (Rmult_eq_reg_l c1); [ | exact Hc1nz ]. field_simplify; [ lra | exact Hc1nz ]. }
            assert (Hrat : is_rational delta).
            { rewrite Hde. apply subfield_div;
                [ apply is_rational_subfield
                | apply subfield_opp; [ apply is_rational_subfield | exact Hc0r ]
                | exact Hc1r | exact Hc1nz ]. }
            apply (heptagon_cubic_no_rat_root delta Hrat). exact HcubicR.
        + (* c2 <> 0: extract the rational root e = (c1 - c2)/c2 *)
          assert (Hdep : c0 + c1*delta + c2*(delta*delta) = 0) by nra.
          set (K0 := c0*c1 - c0*c2 - c2*c2).
          set (K1 := c1*c1 - c0*c2 - c1*c2 - (c2*c2 + c2*c2)).
          assert (HKfc : Fcomb (K0 :: K1 :: nil) (powers delta 2) = 0).
          { replace (Fcomb (K0 :: K1 :: nil) (powers delta 2)) with (K0 + K1 * delta)
              by (unfold powers; cbn [seq map Fcomb]; ring).
            transitivity (c2*c2*(delta*delta*delta + 1*(delta*delta) + (-2)*delta + (-1))
                          + (c1 - c2 - c2*delta)*(c0 + c1*delta + c2*(delta*delta))).
            - unfold K0, K1. ring.
            - rewrite HcubicR, Hdep. ring. }
          assert (HKlen : length (K0 :: K1 :: nil) = length (powers delta 2))
            by (rewrite powers_length; reflexivity).
          assert (HK0r : is_rational K0) by (unfold K0; rclose).
          assert (HK1r : is_rational K1) by (unfold K1; rclose).
          assert (HKrat : Forall is_rational (K0 :: K1 :: nil)).
          { apply Forall_cons; [ exact HK0r | apply Forall_cons; [ exact HK1r | apply Forall_nil ] ]. }
          pose proof (Hindd (K0 :: K1 :: nil) HKlen HKrat HKfc) as HK.
          pose proof (Forall_inv HK) as HK0. pose proof (Forall_inv (Forall_inv_tail HK)) as HK1.
          set (e := (c1 - c2) / c2).
          assert (Hrate : is_rational e).
          { unfold e. apply subfield_div;
              [ apply is_rational_subfield | apply subfield_sub; [ apply is_rational_subfield | exact Hc1r | exact Hc2r ]
              | exact Hc2r | exact Hc2nz ]. }
          assert (Hc2c : c2*c2*c2 <> 0).
          { intro Hc. apply Rmult_integral in Hc. destruct Hc as [Hc | Hc].
            - apply Rmult_integral in Hc. destruct Hc; apply Hc2nz; assumption.
            - apply Hc2nz; exact Hc. }
          apply (heptagon_cubic_no_rat_root e Hrate).
          apply (Rmult_eq_reg_l (c2*c2*c2)); [ | exact Hc2c ].
          rewrite Rmult_0_r.
          transitivity (c2 * K0 + (c1 - c2) * K1).
          * unfold e, K0, K1. field. exact Hc2nz.
          * rewrite HK0, HK1. ring. }
    lia. }
  subst d. exact (Qx_powers_basis delta 3 Hindd Hdepd).
Qed.
Close Scope R_scope.
Close Scope R_scope.
Open Scope R_scope.
(* ============================================================================
   Eisenstein's irreducibility criterion over Z, built on the content and
   convolution machinery above. A polynomial whose lower coefficients are all
   divisible by a prime pi, whose leading coefficient is not, and whose constant
   term is not divisible by pi^2, has no factorization into two integer
   polynomials of positive degree. This is the engine for cyclotomic
   irreducibility (Phi_p via the shift x -> x+1).
   ============================================================================ *)
Close Scope R_scope.
Open Scope R_scope.
Open Scope Z_scope.
(* Convolution is commutative, via real evaluation being a commutative product. *)
Close Scope Z_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Close Scope R_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
(* ============================================================================
   Dickson polynomials D_k (integer coefficient lists): D_0 = 2, D_1 = Y,
   D_{k+1} = Y*D_k - D_{k-1}.  They satisfy the Laurent identity
   D_k(x + 1/x) = x^k + x^(-k) and the Chebyshev relation D_k(2 cos t) = 2 cos(k t),
   the engine for the minimal polynomial of 2cos(2pi/p) at a general prime p.
   ============================================================================ *)
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope R_scope.
Fixpoint dickson (k : nat) : list Z :=
  match k with
  | O => 2%Z :: nil
  | S O => 0%Z :: 1%Z :: nil
  | S (S k' as k1) => Zpadd (0%Z :: dickson k1) (map (Z.mul (-1)%Z) (dickson k'))
  end.

Lemma dickson_SS : forall k',
  dickson (S (S k')) = Zpadd (0%Z :: dickson (S k')) (map (Z.mul (-1)%Z) (dickson k')).
Proof. reflexivity. Qed.

(* the defining trigonometric/Laurent identity, for x <> 0 *)
Lemma peval_dickson : forall k x, x <> 0 ->
  peval (dickson k) (x + / x) = x ^ k + / x ^ k.
Proof.
  intro k. induction k as [k IH] using (well_founded_induction lt_wf).
  intro x. destruct k as [|[|k']]; intro Hx.
  - simpl. replace (IZR 2%Z) with 2 by (simpl; lra). field. exact Hx.
  - cbn [dickson peval]. replace (IZR 0%Z) with 0 by (simpl; lra).
    replace (IZR 1%Z) with 1 by (simpl; lra). simpl. field. exact Hx.
  - rewrite dickson_SS, peval_Zpadd, peval_map_Zmul.
    cbn [peval]. replace (IZR 0%Z) with 0 by (simpl; lra).
    replace (IZR (-1)%Z) with (-1) by (simpl; lra).
    rewrite (IH (S k') ltac:(lia) x Hx), (IH k' ltac:(lia) x Hx).
    assert (Hxk : x ^ k' <> 0) by (apply pow_nonzero; exact Hx).
    simpl pow. field. split; [exact Hxk | exact Hx].
Qed.

(* the Chebyshev relation: D_k(2 cos t) = 2 cos (k t) *)
Lemma dickson_cos : forall k t, peval (dickson k) (2 * cos t) = 2 * cos (INR k * t).
Proof.
  intro k. induction k as [k IH] using (well_founded_induction lt_wf).
  intro t. destruct k as [|[|k']].
  - cbn [dickson peval]. replace (IZR 2%Z) with 2 by (simpl; lra).
    simpl INR. rewrite Rmult_0_l, cos_0. ring.
  - cbn [dickson peval]. replace (IZR 0%Z) with 0 by (simpl; lra).
    replace (IZR 1%Z) with 1 by (simpl; lra). simpl INR. ring_simplify (1 * t). ring.
  - rewrite dickson_SS, peval_Zpadd, peval_map_Zmul.
    cbn [peval]. replace (IZR 0%Z) with 0 by (simpl; lra).
    replace (IZR (-1)%Z) with (-1) by (simpl; lra).
    rewrite (IH (S k') ltac:(lia) t), (IH k' ltac:(lia) t).
    repeat rewrite S_INR. set (a := INR k').
    replace (a * t) with ((a + 1) * t - t) by ring.
    replace ((a + 1 + 1) * t) with ((a + 1) * t + t) by ring.
    rewrite cos_plus, cos_minus. ring.
Qed.
Close Scope R_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
(* ============================================================================
   Cosine sums (Dirichlet kernel) and the minimal polynomial psi_m of
   2cos(2pi/(2m+1)).  psi_m = 1 + D_1 + ... + D_m has 2cos(2pi/(2m+1)) as a root
   for every odd modulus; with cyclotomic_prime_irreducible this drives the
   degree-(p-1)/2 result at prime p.
   ============================================================================ *)
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope R_scope.
Fixpoint psi (m : nat) : list Z :=
  match m with
  | O => 1%Z :: nil
  | S m' => Zpadd (psi m') (dickson (S m'))
  end.

Lemma psi_S : forall m', psi (S m') = Zpadd (psi m') (dickson (S m')).
Proof. reflexivity. Qed.

(* psi evaluated at 2 cos t telescopes to the cosine sum *)
Lemma peval_psi_cos : forall m t, peval (psi m) (2 * cos t) = 2 * cossum (S m) t - 1.
Proof.
  induction m as [|m IH]; intro t.
  - cbn [psi peval]. replace (IZR 1%Z) with 1 by (simpl; lra).
    cbn [cossum]. simpl INR. rewrite Rmult_0_l, cos_0. ring.
  - rewrite psi_S, peval_Zpadd, IH, dickson_cos. cbn [cossum]. ring.
Qed.

(* the half-period value of the cosine sum: (m + 1/2) * (2 pi/(2m+1)) = pi *)
Close Scope R_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope R_scope.
Lemma psi_root : forall m, (1 <= m)%nat ->
  peval (psi m) (2 * cos (2 * PI / INR (2*m+1))) = 0.
Proof.
  intros m Hm. rewrite peval_psi_cos, (cossum_Sm_half m Hm). lra.
Qed.

Lemma length_dickson : forall k, length (dickson k) = S k.
Proof.
  intro k. induction k as [k IH] using (well_founded_induction lt_wf).
  destruct k as [|[|k']]; [reflexivity | reflexivity |].
  rewrite dickson_SS, length_Zpadd, length_map. cbn [length].
  rewrite (IH (S k') ltac:(lia)), (IH k' ltac:(lia)). lia.
Qed.

Lemma length_psi : forall m, length (psi m) = S m.
Proof.
  induction m as [|m IH].
  - reflexivity.
  - rewrite psi_S, length_Zpadd, length_dickson, IH. cbn [length]. lia.
Qed.

(* geometric-sum identity: (x - 1) * Phi_n = x^n - 1, rearranged *)
Close Scope R_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope R_scope.
Lemma peval_psi_geom : forall m x, x <> 0 ->
  x ^ m * peval (psi m) (x + / x) = peval (repeat 1%Z (2*m+1)) x.
Proof.
  induction m as [|m IH]; intros x Hx.
  - simpl. cbn [psi peval]. replace (IZR 1%Z) with 1 by (simpl; lra). ring.
  - rewrite psi_S, peval_Zpadd, (peval_dickson (S m) x Hx), Rmult_plus_distr_l.
    replace (x ^ S m * peval (psi m) (x + / x)) with (x * (x ^ m * peval (psi m) (x + / x)))
      by (simpl pow; ring).
    rewrite (IH x Hx).
    assert (Hxm : x ^ S m <> 0) by (apply pow_nonzero; exact Hx).
    replace (x ^ S m * (x ^ S m + / x ^ S m)) with (x ^ (2*m+2) + 1).
    2:{ replace (x ^ (2*m+2)) with (x ^ S m * x ^ S m)
          by (rewrite <- pow_add; f_equal; lia). field; exact Hxm. }
    replace (2 * S m + 1)%nat with ((2*m+1) + 2)%nat by lia.
    rewrite peval_repeat1_two, peval_repeat1_geom.
    replace (2*m+1+1)%nat with (2*m+2)%nat by lia. ring.
Qed.

(* plift psi_m has the same coefficients as Phi_{2m+1}: the cyclotomic transfer *)
Lemma plift_psi_phi : forall m k, nth k (plift (psi m)) 0%Z = nth k (repeat 1%Z (2*m+1)) 0%Z.
Proof.
  intros m. apply peval_eq_nth_punctured. intros x Hx.
  pose proof (plift_char (psi m) x Hx) as Hpc. rewrite length_psi in Hpc.
  apply (Rmult_eq_reg_l x); [| exact Hx].
  rewrite Hpc.
  replace (x ^ S m * peval (psi m) (x + / x)) with (x * (x ^ m * peval (psi m) (x + / x)))
    by (simpl pow; ring).
  rewrite (peval_psi_geom m x Hx). reflexivity.
Qed.
Close Scope R_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
(* General cyclotomic irreducibility transfer: for prime p = 2m+1, the minimal
   polynomial psi_m of 2cos(2pi/p) admits no positive-degree integer factorization,
   because plift sends any such factorization to one of Phi_p. *)
Theorem psi_no_factor : forall m G H dG dH,
  Znumtheory.prime (Z.of_nat (2*m+1)) ->
  (1 <= dG)%nat -> (1 <= dH)%nat -> (dG + dH = m)%nat ->
  length G = S dG -> length H = S dH ->
  (forall k, nth k (psi m) 0%Z = Zconv G H k) ->
  False.
Proof.
  intros m G H dG dH Hprime HdG HdH Hsum HlenG HlenH Hfact.
  assert (HGn : G <> nil) by (intro Hc; rewrite Hc in HlenG; simpl in HlenG; lia).
  assert (HHn : H <> nil) by (intro Hc; rewrite Hc in HlenH; simpl in HlenH; lia).
  assert (HlenZ : length (Zpmul G H) = S m)
    by (rewrite length_Zpmul by assumption; rewrite HlenG, HlenH; lia).
  assert (Heq : psi m = Zpmul G H).
  { apply (nth_ext (psi m) (Zpmul G H) 0%Z 0%Z).
    - rewrite HlenZ, length_psi. reflexivity.
    - intros k Hk. rewrite Hfact, nth_Zpmul. reflexivity. }
  set (G' := firstn (S (2 * dG)) (plift G)).
  set (H' := firstn (S (2 * dH)) (plift H)).
  assert (HGeq : forall k, nth k G' 0%Z = nth k (plift G) 0%Z).
  { intro k. unfold G'. destruct (Nat.lt_ge_cases k (S (2 * dG))) as [Hlt|Hge].
    - apply nth_firstn_eq; exact Hlt.
    - rewrite nth_overflow with (l := firstn (S (2 * dG)) (plift G)).
      + symmetry. apply plift_high_zero. rewrite HlenG. lia.
      + rewrite length_firstn, length_plift by exact HGn. rewrite HlenG. lia. }
  assert (HHeq : forall k, nth k H' 0%Z = nth k (plift H) 0%Z).
  { intro k. unfold H'. destruct (Nat.lt_ge_cases k (S (2 * dH))) as [Hlt|Hge].
    - apply nth_firstn_eq; exact Hlt.
    - rewrite nth_overflow with (l := firstn (S (2 * dH)) (plift H)).
      + symmetry. apply plift_high_zero. rewrite HlenH. lia.
      + rewrite length_firstn, length_plift by exact HHn. rewrite HlenH. lia. }
  apply (cyclotomic_prime_irreducible (2*m+1) G' H' (2 * dG)%nat (2 * dH)%nat).
  - exact Hprime.
  - lia.
  - lia.
  - lia.
  - unfold G'. rewrite length_firstn, length_plift by exact HGn. rewrite HlenG. lia.
  - unfold H'. rewrite length_firstn, length_plift by exact HHn. rewrite HlenH. lia.
  - intro k. transitivity (nth k (plift (psi m)) 0%Z).
    + symmetry. apply plift_psi_phi.
    + rewrite Heq, plift_Zpmul_nth by assumption. rewrite <- nth_Zpmul.
      apply peval_eq_nth. intro y. rewrite !peval_Zpmul.
      rewrite (peval_ext G' (plift G) HGeq), (peval_ext H' (plift H) HHeq). reflexivity.
Qed.

(* psi_m is monic of degree m with content 1: the inputs the monic Gauss step needs *)
Lemma dickson_monic : forall k, (1 <= k)%nat -> nth k (dickson k) 0%Z = 1%Z.
Proof.
  intro k. induction k as [k IH] using (well_founded_induction lt_wf).
  intro Hk. destruct k as [|[|k']]; [lia | reflexivity |].
  rewrite dickson_SS, nth_Zpadd. cbn [nth].
  rewrite (IH (S k') ltac:(lia) ltac:(lia)), nth_map_Zmul.
  rewrite (nth_overflow (dickson k')) by (rewrite length_dickson; lia). ring.
Qed.

Lemma psi_monic : forall m, nth m (psi m) 0%Z = 1%Z.
Proof.
  induction m as [|m IH]; [reflexivity|].
  rewrite psi_S, nth_Zpadd.
  rewrite (nth_overflow (psi m)) by (rewrite length_psi; lia).
  rewrite (dickson_monic (S m) ltac:(lia)). ring.
Qed.

Lemma Zcontent_psi : forall m, Zcontent (psi m) = 1%Z.
Proof.
  intro m.
  assert (Hdiv : (Zcontent (psi m) | 1%Z)).
  { rewrite <- (psi_monic m). apply (proj1 (divide_content_nth _ _) (Z.divide_refl _)). }
  pose proof (Zcontent_nonneg (psi m)) as Hnn.
  assert (Hpos : 0 < Zcontent (psi m)).
  { destruct (Z.eq_dec (Zcontent (psi m)) 0) as [H0|H0]; [exfalso | lia].
    rewrite H0 in Hdiv. destruct Hdiv as [c Hc]. lia. }
  assert (Hle : Zcontent (psi m) <= 1) by (apply Z.divide_pos_le; [lia | exact Hdiv]).
  lia.
Qed.

(* ============================================================================
   Degree of 2cos(2pi/p) at a general prime p = 2m+1: a polynomial-generic monic
   Gauss step (monic_gauss_factor_gen) feeds psi_no_factor, and the nat_boundary /
   Qx_powers_basis argument pins the algebraic degree to m = (p-1)/2.
   ============================================================================ *)
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Lemma minpoly_no_low_factor_psi : forall m mu q d,
  Znumtheory.prime (Z.of_nat (2*m+1)) ->
  Forall is_rational mu -> Forall is_rational q ->
  length mu = S d -> nth d mu 0%R = 1%R -> (1 <= d <= m-1)%nat ->
  (forall y, pe (map IZR (psi m)) y = (pe mu y * pe q y)%R) -> False.
Proof.
  intros m mu q d Hprime Hmurat Hqrat Hmulen Hmonic Hd Hfact.
  destruct (monic_gauss_factor_gen (psi m) m mu q d (length_psi m) (psi_monic m) (Zcontent_psi m)
              Hmurat Hqrat Hmulen Hmonic ltac:(lia) Hfact)
    as [muZ [qZ [HmapMu [HmuZlen [HmuZmonic [HmapQ Hpevalprod]]]]]].
  assert (Hconv : forall k, Zconv muZ qZ k = nth k (psi m) 0)
    by (intro k; rewrite <- nth_Zpmul; apply (peval_eq_nth _ _ Hpevalprod k)).
  assert (HprodId : forall k, nth k (Zpmul muZ qZ) 0 = (1 * 1) * nth k (psi m) 0)
    by (intro k; rewrite nth_Zpmul, Hconv; ring).
  assert (HmuZmonicNz : nth d muZ 0 <> 0) by (rewrite HmuZmonic; lia).
  assert (Hfdeg : forall j, (m < j)%nat -> nth j (psi m) 0%Z = 0%Z)
    by (intros j Hj; apply nth_overflow; rewrite length_psi; lia).
  pose proof (high_coeff_zero_gen (psi m) m muZ qZ 1 1 d Hfdeg HmuZlen HmuZmonicNz HprodId) as HqZhigh.
  assert (Hmudeg : forall i, (d < i)%nat -> nth i muZ 0 = 0) by (intros i Hi; apply nth_overflow; lia).
  assert (HqdegB : forall j, ((m - d) < j)%nat -> nth j qZ 0 = 0) by (intros j Hj; apply HqZhigh; lia).
  assert (HqZlead : nth (m - d) qZ 0 = 1).
  { pose proof (Zconv_top muZ qZ d (m - d) Hmudeg HqdegB) as Htop.
    replace (d + (m - d))%nat with m in Htop by lia.
    rewrite Hconv, (psi_monic m), HmuZmonic in Htop. lia. }
  assert (HqZlen : (S (m - d) <= length qZ)%nat).
  { destruct (Nat.le_gt_cases (length qZ) (m - d)) as [Hle | Hgt].
    - rewrite nth_overflow in HqZlead by exact Hle. lia.
    - lia. }
  apply (psi_no_factor m muZ (firstn (S (m - d)) qZ) d (m - d)%nat Hprime).
  - lia.
  - lia.
  - lia.
  - exact HmuZlen.
  - rewrite length_firstn. lia.
  - intro k. rewrite <- Hconv, <- !nth_Zpmul.
    apply (peval_eq_nth (Zpmul muZ qZ) (Zpmul muZ (firstn (S (m - d)) qZ))).
    intro y. rewrite !peval_Zpmul. f_equal.
    apply peval_ext. intro j.
    destruct (Nat.lt_ge_cases j (S (m - d))) as [Hlt | Hge].
    + symmetry. apply nth_firstn_eq; exact Hlt.
    + rewrite (nth_overflow (firstn (S (m - d)) qZ)) by (rewrite length_firstn; lia).
      apply HqdegB. lia.
Qed.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope R_scope.
(* The algebraic degree of 2cos(2pi/p) over Q is exactly (p-1)/2 = m for prime
   p = 2m+1: psi_m gives a degree-(m+1) power dependency, and any lower boundary
   would yield a monic rational factor excluded by minpoly_no_low_factor_psi. *)
Theorem cos_2pi_p_degree_exactly : forall m, (1 <= m)%nat ->
  Znumtheory.prime (Z.of_nat (2*m+1)) ->
  basis is_rational (powers (2 * cos (2 * PI / INR (2*m+1))) m)
                    (Qx (2 * cos (2 * PI / INR (2*m+1)))).
Proof.
  intros m Hm Hprime.
  set (delta := 2 * cos (2 * PI / INR (2*m+1))).
  set (fR := map IZR (psi m)).
  assert (HfRrat : Forall is_rational fR).
  { unfold fR. apply Forall_forall. intros z Hz. apply in_map_iff in Hz.
    destruct Hz as [x [Hx _]]. subst z. apply is_rational_IZR. }
  assert (Hroot : pe fR delta = 0).
  { unfold fR, delta. rewrite <- peval_eq_pe. apply psi_root. exact Hm. }
  assert (HfRlen : length fR = S m) by (unfold fR; rewrite length_map; apply length_psi).
  assert (Hval : nth m fR 0%R = 1%R).
  { unfold fR. change (0%R) with (IZR 0%Z). rewrite map_nth, psi_monic. simpl. reflexivity. }
  assert (Hdep : ~ lin_indep is_rational (powers delta (S m))).
  { intro Hli.
    assert (Hlen : length fR = length (powers delta (S m)))
      by (rewrite powers_length, HfRlen; reflexivity).
    assert (Hfc : Fcomb fR (powers delta (S m)) = 0) by (rewrite <- HfRlen; exact Hroot).
    pose proof (Hli fR Hlen HfRrat Hfc) as Hall.
    assert (Hin : In (nth m fR 0%R) fR) by (apply nth_In; rewrite HfRlen; lia).
    rewrite Forall_forall in Hall. pose proof (Hall _ Hin) as Hm0.
    rewrite Hval in Hm0. lra. }
  destruct (nat_boundary (fun k => lin_indep is_rational (powers delta k)) m
              (lin_indep_nil is_rational) Hdep) as [d [Hindd Hdepd]].
  assert (Hdm : d = m).
  { assert (Hle : (d <= m)%nat).
    { destruct (le_lt_dec d m) as [Hok | Hgt]; [exact Hok | exfalso].
      apply Hdep. apply (lin_indep_powers_le delta (S m) d ltac:(lia) Hindd). }
    assert (Hge : (m <= d)%nat).
    { destruct (le_lt_dec m d) as [Hok | Hlt]; [exact Hok | exfalso].
      assert (Hd1 : (1 <= d)%nat).
      { destruct d as [|d']; [| lia]. exfalso. apply Hdepd.
        intros cs Hlen Hrat Hfc.
        destruct cs as [|c0 cs']; simpl in Hlen; [lia|].
        destruct cs' as [|c1 cs'']; simpl in Hlen; [| lia].
        assert (Hc0 : c0 = 0). { cbn in Hfc. lra. }
        subst c0. constructor; [reflexivity | constructor]. }
      assert (Hdm1 : (d <= m-1)%nat) by lia.
      pose proof (Qx_powers_basis delta d Hindd Hdepd) as Hb.
      destruct Hb as [HBd [Hlid Hspd]].
      assert (HspanD : spans is_rational (powers delta d) (delta ^ d))
        by (apply Hspd; apply (subring_pow (Qx delta) delta d (Qx_subring delta) (Qx_x delta))).
      destruct (minpoly_low_degree_factors_gen fR delta d HfRrat Hlid HspanD Hroot)
        as [mu [q [Hmulen [Hmonic [Hmurat [Hqrat Hfact]]]]]].
      exact (minpoly_no_low_factor_psi m mu q d Hprime Hmurat Hqrat Hmulen Hmonic (conj Hd1 Hdm1) Hfact). }
    lia. }
  subst d. exact (Qx_powers_basis delta m Hindd Hdepd).
Qed.

(* For prime p = 2m+1 with (p-1)/2 not 2-3-smooth, cos(2pi/p) is not single-fold
   origami-constructible: it would have 2-3-smooth degree, but its degree is m.
   This generalizes the hendecagon impossibility to every prime. *)
Theorem cos_2pi_p_not_origami : forall m, (1 <= m)%nat ->
  Znumtheory.prime (Z.of_nat (2*m+1)) -> ~ two_three_smooth m ->
  ~ OrigamiNum (cos (2 * PI / INR (2*m+1))).
Proof.
  intros m Hm Hprime Hns HO.
  set (delta := 2 * cos (2 * PI / INR (2*m+1))).
  assert (Hdelta : OrigamiNum delta).
  { unfold delta.
    replace (2 * cos (2 * PI / INR (2*m+1)))
      with (cos (2 * PI / INR (2*m+1)) + cos (2 * PI / INR (2*m+1))) by ring.
    apply ON_add; exact HO. }
  destruct (origami_field_degree_smooth delta Hdelta) as [d [Hbasis Hsmooth]].
  pose proof (cos_2pi_p_degree_exactly m Hm Hprime) as Hbasism. fold delta in Hbasism.
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
Close Scope R_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
(* ============================================================================
   General exact O6 solvability: every cubic has a real root, so the common
   tangent to two parabolas (the Beloch fold) exists for an arbitrary second
   focus/directrix - an exact fold superseding the midpoint approximation.
   ============================================================================ *)
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope R_scope.
(* every cubic with nonzero leading coefficient has a real root, by depressing
   and applying depressed_cubic_root_exists *)
Close Scope R_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Definition Cunit (t : R) : C := (cos t, sin t).

Lemma Cmul_unit : forall a b, Cmul (Cunit a) (Cunit b) = Cunit (a + b).
Proof.
  intros a b. unfold Cmul, Cunit; simpl. f_equal.
  - rewrite cos_plus. ring.
  - rewrite sin_plus. ring.
Qed.

Lemma de_moivre : forall t k, Cpow (Cunit t) k = Cunit (INR k * t).
Proof.
  intros t k. induction k as [|k IH].
  - simpl. unfold Cunit, C1. rewrite Rmult_0_l, cos_0, sin_0. reflexivity.
  - simpl Cpow. rewrite IH, Cmul_unit. unfold Cunit. f_equal.
    + f_equal. rewrite S_INR. ring.
    + f_equal. rewrite S_INR. ring.
Qed.

Definition zeta (n : nat) : C := Cunit (2 * PI / INR n).

Lemma zeta_pow_n : forall n, (1 <= n)%nat -> Cpow (zeta n) n = C1.
Proof.
  intros n Hn. unfold zeta. rewrite de_moivre.
  assert (Hne : INR n <> 0) by (apply not_0_INR; lia).
  replace (INR n * (2 * PI / INR n)) with (2 * PI) by (field; exact Hne).
  unfold Cunit, C1. f_equal.
  - rewrite cos_2PI. reflexivity.
  - rewrite sin_2PI. reflexivity.
Qed.

(* zeta n is a root of x^n - 1 over C: cpe (Xn1 n) (zeta n) = 0. *)
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Theorem zeta_root_Xn1 : forall n, (1 <= n)%nat -> cpe (Xn1 n) (zeta n) = C0.
Proof.
  intros n Hn. rewrite cpe_Xn1 by exact Hn. rewrite zeta_pow_n by exact Hn. ring.
Qed.

(* Complex power laws and the forward order property: n | k => zeta n ^ k = 1. *)
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Theorem zeta_pow_divides : forall n k, (1 <= n)%nat -> Nat.divide n k ->
  Cpow (zeta n) k = C1.
Proof.
  intros n k Hn [j Hj]. subst k. rewrite Nat.mul_comm, Cpow_mul.
  rewrite zeta_pow_n by exact Hn. apply Cpow_C1.
Qed.

(* The order of zeta n is exactly n: zeta n ^ k = 1 iff n | k. The reverse
   direction reduces to cos x = 1 holding on [0,2*PI] only at the endpoints
   (cos_inj), so a nonzero residue r < n would force phi = 2*PI*r/n in (0,2*PI)
   with cos phi = 1, a contradiction. With zeta_pow_divides this identifies the
   primitive n-th roots of unity for the Dedekind argument. *)
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Theorem zeta_pow_r_ne_1 : forall n r, (0 < r < n)%nat -> Cpow (zeta n) r <> C1.
Proof.
  intros n r Hr Hc. unfold zeta in Hc. rewrite de_moivre in Hc.
  unfold Cunit, C1 in Hc. inversion Hc as [[Hcos Hsin]].
  assert (Hne : 0 < INR n) by (apply lt_0_INR; lia).
  assert (HPI : PI > 0) by apply PI_RGT_0.
  set (phi := INR r * (2 * PI / INR n)) in *.
  assert (Hphi0 : 0 < phi).
  { unfold phi. apply Rmult_lt_0_compat; [apply lt_0_INR; lia |].
    apply Rdiv_lt_0_compat; lra. }
  assert (Hrn : INR r < INR n) by (apply lt_INR; lia).
  assert (Hphi2 : phi < 2 * PI).
  { unfold phi. apply (Rmult_lt_reg_r (INR n)); [exact Hne |].
    replace (INR r * (2 * PI / INR n) * INR n) with (INR r * (2 * PI)) by (field; lra).
    nra. }
  destruct (cos_eq_1_in_range phi) as [He | He]; [lra | exact Hcos | lra | lra].
Qed.

Theorem zeta_order : forall n k, (1 <= n)%nat ->
  Cpow (zeta n) k = C1 -> Nat.divide n k.
Proof.
  intros n k Hn Hk.
  set (r := (k mod n)%nat). set (q := (k / n)%nat).
  assert (Hkeq : k = (r + n * q)%nat).
  { unfold r, q. rewrite (Nat.div_mod k n) at 1 by lia. lia. }
  assert (Hr : (r < n)%nat) by (unfold r; apply Nat.mod_upper_bound; lia).
  assert (Hzr : Cpow (zeta n) r = C1).
  { rewrite Hkeq, Cpow_add, Cpow_mul, zeta_pow_n, Cpow_C1 in Hk by exact Hn.
    replace (Cmul (Cpow (zeta n) r) C1) with (Cpow (zeta n) r) in Hk by ring. exact Hk. }
  destruct (Nat.eq_dec r 0) as [Hr0 | Hr0].
  - exists q. rewrite Hkeq, Hr0. lia.
  - exfalso. apply (zeta_pow_r_ne_1 n r); [lia | exact Hzr].
Qed.

(* Complex-coefficient polynomial evaluation and division by (x - a): the factor
   theorem ceval p a = 0 => p(z) = (z - a) * q(z), toward bounding the number of
   roots of an irreducible factor in the Dedekind argument. *)
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope R_scope.
Lemma zeta_neq_0 : forall n, zeta n <> C0.
Proof.
  intros n H. unfold zeta, Cunit, C0 in H. inversion H as [[Hc Hs]].
  pose proof (sin2_cos2 (2 * PI / INR n)) as Hpy. unfold Rsqr in Hpy. nra.
Qed.
Close Scope R_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope R_scope.
Lemma zeta_k_root_Xn1 : forall n k, (1 <= n)%nat -> cpe (Xn1 n) (Cpow (zeta n) k) = C0.
Proof.
  intros n k Hn. rewrite cpe_Xn1 by exact Hn.
  assert (Hpow : Cpow (Cpow (zeta n) k) n = C1).
  { rewrite <- Cpow_mul. rewrite Nat.mul_comm. rewrite Cpow_mul.
    rewrite zeta_pow_n by exact Hn. apply Cpow_C1. }
  rewrite Hpow. ring.
Qed.

(* the powers zeta n ^ 0 .. zeta n ^ (n-1) are pairwise distinct *)
Lemma zeta_powers_distinct : forall n i j,
  (1 <= n)%nat -> (i < n)%nat -> (j < n)%nat ->
  Cpow (zeta n) i = Cpow (zeta n) j -> i = j.
Proof.
  intros n i j Hn Hi Hj Heq.
  destruct (Nat.le_ge_cases i j) as [Hle | Hge].
  - assert (Hzj : Cpow (zeta n) j = Cmul (Cpow (zeta n) (j - i)) (Cpow (zeta n) i)).
    { rewrite <- Cpow_add. f_equal. lia. }
    rewrite Heq in Hzj.
    assert (Hfac : Cmul (Csub (Cpow (zeta n) (j - i)) C1) (Cpow (zeta n) j) = C0).
    { transitivity (Csub (Cmul (Cpow (zeta n) (j-i)) (Cpow (zeta n) j)) (Cpow (zeta n) j)).
      - ring.
      - rewrite <- Hzj. ring. }
    destruct (Cmul_integral _ _ Hfac) as [Hsub | Hbad].
    + assert (Hone : Cpow (zeta n) (j - i) = C1) by (apply Csub_eq_0; exact Hsub).
      apply zeta_order in Hone; [|exact Hn]. destruct Hone as [c Hc].
      destruct c as [|c]; [simpl in Hc; lia | nia].
    + exfalso. apply (Cpow_neq_0 (zeta n) j (zeta_neq_0 n)). exact Hbad.
  - assert (Hzi : Cpow (zeta n) i = Cmul (Cpow (zeta n) (i - j)) (Cpow (zeta n) j)).
    { rewrite <- Cpow_add. f_equal. lia. }
    rewrite Heq in Hzi.
    assert (Hfac : Cmul (Csub (Cpow (zeta n) (i - j)) C1) (Cpow (zeta n) j) = C0).
    { transitivity (Csub (Cmul (Cpow (zeta n) (i-j)) (Cpow (zeta n) j)) (Cpow (zeta n) j)).
      - ring.
      - rewrite <- Hzi. ring. }
    destruct (Cmul_integral _ _ Hfac) as [Hsub | Hbad].
    + assert (Hone : Cpow (zeta n) (i - j) = C1) by (apply Csub_eq_0; exact Hsub).
      apply zeta_order in Hone; [|exact Hn]. destruct Hone as [c Hc].
      destruct c as [|c]; [simpl in Hc; lia | nia].
    + exfalso. apply (Cpow_neq_0 (zeta n) j (zeta_neq_0 n)). exact Hbad.
Qed.
Close Scope R_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope R_scope.
Definition roots_of_unity (n : nat) : list C := map (Cpow (zeta n)) (seq 0 n).

Lemma roots_of_unity_NoDup : forall n, (1 <= n)%nat -> NoDup (roots_of_unity n).
Proof.
  intros n Hn. unfold roots_of_unity. apply pm_NoDup_map_inj_in.
  - intros i j Hi Hj He. apply in_seq in Hi. apply in_seq in Hj.
    apply (zeta_powers_distinct n i j); [exact Hn | lia | lia | exact He].
  - apply seq_NoDup.
Qed.

Lemma roots_of_unity_are_roots : forall n w, (1 <= n)%nat ->
  In w (roots_of_unity n) -> cpe (Xn1 n) w = C0.
Proof.
  intros n w Hn Hin. unfold roots_of_unity in Hin. apply in_map_iff in Hin.
  destruct Hin as [k [Hk _]]. subst w. apply zeta_k_root_Xn1; exact Hn.
Qed.

(* the roots of x^n - 1 over C are exactly the n distinct n-th roots of unity *)
Theorem Xn1_roots_iff : forall n w, (1 <= n)%nat ->
  (cpe (Xn1 n) w = C0 <-> In w (roots_of_unity n)).
Proof.
  intros n w Hn. split.
  - intro Hw.
    destruct (Classical_Prop.classic (In w (roots_of_unity n))) as [Hin | Hnin];
      [exact Hin |].
    exfalso.
    set (zs := w :: roots_of_unity n).
    assert (Hnd : NoDup zs).
    { unfold zs. constructor; [exact Hnin | apply roots_of_unity_NoDup; exact Hn]. }
    assert (Hroots : forall z, In z zs -> cpe (Xn1 n) z = C0).
    { intros z [Hz|Hz]; [subst z; exact Hw | apply roots_of_unity_are_roots; assumption]. }
    assert (Hnz : exists k, nth k (Xn1 n) 0%Z <> 0%Z).
    { exists 0%nat. rewrite nth0_Xn1. discriminate. }
    pose proof (cpe_roots_lt_length (Xn1 n) zs Hnz Hnd Hroots) as Hlt.
    unfold zs in Hlt. cbn [length] in Hlt.
    unfold roots_of_unity in Hlt. rewrite length_map, length_seq in Hlt.
    rewrite length_Xn1 in Hlt by exact Hn. lia.
  - intro Hin. apply roots_of_unity_are_roots; assumption.
Qed.
Close Scope R_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
(* ============================================================================
   Complex polynomial arithmetic and the product of linear factors (toward the
   cyclotomic product formula x^n - 1 = prod_{d|n} Phi_d).  Cpadd/Cpmul mirror
   Zpadd/Zpmul over the complex field; ceval is a ring homomorphism; and the
   product of linear factors prod (x - a_i) evaluates to prod (z - a_i).
   ============================================================================ *)
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope R_scope.
Corollary Xn1_factorization : forall n z, (1 <= n)%nat ->
  cpe (Xn1 n) z = ceval (linprod (roots_of_unity n)) z.
Proof.
  intros n z Hn. apply Xn1_factorization_gen; try exact Hn.
  - unfold roots_of_unity; rewrite length_map, length_seq; reflexivity.
  - apply roots_of_unity_NoDup; exact Hn.
  - intros w Hw. apply roots_of_unity_are_roots; assumption.
Qed.
Close Scope R_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
(* ===== Product formula  x^n - 1 = prod_{d | n} Phi_d  over C =====
   The roots of x^n-1 partition by exact order: each n-th root of unity is a
   primitive d-th root for a unique d | n.  This regrouping is the tot_rhs
   bijection (used for totient_sum) lifted through the map  k |-> zeta n ^ k. *)
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope nat_scope.
(* the primitive d-th roots of unity as a complex list *)
Definition coprimes (d : nat) : list nat := filter (fun j => coprime j d) (seq 1 d).
Definition primroots (d : nat) : list C := map (fun j => Cpow (zeta d) j) (coprimes d).
Definition PhiC (d : nat) : list C := linprod (primroots d).

(* zeta n raised to a divisor cofactor g (g*d = n) is the primitive d-th root zeta d *)
Lemma zeta_pow_eq : forall n g d, 1 <= n -> g * d = n -> Cpow (zeta n) g = zeta d.
Proof.
  intros n g d Hn Hgd.
  assert (Hgd' : (INR g * INR d)%R = INR n) by (rewrite <- mult_INR, Hgd; reflexivity).
  assert (Hg : 1 <= g) by nia. assert (Hd : 1 <= d) by nia.
  assert (HgR : INR g <> 0%R) by (apply not_0_INR; lia).
  assert (HdR : INR d <> 0%R) by (apply not_0_INR; lia).
  unfold zeta. rewrite de_moivre. unfold Cunit.
  assert (Hangle : (INR g * (2 * PI / INR n))%R = (2 * PI / INR d)%R)
    by (rewrite <- Hgd'; field; split; assumption).
  rewrite Hangle. reflexivity.
Qed.
Close Scope nat_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope nat_scope.
Lemma primroots_as_map : forall n d, 1 <= n -> Nat.divide d n ->
  primroots d = map (Cpow (zeta n)) (map (fun j => (n / d) * j) (coprimes d)).
Proof.
  intros n d Hn Hdiv.
  assert (Hd1 : 1 <= d)
    by (destruct (Nat.eq_dec d 0) as [Hz|Hz]; [subst d; destruct Hdiv as [c Hc]; lia | lia]).
  assert (Hd0 : d <> 0) by lia.
  assert (Hndd : (n / d) * d = n) by (apply divides_div_mul; assumption).
  assert (Hzd : Cpow (zeta n) (n / d) = zeta d) by (apply zeta_pow_eq; [exact Hn | exact Hndd]).
  unfold primroots. rewrite map_map. apply map_ext_in. intros j _.
  rewrite Cpow_mul, Hzd. reflexivity.
Qed.

(* the n-th roots of unity, regrouped by exact order, are the zeta n powers over tot_rhs *)
Lemma flatmap_primroots_eq : forall n, 1 <= n ->
  flat_map primroots (divisors n) = map (Cpow (zeta n)) (tot_rhs n).
Proof.
  intros n Hn.
  transitivity (flat_map (fun d => map (Cpow (zeta n)) (map (fun j => (n / d) * j) (coprimes d)))
                         (divisors n)).
  - apply flat_map_ext_in. intros d Hd.
    apply in_divisors in Hd. destruct Hd as [[_ _] Hdiv].
    apply primroots_as_map; [exact Hn | exact Hdiv].
  - rewrite flat_map_map_comm. unfold tot_rhs. reflexivity.
Qed.

(* injectivity of zeta n powers on [1,n] *)
Lemma zeta_pow_inj_1n : forall n a b,
  1 <= n -> 1 <= a <= n -> 1 <= b <= n -> Cpow (zeta n) a = Cpow (zeta n) b -> a = b.
Proof.
  assert (Hkey : forall n a b, 1 <= n -> 1 <= a -> a <= b -> b <= n ->
                 Cpow (zeta n) a = Cpow (zeta n) b -> a = b).
  { intros n a b Hn Ha Hab Hbn Heq.
    destruct (Nat.eq_dec a b) as [E|E]; [exact E|]. exfalso.
    assert (Hlt : a < b) by lia.
    assert (Hzb : Cpow (zeta n) b = Cmul (Cpow (zeta n) (b - a)) (Cpow (zeta n) a)).
    { rewrite <- Cpow_add. f_equal. lia. }
    rewrite <- Heq in Hzb.
    assert (Hfac : Cmul (Csub (Cpow (zeta n) (b - a)) C1) (Cpow (zeta n) a) = C0).
    { transitivity (Csub (Cmul (Cpow (zeta n) (b - a)) (Cpow (zeta n) a)) (Cpow (zeta n) a)).
      - ring.
      - rewrite <- Hzb. ring. }
    destruct (Cmul_integral _ _ Hfac) as [Hsub | Hbad].
    + assert (Hone : Cpow (zeta n) (b - a) = C1) by (apply Csub_eq_0; exact Hsub).
      apply zeta_order in Hone; [|exact Hn]. destruct Hone as [c Hc].
      destruct c as [|c]; [simpl in Hc; lia | nia].
    + exfalso. apply (Cpow_neq_0 (zeta n) a (zeta_neq_0 n)). exact Hbad. }
  intros n a b Hn Ha Hb Heq.
  destruct (Nat.le_ge_cases a b) as [H|H].
  - apply (Hkey n a b); [lia|lia|lia|lia|exact Heq].
  - symmetry. apply (Hkey n b a); [lia|lia|lia|lia|symmetry; exact Heq].
Qed.
Close Scope nat_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope nat_scope.
Lemma roots_regroup_length : forall n, 1 <= n -> length (flat_map primroots (divisors n)) = n.
Proof.
  intros n Hn. rewrite flatmap_primroots_eq by exact Hn. rewrite length_map.
  assert (Hperm : Permutation (seq 1 n) (tot_rhs n)).
  { apply NoDup_Permutation; [apply seq_NoDup | apply NoDup_tot_rhs; exact Hn
    | intro x; apply tot_mem; exact Hn]. }
  apply Permutation_length in Hperm. rewrite length_seq in Hperm. lia.
Qed.

Lemma roots_regroup_NoDup : forall n, 1 <= n -> NoDup (flat_map primroots (divisors n)).
Proof.
  intros n Hn. rewrite flatmap_primroots_eq by exact Hn.
  apply pm_NoDup_map_inj_in.
  - intros a b Ha Hb He.
    apply zeta_pow_inj_1n with (n := n);
      [exact Hn | apply tot_rhs_bounds; assumption | apply tot_rhs_bounds; assumption | exact He].
  - apply NoDup_tot_rhs; exact Hn.
Qed.

Lemma roots_regroup_are_roots : forall n, 1 <= n -> forall w,
  In w (flat_map primroots (divisors n)) -> cpe (Xn1 n) w = C0.
Proof.
  intros n Hn w Hin. rewrite flatmap_primroots_eq in Hin by exact Hn.
  apply in_map_iff in Hin. destruct Hin as [k [Hk _]]. subst w.
  apply zeta_k_root_Xn1; exact Hn.
Qed.

(* product rule for linprod over list concatenation and flat_map *)
Close Scope nat_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope nat_scope.
Theorem Xn1_prod_PhiC : forall n z, 1 <= n ->
  cpe (Xn1 n) z
   = fold_right (fun d acc => Cmul (ceval (PhiC d) z) acc) C1 (divisors n).
Proof.
  intros n z Hn.
  rewrite (Xn1_factorization_gen n (flat_map primroots (divisors n)) Hn
            (roots_regroup_length n Hn) (roots_regroup_NoDup n Hn)
            (roots_regroup_are_roots n Hn) z).
  rewrite linprod_flatmap_eval. unfold PhiC. reflexivity.
Qed.

(* basic properties of PhiC: degree phi(n), monic, and zeta n is a root *)

Lemma length_coprimes : forall n, length (coprimes n) = euler_phi n.
Proof.
  intro n. unfold coprimes, euler_phi. rewrite (count_coprime_filter n n). reflexivity.
Qed.

Lemma length_primroots : forall n, length (primroots n) = euler_phi n.
Proof.
  intro n. unfold primroots. rewrite length_map. apply length_coprimes.
Qed.

Lemma length_PhiC : forall n, length (PhiC n) = S (euler_phi n).
Proof.
  intro n. unfold PhiC. rewrite length_linprod, length_primroots. reflexivity.
Qed.

Lemma PhiC_monic : forall n, nth (euler_phi n) (PhiC n) C0 = C1.
Proof.
  intro n. unfold PhiC. rewrite <- length_primroots. apply linprod_monic.
Qed.

Lemma zeta_in_primroots : forall n, 1 <= n -> In (zeta n) (primroots n).
Proof.
  intros n Hn. unfold primroots. apply in_map_iff. exists 1. split.
  - cbn [Cpow]. ring.
  - unfold coprimes. apply filter_In. split.
    + apply in_seq. lia.
    + apply coprime_1_l. lia.
Qed.

Lemma PhiC_zeta_root : forall n, 1 <= n -> ceval (PhiC n) (zeta n) = C0.
Proof.
  intros n Hn. unfold PhiC. rewrite ceval_linprod. apply linprod_root_in.
  apply zeta_in_primroots; exact Hn.
Qed.
Close Scope nat_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
(* ===== Exact monic division by root-counting =====
   A monic integer polynomial whose dP distinct complex roots are all roots of an
   integer polynomial F divides F over Z: the Zmonic_div remainder has degree < dP
   yet vanishes at dP distinct points, so it is the zero polynomial. *)

(* cpe depends only on the coefficient sequence (nth with default 0) *)
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope nat_scope.
Lemma coprimes_bounds : forall n a, In a (coprimes n) -> 1 <= a <= n.
Proof.
  intros n a Hin. unfold coprimes in Hin. apply filter_In in Hin.
  destruct Hin as [Hseq _]. apply in_seq in Hseq. lia.
Qed.

Lemma NoDup_primroots : forall n, 1 <= n -> NoDup (primroots n).
Proof.
  intros n Hn. unfold primroots. apply pm_NoDup_map_inj_in.
  - intros a b Ha Hb He.
    apply (zeta_pow_inj_1n n a b Hn (coprimes_bounds n a Ha) (coprimes_bounds n b Hb) He).
  - unfold coprimes. apply NoDup_filter_nat. apply seq_NoDup.
Qed.

Lemma primroots_root_Xn1 : forall n r, 1 <= n -> In r (primroots n) -> cpe (Xn1 n) r = C0.
Proof.
  intros n r Hn Hin. unfold primroots in Hin. apply in_map_iff in Hin.
  destruct Hin as [j [Hj _]]. subst r. apply zeta_k_root_Xn1; exact Hn.
Qed.

Lemma primroots_root_PhiC : forall n r, In r (primroots n) -> ceval (PhiC n) r = C0.
Proof.
  intros n r Hin. unfold PhiC. rewrite ceval_linprod. apply linprod_root_in. exact Hin.
Qed.

(* a characterized cyclotomic P (monic, degree phi(n), roots = primitive roots)
   divides x^n - 1 over Z; the cofactor M is the integer product of the other Phi_d *)
Lemma cyclo_char_divides_Xn1 : forall n P, 1 <= n ->
  length P = S (euler_phi n) -> nth (euler_phi n) P 0%Z = 1%Z ->
  (forall z, cpe P z = ceval (PhiC n) z) ->
  exists M, forall k, nth k (Xn1 n) 0%Z = nth k (Zpmul P M) 0%Z.
Proof.
  intros n P Hn HlenP HmonP Hchar.
  apply (monic_roots_divides P (Xn1 n) (primroots n) (euler_phi n)).
  - exact HlenP.
  - exact HmonP.
  - apply length_primroots.
  - apply NoDup_primroots; exact Hn.
  - intros r Hr. rewrite Hchar. apply primroots_root_PhiC; exact Hr.
  - intros r Hr. apply primroots_root_Xn1; [exact Hn | exact Hr].
Qed.
Close Scope nat_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
(* The integer product of a list of cyclotomic polynomials, given that each one in
   the list has an integer representative (monic, degree phi(d), matching PhiC d):
   a single integer poly M, monic of degree sum_d phi(d), with cpe M z =
   prod_d ceval(PhiC d) z.  The product step of building Phi_n over Z. *)
Lemma cyclo_prod_integer : forall (ds : list nat),
  (forall d, In d ds ->
     exists Pd, length Pd = S (euler_phi d) /\ nth (euler_phi d) Pd 0%Z = 1%Z /\
                (forall z, cpe Pd z = ceval (PhiC d) z)) ->
  exists M, length M = S (list_sum (map euler_phi ds)) /\
            nth (list_sum (map euler_phi ds)) M 0%Z = 1%Z /\
            (forall z, cpe M z = fold_right (fun d acc => Cmul (ceval (PhiC d) z) acc) C1 ds).
Proof.
  induction ds as [|d ds IH]; intros Hreps.
  - exists [1%Z]. split; [reflexivity | split; [reflexivity|]].
    intro z. cbn [cpe fold_right]. replace (ZtoC 1%Z) with C1 by reflexivity. ring.
  - destruct (Hreps d (or_introl eq_refl)) as [Pd [HPdlen [HPdmon HPdeval]]].
    destruct IH as [M' [HM'len [HM'mon HM'eval]]].
    { intros d0 Hd0. apply Hreps. right; exact Hd0. }
    exists (Zpmul Pd M'). split; [|split].
    + cbn [map list_sum].
      apply (Zpmul_monic_len Pd M' (euler_phi d) (list_sum (map euler_phi ds)) HPdlen HM'len).
    + cbn [map list_sum].
      apply (Zpmul_monic_top Pd M' (euler_phi d) (list_sum (map euler_phi ds)) HPdlen HPdmon HM'len HM'mon).
    + intro z. rewrite cpe_Zpmul, HPdeval, HM'eval. cbn [fold_right]. reflexivity.
Qed.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
(* --- fold-of-Cmul helpers (toward peeling Phi_n out of the divisor product) --- *)
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Lemma primroots_pow_self : forall d r, (1 <= d)%nat -> In r (primroots d) -> Cpow r d = C1.
Proof.
  intros d r Hd Hin. unfold primroots in Hin. apply in_map_iff in Hin.
  destruct Hin as [j [Hj _]]. subst r. rewrite <- Cpow_mul.
  replace (j * d)%nat with (d * j)%nat by lia.
  rewrite Cpow_mul, zeta_pow_n by exact Hd. apply Cpow_C1.
Qed.

(* zeta_n (order n) is not a primitive d-th root for any proper divisor d < n *)
Lemma zeta_not_in_lower_primroots : forall n d, (0 < d < n)%nat -> ~ In (zeta n) (primroots d).
Proof.
  intros n d Hd Hin. apply (zeta_pow_r_ne_1 n d Hd).
  apply (primroots_pow_self d (zeta n)); [lia | exact Hin].
Qed.

(* hence Phi_d does not vanish at zeta_n for any proper divisor d < n *)
Lemma phiC_ne0_at_zeta : forall n d, (0 < d < n)%nat -> ceval (PhiC d) (zeta n) <> C0.
Proof.
  intros n d Hd. unfold PhiC. apply ceval_linprod_nonzero.
  intros a Hin Heq. subst a. exact (zeta_not_in_lower_primroots n d Hd Hin).
Qed.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope nat_scope.
(* divisors n is the proper divisors followed by n itself *)
Close Scope nat_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope R_scope.
Lemma has_annih_zeta : forall n, (1 <= n)%nat -> has_annih (zeta n) n.
Proof.
  intros n Hn. unfold has_annih. exists (map IZR (Xn1 n)). split; [|split; [|split]].
  - rewrite length_map. apply length_Xn1; exact Hn.
  - replace (0%R) with (IZR 0%Z) by (simpl; reflexivity).
    rewrite map_nth, nth_n_Xn1 by exact Hn. simpl. reflexivity.
  - apply Forall_forall. intros x Hx. apply in_map_iff in Hx.
    destruct Hx as [z [Hz _]]. subst x. apply is_rational_IZR.
  - rewrite rpe_map_IZR. apply zeta_root_Xn1; exact Hn.
Qed.

(* a real polynomial with a nonzero coefficient has a top nonzero index *)
Close Scope R_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope R_scope.
Lemma annih_normalize : forall n r e',
  Forall is_rational r -> rpe r (zeta n) = C0 ->
  nth e' r 0%R <> 0%R -> (forall j, (e' < j)%nat -> nth j r 0%R = 0%R) ->
  has_annih (zeta n) e'.
Proof.
  intros n r e' Hrrat Hrz Hlead Htop.
  set (c := nth e' r 0%R).
  assert (Hcrat : is_rational c)
    by (unfold c; apply (Forall_F_nth is_rational e' r is_rational_subfield Hrrat)).
  assert (Hcinv : is_rational (/ c))
    by (apply subfield_inv; [apply is_rational_subfield | exact Hcrat | exact Hlead]).
  set (scaled := map (Rmult (/ c)) r).
  assert (He'len : (e' < length r)%nat).
  { destruct (Nat.lt_ge_cases e' (length r)) as [Hl|Hg]; [exact Hl|].
    exfalso. apply Hlead. unfold c. apply nth_overflow. exact Hg. }
  assert (Hscaled_nth : forall k, nth k scaled 0%R = (/ c) * nth k r 0%R).
  { intro k. unfold scaled. rewrite nth_map_Rmult. reflexivity. }
  exists (firstn (S e') scaled). split; [|split; [|split]].
  - rewrite firstn_length. unfold scaled. rewrite length_map. lia.
  - rewrite nth_firstn_lt by lia. rewrite Hscaled_nth. fold c.
    field. exact Hlead.
  - apply Forall_forall. intros x Hx.
    apply (In_nth _ x 0%R) in Hx. destruct Hx as [i [Hi Hxi]]. rewrite <- Hxi.
    destruct (Nat.lt_ge_cases i (S e')) as [Hi'|Hi'].
    + rewrite nth_firstn_lt by exact Hi'. rewrite Hscaled_nth.
      apply subfield_mul; [apply is_rational_subfield | exact Hcinv |
        apply (Forall_F_nth is_rational i r is_rational_subfield Hrrat)].
    + rewrite nth_overflow by (rewrite firstn_length; unfold scaled; rewrite length_map; lia).
      apply (subfield_0 is_rational is_rational_subfield).
  - assert (Hext : rpe (firstn (S e') scaled) (zeta n) = rpe scaled (zeta n)).
    { apply rpe_nth_ext. intro k.
      destruct (Nat.lt_ge_cases k (S e')) as [Hk|Hk].
      - rewrite nth_firstn_lt by exact Hk. reflexivity.
      - rewrite (nth_overflow (firstn (S e') scaled))
          by (rewrite firstn_length; unfold scaled; rewrite length_map; lia).
        rewrite Hscaled_nth. rewrite Htop by lia. ring. }
    rewrite Hext. unfold scaled. rewrite rpe_scale, Hrz. ring.
Qed.

(* the minimal monic rational annihilator of zeta_n divides every rational
   polynomial that vanishes at zeta_n *)
Lemma minpoly_divides : forall n m e,
  (1 <= n)%nat ->
  length m = S e -> nth e m 0%R = 1%R -> Forall is_rational m -> rpe m (zeta n) = C0 ->
  (forall k, (k < e)%nat -> ~ has_annih (zeta n) k) ->
  forall h, Forall is_rational h -> rpe h (zeta n) = C0 ->
  exists q, Forall is_rational q /\ (forall y, pe h y = pe m y * pe q y).
Proof.
  intros n m e Hn Hlen Hmonic Hmrat Hmz Hmin h Hhrat Hhz.
  destruct (monic_div_exists m e Hlen Hmonic Hmrat (length h) h (le_n _) Hhrat)
    as [q [r [Hid [Hrlen [Hqrat Hrrat]]]]].
  exists q. split; [exact Hqrat|].
  assert (Hrz : rpe r (zeta n) = C0).
  { assert (Htrans : rpe h (zeta n) = rpe (padd (pmul m q) r) (zeta n)).
    { apply rpe_transfer;
        [exact Hhrat | apply Forall_rat_padd; [apply Forall_rat_pmul; assumption | exact Hrrat] |].
      intro y. rewrite (Hid y), pe_padd, pe_pmul. ring. }
    rewrite Hhz, rpe_padd, rpe_pmul, Hmz in Htrans.
    transitivity (Cadd (Cmul C0 (rpe q (zeta n))) (rpe r (zeta n))).
    - ring.
    - symmetry. exact Htrans. }
  assert (Hrcoeff : forall k, nth k r 0%R = 0%R).
  { destruct (Classical_Prop.classic (exists k, nth k r 0%R <> 0%R)) as [Hex|Hno].
    - exfalso. destruct (real_deg_exists r Hex) as [e' [He'1 He'2]].
      assert (He'len : (e' < length r)%nat).
      { destruct (Nat.lt_ge_cases e' (length r)) as [Hl|Hg];
          [exact Hl | exfalso; apply He'1; apply nth_overflow; exact Hg]. }
      assert (He'e : (e' < e)%nat) by lia.
      apply (Hmin e' He'e). apply (annih_normalize n r e' Hrrat Hrz He'1 He'2).
    - intro k. destruct (Classical_Prop.classic (nth k r 0%R = 0%R)) as [H|H];
        [exact H | exfalso; apply Hno; exists k; exact H]. }
  intro y. rewrite (Hid y), (pe_all0 r y Hrcoeff). ring.
Qed.
Close Scope R_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Lemma zeta_minpoly_Z : forall n, (1 <= n)%nat ->
  exists mZ e qZ,
    length mZ = S e /\ nth e mZ 0%Z = 1%Z /\ (e <= n)%nat /\
    cpe mZ (zeta n) = C0 /\
    (forall k, (k < e)%nat -> ~ has_annih (zeta n) k) /\
    (forall k, nth k (Xn1 n) 0%Z = nth k (Zpmul mZ qZ) 0%Z).
Proof.
  intros n Hn.
  destruct (min_annih_exists (zeta n) (ex_intro _ n (has_annih_zeta n Hn))) as [e [He Hmin]].
  destruct He as [m [Hmlen [Hmmonic [Hmrat Hmz]]]].
  assert (Hen : (e <= n)%nat).
  { destruct (Nat.le_gt_cases e n) as [H|H]; [exact H|].
    exfalso. exact (Hmin n H (has_annih_zeta n Hn)). }
  assert (HXrat : Forall is_rational (map IZR (Xn1 n))).
  { apply Forall_forall. intros x Hx. apply in_map_iff in Hx.
    destruct Hx as [z [Hz _]]. subst x. apply is_rational_IZR. }
  assert (HXz : rpe (map IZR (Xn1 n)) (zeta n) = C0)
    by (rewrite rpe_map_IZR; apply zeta_root_Xn1; exact Hn).
  destruct (minpoly_divides n m e Hn Hmlen Hmmonic Hmrat Hmz Hmin (map IZR (Xn1 n)) HXrat HXz)
    as [q [Hqrat Hfact]].
  destruct (monic_gauss_factor_gen (Xn1 n) n m q e (length_Xn1 n Hn) (nth_n_Xn1 n Hn)
              (Zcontent_Xn1 n Hn) Hmrat Hqrat Hmlen Hmmonic Hen Hfact)
    as [muZ [qZ [HmapMu [HmuZlen [HmuZmonic [HmapQ Hpevalprod]]]]]].
  exists muZ. exists e. exists qZ. split; [|split; [|split; [|split; [|split]]]].
  - exact HmuZlen.
  - exact HmuZmonic.
  - exact Hen.
  - rewrite <- rpe_map_IZR, HmapMu. exact Hmz.
  - exact Hmin.
  - intro k. apply (peval_eq_nth (Xn1 n) (Zpmul muZ qZ)). intro y. symmetry. apply Hpevalprod.
Qed.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope R_scope.
Lemma minpoly_min_no_smaller : forall n e (p : list Z),
  (forall k, (k < e)%nat -> ~ has_annih (zeta n) k) ->
  cpe p (zeta n) = C0 ->
  (exists k, nth k p 0%Z <> 0%Z) ->
  (forall j, (e <= j)%nat -> nth j p 0%Z = 0%Z) ->
  False.
Proof.
  intros n e p Hmin Hcpe [k Hk] Hdeg.
  assert (Hrat : Forall is_rational (map IZR p)).
  { apply Forall_forall. intros x Hx. apply in_map_iff in Hx.
    destruct Hx as [z [Hz _]]. subst x. apply is_rational_IZR. }
  assert (Hrz : rpe (map IZR p) (zeta n) = C0) by (rewrite rpe_map_IZR; exact Hcpe).
  assert (Hnz : exists i, nth i (map IZR p) 0%R <> 0%R).
  { exists k. rewrite nth_map_IZR. apply not_0_IZR. exact Hk. }
  destruct (real_deg_exists (map IZR p) Hnz) as [e' [He'1 He'2]].
  assert (He'e : (e' < e)%nat).
  { destruct (Nat.lt_ge_cases e' e) as [H|H]; [exact H|].
    exfalso. apply He'1. rewrite nth_map_IZR, (Hdeg e' H). reflexivity. }
  apply (Hmin e' He'e). apply (annih_normalize n (map IZR p) e' Hrat Hrz He'1 He'2).
Qed.
Close Scope R_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
(* the integer minimal polynomial divides every integer polynomial vanishing at zeta_n *)
Lemma minpoly_Z_divides : forall n mZ e,
  (1 <= n)%nat -> length mZ = S e -> nth e mZ 0%Z = 1%Z -> cpe mZ (zeta n) = C0 ->
  (forall k, (k < e)%nat -> ~ has_annih (zeta n) k) ->
  forall h, cpe h (zeta n) = C0 ->
  exists qq, forall k, nth k h 0 = nth k (Zpmul mZ qq) 0.
Proof.
  intros n mZ e Hn Hlen Hmonic Hmz Hmin h Hhz.
  destruct (Zmonic_div mZ e Hlen Hmonic (length h) h (le_n _)) as [qq [rr [Hid Hrlen]]].
  exists qq.
  assert (Hcoeff : forall k, nth k h 0 = nth k (Zpadd (Zpmul mZ qq) rr) 0).
  { apply peval_eq_nth. intro y. rewrite peval_Zpadd, peval_Zpmul. apply Hid. }
  assert (Hrr0 : forall k, nth k rr 0 = 0).
  { assert (Hrrz : cpe rr (zeta n) = C0).
    { assert (Hsp : cpe h (zeta n)
                  = Cadd (Cmul (cpe mZ (zeta n)) (cpe qq (zeta n))) (cpe rr (zeta n))).
      { rewrite (cpe_nth_ext h (Zpadd (Zpmul mZ qq) rr) (zeta n) Hcoeff).
        rewrite cpe_Zpadd, cpe_Zpmul. reflexivity. }
      rewrite Hhz, Hmz in Hsp.
      transitivity (Cadd (Cmul C0 (cpe qq (zeta n))) (cpe rr (zeta n)));
        [ring | symmetry; exact Hsp]. }
    destruct (Classical_Prop.classic (exists k, nth k rr 0 <> 0)) as [Hex|Hno].
    - exfalso. apply (minpoly_min_no_smaller n e rr Hmin Hrrz Hex).
      intros j Hj. apply nth_overflow. lia.
    - intro k. destruct (Classical_Prop.classic (nth k rr 0 = 0)) as [H|H];
        [exact H | exfalso; apply Hno; exists k; exact H]. }
  intro k. rewrite (Hcoeff k), nth_Zpadd, Hrr0. lia.
Qed.

(* the integer minimal polynomial is irreducible: no positive-degree factorization *)
Lemma minpoly_Z_irred : forall n mZ e,
  (1 <= n)%nat -> length mZ = S e -> nth e mZ 0%Z = 1%Z -> cpe mZ (zeta n) = C0 ->
  (forall k, (k < e)%nat -> ~ has_annih (zeta n) k) ->
  forall a b da db, (1 <= da)%nat -> (1 <= db)%nat -> (da + db = e)%nat ->
    length a = S da -> length b = S db ->
    (forall k, nth k mZ 0 = nth k (Zpmul a b) 0) -> False.
Proof.
  intros n mZ e Hn Hlen Hmonic Hmz Hmin a b da db Hda Hdb Hsum Hla Hlb Hfact.
  assert (Hab0 : Cmul (cpe a (zeta n)) (cpe b (zeta n)) = C0).
  { rewrite <- cpe_Zpmul. rewrite <- (cpe_nth_ext mZ (Zpmul a b) (zeta n) Hfact). exact Hmz. }
  assert (Hlead : nth da a 0 * nth db b 0 = 1).
  { pose proof (Hfact e) as Hf. rewrite Hmonic, nth_Zpmul, <- Hsum in Hf.
    rewrite (Zconv_top a b da db) in Hf.
    - lia.
    - intros i Hi. apply nth_overflow. lia.
    - intros j Hj. apply nth_overflow. lia. }
  destruct (Cmul_integral _ _ Hab0) as [Ha | Hb].
  - apply (minpoly_min_no_smaller n e a Hmin Ha).
    + exists da. intro Hc. rewrite Hc in Hlead. lia.
    + intros j Hj. apply nth_overflow. lia.
  - apply (minpoly_min_no_smaller n e b Hmin Hb).
    + exists db. intro Hc. rewrite Hc in Hlead. lia.
    + intros j Hj. apply nth_overflow. lia.
Qed.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
(* ===== General-z versions of the minimal-polynomial lemmas, needed to treat the
   conjugate roots zeta_n^k as well as zeta_n itself. ===== *)
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Lemma minpoly_root_divides : forall n mZ e w,
  (1 <= n)%nat -> length mZ = S e -> nth e mZ 0%Z = 1%Z -> (1 <= e)%nat ->
  cpe mZ (zeta n) = C0 ->
  (forall k, (k < e)%nat -> ~ has_annih (zeta n) k) ->
  cpe (Xn1 n) w = C0 -> cpe mZ w = C0 ->
  forall h, cpe h w = C0 ->
  exists qq, forall k, nth k h 0 = nth k (Zpmul mZ qq) 0.
Proof.
  intros n mZ e w Hn Hlen Hmonic He HmzZ Hmin HXw Hmzw h Hhw.
  destruct (root_minpoly_Z n w Hn HXw)
    as [mw [ew [qw [Hmwlen [Hmwmonic [Hewn [Hmwz [Hmwmin _]]]]]]]].
  assert (Hew1 : (1 <= ew)%nat).
  { destruct ew as [|ew']; [|lia]. exfalso.
    destruct mw as [|a mw']; [cbn in Hmwlen; lia|].
    assert (Hnil : mw' = nil) by (destruct mw'; [reflexivity | cbn in Hmwlen; lia]). subst mw'.
    cbn [nth] in Hmwmonic. subst a. cbn [cpe] in Hmwz.
    replace (ZtoC 1%Z) with C1 in Hmwz by reflexivity.
    apply C1_neq_C0. rewrite <- Hmwz. ring. }
  destruct (minpoly_Z_divides_z w mw ew Hmwlen Hmwmonic Hmwz Hmwmin mZ Hmzw) as [c Hc].
  assert (HmZdeg : forall j, (e < j)%nat -> nth j mZ 0 = 0) by (intros j Hj; apply nth_overflow; lia).
  assert (Hmwlead : nth ew mw 0 <> 0) by (rewrite Hmwmonic; lia).
  assert (Hprodid : forall k, nth k (Zpmul mw c) 0 = (1 * 1) * nth k mZ 0)
    by (intro k; rewrite <- Hc; ring).
  pose proof (high_coeff_zero_gen mZ e mw c 1 1 ew HmZdeg Hmwlen Hmwlead Hprodid) as Hchigh.
  assert (Hewle : (ew <= e)%nat).
  { destruct (Nat.le_gt_cases ew e) as [H|H]; [exact H|]. exfalso.
    assert (Hcall : forall j, nth j c 0 = 0) by (intro j; apply Hchigh; lia).
    pose proof (Hc e) as HcE. rewrite nth_Zpmul, (Zconv_zero_r c Hcall mw e), Hmonic in HcE. lia. }
  assert (Hewe : ew = e).
  { destruct (Nat.eq_dec ew e) as [Heq|Hne]; [exact Heq|]. exfalso.
    assert (Hewlt : (ew < e)%nat) by lia.
    assert (Hsplit : Cmul (cpe mw (zeta n)) (cpe c (zeta n)) = C0).
    { rewrite <- cpe_Zpmul. rewrite <- (cpe_nth_ext mZ (Zpmul mw c) (zeta n) Hc). exact HmzZ. }
    destruct (Cmul_integral _ _ Hsplit) as [Hmw0 | Hc0].
    - apply (minpoly_min_no_smaller_z (zeta n) e mw Hmin Hmw0).
      + exists ew. rewrite Hmwmonic. lia.
      + intros j Hj. apply nth_overflow. lia.
    - apply (minpoly_min_no_smaller_z (zeta n) e c Hmin Hc0).
      + exists (e - ew)%nat.
        assert (Htop : nth e mZ 0 = nth ew mw 0 * nth (e - ew) c 0).
        { pose proof (Hc e) as HcE. rewrite nth_Zpmul in HcE.
          replace e with (ew + (e - ew))%nat in HcE at 2 by lia.
          rewrite (Zconv_top mw c ew (e - ew)) in HcE.
          - replace (ew + (e - ew))%nat with e in HcE by lia. exact HcE.
          - intros i Hi. apply nth_overflow. lia.
          - intros j Hj. apply Hchigh. lia. }
        rewrite Hmonic, Hmwmonic in Htop. intro Hc0'. rewrite Hc0' in Htop. lia.
      + intros j Hj. apply Hchigh. lia. }
  destruct (Zmonic_div mZ e Hlen Hmonic (length h) h (le_n _)) as [qq [rr [Hid Hrlen]]].
  exists qq.
  assert (Hcoeff : forall k, nth k h 0 = nth k (Zpadd (Zpmul mZ qq) rr) 0).
  { apply peval_eq_nth. intro y. rewrite peval_Zpadd, peval_Zpmul. apply Hid. }
  assert (Hrr0 : forall k, nth k rr 0 = 0).
  { assert (Hrrw : cpe rr w = C0).
    { assert (Hsp : cpe h w = Cadd (Cmul (cpe mZ w) (cpe qq w)) (cpe rr w)).
      { rewrite (cpe_nth_ext h (Zpadd (Zpmul mZ qq) rr) w Hcoeff).
        rewrite cpe_Zpadd, cpe_Zpmul. reflexivity. }
      rewrite Hhw, Hmzw in Hsp.
      transitivity (Cadd (Cmul C0 (cpe qq w)) (cpe rr w)); [ring | symmetry; exact Hsp]. }
    destruct (Classical_Prop.classic (exists k, nth k rr 0 <> 0)) as [Hex|Hno].
    - exfalso. apply (minpoly_min_no_smaller_z w ew rr Hmwmin Hrrw Hex).
      intros j Hj. apply nth_overflow. lia.
    - intro k. destruct (Classical_Prop.classic (nth k rr 0 = 0)) as [H|H];
        [exact H | exfalso; apply Hno; exists k; exact H]. }
  intro k. rewrite (Hcoeff k), nth_Zpadd, Hrr0. lia.
Qed.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Lemma dedekind_conjugate_step : forall n mZ e g p w,
  Znumtheory.prime (Z.of_nat p) -> ~ (Z.of_nat p | Z.of_nat n) -> (1 <= n)%nat ->
  length mZ = S e -> nth e mZ 0%Z = 1%Z -> (1 <= e)%nat ->
  cpe mZ (zeta n) = C0 ->
  (forall k, (k < e)%nat -> ~ has_annih (zeta n) k) ->
  (forall k, nth k (Xn1 n) 0%Z = nth k (Zpmul mZ g) 0%Z) ->
  cpe (Xn1 n) w = C0 -> cpe mZ w = C0 ->
  cpe mZ (Cpow w p) = C0.
Proof.
  intros n mZ e g p w Hprime Hpn Hn Hlen Hmonic He HmzZ Hmin Hfact HXw Hmzw.
  set (P := Z.of_nat p) in *.
  assert (Hp1 : (1 <= p)%nat) by (destruct Hprime as [Hpp _]; lia).
  assert (HP1 : (1 < P)%Z) by (destruct Hprime; assumption).
  assert (Hwn : Cpow w n = C1) by (apply Csub_eq_0; rewrite <- (cpe_Xn1 n w Hn); exact HXw).
  assert (HXwp : cpe (Xn1 n) (Cpow w p) = C0).
  { rewrite (cpe_Xn1 n (Cpow w p) Hn).
    replace (Cpow (Cpow w p) n) with C1; [ring|].
    rewrite <- Cpow_mul, Nat.mul_comm, Cpow_mul, Hwn, Cpow_C1. reflexivity. }
  assert (Hor : Cmul (cpe mZ (Cpow w p)) (cpe g (Cpow w p)) = C0).
  { rewrite <- cpe_Zpmul.
    rewrite <- (cpe_nth_ext (Xn1 n) (Zpmul mZ g) (Cpow w p) Hfact). exact HXwp. }
  destruct (Cmul_integral _ _ Hor) as [Hgood | Hgbad]; [exact Hgood|].
  exfalso.
  assert (Hsubvan : cpe (subst_xp p g) w = C0)
    by (rewrite cpe_subst_xp by exact Hp1; exact Hgbad).
  destruct (minpoly_root_divides n mZ e w Hn Hlen Hmonic He HmzZ Hmin HXw Hmzw
              (subst_xp p g) Hsubvan) as [qd Hqd].
  assert (HmZsubst : pdvd_mod P mZ (subst_xp p g))
    by (exists qd; apply pcong_of_eq_nth; intro k; apply Hqd).
  assert (HmZgp : pdvd_mod P mZ (Zppow g p)).
  { destruct HmZsubst as [q Hq]. exists q.
    apply (pcong_trans P (Zppow g p) (subst_xp p g)); [apply (frobenius p g Hprime) | exact Hq]. }
  assert (HmZgXn1 : pdvd_mod P (Zpmul mZ g) (Xn1 n)).
  { exists [1%Z]. apply pcong_of_eq_nth. intro k. rewrite Hfact.
    apply (peval_eq_nth (Zpmul mZ g) (Zpmul (Zpmul mZ g) [1%Z])). intro y.
    rewrite !peval_Zpmul. cbn [peval]. simpl IZR. ring. }
  apply (dedekind_conjugate_absurd p mZ g n Hprime Hn Hpn); [|exact HmZgp | exact HmZgXn1].
  exists e. split; [exact He | split].
  - rewrite Hmonic. intro Hbad.
    pose proof (Znumtheory.Zdivide_le P 1 ltac:(lia) ltac:(lia) Hbad). lia.
  - intros j Hj. rewrite nth_overflow by lia. apply Z.divide_0_r.
Qed.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
(* every natural number >= 2 has a prime factor (as a nat whose Z cast is prime) *)
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Lemma conj_orbit : forall n mZ e g,
  (1 <= n)%nat -> length mZ = S e -> nth e mZ 0%Z = 1%Z -> (1 <= e)%nat ->
  cpe mZ (zeta n) = C0 ->
  (forall j, (j < e)%nat -> ~ has_annih (zeta n) j) ->
  (forall j, nth j (Xn1 n) 0%Z = nth j (Zpmul mZ g) 0%Z) ->
  forall k, 1 <= k -> Nat.gcd k n = 1 -> cpe mZ (Cpow (zeta n) k) = C0.
Proof.
  intros n mZ e g Hn Hlen Hmonic He HmzZ Hmin Hfact.
  intro k. induction k as [k IH] using (well_founded_induction Wf_nat.lt_wf).
  intros Hk1 Hgcd.
  destruct (Nat.eq_dec k 1) as [Hk1eq | Hkne].
  - subst k. replace (Cpow (zeta n) 1) with (zeta n) by (cbn [Cpow]; ring). exact HmzZ.
  - assert (Hk2 : 2 <= k) by lia.
    destruct (prime_factor_nat k Hk2) as [p [Hpp Hpk]].
    assert (Hpge2 : (2 <= Z.of_nat p)%Z) by (destruct Hpp; lia).
    assert (Hp2 : 2 <= p) by lia.
    assert (Hgpn : Nat.gcd p n = 1) by (apply (gcd1_of_divisor p k n Hpk Hgcd)).
    assert (Hpn_nat : ~ Nat.divide p n).
    { intro Hpn. assert (H : Nat.divide p (Nat.gcd p n)) by (apply Nat.gcd_greatest; [exists 1; lia | exact Hpn]).
      rewrite Hgpn in H. apply Nat.divide_1_r in H. lia. }
    assert (Hpn_Z : ~ (Z.of_nat p | Z.of_nat n)).
    { intro Hz. apply Hpn_nat. destruct Hz as [c Hc].
      exists (Z.to_nat c). apply Nat2Z.inj.
      assert (Hcpos : (0 <= c)%Z) by nia.
      rewrite Nat2Z.inj_mul, Z2Nat.id by exact Hcpos. lia. }
    set (k' := k / p).
    assert (Hkpk : k' * p = k) by (unfold k'; apply divides_div_mul; [lia | exact Hpk]).
    assert (Hk'1 : 1 <= k') by nia.
    assert (Hk'k : k' < k) by nia.
    assert (Hgk'n : Nat.gcd k' n = 1) by (apply (gcd1_of_divisor k' k n); [exists p; lia | exact Hgcd]).
    assert (Hk'root : cpe mZ (Cpow (zeta n) k') = C0) by (apply (IH k' Hk'k Hk'1 Hgk'n)).
    assert (HXk' : cpe (Xn1 n) (Cpow (zeta n) k') = C0) by (apply zeta_k_root_Xn1; exact Hn).
    pose proof (dedekind_conjugate_step n mZ e g p (Cpow (zeta n) k')
                  Hpp Hpn_Z Hn Hlen Hmonic He HmzZ Hmin Hfact HXk' Hk'root) as Hstep.
    rewrite <- Cpow_mul, Hkpk in Hstep. exact Hstep.
Qed.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
(* ===== COMPOSITE CYCLOTOMIC IRREDUCIBILITY (Dedekind) =====
   Any monic integer polynomial P whose complex roots are exactly the primitive
   n-th roots of unity (i.e. P = Phi_n) admits no positive-degree integer
   factorization.  This completes the cyclotomic-irreducibility theorem for all n:
   the prime case is cyclotomic_prime_irreducible (Eisenstein); this is the
   general (composite) case via the Dedekind zeta -> zeta^p reduction-mod-p
   argument, the minimal polynomial of zeta_n, and its conjugate orbit. *)
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope Z_scope.
Theorem cyclotomic_irreducible_composite : forall n P G H dg dh,
  (1 <= n)%nat ->
  length P = S (euler_phi n) -> nth (euler_phi n) P 0%Z = 1%Z ->
  (forall z, cpe P z = ceval (PhiC n) z) ->
  (1 <= dg)%nat -> (1 <= dh)%nat -> (dg + dh = euler_phi n)%nat ->
  length G = S dg -> length H = S dh ->
  (forall k, nth k P 0%Z = Zconv G H k) ->
  False.
Proof.
  intros n P G H dg dh Hn HlenP HmonP Hchar Hdg Hdh Hsum HlenG HlenH Hfact.
  assert (HPz : cpe P (zeta n) = C0) by (rewrite Hchar; apply PhiC_zeta_root; exact Hn).
  destruct (zeta_minpoly_Z n Hn) as [mZ [e [qZ [Hmlen [Hmmonic [Hen [Hmz [Hmin Hmfact]]]]]]]].
  assert (He1 : (1 <= e)%nat).
  { destruct e as [|e']; [|lia]. exfalso.
    destruct mZ as [|a mZ']; [cbn in Hmlen; lia|].
    assert (Hnil : mZ' = nil) by (destruct mZ'; [reflexivity | cbn in Hmlen; lia]). subst mZ'.
    cbn [nth] in Hmmonic. subst a. cbn [cpe] in Hmz.
    replace (ZtoC 1%Z) with C1 in Hmz by reflexivity. apply C1_neq_C0. rewrite <- Hmz. ring. }
  assert (Hephi : (euler_phi n <= e)%nat).
  { assert (Hlt : (length (primroots n) < length mZ)%nat).
    { apply (cpe_roots_lt_length mZ (primroots n)).
      - exists e. rewrite Hmmonic. discriminate.
      - apply NoDup_primroots; exact Hn.
      - intros w Hw. unfold primroots in Hw. apply in_map_iff in Hw.
        destruct Hw as [j [Hj Hjin]]. subst w.
        unfold coprimes in Hjin. apply filter_In in Hjin. destruct Hjin as [Hjseq Hjcop].
        apply in_seq in Hjseq.
        apply (conj_orbit n mZ e qZ Hn Hmlen Hmmonic He1 Hmz Hmin Hmfact j);
          [lia | unfold coprime in Hjcop; apply Nat.eqb_eq in Hjcop; exact Hjcop]. }
    rewrite length_primroots, Hmlen in Hlt. lia. }
  assert (HPGH : forall k, nth k P 0 = nth k (Zpmul G H) 0)
    by (intro k; rewrite Hfact, nth_Zpmul; reflexivity).
  assert (HGH0 : Cmul (cpe G (zeta n)) (cpe H (zeta n)) = C0).
  { rewrite <- cpe_Zpmul. rewrite <- (cpe_nth_ext P (Zpmul G H) (zeta n) HPGH). exact HPz. }
  assert (Hlead : nth dg G 0 * nth dh H 0 = 1).
  { pose proof (HPGH (euler_phi n)) as HP. rewrite HmonP, nth_Zpmul, <- Hsum in HP.
    rewrite (Zconv_top G H dg dh) in HP.
    - lia.
    - intros i Hi. apply nth_overflow. lia.
    - intros j Hj. apply nth_overflow. lia. }
  destruct (Cmul_integral _ _ HGH0) as [HG0 | HH0].
  - apply (minpoly_min_no_smaller n e G Hmin HG0).
    + exists dg. intro Hc. rewrite Hc in Hlead. lia.
    + intros j Hj. apply nth_overflow. lia.
  - apply (minpoly_min_no_smaller n e H Hmin HH0).
    + exists dh. intro Hc. rewrite Hc in Hlead. lia.
    + intros j Hj. apply nth_overflow. lia.
Qed.
Close Scope Z_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
(* ===== Toward item 2: degree of cos(2 pi / n) = phi(n)/2 (composite case). ===== *)

(* 2 cos(2 pi / n) = zeta_n + zeta_n^(n-1) = zeta_n + conj(zeta_n) *)
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope R_scope.
Lemma RtoC_2cos_zeta : forall n, (1 <= n)%nat ->
  RtoC (2 * cos (2 * PI / INR n)) = Cadd (zeta n) (Cpow (zeta n) (n - 1)).
Proof.
  intros n Hn.
  assert (HnR : INR n <> 0) by (apply not_0_INR; lia).
  unfold zeta. rewrite de_moivre.
  assert (Hangle : INR (n - 1) * (2 * PI / INR n) = 2 * PI - 2 * PI / INR n).
  { rewrite minus_INR by exact Hn. simpl. field. exact HnR. }
  rewrite Hangle.
  unfold Cunit, Cadd, RtoC. f_equal; simpl.
  - rewrite cos_minus, cos_2PI, sin_2PI. ring.
  - rewrite sin_minus, sin_2PI, cos_2PI. ring.
Qed.

(* zeta_n satisfies the degree-2 relation  X^2 - (2cos)*X + 1 = 0  over Q(2cos):
   zeta_n^2 = (2cos) * zeta_n - 1.  Hence [Q(zeta_n) : Q(2cos)] <= 2, the source of
   the degree halving phi(n) -> phi(n)/2. *)
Lemma zeta_quadratic : forall n, (1 <= n)%nat ->
  Cmul (zeta n) (zeta n) = Csub (Cmul (RtoC (2 * cos (2 * PI / INR n))) (zeta n)) C1.
Proof.
  intros n Hn.
  assert (Hsucc : forall z k, Cmul (Cpow z k) z = Cpow z (S k))
    by (intros z0 k; cbn [Cpow]; ring).
  assert (Hinv : Cmul (Cpow (zeta n) (n - 1)) (zeta n) = C1).
  { rewrite Hsucc. replace (S (n - 1))%nat with n by lia. apply zeta_pow_n; exact Hn. }
  rewrite (RtoC_2cos_zeta n Hn).
  replace (Cmul (Cadd (zeta n) (Cpow (zeta n) (n - 1))) (zeta n))
     with (Cadd (Cmul (zeta n) (zeta n)) (Cmul (Cpow (zeta n) (n - 1)) (zeta n))) by ring.
  rewrite Hinv. ring.
Qed.
Close Scope R_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
(* the minimal polynomial of zeta_n has degree at least phi(n): all phi(n)
   primitive roots are among its (distinct) roots *)
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope Z_scope.
Lemma zeta_minpoly_deg_ge_phi : forall n mZ e g,
  (1 <= n)%nat -> length mZ = S e -> nth e mZ 0%Z = 1%Z -> (1 <= e)%nat ->
  cpe mZ (zeta n) = C0 ->
  (forall k, (k < e)%nat -> ~ has_annih (zeta n) k) ->
  (forall k, nth k (Xn1 n) 0%Z = nth k (Zpmul mZ g) 0%Z) ->
  (euler_phi n <= e)%nat.
Proof.
  intros n mZ e g Hn Hlen Hmonic He HmzZ Hmin Hfact.
  assert (Hlt : (length (primroots n) < length mZ)%nat).
  { apply (cpe_roots_lt_length mZ (primroots n)).
    - exists e. rewrite Hmonic. discriminate.
    - apply NoDup_primroots; exact Hn.
    - intros w Hw. unfold primroots in Hw. apply in_map_iff in Hw.
      destruct Hw as [j [Hj Hjin]]. subst w.
      unfold coprimes in Hjin. apply filter_In in Hjin. destruct Hjin as [Hjseq Hjcop].
      apply in_seq in Hjseq.
      apply (conj_orbit n mZ e g Hn Hlen Hmonic He HmzZ Hmin Hfact j);
        [lia | unfold coprime in Hjcop; apply Nat.eqb_eq in Hjcop; exact Hjcop]. }
  rewrite length_primroots, Hlen in Hlt. lia.
Qed.
Close Scope Z_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope R_scope.
(* key identity: 1 + zeta_n^2 = zeta_n * (2cos), avoiding complex inverses *)
Lemma one_plus_zeta_sq : forall n, (1 <= n)%nat ->
  rpe [1; 0; 1] (zeta n) = Cmul (zeta n) (RtoC (2 * cos (2 * PI / INR n))).
Proof.
  intros n Hn.
  assert (Hsucc : Cmul (zeta n) (Cpow (zeta n) (n - 1)) = C1).
  { replace (Cmul (zeta n) (Cpow (zeta n) (n - 1))) with (Cpow (zeta n) (S (n - 1)))
      by (cbn [Cpow]; ring).
    replace (S (n - 1))%nat with n by lia. apply zeta_pow_n; exact Hn. }
  rewrite (RtoC_2cos_zeta n Hn).
  replace (Cmul (zeta n) (Cadd (zeta n) (Cpow (zeta n) (n - 1))))
     with (Cadd (Cmul (zeta n) (zeta n)) (Cmul (zeta n) (Cpow (zeta n) (n - 1)))) by ring.
  rewrite Hsucc. cbn [rpe].
  replace (RtoC 0) with C0 by reflexivity. replace (RtoC 1) with C1 by reflexivity. ring.
Qed.
Close Scope R_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope R_scope.
Lemma rpe_lift_aux_zeta : forall n, (1 <= n)%nat -> forall m d, length m = S d ->
  rpe (lift_aux d m) (zeta n)
   = Cmul (Cpow (zeta n) d) (rpe m (RtoC (2 * cos (2 * PI / INR n)))).
Proof.
  intros n Hn. induction m as [|c m' IH]; intros d Hlen; [cbn in Hlen; lia|].
  cbn [lift_aux]. rewrite rpe_padd, rpe_scale, rpe_repeat0_app, rpe_mx2.
  assert (H1z2 : Cadd C1 (Cmul (zeta n) (zeta n))
                 = Cmul (zeta n) (RtoC (2 * cos (2 * PI / INR n)))).
  { rewrite <- (one_plus_zeta_sq n Hn). cbn [rpe].
    replace (RtoC 0) with C0 by reflexivity. replace (RtoC 1) with C1 by reflexivity. ring. }
  rewrite H1z2.
  assert (Hr1 : rpe [1] (zeta n) = C1)
    by (cbn [rpe]; replace (RtoC 1) with C1 by reflexivity; ring).
  rewrite Hr1.
  destruct m' as [|c' m''].
  - cbn in Hlen. assert (Hd0 : d = 0%nat) by lia. subst d.
    cbn [Nat.pred lift_aux rpe Cpow]. ring.
  - assert (Hlen' : length (c' :: m'') = S (Nat.pred d)) by (cbn in Hlen |- *; lia).
    rewrite (IH (Nat.pred d) Hlen').
    assert (Hd1 : (1 <= d)%nat) by (cbn in Hlen; lia).
    assert (Hpow : Cpow (zeta n) d = Cmul (zeta n) (Cpow (zeta n) (Nat.pred d)))
      by (replace d with (S (Nat.pred d))%nat at 1 by lia; cbn [Cpow]; ring).
    rewrite Hpow. cbn [rpe]. ring.
Qed.

(* rpe of a real-coeff poly at a real point = RtoC of the real evaluation *)
Close Scope R_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope R_scope.
Lemma cos_annih_lifts : forall n m d, (1 <= n)%nat ->
  length m = S d -> nth d m 0 = 1 -> Forall is_rational m ->
  pe m (2 * cos (2 * PI / INR n)) = 0 ->
  has_annih (zeta n) (2 * d)%nat.
Proof.
  intros n m d Hn Hlen Hmonic Hrat Hroot.
  apply (annih_normalize n (lift_aux d m) (2*d)%nat).
  - apply lift_aux_rational. exact Hrat.
  - rewrite (rpe_lift_aux_zeta n Hn m d Hlen), rpe_RtoC, Hroot.
    replace (RtoC 0) with C0 by reflexivity. ring.
  - rewrite (lift_aux_lead m d Hlen), Hmonic. lra.
  - intros j Hj. apply (lift_aux_high0 m d Hlen). lia.
Qed.

(* any monic rational annihilator of zeta_n has degree at least phi(n) *)
Lemma zeta_annih_deg_ge_phi : forall n d, (1 <= n)%nat ->
  has_annih (zeta n) d -> (euler_phi n <= d)%nat.
Proof.
  intros n d Hn Hann.
  destruct (zeta_minpoly_Z n Hn) as [mZ [e [qZ [Hlen [Hmonic [Hen [Hcpe [Hmin Hfact]]]]]]]].
  assert (He1 : (1 <= e)%nat).
  { destruct e as [|e']; [exfalso | lia].
    destruct mZ as [|a [|b t]]; cbn in Hlen; try lia.
    cbn in Hmonic. subst a.
    cbn [cpe] in Hcpe. rewrite ZtoC_1 in Hcpe.
    apply C1_neq_C0. rewrite <- Hcpe. ring. }
  assert (Hphi_e : (euler_phi n <= e)%nat)
    by (apply (zeta_minpoly_deg_ge_phi n mZ e qZ Hn Hlen Hmonic He1 Hcpe Hmin Hfact)).
  assert (He_d : (e <= d)%nat).
  { destruct (Nat.le_gt_cases e d) as [H|H]; [exact H|].
    exfalso. exact (Hmin d H Hann). }
  lia.
Qed.

(* LOWER BOUND: if 2cos has a monic rational annihilator of degree d, then phi(n) <= 2d,
   i.e. the degree of 2cos(2pi/n) over Q is at least phi(n)/2 *)
Lemma cos_degree_ge_phi_half : forall n m d, (1 <= n)%nat ->
  length m = S d -> nth d m 0 = 1 -> Forall is_rational m ->
  pe m (2 * cos (2 * PI / INR n)) = 0 ->
  (euler_phi n <= 2 * d)%nat.
Proof.
  intros n m d Hn Hlen Hmonic Hrat Hroot.
  apply (zeta_annih_deg_ge_phi n (2*d)%nat Hn).
  apply (cos_annih_lifts n m d Hn Hlen Hmonic Hrat Hroot).
Qed.
Close Scope R_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
(* ===== The integer cyclotomic polynomial Phi_n (existence) ===== *)
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Lemma PhiZ_exists : forall n, (1 <= n)%nat ->
  exists P, length P = S (euler_phi n) /\ nth (euler_phi n) P 0%Z = 1%Z /\
            (forall z, cpe P z = ceval (PhiC n) z).
Proof.
  intro n. induction n as [n IH] using (well_founded_induction lt_wf). intro Hn.
  set (PD := filter (fun d => Nat.eqb (n mod d) 0)%nat (seq 1 (n-1))).
  assert (HPDspec : forall d, In d PD -> (1 <= d < n)%nat).
  { intros d Hd. unfold PD in Hd. apply filter_In in Hd. destruct Hd as [Hseq _].
    apply in_seq in Hseq. lia. }
  assert (Hreps : forall d, In d PD ->
     exists Pd, length Pd = S (euler_phi d) /\ nth (euler_phi d) Pd 0%Z = 1%Z /\
                (forall z, cpe Pd z = ceval (PhiC d) z)).
  { intros d Hd. destruct (HPDspec d Hd) as [Hd1 Hdn]. apply IH; lia. }
  destruct (cyclo_prod_integer PD Hreps) as [M [HMlen [HMmon HMeval]]].
  set (dM := list_sum (map euler_phi PD)) in *.
  assert (HdivApp : divisors n = PD ++ [n]) by (apply divisors_app_last; exact Hn).
  assert (HdM : (dM + euler_phi n = n)%nat).
  { pose proof (totient_sum n Hn) as Hsum. rewrite HdivApp, map_app, list_sum_app in Hsum.
    cbn [map] in Hsum.
    assert (Hone : list_sum [euler_phi n] = (euler_phi n + 0)%nat) by reflexivity.
    rewrite Hone in Hsum. unfold dM. lia. }
  assert (Hfact : forall z, cpe (Xn1 n) z = Cmul (ceval (PhiC n) z) (cpe M z)).
  { intro z. rewrite (Xn1_prod_PhiC n z Hn), HdivApp, fold_right_app. cbn [fold_right].
    rewrite (fold_cmul_pull (fun d => ceval (PhiC d) z) (ceval (PhiC n) z) PD), HMeval.
    reflexivity. }
  set (rts := flat_map primroots PD).
  assert (Hrtslen : length rts = dM).
  { unfold rts, dM. rewrite length_flat_map_sum. f_equal. apply map_ext.
    intro d. apply length_primroots. }
  assert (HfullND : NoDup (flat_map primroots (divisors n))) by (apply roots_regroup_NoDup; exact Hn).
  rewrite HdivApp, flat_map_app in HfullND. cbn [flat_map] in HfullND. rewrite app_nil_r in HfullND.
  assert (HrtsND : NoDup rts) by (apply (NoDup_app_prefix _ rts (primroots n)); exact HfullND).
  assert (HrtsM : forall r, In r rts -> cpe M r = C0).
  { intros r Hr. unfold rts in Hr. apply in_flat_map in Hr. destruct Hr as [d [HdPD Hrd]].
    rewrite HMeval. apply (fold_cmul_zero (fun d => ceval (PhiC d) r) PD d HdPD).
    apply primroots_root_PhiC; exact Hrd. }
  assert (HrtsXn1 : forall r, In r rts -> cpe (Xn1 n) r = C0).
  { intros r Hr. apply (roots_regroup_are_roots n Hn).
    rewrite HdivApp, flat_map_app. apply in_or_app. left. exact Hr. }
  destruct (monic_roots_divides M (Xn1 n) rts dM HMlen HMmon Hrtslen HrtsND HrtsM HrtsXn1) as [q Hq].
  assert (HMprim : forall r, In r (primroots n) -> cpe M r <> C0).
  { intros r Hr. rewrite HMeval. apply (fold_cmul_nonzero (fun d => ceval (PhiC d) r) PD).
    intros d Hd. apply ceval_linprod_nonzero. unfold PhiC. intros a Hain Heq. subst a.
    apply (NoDup_app_disjoint _ rts (primroots n) r HfullND); [|exact Hr].
    unfold rts. apply in_flat_map. exists d. split; [exact Hd | exact Hain]. }
  assert (HqPrim : forall r, In r (primroots n) -> cpe q r = C0).
  { intros r Hr.
    assert (Hp : cpe (Xn1 n) r = Cmul (cpe M r) (cpe q r))
      by (rewrite (cpe_nth_ext (Xn1 n) (Zpmul M q) r Hq), cpe_Zpmul; reflexivity).
    rewrite (primroots_root_Xn1 n r Hn Hr) in Hp. symmetry in Hp.
    destruct (Cmul_integral _ _ Hp) as [HM0|Hq0];
      [exfalso; apply (HMprim r Hr); exact HM0 | exact Hq0]. }
  assert (Hqnz' : exists k, nth k (map IZR q) 0%R <> 0%R).
  { destruct (Classical_Prop.classic (exists k, nth k q 0%Z <> 0%Z)) as [[k Hk]|H].
    - exists k. rewrite nth_map_IZR. apply not_0_IZR. exact Hk.
    - exfalso. assert (Hq0 : forall k, nth k q 0%Z = 0%Z).
      { intro k. destruct (Z.eq_dec (nth k q 0%Z) 0%Z) as [E|E];
          [exact E | exfalso; apply H; exists k; exact E]. }
      pose proof (Hq n) as HqN. rewrite nth_Zpmul, (Zconv_zero_r q Hq0 M n) in HqN.
      rewrite nth_n_Xn1 in HqN by exact Hn. discriminate. }
  destruct (real_deg_exists (map IZR q) Hqnz') as [dq [Hdq1 Hdq2]].
  assert (HqdqZ : nth dq q 0%Z <> 0%Z)
    by (intro Hc; apply Hdq1; rewrite nth_map_IZR, Hc; reflexivity).
  assert (HqhighZ : forall j, (dq < j)%nat -> nth j q 0%Z = 0%Z).
  { intros j Hj. apply eq_IZR. rewrite <- nth_map_IZR. rewrite (Hdq2 j Hj). reflexivity. }
  assert (HMhigh : forall i, (dM < i)%nat -> nth i M 0%Z = 0%Z)
    by (intros i Hi; apply nth_overflow; lia).
  assert (Hdqle : (dq <= euler_phi n)%nat).
  { destruct (Nat.le_gt_cases dq (euler_phi n)) as [H|H]; [exact H|exfalso].
    pose proof (Hq (dM + dq)%nat) as HqD.
    rewrite nth_Zpmul, (Zconv_top M q dM dq HMhigh HqhighZ), HMmon in HqD.
    assert (Hov : nth (dM + dq)%nat (Xn1 n) 0%Z = 0%Z)
      by (apply nth_overflow; rewrite length_Xn1 by exact Hn; lia).
    rewrite Hov in HqD. apply HqdqZ. lia. }
  assert (Hqhigh2 : forall j, (euler_phi n < j)%nat -> nth j q 0%Z = 0%Z)
    by (intros j Hj; apply HqhighZ; lia).
  assert (Hqmon : nth (euler_phi n) q 0%Z = 1%Z).
  { pose proof (Hq n) as HqN. rewrite nth_n_Xn1 in HqN by exact Hn.
    rewrite nth_Zpmul in HqN.
    replace n with (dM + euler_phi n)%nat in HqN by lia.
    rewrite (Zconv_top M q dM (euler_phi n) HMhigh Hqhigh2), HMmon in HqN. lia. }
  assert (Hqlb : (euler_phi n < length q)%nat).
  { destruct (le_lt_dec (length q) (euler_phi n)) as [Hle|Hlt]; [exfalso|exact Hlt].
    assert (Hov2 : nth (euler_phi n) q 0%Z = 0%Z) by (apply nth_overflow; exact Hle).
    rewrite Hov2 in Hqmon. discriminate. }
  set (P := firstn (S (euler_phi n)) q).
  assert (HPlen : length P = S (euler_phi n))
    by (unfold P; rewrite firstn_length; lia).
  assert (HPmon : nth (euler_phi n) P 0%Z = 1%Z)
    by (unfold P; rewrite nth_firstn_lt by lia; exact Hqmon).
  assert (HPeval : forall w, cpe P w = cpe q w).
  { intro w. apply cpe_nth_ext. intro k.
    destruct (Nat.lt_ge_cases k (S (euler_phi n))) as [Hk|Hk].
    - unfold P. rewrite nth_firstn_lt by exact Hk. reflexivity.
    - unfold P.
      assert (Hov3 : nth k (firstn (S (euler_phi n)) q) 0%Z = 0%Z)
        by (apply nth_overflow; rewrite firstn_length; lia).
      rewrite Hov3. symmetry. apply Hqhigh2. lia. }
  exists P. split; [exact HPlen | split; [exact HPmon|]].
  intro z. rewrite cpe_ceval.
  apply (monic_Cpoly_unique (map ZtoC P) (PhiC n) (primroots n) (euler_phi n)).
  - rewrite length_map. exact HPlen.
  - change C0 with (ZtoC 0%Z). rewrite map_nth, HPmon. apply ZtoC_1.
  - apply length_PhiC.
  - apply PhiC_monic.
  - apply length_primroots.
  - apply NoDup_primroots; exact Hn.
  - intros r Hr. rewrite <- cpe_ceval, HPeval. exact (HqPrim r Hr).
  - intros r Hr. apply primroots_root_PhiC; exact Hr.
Qed.

(* zeta_n has a monic rational annihilator of degree exactly phi(n): the cast of the
   integer cyclotomic Phi_n.  With zeta_annih_deg_ge_phi this fixes the minimal degree. *)
Lemma zeta_has_annih_phi : forall n, (1 <= n)%nat -> has_annih (zeta n) (euler_phi n).
Proof.
  intros n Hn. destruct (PhiZ_exists n Hn) as [P [HPlen [HPmon HPeval]]].
  unfold has_annih. exists (map IZR P). split; [|split; [|split]].
  - rewrite length_map. exact HPlen.
  - rewrite nth_map_IZR, HPmon. reflexivity.
  - apply Forall_forall. intros x Hx. apply in_map_iff in Hx.
    destruct Hx as [z [Hz _]]. subst x. apply is_rational_IZR.
  - rewrite rpe_map_IZR, HPeval. apply PhiC_zeta_root. exact Hn.
Qed.

(* the minimal monic rational annihilator degree of zeta_n is exactly phi(n) *)
Lemma zeta_min_annih_phi : forall n, (1 <= n)%nat ->
  has_annih (zeta n) (euler_phi n) /\
  (forall d, has_annih (zeta n) d -> (euler_phi n <= d)%nat).
Proof.
  intros n Hn. split.
  - apply zeta_has_annih_phi; exact Hn.
  - intros d Hd. apply (zeta_annih_deg_ge_phi n d Hn Hd).
Qed.

(* ===== Constant term of the cyclotomic polynomial Phi_n(0) = 1 (n >= 2) ===== *)
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Lemma PhiC_1_at_0 : ceval (PhiC 1) C0 = Copp C1.
Proof.
  unfold PhiC. rewrite ceval_linprod.
  assert (Hc1 : coprimes 1 = [1%nat]) by reflexivity.
  unfold primroots. rewrite Hc1. cbn [map fold_right].
  rewrite (zeta_pow_n 1 ltac:(lia)). ring.
Qed.

(* the constant term of Phi_n is 1 for n >= 2:  prod_{d|n} Phi_d(0) = 0^n - 1 = -1,
   the d=1 factor is -1, and all proper factors are 1 by strong induction. *)
Lemma PhiC_const_one : forall n, (2 <= n)%nat -> ceval (PhiC n) C0 = C1.
Proof.
  intro n. induction n as [n IH] using (well_founded_induction lt_wf). intro Hn.
  assert (Hprod : fold_right (fun d acc => Cmul (ceval (PhiC d) C0) acc) C1 (divisors n) = Copp C1).
  { rewrite <- (Xn1_prod_PhiC n C0 ltac:(lia)). rewrite cpe_Xn1 by lia.
    assert (Hp0 : Cpow C0 n = C0) by (destruct n; [lia | cbn [Cpow]; ring]).
    rewrite Hp0. ring. }
  rewrite (divisors_app_last n ltac:(lia)), fold_right_app in Hprod. cbn [fold_right] in Hprod.
  rewrite (fold_cmul_pull (fun d => ceval (PhiC d) C0) (ceval (PhiC n) C0)
             (filter (fun d => Nat.eqb (n mod d) 0) (seq 1 (n-1)))) in Hprod.
  assert (HPD : fold_right (fun d acc => Cmul (ceval (PhiC d) C0) acc) C1
                  (filter (fun d => Nat.eqb (n mod d) 0) (seq 1 (n-1))) = Copp C1).
  { assert (Hseq12 : seq 1 (n-1) = 1%nat :: seq 2 (n-2)).
    { replace (n-1)%nat with (S (n-2)) by lia. reflexivity. }
    rewrite Hseq12. cbn [filter].
    assert (Hp1 : (n mod 1 =? 0)%nat = true) by (rewrite Nat.mod_1_r; reflexivity).
    rewrite Hp1. cbn [fold_right].
    rewrite PhiC_1_at_0.
    assert (Hmid : fold_right (fun d acc => Cmul (ceval (PhiC d) C0) acc) C1
                     (filter (fun d => Nat.eqb (n mod d) 0) (seq 2 (n-2))) = C1).
    { apply fold_cmul_allone. intros d Hd. apply filter_In in Hd. destruct Hd as [Hseq Hmod].
      apply in_seq in Hseq. apply IH; lia. }
    rewrite Hmid. ring. }
  rewrite HPD in Hprod.
  transitivity (Cmul (Cmul (ceval (PhiC n) C0) (Copp C1)) (Copp C1)); [ring | rewrite Hprod; ring].
Qed.

(* ===== Reciprocal reduction: degree-phi(n)/2 annihilator of 2cos(2pi/n) ===== *)
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope R_scope.
(* general angle: 2 cos(j * 2pi/n) = zeta_n^j + zeta_n^((n-1)*j) = zeta_n^j + conj(zeta_n^j) *)
Lemma RtoC_2cos_zeta_j : forall n j, (1 <= n)%nat ->
  RtoC (2 * cos (INR j * (2 * PI / INR n)))
  = Cadd (Cpow (zeta n) j) (Cpow (zeta n) ((n-1)*j)).
Proof.
  intros n j Hn. assert (HnR : INR n <> 0) by (apply not_0_INR; lia).
  unfold zeta. rewrite !de_moivre.
  assert (Hangle : INR ((n-1)*j) * (2 * PI / INR n)
                   = - (INR j * (2 * PI / INR n)) + 2 * INR j * PI).
  { rewrite mult_INR, minus_INR by lia. simpl. field. exact HnR. }
  rewrite Hangle. unfold Cunit, Cadd, RtoC. f_equal; simpl.
  - rewrite cos_period, cos_neg. ring.
  - rewrite sin_period, sin_neg. ring.
Qed.
Close Scope R_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
(* evaluation of a concatenation of integer polynomials *)
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Lemma cpe_dickson : forall j z w, Cmul z w = C1 ->
  cpe (dickson j) (Cadd z w) = Cadd (Cpow z j) (Cpow w j).
Proof.
  intro j. induction j as [j IH] using (well_founded_induction lt_wf). intros z w Hzw.
  destruct j as [|[|j']].
  - cbn [dickson cpe Cpow].
    assert (H2 : ZtoC 2%Z = Cadd C1 C1) by (unfold ZtoC, RtoC, Cadd, C1; f_equal; simpl; ring).
    rewrite H2. ring.
  - cbn [dickson cpe Cpow].
    replace (ZtoC 0%Z) with C0 by reflexivity.
    replace (ZtoC 1%Z) with C1 by reflexivity. ring.
  - rewrite dickson_SS, cpe_Zpadd, cpe_map_Zmul. cbn [cpe].
    rewrite (IH (S j') ltac:(lia) z w Hzw), (IH j' ltac:(lia) z w Hzw), ZtoC_m1.
    replace (Copp C1) with (Copp (Cmul z w)) by (rewrite Hzw; reflexivity).
    cbn [Cpow]. replace (ZtoC 0%Z) with C0 by reflexivity. ring.
Qed.

(* (w z)^m = 1 when z w = 1 *)
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Fixpoint recip_reduce (k : nat) (P : list Z) : list Z :=
  match k with
  | O => [ (2 * nth 0 P 0)%Z ]
  | S k' => Zpadd (recip_reduce k' (removelast (tl P)))
                  (map (Z.mul (nth 0 P 0 + nth (2 * S k') P 0)%Z) (dickson (S k')))
  end.

(* KEY identity: cpe (recip_reduce k P) (z+w) = w^k cpe P z + z^k cpe P w, when zw=1
   and P has degree 2k.  Proven by induction on k peeling the outer coefficients. *)
Lemma recip_key : forall k P z w, Cmul z w = C1 -> length P = S (2*k)%nat ->
  cpe (recip_reduce k P) (Cadd z w)
  = Cadd (Cmul (Cpow w k) (cpe P z)) (Cmul (Cpow z k) (cpe P w)).
Proof.
  induction k as [|k IH]; intros P z w Hzw Hlen.
  - destruct P as [|c [|? ?]]; cbn [length] in Hlen; try lia.
    cbn [recip_reduce nth]. cbn [cpe Cpow].
    assert (Hc2 : ZtoC (2*c)%Z = Cadd (ZtoC c) (ZtoC c))
      by (rewrite <- ZtoC_add; f_equal; ring).
    rewrite Hc2. ring.
  - destruct P as [|c rest]; cbn [length] in Hlen; [lia|].
    assert (Hrlen : length rest = S (2*k+1)%nat) by lia.
    assert (Hrne : rest <> []) by (intro Hc; rewrite Hc in Hrlen; cbn in Hrlen; lia).
    set (Q := removelast rest). set (d := last rest 0%Z).
    assert (Hrest : rest = Q ++ [d]) by (apply app_removelast_last; exact Hrne).
    assert (HQlen : length Q = S (2*k)%nat).
    { assert (length rest = length (Q ++ [d])) by (rewrite <- Hrest; reflexivity).
      rewrite length_app in H. cbn [length] in H. lia. }
    assert (Hcoef : (nth 0 (c :: rest) 0 + nth (2 * S k) (c :: rest) 0)%Z = (c + d)%Z).
    { cbn [nth]. f_equal. replace (2 * S k)%nat with (S (2*k+1)) by lia. cbn [nth].
      rewrite Hrest, app_nth2 by (rewrite HQlen; lia).
      rewrite HQlen. replace (2*k+1 - S (2*k))%nat with 0%nat by lia. reflexivity. }
    cbn [recip_reduce]. cbn [tl]. fold Q. rewrite Hcoef.
    rewrite cpe_Zpadd, cpe_map_Zmul, (IH Q z w Hzw HQlen), (cpe_dickson (S k) z w Hzw).
    assert (Hcr : forall y, cpe (c :: rest) y
                  = Cadd (ZtoC c) (Cmul y (Cadd (cpe Q y) (Cmul (Cpow y (S (2*k))) (ZtoC d))))).
    { intro y. cbn [cpe]. rewrite Hrest, cpe_app, HQlen. cbn [cpe]. rewrite <- HQlen.
      replace (cpe [d] y) with (Cadd (ZtoC d) (Cmul y C0)) by (cbn [cpe]; reflexivity).
      rewrite HQlen. ring. }
    rewrite ZtoC_add.
    assert (Hwz : Cmul w z = C1) by (rewrite <- Hzw; ring).
    assert (HwSkz : Cmul (Cpow w (S k)) z = Cpow w k).
    { cbn [Cpow]. transitivity (Cmul (Cpow w k) (Cmul w z)); [ring|]. rewrite Hwz; ring. }
    assert (HzSkw : Cmul (Cpow z (S k)) w = Cpow z k).
    { cbn [Cpow]. transitivity (Cmul (Cpow z k) (Cmul z w)); [ring|]. rewrite Hzw; ring. }
    assert (HwSk_z2 : Cmul (Cpow w (S k)) (Cmul z (Cpow z (S (2*k)))) = Cpow z (S k)).
    { replace (S (2*k)) with (k + S k)%nat by lia.
      rewrite Cpow_add. transitivity (Cmul (Cmul (Cpow w (S k)) (Cpow z (S k))) (Cmul z (Cpow z k))).
      { cbn [Cpow]. ring. }
      rewrite (wz_pow_one w z (S k) Hzw). cbn [Cpow]. ring. }
    assert (HzSk_w2 : Cmul (Cpow z (S k)) (Cmul w (Cpow w (S (2*k)))) = Cpow w (S k)).
    { replace (S (2*k)) with (k + S k)%nat by lia.
      rewrite Cpow_add. transitivity (Cmul (Cmul (Cpow w (S k)) (Cpow z (S k))) (Cmul w (Cpow w k))).
      { cbn [Cpow]. ring. }
      rewrite (wz_pow_one w z (S k) Hzw). cbn [Cpow]. ring. }
    assert (HL : Cmul (Cpow w (S k)) (cpe (c :: rest) z)
                 = Cadd (Cmul (Cpow w (S k)) (ZtoC c))
                        (Cadd (Cmul (Cpow w k) (cpe Q z)) (Cmul (Cpow z (S k)) (ZtoC d)))).
    { transitivity (Cadd (Cmul (Cpow w (S k)) (ZtoC c))
                     (Cadd (Cmul (Cmul (Cpow w (S k)) z) (cpe Q z))
                           (Cmul (Cmul (Cpow w (S k)) (Cmul z (Cpow z (S (2*k))))) (ZtoC d)))).
      { rewrite (Hcr z). ring. }
      rewrite HwSkz, HwSk_z2. reflexivity. }
    assert (HR : Cmul (Cpow z (S k)) (cpe (c :: rest) w)
                 = Cadd (Cmul (Cpow z (S k)) (ZtoC c))
                        (Cadd (Cmul (Cpow z k) (cpe Q w)) (Cmul (Cpow w (S k)) (ZtoC d)))).
    { transitivity (Cadd (Cmul (Cpow z (S k)) (ZtoC c))
                     (Cadd (Cmul (Cmul (Cpow z (S k)) w) (cpe Q w))
                           (Cmul (Cmul (Cpow z (S k)) (Cmul w (Cpow w (S (2*k))))) (ZtoC d)))).
      { rewrite (Hcr w). ring. }
      rewrite HzSkw, HzSk_w2. reflexivity. }
    rewrite HL, HR. ring.
Qed.

Lemma recip_reduce_length : forall k P, length (recip_reduce k P) = S k.
Proof.
  induction k as [|k IH]; intros P; [reflexivity|].
  cbn [recip_reduce]. rewrite length_Zpadd, IH, length_map, length_dickson. lia.
Qed.

Lemma recip_reduce_lead : forall k P, (1 <= k)%nat ->
  nth k (recip_reduce k P) 0%Z = (nth 0 P 0 + nth (2*k) P 0)%Z.
Proof.
  intros [|k'] P Hk; [lia|]. cbn [recip_reduce]. rewrite nth_Zpadd.
  rewrite (nth_overflow (recip_reduce k' (removelast (tl P)))) by (rewrite recip_reduce_length; lia).
  rewrite nth_map_Zmul, dickson_monic by lia. ring.
Qed.

(* gcd(n-1, n) = 1 *)
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Lemma euler_phi_pos : forall n, (1 <= n)%nat -> (1 <= euler_phi n)%nat.
Proof.
  intros n Hn. rewrite <- length_coprimes.
  assert (Hin : In 1%nat (coprimes n)).
  { unfold coprimes. apply filter_In. split; [apply in_seq; lia | apply coprime_1_l; lia]. }
  destruct (coprimes n); [destruct Hin | cbn [length]; lia].
Qed.

(* 2cos(2pi/n) has an integer annihilator of degree exactly phi(n)/2, with nonzero
   leading coefficient: the reciprocal reduction of the cyclotomic Phi_n. *)
Lemma cos_recip_annih : forall n k, (3 <= n)%nat -> (euler_phi n = 2*k)%nat ->
  exists R, length R = S k /\ nth k R 0%Z <> 0%Z /\
            peval R (2 * cos (2 * PI / INR n)) = 0%R.
Proof.
  intros n k Hn Hphi.
  destruct (PhiZ_exists n ltac:(lia)) as [P [HPlen [HPmon HPeval]]].
  assert (HP0 : nth 0 P 0%Z = 1%Z).
  { assert (HZ : ZtoC (nth 0 P 0%Z) = ZtoC 1%Z).
    { rewrite <- cpe_at_0, (HPeval C0), (PhiC_const_one n ltac:(lia)), <- ZtoC_1. reflexivity. }
    apply eq_IZR, RtoC_inj. exact HZ. }
  assert (HPlen2 : length P = S (2 * k)%nat) by (rewrite HPlen, Hphi; reflexivity).
  exists (recip_reduce k P). split; [|split].
  - apply recip_reduce_length.
  - assert (Hk1 : (1 <= k)%nat) by (pose proof (euler_phi_pos n ltac:(lia)); lia).
    rewrite recip_reduce_lead by exact Hk1. rewrite HP0.
    replace (2*k)%nat with (euler_phi n) by lia. rewrite HPmon. lia.
  - apply RtoC_inj. rewrite <- cpe_RtoC, (RtoC_2cos_zeta n ltac:(lia)).
    set (z := zeta n). set (w := Cpow z (n-1)).
    assert (Hzw : Cmul z w = C1).
    { unfold w. replace z with (Cpow z 1) at 1 by (cbn [Cpow]; ring).
      rewrite <- Cpow_add. replace (1 + (n-1))%nat with n by lia.
      unfold z. apply zeta_pow_n; lia. }
    rewrite (recip_key k P z w Hzw HPlen2).
    assert (HPz : cpe P z = C0)
      by (unfold z; rewrite (HPeval (zeta n)); apply PhiC_zeta_root; lia).
    assert (HPw : cpe P w = C0).
    { unfold w, z. rewrite (HPeval (Cpow (zeta n) (n-1))). apply primroots_root_PhiC.
      unfold primroots. apply in_map_iff. exists (n-1)%nat. split; [reflexivity|].
      unfold coprimes. apply filter_In. split; [apply in_seq; lia|].
      unfold coprime. apply Nat.eqb_eq. apply gcd_pred_n; lia. }
    rewrite HPz, HPw. replace (RtoC 0) with C0 by reflexivity. ring.
Qed.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope R_scope.
(* THE COMPOSITE-n DEGREE THEOREM: for n >= 3 with phi(n) = 2k, the powers
   1, 2cos, ..., (2cos)^(k-1) are a Q-basis of Q(2cos(2pi/n)); i.e. [Q(2cos):Q] = phi(n)/2.
   Upper bound from cos_recip_annih, lower bound from cos_degree_ge_phi_half. *)
Theorem cos_2pi_n_degree_exactly : forall n k, (3 <= n)%nat -> (euler_phi n = 2*k)%nat ->
  basis is_rational (powers (2 * cos (2 * PI / INR n)) k)
                    (Qx (2 * cos (2 * PI / INR n))).
Proof.
  intros n k Hn Hphi.
  set (delta := 2 * cos (2 * PI / INR n)).
  destruct (cos_recip_annih n k Hn Hphi) as [R [HRlen [HRlead HRroot]]].
  set (fR := map IZR R).
  assert (HfRrat : Forall is_rational fR).
  { unfold fR. apply Forall_forall. intros z Hz. apply in_map_iff in Hz.
    destruct Hz as [x [Hx _]]. subst z. apply is_rational_IZR. }
  assert (Hroot : pe fR delta = 0).
  { unfold fR, delta. rewrite <- peval_eq_pe. exact HRroot. }
  assert (HfRlen : length fR = S k) by (unfold fR; rewrite length_map; exact HRlen).
  assert (Hval : nth k fR 0%R <> 0%R)
    by (unfold fR; rewrite nth_map_IZR; apply not_0_IZR; exact HRlead).
  assert (Hdep : ~ lin_indep is_rational (powers delta (S k))).
  { intro Hli.
    assert (Hlen : length fR = length (powers delta (S k)))
      by (rewrite powers_length, HfRlen; reflexivity).
    assert (Hfc : Fcomb fR (powers delta (S k)) = 0) by (rewrite <- HfRlen; exact Hroot).
    pose proof (Hli fR Hlen HfRrat Hfc) as Hall.
    assert (Hin : In (nth k fR 0%R) fR) by (apply nth_In; rewrite HfRlen; lia).
    rewrite Forall_forall in Hall. apply Hval; exact (Hall _ Hin). }
  destruct (nat_boundary (fun j => lin_indep is_rational (powers delta j)) k
              (lin_indep_nil is_rational) Hdep) as [d [Hindd Hdepd]].
  assert (Hdk : d = k).
  { assert (Hle : (d <= k)%nat).
    { destruct (le_lt_dec d k) as [Hok | Hgt]; [exact Hok | exfalso].
      apply Hdep. apply (lin_indep_powers_le delta (S k) d ltac:(lia) Hindd). }
    assert (Hge : (k <= d)%nat).
    { destruct (le_lt_dec k d) as [Hok | Hlt]; [exact Hok | exfalso].
      pose proof (Qx_powers_basis delta d Hindd Hdepd) as Hb.
      destruct Hb as [HBd [Hlid Hspd]].
      assert (HspanD : spans is_rational (powers delta d) (delta ^ d))
        by (apply Hspd; apply (subring_pow (Qx delta) delta d (Qx_subring delta) (Qx_x delta))).
      destruct HspanD as [a [Hla [Hra Hfa]]].
      assert (Hald : length a = d) by (rewrite Hla, powers_length; reflexivity).
      set (mu := map (Rmult (-1)) a ++ [1%R]).
      assert (Hmulen : length mu = S d)
        by (unfold mu; rewrite length_app, length_map, Hald; simpl; lia).
      assert (Hmumon : nth d mu 0%R = 1%R).
      { unfold mu. rewrite app_nth2; rewrite length_map, Hald;
          [replace (d - d)%nat with 0%nat by lia; reflexivity | lia]. }
      assert (Hmurat : Forall is_rational mu).
      { unfold mu. apply Forall_app. split.
        - apply Forall_rat_map_mult; [apply is_rational_m1 | exact Hra].
        - repeat constructor. apply is_rational_1. }
      assert (Hpa : pe a delta = delta ^ d) by (unfold pe; rewrite Hald; exact Hfa).
      assert (Hmuroot : pe mu delta = 0%R).
      { unfold mu. rewrite pe_app, pe_scale, length_map, Hald, Hpa.
        assert (Hpe1 : pe [1%R] delta = 1%R) by (rewrite pe_cons, pe_nil; ring).
        rewrite Hpe1. ring. }
      pose proof (cos_degree_ge_phi_half n mu d ltac:(lia) Hmulen Hmumon Hmurat Hmuroot) as Hbound.
      lia. }
    lia. }
  subst d. exact (Qx_powers_basis delta k Hindd Hdepd).
Qed.

(* Composite-n single-fold impossibility: if phi(n)/2 is not 2-3-smooth, then
   cos(2pi/n) is not single-fold origami-constructible.  Its degree over Q is
   phi(n)/2 (cos_2pi_n_degree_exactly), but origami numbers have 2-3-smooth degree. *)
Theorem cos_2pi_n_not_origami : forall n k, (3 <= n)%nat -> (euler_phi n = 2*k)%nat ->
  ~ two_three_smooth k -> ~ OrigamiNum (cos (2 * PI / INR n)).
Proof.
  intros n k Hn Hphi Hns HO.
  set (delta := 2 * cos (2 * PI / INR n)).
  assert (Hdelta : OrigamiNum delta).
  { unfold delta.
    replace (2 * cos (2 * PI / INR n))
      with (cos (2 * PI / INR n) + cos (2 * PI / INR n)) by ring.
    apply ON_add; exact HO. }
  destruct (origami_field_degree_smooth delta Hdelta) as [d [Hbasis Hsmooth]].
  pose proof (cos_2pi_n_degree_exactly n k Hn Hphi) as Hbasisk. fold delta in Hbasisk.
  destruct Hbasis as [HBd [Hlid Hspd]].
  destruct Hbasisk as [HBk [Hlik Hspk]].
  assert (Hdk : (d <= k)%nat).
  { pose proof (indep_le_span is_rational (powers delta d) (powers delta k) (Qx delta)
                  is_rational_subfield Hlid HBd Hspk) as Hle.
    rewrite !powers_length in Hle. exact Hle. }
  assert (Hkd : (k <= d)%nat).
  { pose proof (indep_le_span is_rational (powers delta k) (powers delta d) (Qx delta)
                  is_rational_subfield Hlik HBk Hspd) as Hle.
    rewrite !powers_length in Hle. exact Hle. }
  assert (Hdeq : d = k) by lia. subst d. exact (Hns Hsmooth).
Qed.
Close Scope R_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
(* ===== phi(n) is even for n >= 3, via a fixpoint-free involution on the units ===== *)
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Lemma euler_phi_even : forall n, (3 <= n)%nat -> exists k, euler_phi n = 2 * k.
Proof.
  intros n Hn.
  assert (Heven : Nat.Even (euler_phi n)).
  { rewrite <- length_coprimes.
    apply (involution_even (length (coprimes n)) (coprimes n) (fun j => n - j) eq_refl).
    - unfold coprimes. apply NoDup_filter_nat. apply seq_NoDup.
    - intros x Hx. unfold coprimes in Hx. apply filter_In in Hx. destruct Hx as [Hseq Hcop].
      apply in_seq in Hseq. apply Nat.eqb_eq in Hcop. intro Ec.
      assert (Hn2x : n = 2 * x) by lia.
      assert (Hxn : Nat.divide x n) by (exists 2; lia).
      assert (Hgx : Nat.gcd x n = x)
        by (apply Nat.divide_antisym;
            [apply Nat.gcd_divide_l | apply Nat.gcd_greatest; [apply Nat.divide_refl | exact Hxn]]).
      rewrite Hcop in Hgx. lia.
    - intros x Hx. unfold coprimes in Hx |- *. apply filter_In in Hx. destruct Hx as [Hseq Hcop].
      apply in_seq in Hseq. apply Nat.eqb_eq in Hcop. apply filter_In. split.
      + apply in_seq. assert (Hxlt : (x < n)%nat).
        { destruct (Nat.eq_dec x n) as [E|E]; [subst x; rewrite Nat.gcd_diag in Hcop; lia | lia]. }
        lia.
      + rewrite coprime_sub by lia. apply Nat.eqb_eq. exact Hcop.
    - intros x Hx. unfold coprimes in Hx. apply filter_In in Hx. destruct Hx as [Hseq _].
      apply in_seq in Hseq. lia. }
  destruct Heven as [k Hk]. exists k. lia.
Qed.

(* doubling preserves 2-3-smoothness *)
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope R_scope.
Theorem cos_2pi_n_not_origami_clean : forall n, (3 <= n)%nat ->
  ~ two_three_smooth (euler_phi n) -> ~ OrigamiNum (cos (2 * PI / INR n)).
Proof.
  intros n Hn Hns.
  destruct (euler_phi_even n Hn) as [k Hk].
  apply (cos_2pi_n_not_origami n k Hn Hk).
  intro Hsk. apply Hns. rewrite Hk. apply two_three_smooth_2k. exact Hsk.
Qed.

(* ===== Constructive direction (small-degree cases) ===== *)

(* a root of any monic cubic with origami coefficients is origami (depress and
   apply the depressed-cubic closure) *)
Close Scope R_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope R_scope.
Theorem cos_2pi_n_not_euclid : forall n k, (3 <= n)%nat -> (euler_phi n = 2*k)%nat ->
  ~ is_power_of_2 k -> ~ EuclidNum (cos (2 * PI / INR n)).
Proof.
  intros n k Hn Hphi Hns HE.
  set (delta := 2 * cos (2 * PI / INR n)).
  assert (Hdelta : EuclidNum delta).
  { unfold delta.
    replace (2 * cos (2 * PI / INR n))
      with (cos (2 * PI / INR n) + cos (2 * PI / INR n)) by ring.
    apply EN_add; exact HE. }
  destruct (euclid_field_degree_pow2 delta Hdelta) as [d [Hbasis Hpow]].
  pose proof (cos_2pi_n_degree_exactly n k Hn Hphi) as Hbasisk. fold delta in Hbasisk.
  destruct Hbasis as [HBd [Hlid Hspd]].
  destruct Hbasisk as [HBk [Hlik Hspk]].
  assert (Hdk : (d <= k)%nat).
  { pose proof (indep_le_span is_rational (powers delta d) (powers delta k) (Qx delta)
                  is_rational_subfield Hlid HBd Hspk) as Hle.
    rewrite !powers_length in Hle. exact Hle. }
  assert (Hkd : (k <= d)%nat).
  { pose proof (indep_le_span is_rational (powers delta k) (powers delta d) (Qx delta)
                  is_rational_subfield Hlik HBk Hspd) as Hle.
    rewrite !powers_length in Hle. exact Hle. }
  assert (Hdeq : d = k) by lia. subst d. exact (Hns Hpow).
Qed.

(* CLEAN form for all n >= 3: cos(2pi/n) is not compass-straightedge constructible
   whenever phi(n) is not a power of 2. *)
Theorem cos_2pi_n_not_euclid_clean : forall n, (3 <= n)%nat ->
  ~ is_power_of_2 (euler_phi n) -> ~ EuclidNum (cos (2 * PI / INR n)).
Proof.
  intros n Hn Hns.
  destruct (euler_phi_even n Hn) as [k Hk].
  apply (cos_2pi_n_not_euclid n k Hn Hk).
  intro Hsk. apply Hns. rewrite Hk. apply is_power_of_2_2k. exact Hsk.
Qed.

(* ===== The 2^a-gons are compass-straightedge constructible (repeated bisection) ===== *)
Close Scope R_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Close Scope R_scope.
Close Scope R_scope.
Close Scope R_scope.
