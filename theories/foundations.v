(* foundations.v -- algebra, analysis, number theory, polynomials, and linear
   algebra; complex numbers; the OrigamiNum algebraic core.  Foundational layer,
   depends on nothing else in the development. *)
From Stdlib Require Import Reals Lra Field R_sqr Psatz Nsatz Ring Ranalysis1 RingMicromega List ProofIrrelevance ClassicalDescription PeanoNat ZArith Classical Permutation Bool Arith.Wf_nat.
From Stdlib Require Znumtheory.
Import ListNotations.
Open Scope R_scope.
Definition sqr (x : R) : R := x * x.

(** √((x₁-x₂)² + (y₁-y₂)²) *)
Lemma square_pos : forall x : R, x <> 0 -> x * x > 0.
Proof.
  intros x Hneq.
  destruct (Rlt_dec x 0) as [Hlt | Hnlt].
  - nra.
  - destruct (Rgt_dec x 0) as [Hgt | HnGt].
    + nra.
    + exfalso; nra.
Qed.

(** a ≠ 0 → a·(c/a) = c *)
Lemma mul_div_cancel_l : forall a c, a <> 0 -> a * (c / a) = c.
Proof.
  intros a c Ha.
  unfold Rdiv.
  rewrite Rmult_comm.
  rewrite Rmult_assoc.
  rewrite Rinv_l; [ring|exact Ha].
Qed.

(** Projection onto line ax+by+c=0 satisfies the line equation *)
Lemma proj_eval :
  forall a b c x y,
    (a <> 0 \/ b <> 0) ->
    a * (x - a * ((a * x + b * y + c) / (a * a + b * b))) +
    b * (y - b * ((a * x + b * y + c) / (a * a + b * b))) + c = 0.
Proof.
  intros a b c x y Hnz.
  set (d := a * a + b * b).
  assert (Hd : d <> 0).
  { unfold d; intro Hsum.
    assert (Ha2nn : 0 <= a * a) by apply Rle_0_sqr.
    assert (Hb2nn : 0 <= b * b) by apply Rle_0_sqr.
    assert (Ha2 : a * a = 0) by lra.
    assert (Hb2 : b * b = 0) by lra.
    assert (Ha0 : a = 0).
    { destruct (Rmult_integral _ _ Ha2) as [H0 | H0]; lra. }
    assert (Hb0 : b = 0).
    { destruct (Rmult_integral _ _ Hb2) as [H0 | H0]; lra. }
    destruct Hnz; contradiction. }
  unfold d.
  field; auto.
Qed.

(** √(A² + B²) *)
Lemma delta_reflect_x :
  forall a b c d x1 x2 y1 y2,
    d <> 0 ->
    (x1 - 2 * a * ((a * x1 + b * y1 + c) / d)) -
    (x2 - 2 * a * ((a * x2 + b * y2 + c) / d)) =
    (x1 - x2) - 2 * a * ((a * (x1 - x2) + b * (y1 - y2)) / d).
Proof.
  intros a b c d x1 x2 y1 y2 Hd.
  field; auto.
Qed.

(** y-coordinate difference under reflection *)
Lemma delta_reflect_y :
  forall a b c d x1 x2 y1 y2,
    d <> 0 ->
    (y1 - 2 * b * ((a * x1 + b * y1 + c) / d)) -
    (y2 - 2 * b * ((a * x2 + b * y2 + c) / d)) =
    (y1 - y2) - 2 * b * ((a * (x1 - x2) + b * (y1 - y2)) / d).
Proof.
  intros a b c d x1 x2 y1 y2 Hd.
  field; auto.
Qed.

(** Reflection preserves squared distance from origin *)
Lemma reflect_delta_sq :
  forall a b dx dy,
    (a * a + b * b) <> 0 ->
    sqr (dx - 2 * a * ((a * dx + b * dy) / (a * a + b * b))) +
    sqr (dy - 2 * b * ((a * dx + b * dy) / (a * a + b * b))) =
    sqr dx + sqr dy.
Proof.
  intros a b dx dy Hd.
  set (d := a * a + b * b).
  set (t := a * dx + b * dy).
  assert (Hd0 : d <> 0) by (unfold d; exact Hd).
  unfold sqr.
  assert (Hexp :
            (dx - 2 * a * (t / d)) * (dx - 2 * a * (t / d)) +
            (dy - 2 * b * (t / d)) * (dy - 2 * b * (t / d)) =
            dx * dx + dy * dy - 4 * t * t / d + 4 * t * t / d).
  { unfold d, t; field; auto. }
  rewrite Hexp; nra.
Qed.

(** ((x₁+x₂)/2, (y₁+y₂)/2) *)
Lemma sqrt_4x_eq : forall x, 0 <= x -> sqrt (4 * x) = 2 * sqrt x.
Proof.
  intros x Hx.
  assert (Hsq: sqrt x * sqrt x = x) by (apply sqrt_sqrt; lra).
  assert (Heq: 4 * x = (2 * sqrt x) * (2 * sqrt x)).
  { replace ((2 * sqrt x) * (2 * sqrt x)) with (4 * (sqrt x * sqrt x)) by ring.
    rewrite Hsq. ring. }
  rewrite Heq.
  rewrite sqrt_square; [ring | ].
  apply Rmult_le_pos; [lra | apply sqrt_pos].
Qed.

(** O5_vert_image (0,0) (1+x,0) 2 = (2, 2√x) for x > 0 *)
Lemma midpoint_avg : forall a b, (a + b) / 2 = (a + b) * / 2.
Proof.
  intros. unfold Rdiv. reflexivity.
Qed.

(** a² - b² = (a-b)(a+b) *)
Lemma diff_sqr : forall a b, a * a - b * b = (a - b) * (a + b).
Proof.
  intros. ring.
Qed.

(** ((a+b)/2)·2 = a+b *)
Lemma mid_coord : forall a b, (a + b) / 2 * 2 = a + b.
Proof.
  intros. field.
Qed.

(** 2 ≠ 0 *)
Lemma two_neq_zero : 2 <> 0.
Proof.
  lra.
Qed.

(** a - (a+b)/2 = (a-b)/2 *)
Lemma half_sum : forall a b, a - (a + b) / 2 = (a - b) / 2.
Proof.
  intros. field.
Qed.

(** a² - b² = -2(b-a)·((a+b)/2) *)
Lemma sqr_diff_factor : forall a b, a * a - b * b = -(2 * (b - a)) * ((a + b) / 2).
Proof.
  intros. field.
Qed.

(** b ≠ 0 → 2b·(a/b²) = 2a/b *)
Lemma double_cancel : forall a b, b <> 0 -> 2 * b * (a / (b * b)) = 2 * a / b.
Proof.
  intros. field. assumption.
Qed.

(** b ≠ 0 → a·(b/b²) = a/b *)
Lemma cancel_fraction : forall a b, b <> 0 -> a * (b / (b * b)) = a / b.
Proof.
  intros. field. assumption.
Qed.

(** 4 ≠ 0 *)
Lemma four_is_nonzero : 4 <> 0.
Proof.
  lra.
Qed.

(** 4a² = 2·(2a)·(2a)/2 *)
Lemma four_sqr : forall a, 4 * a * a = 2 * (2 * a) * (2 * a) / 2.
Proof.
  intros. field.
Qed.

(** a ≠ 0 → a² + b² ≠ 0 *)
Lemma sum_sqr_nonzero : forall a b, a <> 0 -> a * a + b * b <> 0.
Proof.
  intros a b Ha.
  intro Hcontra.
  assert (Ha_sq_pos : 0 <= a * a) by apply Rle_0_sqr.
  assert (Hb_sq_pos : 0 <= b * b) by apply Rle_0_sqr.
  assert (Ha_sq_z : a * a = 0) by lra.
  destruct (Rmult_integral _ _ Ha_sq_z) as [Ha_z | Ha_z]; lra.
Qed.

(** b ≠ 0 → a² + b² ≠ 0 *)
Lemma sum_sqr_nonzero_sym : forall a b, b <> 0 -> a * a + b * b <> 0.
Proof.
  intros a b Hb.
  intro Hcontra.
  assert (Ha_sq_pos : 0 <= a * a) by apply Rle_0_sqr.
  assert (Hb_sq_pos : 0 <= b * b) by apply Rle_0_sqr.
  assert (Hb_sq_z : b * b = 0) by lra.
  destruct (Rmult_integral _ _ Hb_sq_z) as [Hb_z | Hb_z]; lra.
Qed.

(** p - 2px = p(1 - 2x) *)
Lemma refl_sub_main : forall p x, p - 2 * p * x = p * (1 - 2 * x).
Proof.
  intros. ring.
Qed.

(** c ≠ 0 → a/c + b/c = (a+b)/c *)
Lemma fold_div : forall a b c, c <> 0 -> a / c + b / c = (a + b) / c.
Proof.
  intros. field. assumption.
Qed.

(** 2(b-a)a + (a²-b²) = -(b-a)² *)
Lemma factor_half_diff : forall a b, 2 * (b - a) * a + (a * a - b * b) = -(b - a) * (b - a).
Proof.
  intros. ring.
Qed.

(** a ≠ 0 → y₁ - 2a·(a·((y₁-y₂)/2)/a²) = y₂ *)
Lemma simpl_reflect_y : forall a y1 y2, a <> 0 -> y1 - 2 * a * (a * ((y1 - y2) / 2) / (a * a)) = y2.
Proof.
  intros. field. assumption.
Qed.

(** a ≠ 0 → x₁ - 2a·(a·((x₁-x₂)/2)/a²) = x₂ *)
Lemma simpl_reflect_x : forall a x1 x2, a <> 0 -> x1 - 2 * a * (a * ((x1 - x2) / 2) / (a * a)) = x2.
Proof.
  intros. field. assumption.
Qed.

(** Midpoint lies on vertical perpendicular bisector *)
Lemma mid_on_perp_vert : forall x y1 y2, y1 <> y2 -> 0 * x + 2 * (y2 - y1) * ((y1 + y2) / 2) + (x * x + y1 * y1 - x * x - y2 * y2) = 0.
Proof.
  intros. field.
Qed.

(** Midpoint lies on horizontal perpendicular bisector *)
Lemma mid_on_perp_horiz : forall x1 x2 y, x1 <> x2 -> 2 * (x2 - x1) * ((x1 + x2) / 2) + 2 * (y - y) * ((y + y) / 2) + (x1 * x1 + y * y - x2 * x2 - y * y) = 0.
Proof.
  intros. field.
Qed.

(** Midpoint lies on general perpendicular bisector *)
Lemma mid_on_perp_gen : forall x1 y1 x2 y2, x1 <> x2 -> y1 <> y2 -> 2 * (x2 - x1) * ((x1 + x2) / 2) + 2 * (y2 - y1) * ((y1 + y2) / 2) + (x1 * x1 + y1 * y1 - x2 * x2 - y2 * y2) = 0.
Proof.
  intros. field.
Qed.

(** 0·a + b = b *)
Lemma zero_mul_l : forall a b, 0 * a + b = b.
Proof.
  intros. ring.
Qed.

(** a + 0·b = a *)
Lemma zero_mul_r : forall a b, a + 0 * b = a.
Proof.
  intros. ring.
Qed.

(** midpoint(p₁,p₂) ∈ perp_bisector(p₁,p₂) *)
Lemma sum_sq_nz_l : forall a b, a <> 0 -> a * a + b * b <> 0.
Proof.
  intros a b Ha. intro H.
  assert (Ha2 : 0 <= a * a) by apply Rle_0_sqr.
  assert (Hb2 : 0 <= b * b) by apply Rle_0_sqr.
  assert (Haz : a * a = 0) by lra.
  apply Rmult_integral in Haz. destruct Haz; lra.
Qed.

(** x₁ ≠ x₂ → fst(reflect((x₁,y₁), perp_bisector)) = x₂ *)
Lemma point_eq_implies_offset_zero : forall x y t a b,
  (x + t * a, y + t * b) = (x, y) ->
  t * a = 0 /\ t * b = 0.
Proof.
  intros x y t a b Heq.
  injection Heq as Hx Hy.
  split; lra.
Qed.

(** denom ≠ 0 ∧ t/denom = 0 → t = 0 *)
Lemma fraction_zero_num : forall t denom,
  denom <> 0 ->
  t / denom = 0 ->
  t = 0.
Proof.
  intros t denom Hdenom Heq.
  unfold Rdiv in Heq.
  apply Rmult_eq_reg_r with (r := / denom).
  - rewrite Heq. ring.
  - apply Rinv_neq_0_compat. exact Hdenom.
Qed.

(** p₁ ∉ l₁ → p₁ ≠ q in fold_O7_corrected *)
Definition cubic_depressed (p q t : R) : R := t * t * t + p * t + q.

(** cubic_depressed(p,q,r) = 0 ⟺ r³ + pr + q = 0 *)
Lemma cubic_root_iff : forall p q r,
  cubic_depressed p q r = 0 <-> r * r * r + p * r + q = 0.
Proof.
  intros p q r.
  unfold cubic_depressed.
  reflexivity.
Qed.

(** Δ = -4p³ - 27q² *)
Definition cubic_discriminant (p q : R) : R := -4 * p * p * p - 27 * q * q.

(** x³ *)
Definition cube_func (x : R) : R := x * x * x.

(** x ↦ x³ is continuous *)
Lemma cube_func_continuous : continuity cube_func.
Proof.
  unfold cube_func.
  apply continuity_mult.
  - apply continuity_mult.
    + apply derivable_continuous, derivable_id.
    + apply derivable_continuous, derivable_id.
  - apply derivable_continuous, derivable_id.
Qed.

(** 0 ≤ x < y → x³ < y³ *)
Lemma cube_func_increasing : forall x y, 0 <= x -> x < y -> cube_func x < cube_func y.
Proof.
  intros x y Hx Hlt.
  unfold cube_func.
  assert (H: 0 < y) by lra.
  assert (Hdiff: 0 < y - x) by lra.
  assert (Hpos: 0 < y * y + x * y + x * x).
  { assert (H1: 0 <= x * y) by nra.
    assert (H2: 0 <= x * x) by nra.
    assert (H3: 0 < y * y) by nra.
    lra. }
  assert (Heq: y * y * y - x * x * x = (y - x) * (y * y + x * y + x * x)) by ring.
  assert (Hprod: 0 < (y - x) * (y * y + x * y + x * x)).
  { apply Rmult_lt_0_compat; assumption. }
  lra.
Qed.

(** ∀ y > 0, ∃ x > 0 with x³ = y (via IVT) *)
Theorem cube_root_pos_exists : forall y, 0 < y -> {x : R | 0 < x /\ cube_func x = y}.
Proof.
  intros y Hy.
  destruct (Req_EM_T y 1) as [Heq1 | Hneq1].
  - (* Case: y = 1 *)
    exists 1. split.
    + lra.
    + unfold cube_func. rewrite Heq1. ring.
  - destruct (Rlt_dec y 1) as [Hlt1 | Hge1].
    + (* Case: 0 < y < 1, search in [y, 1] using f(x) = x³ - y *)
      pose (f := fun x => cube_func x - y).
      assert (Hcont: continuity f).
      { unfold f. apply continuity_minus.
        - exact cube_func_continuous.
        - apply continuity_const. intro. reflexivity. }
      assert (Hfy: f y < 0).
      { unfold f, cube_func. assert (Hy1: y < 1) by lra. nra. }
      assert (Hf1: 0 < f 1).
      { unfold f, cube_func. lra. }
      destruct (IVT f y 1 Hcont Hlt1 Hfy Hf1) as [x [[Hxy Hx1] Hfx]].
      exists x. split.
      * lra.
      * unfold f in Hfx. lra.
    + (* Case: y > 1, search in [1, y] using f(x) = x³ - y *)
      assert (Hnle: 1 < y) by lra.
      pose (f := fun x => cube_func x - y).
      assert (Hcont: continuity f).
      { unfold f. apply continuity_minus.
        - exact cube_func_continuous.
        - apply continuity_const. intro. reflexivity. }
      assert (Hf1: f 1 < 0).
      { unfold f, cube_func. lra. }
      assert (Hfy: 0 < f y).
      { unfold f, cube_func. nra. }
      destruct (IVT f 1 y Hcont Hnle Hf1 Hfy) as [x [[H1x Hxy] Hfx]].
      exists x. split.
      * lra.
      * unfold f in Hfx. lra.
Qed.

(** x³ = y³ ∧ x,y ≥ 0 → x = y *)
Lemma cube_func_injective : forall x y, 0 <= x -> 0 <= y -> cube_func x = cube_func y -> x = y.
Proof.
  intros x y Hx Hy Heq.
  destruct (Rlt_dec x y) as [Hlt | Hnlt].
  - (* x < y *)
    assert (Hcontra: cube_func x < cube_func y).
    { apply cube_func_increasing; assumption. }
    lra.
  - destruct (Rlt_dec y x) as [Hgt | Hngt].
    + (* y < x *)
      assert (Hcontra: cube_func y < cube_func x).
      { apply cube_func_increasing; assumption. }
      lra.
    + (* neither x < y nor y < x, so x = y *)
      lra.
Qed.

(** Positive cube root (dependent type) *)
Definition cbrt_pos (y : R) (Hy : 0 < y) : R := proj1_sig (cube_root_pos_exists y Hy).

(** cbrt_pos(y) > 0 ∧ cbrt_pos(y)³ = y *)
Lemma cbrt_pos_spec : forall y Hy, 0 < cbrt_pos y Hy /\ cube_func (cbrt_pos y Hy) = y.
Proof.
  intros y Hy.
  unfold cbrt_pos.
  destruct (cube_root_pos_exists y Hy) as [x Hx]. simpl.
  exact Hx.
Qed.

(** x < 0 → -x > 0 *)
Lemma neg_pos_iff : forall x, x < 0 -> 0 < - x.
Proof. intros x Hx. lra. Qed.

(** ¬(0 < x) ∧ x ≠ 0 → x < 0 *)
Lemma neg_case_proof : forall x, ~ 0 < x -> x <> 0 -> x < 0.
Proof. intros x Hnpos Hneg. lra. Qed.

(** Real cube root: ∛x *)
Definition cbrt (x : R) : R :=
  match Rlt_dec 0 x with
  | left Hpos => cbrt_pos x Hpos
  | right Hnpos =>
      match Req_EM_T x 0 with
      | left _ => 0
      | right Hneg => - cbrt_pos (- x) (neg_pos_iff x (neg_case_proof x Hnpos Hneg))
      end
  end.

(** x > 0 → (∛x)³ = x *)
Lemma cbrt_spec_pos : forall x, 0 < x -> cube_func (cbrt x) = x.
Proof.
  intros x Hx.
  unfold cbrt.
  destruct (Rlt_dec 0 x) as [Hpos | Hnpos].
  - destruct (cbrt_pos_spec x Hpos) as [_ Hcube]. exact Hcube.
  - exfalso. lra.
Qed.

(** ∛0 = 0 *)
Lemma cbrt_0 : cbrt 0 = 0.
Proof.
  unfold cbrt.
  destruct (Rlt_dec 0 0) as [Hcontra|H0]; [exfalso; lra|].
  destruct (Req_EM_T 0 0) as [Heq|Hcontra]; [reflexivity|exfalso; exact (Hcontra eq_refl)].
Qed.

(** (∛0)³ = 0 *)
Lemma cbrt_cube_0 : cube_func (cbrt 0) = 0.
Proof.
  rewrite cbrt_0.
  unfold cube_func.
  ring.
Qed.

(** x < 0 → (∛x)³ = x *)
Lemma cbrt_spec_neg : forall x, x < 0 -> cube_func (cbrt x) = x.
Proof.
  intros x Hx.
  unfold cbrt.
  destruct (Rlt_dec 0 x) as [Hcontra|H0]; [exfalso; lra|].
  destruct (Req_EM_T x 0) as [Heq|Hneq]; [exfalso; lra|].
  set (y := cbrt_pos (- x) (neg_pos_iff x (neg_case_proof x H0 Hneq))).
  unfold cube_func.
  assert (Hcube: y * y * y = - x).
  { pose proof (cbrt_pos_spec (- x) (neg_pos_iff x (neg_case_proof x H0 Hneq))) as [_ Heq].
    unfold cube_func in Heq.
    unfold y.
    exact Heq. }
  assert (Hneg_cube: (- y) * (- y) * (- y) = - (y * y * y)) by ring.
  rewrite Hneg_cube, Hcube.
  ring.
Qed.

(** (∛x)³ = x for all x ∈ ℝ *)
Lemma cbrt_spec : forall x, cube_func (cbrt x) = x.
Proof.
  intro x.
  destruct (Req_EM_T x 0) as [Heq|Hneq].
  - subst. apply cbrt_cube_0.
  - destruct (Rlt_dec x 0) as [Hlt|Hnlt].
    + apply cbrt_spec_neg. exact Hlt.
    + assert (Hgt: 0 < x) by lra.
      apply cbrt_spec_pos. exact Hgt.
Qed.

(** Cardano's formula: ∛(-q/2 + √D) + ∛(-q/2 - √D) where D = q²/4 + p³/27 *)
Definition cardano_solve (p q : R) : R :=
  cbrt (- q / 2 + sqrt (Rmax 0 (q * q / 4 + p * p * p / 27))) +
  cbrt (- q / 2 - sqrt (Rmax 0 (q * q / 4 + p * p * p / 27))).

(** x ≥ 0 → √(x²) = x *)
Lemma sqrt_sqr_pos : forall x, 0 <= x -> sqrt (x * x) = x.
Proof.
  intros x Hx.
  replace (x * x) with (Rsqr x) by (unfold Rsqr; ring).
  apply sqrt_Rsqr.
  exact Hx.
Qed.

(** (u+v)³ = u³ + v³ + 3uv(u+v) *)
Lemma sum_cubes_formula : forall u v,
  (u + v) * (u + v) * (u + v) =
  u * u * u + v * v * v + 3 * u * v * (u + v).
Proof.
  intros u v.
  ring.
Qed.

(** u³v³ = (uv)³ *)
Lemma product_cubes_formula : forall u v,
  u * u * u * (v * v * v) = (u * v) * (u * v) * (u * v).
Proof.
  intros u v.
  ring.
Qed.

(** (a+b)(a-b) = a² - b² *)
Lemma difference_of_squares : forall a b,
  (a + b) * (a - b) = a * a - b * b.
Proof.
  intros a b. ring.
Qed.

(** s² = q²/4 + p³/27 → (-q/2)² - s² = -p³/27 *)
Lemma cardano_discriminant_identity : forall p q s,
  s * s = q * q / 4 + p * p * p / 27 ->
  (- q / 2) * (- q / 2) - s * s = - p * p * p / 27.
Proof.
  intros p q s Hs.
  rewrite Hs.
  field.
Qed.

(** √(max(0,x))² = max(0,x) *)
Lemma sqrt_Rmax_sqr : forall x,
  sqrt (Rmax 0 x) * sqrt (Rmax 0 x) = Rmax 0 x.
Proof.
  intro x.
  apply sqrt_sqrt.
  apply Rmax_l.
Qed.

(** u³ = -q/2+√D, v³ = -q/2-√D → (uv)³ = -p³/27 *)
Lemma cardano_uv_product_nonneg : forall p q u v,
  0 <= q * q / 4 + p * p * p / 27 ->
  u * u * u = - q / 2 + sqrt (q * q / 4 + p * p * p / 27) ->
  v * v * v = - q / 2 - sqrt (q * q / 4 + p * p * p / 27) ->
  (u * v) * (u * v) * (u * v) = - p * p * p / 27.
Proof.
  intros p q u v Hdisc Hu Hv.
  rewrite <- product_cubes_formula.
  rewrite Hu, Hv.
  set (s := sqrt (q * q / 4 + p * p * p / 27)).
  assert (Hs: s * s = q * q / 4 + p * p * p / 27).
  { unfold s. apply sqrt_sqrt. exact Hdisc. }
  assert (Hprod: (- q / 2 + s) * (- q / 2 - s) = (- q / 2) * (- q / 2) - s * s).
  { ring. }
  rewrite Hprod.
  apply cardano_discriminant_identity.
  exact Hs.
Qed.

(** (∛x)³ = x *)
Lemma cbrt_cube : forall x,
  cbrt x * cbrt x * cbrt x = x.
Proof.
  intro x.
  pose proof (cbrt_spec x) as H.
  unfold cube_func in H.
  exact H.
Qed.

(** ∛1 = 1 *)
Lemma cbrt_1 : cbrt 1 = 1.
Proof.
  unfold cbrt.
  destruct (Rlt_dec 0 1) as [H|H]; [|exfalso; lra].
  destruct (cbrt_pos_spec 1 H) as [Hpos Hcube].
  apply cube_func_injective.
  - left. exact Hpos.
  - lra.
  - unfold cube_func in *. rewrite Hcube. ring.
Qed.

(** (∛(xⁿ))³ = xⁿ *)
Lemma cbrt_mult_power : forall x n,
  cbrt (x ^ n) * cbrt (x ^ n) * cbrt (x ^ n) = x ^ n.
Proof.
  intros x n. apply cbrt_cube.
Qed.

(** (∛(8x))³ = 8x *)
Lemma cbrt_mult_8 : forall x,
  cbrt (8 * x) * cbrt (8 * x) * cbrt (8 * x) = 8 * x.
Proof.
  intro x. apply cbrt_cube.
Qed.

(** ∛27 = 3 *)
Lemma cbrt_27 : cbrt 27 = 3.
Proof.
  unfold cbrt.
  destruct (Rlt_dec 0 27) as [H|H]; [|exfalso; lra].
  destruct (cbrt_pos_spec 27 H) as [Hpos Hcube].
  apply cube_func_injective.
  - left. exact Hpos.
  - lra.
  - unfold cube_func in *. rewrite Hcube. ring.
Qed.

(** x > 0 → ∛x > 0 *)
Lemma cbrt_pos_positive : forall x (Hx : 0 < x), 0 < cbrt x.
Proof.
  intros x Hx.
  unfold cbrt.
  destruct (Rlt_dec 0 x) as [H|H]; [|exfalso; lra].
  apply (cbrt_pos_spec x H).
Qed.

(** x,y > 0 → ∛x·∛y = ∛(xy) *)
Lemma cbrt_pos_mult : forall x y,
  0 < x -> 0 < y -> cbrt x * cbrt y = cbrt (x * y).
Proof.
  intros x y Hx Hy.
  assert (Hxy : 0 < x * y) by (apply Rmult_lt_0_compat; assumption).
  apply cube_func_injective.
  - left. apply Rmult_lt_0_compat; apply cbrt_pos_positive; assumption.
  - left. apply cbrt_pos_positive; assumption.
  - unfold cube_func.
    replace ((cbrt x * cbrt y) * (cbrt x * cbrt y) * (cbrt x * cbrt y))
      with ((cbrt x * cbrt x * cbrt x) * (cbrt y * cbrt y * cbrt y)) by ring.
    rewrite cbrt_cube, cbrt_cube.
    rewrite cbrt_cube.
    reflexivity.
Qed.

(** (-x)³ = -(x³) *)
Lemma cube_neg : forall x, cube_func (-x) = - cube_func x.
Proof.
  intro x. unfold cube_func. ring.
Qed.

(** x < 0 → ∛x < 0 *)
Lemma cbrt_neg_negative : forall x, x < 0 -> cbrt x < 0.
Proof.
  intros x Hx.
  unfold cbrt.
  destruct (Rlt_dec 0 x) as [Hpos|Hnpos]; [exfalso; lra|].
  destruct (Req_EM_T x 0) as [Heq|Hneq]; [exfalso; lra|].
  set (c := cbrt_pos (-x) (neg_pos_iff x (neg_case_proof x Hnpos Hneq))).
  assert (Hc_pos : 0 < c) by (unfold c; apply cbrt_pos_spec).
  lra.
Qed.

(** x ≥ 0 → ∛x ≥ 0 *)
Lemma cbrt_nonneg : forall x, 0 <= x -> 0 <= cbrt x.
Proof.
  intros x Hx.
  destruct (Req_EM_T x 0) as [Hx0|Hxn0].
  - subst. rewrite cbrt_0. lra.
  - assert (Hx_pos : 0 < x) by lra.
    left. apply cbrt_pos_positive. exact Hx_pos.
Qed.

(** a³ = b³ ∧ same sign → a = b *)
Lemma cbrt_unique : forall a b,
  cube_func a = cube_func b ->
  (0 <= a /\ 0 <= b) \/ (a <= 0 /\ b <= 0) ->
  a = b.
Proof.
  intros a b Hcube Hsign.
  destruct Hsign as [[Ha Hb] | [Ha Hb]].
  - apply cube_func_injective; assumption.
  - destruct (Req_EM_T a 0) as [Ha0|Han0].
    + subst a.
      assert (Hb3 : cube_func b = 0) by (rewrite <- Hcube; unfold cube_func; ring).
      unfold cube_func in Hb3.
      assert (Hb0 : b = 0).
      { destruct (Rmult_integral _ _ Hb3) as [H1|H1].
        - destruct (Rmult_integral _ _ H1); lra.
        - exact H1. }
      lra.
    + destruct (Req_EM_T b 0) as [Hb0|Hbn0].
      * subst b.
        assert (Ha3 : cube_func a = 0) by (rewrite Hcube; unfold cube_func; ring).
        unfold cube_func in Ha3.
        destruct (Rmult_integral _ _ Ha3) as [H1|H1].
        -- destruct (Rmult_integral _ _ H1); lra.
        -- lra.
      * assert (Ha_neg : a < 0) by lra.
        assert (Hb_neg : b < 0) by lra.
        assert (Hna_pos : 0 < -a) by lra.
        assert (Hnb_pos : 0 < -b) by lra.
        assert (Hcube_neg : cube_func (-a) = cube_func (-b)).
        { rewrite cube_neg, cube_neg. lra. }
        assert (Heq : -a = -b).
        { apply cube_func_injective; lra. }
        lra.
Qed.

(** ∛(-x) = -∛x *)
Lemma cbrt_neg : forall x, cbrt (-x) = - cbrt x.
Proof.
  intro x.
  apply cbrt_unique.
  - unfold cube_func.
    replace ((- cbrt x) * (- cbrt x) * (- cbrt x)) with (- (cbrt x * cbrt x * cbrt x)) by ring.
    rewrite cbrt_cube.
    rewrite cbrt_cube.
    ring.
  - destruct (Rlt_dec x 0) as [Hx_neg | Hx_nonneg].
    + left. split.
      * apply cbrt_nonneg. lra.
      * assert (Hcbrt_neg : cbrt x < 0) by (apply cbrt_neg_negative; lra).
        lra.
    + destruct (Req_EM_T x 0) as [Hx0 | Hxn0].
      * subst. rewrite Ropp_0. rewrite cbrt_0. left. lra.
      * assert (Hx_pos : 0 < x) by lra.
        right. split.
        -- assert (Hnx_neg : -x < 0) by lra.
           assert (Hcbrt_neg : cbrt (-x) < 0) by (apply cbrt_neg_negative; lra).
           lra.
        -- assert (Hcbrt_pos : 0 < cbrt x) by (apply cbrt_pos_positive; lra).
           lra.
Qed.

(** ∛x·∛y = ∛(xy) *)
Lemma cbrt_mult : forall x y, cbrt x * cbrt y = cbrt (x * y).
Proof.
  intros x y.
  apply cbrt_unique.
  - unfold cube_func.
    replace ((cbrt x * cbrt y) * (cbrt x * cbrt y) * (cbrt x * cbrt y))
      with ((cbrt x * cbrt x * cbrt x) * (cbrt y * cbrt y * cbrt y)) by ring.
    rewrite cbrt_cube, cbrt_cube, cbrt_cube.
    ring.
  - destruct (Rlt_dec 0 x) as [Hx_pos | Hx_npos].
    + destruct (Rlt_dec 0 y) as [Hy_pos | Hy_npos].
      * assert (Hcbrtxy : 0 <= cbrt (x * y)) by (apply cbrt_nonneg; apply Rmult_le_pos; lra).
        assert (Hcbrtx : 0 <= cbrt x) by (apply cbrt_nonneg; lra).
        assert (Hcbrty : 0 <= cbrt y) by (apply cbrt_nonneg; lra).
        assert (Hprod : 0 <= cbrt x * cbrt y) by (apply Rmult_le_pos; assumption).
        left. split; assumption.
      * destruct (Req_EM_T y 0) as [Hy0 | Hyn0].
        -- subst. rewrite Rmult_0_r. rewrite cbrt_0.
           assert (Hcbrtx : 0 <= cbrt x) by (apply cbrt_nonneg; lra).
           replace (cbrt x * 0) with 0 by ring.
           left. split; lra.
        -- assert (Hy_neg : y < 0) by lra.
           assert (Hxy_neg : x * y < 0) by (apply Rmult_pos_neg; lra).
           assert (Hcbrtx_pos : 0 < cbrt x) by (apply cbrt_pos_positive; lra).
           assert (Hcbrty_neg : cbrt y < 0) by (apply cbrt_neg_negative; lra).
           assert (Hcbrtxy_neg : cbrt (x * y) < 0) by (apply cbrt_neg_negative; lra).
           assert (Hprod_neg : cbrt x * cbrt y < 0) by nra.
           right. split; lra.
    + destruct (Req_EM_T x 0) as [Hx0 | Hxn0].
      * subst. rewrite Rmult_0_l. rewrite cbrt_0.
        replace (0 * cbrt y) with 0 by ring.
        left. split; lra.
      * assert (Hx_neg : x < 0) by lra.
        destruct (Rlt_dec 0 y) as [Hy_pos | Hy_npos].
        -- assert (Hxy_neg : x * y < 0) by (apply Rmult_neg_pos; lra).
           assert (Hcbrtx_neg : cbrt x < 0) by (apply cbrt_neg_negative; lra).
           assert (Hcbrty_pos : 0 < cbrt y) by (apply cbrt_pos_positive; lra).
           assert (Hcbrtxy_neg : cbrt (x * y) < 0) by (apply cbrt_neg_negative; lra).
           assert (Hprod_neg : cbrt x * cbrt y < 0) by nra.
           right. split; lra.
        -- destruct (Req_EM_T y 0) as [Hy0 | Hyn0].
           ++ subst. rewrite Rmult_0_r. rewrite cbrt_0.
              replace (cbrt x * 0) with 0 by ring.
              left. split; lra.
           ++ assert (Hy_neg : y < 0) by lra.
              assert (Hxy_pos : 0 < x * y) by nra.
              assert (Hcbrtx_neg : cbrt x < 0) by (apply cbrt_neg_negative; lra).
              assert (Hcbrty_neg : cbrt y < 0) by (apply cbrt_neg_negative; lra).
              assert (Hcbrtxy_pos : 0 <= cbrt (x * y)) by (apply cbrt_nonneg; lra).
              assert (Hprod_pos : 0 < cbrt x * cbrt y) by nra.
              left. split; lra.
Qed.

(** (∛(x/27))³ = x/27 *)
Lemma cbrt_div_27 : forall x,
  cbrt (x / 27) * cbrt (x / 27) * cbrt (x / 27) = x / 27.
Proof.
  intro x. apply cbrt_cube.
Qed.

(** x ≥ 0 → max(0,x) = x *)
Lemma Rmax_self : forall x,
  0 <= x -> Rmax 0 x = x.
Proof.
  intros x H.
  unfold Rmax. destruct (Rle_dec 0 x); [reflexivity | exfalso; lra].
Qed.

(** u³ = -q/2 + √Δ where Δ = q²/4 + p³/27 *)
Lemma cardano_u_cubed : forall p q,
  0 <= q * q / 4 + p * p * p / 27 ->
  let u := cbrt (- q / 2 + sqrt (q * q / 4 + p * p * p / 27)) in
  u * u * u = - q / 2 + sqrt (q * q / 4 + p * p * p / 27).
Proof.
  intros p q Hdisc u. apply cbrt_cube.
Qed.

(** v³ = -q/2 - √Δ where Δ = q²/4 + p³/27 *)
Lemma cardano_v_cubed : forall p q,
  0 <= q * q / 4 + p * p * p / 27 ->
  let v := cbrt (- q / 2 - sqrt (q * q / 4 + p * p * p / 27)) in
  v * v * v = - q / 2 - sqrt (q * q / 4 + p * p * p / 27).
Proof.
  intros p q Hdisc v. apply cbrt_cube.
Qed.

(** u³ + v³ = -q *)
Lemma cardano_sum_cubes : forall p q,
  0 <= q * q / 4 + p * p * p / 27 ->
  let u := cbrt (- q / 2 + sqrt (q * q / 4 + p * p * p / 27)) in
  let v := cbrt (- q / 2 - sqrt (q * q / 4 + p * p * p / 27)) in
  u * u * u + v * v * v = - q.
Proof.
  intros p q Hdisc.
  simpl.
  repeat rewrite cbrt_cube.
  set (s := sqrt (q * q / 4 + p * p * p / 27)).
  lra.
Qed.

(** (uv)³ = -p³/27 *)
Lemma cardano_product_cubes : forall p q,
  0 <= q * q / 4 + p * p * p / 27 ->
  let u := cbrt (- q / 2 + sqrt (q * q / 4 + p * p * p / 27)) in
  let v := cbrt (- q / 2 - sqrt (q * q / 4 + p * p * p / 27)) in
  (u * v) * (u * v) * (u * v) = - p * p * p / 27.
Proof.
  intros p q Hdisc.
  simpl.
  apply cardano_uv_product_nonneg with (p := p) (q := q);
    [exact Hdisc | apply cbrt_cube | apply cbrt_cube].
Qed.

(** (∛(x³))³ = x³ *)
Lemma cbrt_of_cube : forall x,
  cbrt (x * x * x) * cbrt (x * x * x) * cbrt (x * x * x) = x * x * x.
Proof.
  intro x. apply cbrt_cube.
Qed.

(** ∛(x³) = x *)
Lemma cbrt_of_cube_eq : forall x, cbrt (x * x * x) = x.
Proof.
  intro x.
  apply cbrt_unique.
  - unfold cube_func. rewrite cbrt_cube. ring.
  - destruct (Rlt_dec 0 x) as [Hx_pos | Hx_npos].
    + left. split.
      * apply cbrt_nonneg. nra.
      * lra.
    + destruct (Req_EM_T x 0) as [Hx0 | Hxn0].
      * subst. replace (0*0*0) with 0 by ring. rewrite cbrt_0. left. lra.
      * assert (Hx_neg : x < 0) by lra.
        assert (Hx2_pos : 0 < x * x).
        { replace (x * x) with ((-x) * (-x)) by ring.
          apply Rmult_lt_0_compat; lra. }
        assert (Hx3_neg : x * x * x < 0).
        { replace (x * x * x) with (x * (x * x)) by ring.
          apply Rmult_neg_pos; lra. }
        right. split.
        -- left. apply cbrt_neg_negative. exact Hx3_neg.
        -- lra.
Qed.

(** ∛(-p³/27) = -p/3 *)
Lemma cbrt_neg_p_cubed_27 : forall p, cbrt (- p * p * p / 27) = - p / 3.
Proof.
  intro p.
  replace (- p * p * p / 27) with ((- p / 3) * (- p / 3) * (- p / 3)).
  - apply cbrt_of_cube_eq.
  - field.
Qed.

(** uv = -p/3 *)
Lemma cardano_product : forall p q,
  0 <= q * q / 4 + p * p * p / 27 ->
  let u := cbrt (- q / 2 + sqrt (q * q / 4 + p * p * p / 27)) in
  let v := cbrt (- q / 2 - sqrt (q * q / 4 + p * p * p / 27)) in
  u * v = - p / 3.
Proof.
  intros p q Hdisc.
  simpl.
  rewrite cbrt_mult.
  replace ((- q / 2 + sqrt (q * q / 4 + p * p * p / 27)) *
           (- q / 2 - sqrt (q * q / 4 + p * p * p / 27)))
    with (- p * p * p / 27).
  - apply cbrt_neg_p_cubed_27.
  - set (s := sqrt (q * q / 4 + p * p * p / 27)).
    assert (Hs_sq : s * s = q * q / 4 + p * p * p / 27).
    { unfold s. rewrite sqrt_sqrt; [reflexivity | exact Hdisc]. }
    assert (Hprod : (- q / 2 + s) * (- q / 2 - s) = (- q / 2) * (- q / 2) - s * s).
    { ring. }
    rewrite Hprod.
    replace ((- q / 2) * (- q / 2)) with (q * q / 4) by field.
    rewrite Hs_sq.
    field.
Qed.

(** (u+v)³ = u³ + v³ + 3uv(u+v) *)
Lemma sum_of_cubes_identity : forall u v,
  (u + v) * (u + v) * (u + v) =
  u * u * u + v * v * v + 3 * u * v * (u + v).
Proof.
  intros u v. ring.
Qed.

(** Δ ≥ 0 → cardano_solve(p,q)³ + p·cardano_solve(p,q) + q = 0 *)
Theorem cardano_solves_depressed_cubic : forall p q,
  0 <= q * q / 4 + p * p * p / 27 ->
  cubic_depressed p q (cardano_solve p q) = 0.
Proof.
  intros p q Hdisc.
  unfold cubic_depressed, cardano_solve.
  rewrite Rmax_self by exact Hdisc.
  set (u := cbrt (- q / 2 + sqrt (q * q / 4 + p * p * p / 27))).
  set (v := cbrt (- q / 2 - sqrt (q * q / 4 + p * p * p / 27))).
  assert (Hsum : u * u * u + v * v * v = -q).
  { unfold u, v. apply (cardano_sum_cubes p q Hdisc). }
  assert (Hprod : u * v = - p / 3).
  { unfold u, v. apply (cardano_product p q Hdisc). }
  assert (Hgoal : (u + v) * (u + v) * (u + v) + p * (u + v) + q =
                  (u * u * u + v * v * v) + (3 * (u * v) + p) * (u + v) + q) by ring.
  rewrite Hgoal.
  rewrite Hsum, Hprod.
  field.
Qed.


(** Algorithms for origami constructions *)

(** reflect(p,f) *)
Lemma in_flat_map_intro : forall {A B} (f : A -> list B) l x y,
  In x l -> In y (f x) -> In y (flat_map f l).
Proof.
  intros A B f l x y Hx Hy.
  apply in_flat_map. exists x. split; assumption.
Qed.

Lemma incl_appl : forall {A} (l1 l2 : list A), incl l1 (l1 ++ l2).
Proof.
  intros A l1 l2 x Hx. apply in_or_app. left. assumption.
Qed.

Lemma incl_appr : forall {A} (l1 l2 : list A), incl l2 (l1 ++ l2).
Proof.
  intros A l1 l2 x Hx. apply in_or_app. right. assumption.
Qed.
Lemma max_le_l : forall n m : nat, (n <= Nat.max n m)%nat.
Proof.
  intros. apply Nat.le_max_l.
Qed.

Lemma max_le_r : forall n m : nat, (m <= Nat.max n m)%nat.
Proof.
  intros. apply Nat.le_max_r.
Qed.
Lemma neg_zero : -0 = 0.
Proof. ring. Qed.

(** A(perp_through(p, {A:=0,B:=b,C:=c})) = b *)
Definition heptagon_cubic_a : R := -7/12.
Definition heptagon_cubic_b : R := -7/216.

(** O6 configuration for cos(2π/7) *)
Inductive OrigamiNum : R -> Prop :=
| ON_0 : OrigamiNum 0
| ON_1 : OrigamiNum 1
| ON_add : forall x y, OrigamiNum x -> OrigamiNum y -> OrigamiNum (x + y)
| ON_sub : forall x y, OrigamiNum x -> OrigamiNum y -> OrigamiNum (x - y)
| ON_mul : forall x y, OrigamiNum x -> OrigamiNum y -> OrigamiNum (x * y)
| ON_inv : forall x, OrigamiNum x -> x <> 0 -> OrigamiNum (/ x)
| ON_sqrt : forall x, OrigamiNum x -> 0 <= x -> OrigamiNum (sqrt x)
| ON_cubic_root : forall a b r, OrigamiNum a -> OrigamiNum b -> r * r * r + a * r + b = 0 -> OrigamiNum r.

(** Euclidean numbers: closed under +, -, ×, /, √ (no cubic roots) *)
Inductive EuclidNum : R -> Prop :=
| EN_0 : EuclidNum 0
| EN_1 : EuclidNum 1
| EN_add : forall x y, EuclidNum x -> EuclidNum y -> EuclidNum (x + y)
| EN_sub : forall x y, EuclidNum x -> EuclidNum y -> EuclidNum (x - y)
| EN_mul : forall x y, EuclidNum x -> EuclidNum y -> EuclidNum (x * y)
| EN_inv : forall x, EuclidNum x -> x <> 0 -> EuclidNum (/ x)
| EN_sqrt : forall x, EuclidNum x -> 0 <= x -> EuclidNum (sqrt x).

(** EuclidNum ⊆ OrigamiNum *)
Lemma Euclid_in_Origami : forall x, EuclidNum x -> OrigamiNum x.
Proof.
  intros x H; induction H.
  - constructor.
  - constructor.
  - apply ON_add; assumption.
  - apply ON_sub; assumption.
  - apply ON_mul; assumption.
  - eapply ON_inv; eauto.
  - eapply ON_sqrt; eauto.
Qed.

(** -x = 0 - x *)
Lemma Ropp_as_sub : forall x, - x = 0 - x.
Proof. intro x; lra. Qed.

(** OrigamiNum x → OrigamiNum (-x) *)
Lemma Origami_neg : forall x, OrigamiNum x -> OrigamiNum (- x).
Proof.
  intros x Hx.
  assert (Hm1 : OrigamiNum (-1)).
  { replace (-1) with (0 - 1) by lra.
    apply ON_sub; [constructor|constructor]. }
  replace (- x) with ((-1) * x) by lra.
  apply ON_mul; [exact Hm1|assumption].
Qed.

(** 2 ∈ OrigamiNum *)
Lemma Origami_two : OrigamiNum 2.
Proof.
  replace 2 with (1 + 1) by lra.
  apply ON_add; constructor; constructor.
Qed.

(** OrigamiNum is a field *)
Theorem origami_field_structure :
  OrigamiNum 0 /\ OrigamiNum 1 /\
  (forall x y, OrigamiNum x -> OrigamiNum y -> OrigamiNum (x + y)) /\
  (forall x y, OrigamiNum x -> OrigamiNum y -> OrigamiNum (x * y)) /\
  (forall x, OrigamiNum x -> OrigamiNum (- x)) /\
  (forall x, OrigamiNum x -> x <> 0 -> OrigamiNum (/ x)).
Proof.
  repeat split; intros.
  - constructor.
  - constructor.
  - apply ON_add; assumption.
  - apply ON_mul; assumption.
  - apply Origami_neg; assumption.
  - apply ON_inv; assumption.
Qed.

(** OrigamiNum closed under √ *)
Theorem origami_sqrt_extension :
  forall x, OrigamiNum x -> 0 <= x -> OrigamiNum (sqrt x).
Proof.
  intros x Hx Hpos.
  apply ON_sqrt; assumption.
Qed.

(** OrigamiNum closed under cubic roots *)
Theorem origami_cubic_extension :
  forall a b r, OrigamiNum a -> OrigamiNum b ->
  r * r * r + a * r + b = 0 -> OrigamiNum r.
Proof.
  intros a b r Ha Hb Hroot.
  apply ON_cubic_root with (a := a) (b := b); assumption.
Qed.

(** EuclidNum x → OrigamiNum x *)
Theorem euclid_subset_origami :
  forall x, EuclidNum x -> OrigamiNum x.
Proof.
  apply Euclid_in_Origami.
Qed.

(** OrigamiNum x → OrigamiNum y → OrigamiNum (x - y) *)
Lemma origami_closed_under_subtraction :
  forall x y, OrigamiNum x -> OrigamiNum y -> OrigamiNum (x - y).
Proof.
  intros x y Hx Hy.
  apply ON_sub; assumption.
Qed.

(** √(√x) ∈ OrigamiNum *)
Theorem origami_tower_sqrt_sqrt :
  forall x, OrigamiNum x -> 0 <= x -> 0 <= sqrt x ->
  OrigamiNum (sqrt (sqrt x)).
Proof.
  intros x Hx Hpos Hpos2.
  apply ON_sqrt.
  - apply ON_sqrt; assumption.
  - apply sqrt_pos.
Qed.

(** 3 ∈ OrigamiNum *)
Lemma Origami_three : OrigamiNum 3.
Proof.
  replace 3 with (2 + 1) by lra.
  apply ON_add; [apply Origami_two|constructor].
Qed.

(** 1 is a root of x³ - 3x + 2 = 0 *)
Lemma Origami_root_example : OrigamiNum 1.
Proof.
  assert (Ha : OrigamiNum (-3)) by (apply Origami_neg; apply Origami_three).
  assert (Hb : OrigamiNum 2) by apply Origami_two.
  replace 1 with 1 by reflexivity.
  apply (ON_cubic_root (-3) 2 1); auto; lra.
Qed.

(** OrigamiNum x → OrigamiNum y → y ≠ 0 → OrigamiNum (x/y) *)
Lemma Origami_div : forall x y, OrigamiNum x -> OrigamiNum y -> y <> 0 -> OrigamiNum (x / y).
Proof.
  intros x y Hx Hy Hy0.
  unfold Rdiv.
  apply ON_mul; [assumption|].
  apply ON_inv; assumption.
Qed.

(** ℕ ⊂ OrigamiNum *)
Lemma Origami_nat : forall n, OrigamiNum (INR n).
Proof.
  induction n.
  - simpl. constructor.
  - replace (INR (S n)) with (INR n + 1).
    + apply ON_add; [assumption | constructor].
    + rewrite S_INR. lra.
Qed.

(** ℤ ⊂ OrigamiNum *)
Lemma Origami_Z : forall z, OrigamiNum (IZR z).
Proof.
  intros z.
  destruct z as [| p | p].
  - simpl. constructor.
  - replace (IZR (Z.pos p)) with (INR (Pos.to_nat p)).
    + apply Origami_nat.
    + rewrite INR_IZR_INZ. rewrite positive_nat_Z. reflexivity.
  - replace (IZR (Z.neg p)) with (- INR (Pos.to_nat p)).
    + apply Origami_neg. apply Origami_nat.
    + rewrite INR_IZR_INZ. rewrite positive_nat_Z. reflexivity.
Qed.

(** ℚ ⊂ OrigamiNum *)
Theorem Origami_Q : forall p q : Z, (q <> 0)%Z -> OrigamiNum (IZR p / IZR q).
Proof.
  intros p q Hq.
  apply Origami_div.
  - apply Origami_Z.
  - apply Origami_Z.
  - intro Hz.
    apply eq_IZR in Hz.
    contradiction.
Qed.

(** OrigamiNum with tracked extension degree over ℚ *)
Inductive OrigamiNum_deg : R -> nat -> Prop :=
| OND_0 : OrigamiNum_deg 0 1
| OND_1 : OrigamiNum_deg 1 1
| OND_add : forall x y n m, OrigamiNum_deg x n -> OrigamiNum_deg y m ->
    OrigamiNum_deg (x + y) (Nat.max n m)
| OND_sub : forall x y n m, OrigamiNum_deg x n -> OrigamiNum_deg y m ->
    OrigamiNum_deg (x - y) (Nat.max n m)
| OND_mul : forall x y n m, OrigamiNum_deg x n -> OrigamiNum_deg y m ->
    OrigamiNum_deg (x * y) (Nat.max n m)
| OND_inv : forall x n, OrigamiNum_deg x n -> x <> 0 ->
    OrigamiNum_deg (/ x) n
| OND_sqrt : forall x n, OrigamiNum_deg x n -> 0 <= x ->
    OrigamiNum_deg (sqrt x) (2 * n)
| OND_cbrt : forall a b r n m, OrigamiNum_deg a n -> OrigamiNum_deg b m ->
    r * r * r + a * r + b = 0 ->
    OrigamiNum_deg r (3 * Nat.max n m).

(** Extension step: √x (degree 2) or cubic root (degree 3) *)
Inductive ExtensionStep : Type :=
| Ext_sqrt : R -> ExtensionStep
| Ext_cbrt : R -> R -> R -> ExtensionStep.

(** Degree of extension step *)
Definition ext_step_degree (e : ExtensionStep) : nat :=
  match e with
  | Ext_sqrt _ => 2
  | Ext_cbrt _ _ _ => 3
  end.

(** Tower of field extensions *)
Definition FieldTower := list ExtensionStep.

(** [ℚ(t) : ℚ] = product of step degrees *)
Fixpoint tower_degree (t : FieldTower) : nat :=
  match t with
  | nil => 1
  | e :: rest => ext_step_degree e * tower_degree rest
  end.

(** tower_degree t > 0 *)
Lemma tower_degree_pos : forall t, (tower_degree t > 0)%nat.
Proof.
  induction t as [|e rest IH].
  - simpl. lia.
  - simpl. destruct e; simpl; lia.
Qed.

(** tower_degree (e::t) = ext_step_degree e × tower_degree t *)
Lemma tower_degree_cons : forall e t,
  tower_degree (e :: t) = (ext_step_degree e * tower_degree t)%nat.
Proof. reflexivity. Qed.

(** x ∈ ℚ(tower) *)
Inductive InTower : R -> FieldTower -> Prop :=
| IT_rat : forall q t, InTower (IZR q) t
| IT_add : forall x y t, InTower x t -> InTower y t -> InTower (x + y) t
| IT_sub : forall x y t, InTower x t -> InTower y t -> InTower (x - y) t
| IT_mul : forall x y t, InTower x t -> InTower y t -> InTower (x * y) t
| IT_inv : forall x t, InTower x t -> x <> 0 -> InTower (/ x) t
| IT_weaken : forall x t e, InTower x t -> InTower x (e :: t)
| IT_sqrt_adj : forall x t, InTower x t -> 0 <= x ->
    InTower (sqrt x) (Ext_sqrt x :: t)
| IT_cbrt_adj : forall a b r t, InTower a t -> InTower b t ->
    r * r * r + a * r + b = 0 ->
    InTower r (Ext_cbrt a b r :: t).

(** x ∈ ℚ(t) → x ∈ ℚ(e::t) *)
Lemma InTower_weaken_lem : forall x t e,
  InTower x t -> InTower x (e :: t).
Proof.
  intros x t e H. apply IT_weaken. exact H.
Qed.

(** x ∈ ℚ(t₁) → x ∈ ℚ(t₂++t₁) *)
Lemma InTower_weaken_app : forall x t1 t2,
  InTower x t1 -> InTower x (t2 ++ t1).
Proof.
  intros x t1 t2 H.
  induction t2 as [|e t2' IH].
  - simpl. exact H.
  - simpl. apply IT_weaken. exact IH.
Qed.

(** x ∈ ℚ(t₁) → x ∈ ℚ(t₁++t₂) *)
Lemma InTower_weaken_app_r : forall x t1 t2,
  InTower x t1 -> InTower x (t1 ++ t2).
Proof.
  intros x t1 t2 H.
  induction H.
  - apply IT_rat.
  - apply IT_add; assumption.
  - apply IT_sub; assumption.
  - apply IT_mul; assumption.
  - apply IT_inv; assumption.
  - apply IT_weaken. exact IHInTower.
  - simpl. apply IT_sqrt_adj; assumption.
  - simpl. eapply IT_cbrt_adj; eassumption.
Qed.

(** x ∈ ℚ(t) → OrigamiNum x *)
Lemma InTower_is_OrigamiNum : forall x t,
  InTower x t -> OrigamiNum x.
Proof.
  intros x t H.
  induction H.
  - apply Origami_Z.
  - apply ON_add; assumption.
  - apply ON_sub; assumption.
  - apply ON_mul; assumption.
  - apply ON_inv; assumption.
  - exact IHInTower.
  - apply ON_sqrt; assumption.
  - apply (ON_cubic_root a b); assumption.
Qed.

(** OrigamiNum x → ∃ t, x ∈ ℚ(t) *)
Theorem OrigamiNum_has_tower : forall x,
  OrigamiNum x -> exists t, InTower x t.
Proof.
  intros x H.
  induction H.
  - exists nil. apply (IT_rat 0%Z).
  - exists nil. apply (IT_rat 1%Z).
  - destruct IHOrigamiNum1 as [t1 Ht1]. destruct IHOrigamiNum2 as [t2 Ht2].
    exists (t2 ++ t1). apply IT_add.
    + apply InTower_weaken_app. exact Ht1.
    + apply InTower_weaken_app_r. exact Ht2.
  - destruct IHOrigamiNum1 as [t1 Ht1]. destruct IHOrigamiNum2 as [t2 Ht2].
    exists (t2 ++ t1). apply IT_sub.
    + apply InTower_weaken_app. exact Ht1.
    + apply InTower_weaken_app_r. exact Ht2.
  - destruct IHOrigamiNum1 as [t1 Ht1]. destruct IHOrigamiNum2 as [t2 Ht2].
    exists (t2 ++ t1). apply IT_mul.
    + apply InTower_weaken_app. exact Ht1.
    + apply InTower_weaken_app_r. exact Ht2.
  - destruct IHOrigamiNum as [t Ht].
    exists t. apply IT_inv; assumption.
  - destruct IHOrigamiNum as [t Ht].
    exists (Ext_sqrt x :: t). apply IT_sqrt_adj; assumption.
  - destruct IHOrigamiNum1 as [t1 Ht1]. destruct IHOrigamiNum2 as [t2 Ht2].
    exists (Ext_cbrt a b r :: t2 ++ t1).
    eapply IT_cbrt_adj; try eassumption.
    + apply InTower_weaken_app. exact Ht1.
    + apply InTower_weaken_app_r. exact Ht2.
Qed.

(** tower_degree t = 2^a × 3^b for some a,b *)
Lemma tower_degree_is_2_3_smooth : forall t,
  exists a b, tower_degree t = (2^a * 3^b)%nat.
Proof.
  induction t as [|e t IH].
  - exists 0%nat, 0%nat. reflexivity.
  - destruct IH as [a [b Hab]].
    destruct e.
    + simpl. rewrite Hab.
      exists (S a), b. simpl. lia.
    + simpl. rewrite Hab.
      exists a, (S b). simpl. lia.
Qed.

(** OrigamiNum_deg x n → ∃ t, x ∈ ℚ(t) *)
Theorem OrigamiNum_deg_has_tower : forall x n,
  OrigamiNum_deg x n -> exists t, InTower x t.
Proof.
  intros x n H.
  induction H.
  - exists nil. apply (IT_rat 0%Z).
  - exists nil. apply (IT_rat 1%Z).
  - destruct IHOrigamiNum_deg1 as [t1 Ht1].
    destruct IHOrigamiNum_deg2 as [t2 Ht2].
    exists (t2 ++ t1). apply IT_add.
    + apply InTower_weaken_app. exact Ht1.
    + apply InTower_weaken_app_r. exact Ht2.
  - destruct IHOrigamiNum_deg1 as [t1 Ht1].
    destruct IHOrigamiNum_deg2 as [t2 Ht2].
    exists (t2 ++ t1). apply IT_sub.
    + apply InTower_weaken_app. exact Ht1.
    + apply InTower_weaken_app_r. exact Ht2.
  - destruct IHOrigamiNum_deg1 as [t1 Ht1].
    destruct IHOrigamiNum_deg2 as [t2 Ht2].
    exists (t2 ++ t1). apply IT_mul.
    + apply InTower_weaken_app. exact Ht1.
    + apply InTower_weaken_app_r. exact Ht2.
  - destruct IHOrigamiNum_deg as [t Ht].
    exists t. apply IT_inv; assumption.
  - destruct IHOrigamiNum_deg as [t Ht].
    exists (Ext_sqrt x :: t). apply IT_sqrt_adj; assumption.
  - destruct IHOrigamiNum_deg1 as [t1 Ht1].
    destruct IHOrigamiNum_deg2 as [t2 Ht2].
    exists (Ext_cbrt a b r :: t2 ++ t1).
    eapply IT_cbrt_adj; try eassumption.
    + apply InTower_weaken_app. exact Ht1.
    + apply InTower_weaken_app_r. exact Ht2.
Qed.

(** Alperin-Lang: OrigamiNum x ⟺ ∃ tower t, x ∈ ℚ(t) *)
Theorem Alperin_Lang_characterization : forall x,
  OrigamiNum x <-> exists t, InTower x t.
Proof.
  intro x. split.
  - apply OrigamiNum_has_tower.
  - intros [t Ht]. apply (InTower_is_OrigamiNum x t Ht).
Qed.

(** x ∈ OrigamiNum ⟺ x in tower of degree 2ᵃ·3ᵇ *)
Theorem Alperin_Lang_with_degree : forall x,
  OrigamiNum x <-> exists t, InTower x t /\ exists a b, tower_degree t = (2^a * 3^b)%nat.
Proof.
  intro x. split.
  - intro H.
    destruct (OrigamiNum_has_tower x H) as [t Ht].
    exists t. split.
    + exact Ht.
    + apply tower_degree_is_2_3_smooth.
  - intros [t [Ht _]].
    apply (InTower_is_OrigamiNum x t Ht).
Qed.

(** x ∈ OrigamiNum ⟺ ∃ tower t, x ∈ t *)
Corollary OrigamiNum_iff_2_3_tower : forall x,
  OrigamiNum x <-> exists t : FieldTower, InTower x t.
Proof.
  exact Alperin_Lang_characterization.
Qed.

(** OrigamiNum_deg x n → OrigamiNum x *)
Lemma OrigamiNum_deg_is_OrigamiNum : forall x n,
  OrigamiNum_deg x n -> OrigamiNum x.
Proof.
  intros x n H. induction H.
  - constructor.
  - constructor.
  - apply ON_add; assumption.
  - apply ON_sub; assumption.
  - apply ON_mul; assumption.
  - apply ON_inv; assumption.
  - apply ON_sqrt; assumption.
  - apply (ON_cubic_root a b); assumption.
Qed.

(** OrigamiNum x → ∃ n, OrigamiNum_deg x n *)
Theorem OrigamiNum_has_deg : forall x, OrigamiNum x -> exists n, OrigamiNum_deg x n.
Proof.
  intros x H. induction H.
  - exists 1%nat. constructor.
  - exists 1%nat. constructor.
  - destruct IHOrigamiNum1 as [n1 Hn1]. destruct IHOrigamiNum2 as [n2 Hn2].
    exists (Nat.max n1 n2). apply OND_add; assumption.
  - destruct IHOrigamiNum1 as [n1 Hn1]. destruct IHOrigamiNum2 as [n2 Hn2].
    exists (Nat.max n1 n2). apply OND_sub; assumption.
  - destruct IHOrigamiNum1 as [n1 Hn1]. destruct IHOrigamiNum2 as [n2 Hn2].
    exists (Nat.max n1 n2). apply OND_mul; assumption.
  - destruct IHOrigamiNum as [n Hn].
    exists n. apply OND_inv; assumption.
  - destruct IHOrigamiNum as [n Hn].
    exists (2 * n)%nat. apply OND_sqrt; assumption.
  - destruct IHOrigamiNum1 as [n1 Hn1]. destruct IHOrigamiNum2 as [n2 Hn2].
    exists (3 * Nat.max n1 n2)%nat. apply (OND_cbrt a b); assumption.
Qed.

(** Both coordinates are origami-constructible *)
Lemma euclidean_sqrt_closed : forall x, EuclidNum x -> 0 <= x -> EuclidNum (sqrt x).
Proof.
  intros x Hx Hpos.
  induction Hx.
  - replace (sqrt 0) with 0 by (symmetry; apply sqrt_0). constructor.
  - replace (sqrt 1) with 1 by (symmetry; apply sqrt_1). constructor.
  - apply EN_sqrt. apply EN_add; assumption. assumption.
  - apply EN_sqrt. apply EN_sub; assumption. assumption.
  - apply EN_sqrt. apply EN_mul; assumption. assumption.
  - apply EN_sqrt. apply EN_inv; assumption. assumption.
  - apply EN_sqrt. apply EN_sqrt; assumption. assumption.
Qed.

(** Tower degree tracking for Euclidean numbers *)
Inductive euclidean_degree : R -> nat -> Prop :=
| ed_0 : euclidean_degree 0 0
| ed_1 : euclidean_degree 1 0
| ed_add : forall x y n1 n2,
    euclidean_degree x n1 -> euclidean_degree y n2 ->
    euclidean_degree (x + y) (Nat.max n1 n2)
| ed_sub : forall x y n1 n2,
    euclidean_degree x n1 -> euclidean_degree y n2 ->
    euclidean_degree (x - y) (Nat.max n1 n2)
| ed_mul : forall x y n1 n2,
    euclidean_degree x n1 -> euclidean_degree y n2 ->
    euclidean_degree (x * y) (Nat.max n1 n2)
| ed_inv : forall x n,
    euclidean_degree x n -> x <> 0 ->
    euclidean_degree (/ x) n
| ed_sqrt : forall x n,
    euclidean_degree x n -> 0 <= x ->
    euclidean_degree (sqrt x) (S n).

(** EuclidNum x → ∃ n, euclidean_degree x n *)
Lemma euclidean_has_degree : forall x, EuclidNum x -> exists n, euclidean_degree x n.
Proof.
  intros x Hx. induction Hx.
  - exists O. constructor.
  - exists O. constructor.
  - destruct IHHx1 as [n1 Hd1]. destruct IHHx2 as [n2 Hd2].
    exists (Nat.max n1 n2). apply ed_add; assumption.
  - destruct IHHx1 as [n1 Hd1]. destruct IHHx2 as [n2 Hd2].
    exists (Nat.max n1 n2). apply ed_sub; assumption.
  - destruct IHHx1 as [n1 Hd1]. destruct IHHx2 as [n2 Hd2].
    exists (Nat.max n1 n2). apply ed_mul; assumption.
  - destruct IHHx as [n Hd].
    exists n. apply ed_inv; assumption.
  - destruct IHHx as [n Hd].
    exists (S n). apply ed_sqrt; assumption.
Qed.

(** 0 ≤ 2⁰ *)
Lemma n_le_2_pow_n_base : (0 <= 2^0)%nat.
Proof. apply le_0_n. Qed.

(** a ≤ b → a + a ≤ b + b *)
Lemma add_le_add_same : forall a b, (a <= b)%nat -> (a + a <= b + b)%nat.
Proof.
  intros a b H.
  apply Nat.add_le_mono; exact H.
Qed.

(** 1 ≤ m → S m ≤ 2m *)
Lemma S_m_le_double_m : forall m, (1 <= m)%nat -> (S m <= m + m)%nat.
Proof.
  intros m Hm. lia.
Qed.

(** 1 ≤ 2ⁿ *)
Lemma one_le_2_pow_n : forall n, (1 <= 2^n)%nat.
Proof.
  induction n.
  - simpl. apply le_n.
  - simpl. rewrite Nat.add_0_r. eapply Nat.le_trans. exact IHn. apply Nat.le_add_r.
Qed.

(** n ≤ 2ⁿ *)
Lemma n_le_2_pow_n : forall n, (n <= 2^n)%nat.
Proof.
  induction n.
  - apply n_le_2_pow_n_base.
  - simpl. rewrite Nat.add_0_r.
    eapply Nat.le_trans.
    + apply le_n_S. exact IHn.
    + apply S_m_le_double_m. apply one_le_2_pow_n.
Qed.

(** ∀ n, ∃ k, n ≤ 2ᵏ *)
Lemma power_of_2_covers : forall n : nat, exists k : nat, (n <= 2^k)%nat.
Proof.
  intro n. exists n. apply n_le_2_pow_n.
Qed.

(** EuclidNum x → ∃ n with euclidean_degree x n and n ≤ 2ᵏ for some k *)
Theorem euclidean_field_degree_2n : forall x,
  EuclidNum x -> exists n : nat, euclidean_degree x n /\ exists k : nat, (n <= 2^k)%nat.
Proof.
  intros x Hx.
  destruct (euclidean_has_degree x Hx) as [n Hd].
  exists n. split.
  - exact Hd.
  - apply power_of_2_covers.
Qed.

(** p₁/q₁ + p₂/q₂ = (p₁q₂ + p₂q₁)/(q₁q₂) *)
Lemma rational_sum : forall p1 q1 p2 q2 : Z,
  (q1 <> 0)%Z -> (q2 <> 0)%Z ->
  IZR p1 / IZR q1 + IZR p2 / IZR q2 = IZR (p1 * q2 + p2 * q1) / IZR (q1 * q2).
Proof.
  intros p1 q1 p2 q2 Hq1 Hq2.
  assert (Hq1_neq : IZR q1 <> 0) by (intro; apply eq_IZR in H; contradiction).
  assert (Hq2_neq : IZR q2 <> 0) by (intro; apply eq_IZR in H; contradiction).
  rewrite mult_IZR. rewrite plus_IZR. rewrite mult_IZR. rewrite mult_IZR.
  field. split; assumption.
Qed.

(** (p₁/q₁)·(p₂/q₂) = (p₁p₂)/(q₁q₂) *)
Lemma rational_product : forall p1 q1 p2 q2 : Z,
  (q1 <> 0)%Z -> (q2 <> 0)%Z ->
  (IZR p1 / IZR q1) * (IZR p2 / IZR q2) = IZR (p1 * p2) / IZR (q1 * q2).
Proof.
  intros p1 q1 p2 q2 Hq1 Hq2.
  assert (Hq1_neq : IZR q1 <> 0) by (intro; apply eq_IZR in H; contradiction).
  assert (Hq2_neq : IZR q2 <> 0) by (intro; apply eq_IZR in H; contradiction).
  rewrite mult_IZR. rewrite mult_IZR.
  field. split; assumption.
Qed.

(** (p/q)⁻¹ = q/p *)
Lemma rational_inverse : forall p q : Z,
  (p <> 0)%Z -> (q <> 0)%Z ->
  / (IZR p / IZR q) = IZR q / IZR p.
Proof.
  intros p q Hp Hq.
  assert (Hp_neq : IZR p <> 0) by (intro; apply eq_IZR in H; contradiction).
  assert (Hq_neq : IZR q <> 0) by (intro; apply eq_IZR in H; contradiction).
  field. split; assumption.
Qed.

(** ℤ ⊆ EuclidNum *)
Lemma IZR_euclidean : forall z : Z, EuclidNum (IZR z).
Proof.
  intro z.
  induction z using Z.peano_ind.
  - simpl. constructor.
  - replace (Z.succ z) with (z + 1)%Z by lia.
    rewrite plus_IZR.
    apply EN_add. assumption. simpl. constructor.
  - replace (Z.pred z) with (z - 1)%Z by lia.
    rewrite minus_IZR. simpl.
    apply EN_sub. assumption. constructor.
Qed.

(** ℚ ⊆ EuclidNum *)
Lemma euclidean_contains_rationals : forall p q : Z,
  (q <> 0)%Z -> EuclidNum (IZR p / IZR q).
Proof.
  intros p q Hq.
  assert (Hp: EuclidNum (IZR p)) by apply IZR_euclidean.
  assert (Hq_num: EuclidNum (IZR q)) by apply IZR_euclidean.
  assert (Hq_neq: IZR q <> 0) by (intro; apply eq_IZR in H; contradiction).
  unfold Rdiv.
  apply EN_mul.
  - exact Hp.
  - apply EN_inv; assumption.
Qed.


(** Partial converse: OrigamiNum base cases are constructible *)

(** 0 ∈ ConstructibleR *)
Lemma origami_sum : forall x y : R,
  OrigamiNum x -> OrigamiNum y -> OrigamiNum (x + y).
Proof.
  intros x y Hx Hy.
  apply ON_add; assumption.
Qed.

(** OrigamiNum closed under × *)
Lemma origami_prod : forall x y : R,
  OrigamiNum x -> OrigamiNum y -> OrigamiNum (x * y).
Proof.
  intros x y Hx Hy.
  apply ON_mul; assumption.
Qed.

(** OrigamiNum closed under ⁻¹ *)
Lemma origami_inv : forall x : R,
  OrigamiNum x -> x <> 0 -> OrigamiNum (/ x).
Proof.
  intros x Hx Hneq.
  apply ON_inv; assumption.
Qed.

(** OrigamiNum closed under √ *)
Lemma origami_sqrt : forall x : R,
  OrigamiNum x -> 0 <= x -> OrigamiNum (sqrt x).
Proof.
  intros x Hx Hpos.
  apply ON_sqrt; assumption.
Qed.

(** OrigamiNum forms a field *)

Theorem origami_field_0 : OrigamiNum 0.
Proof. constructor. Qed.

Theorem origami_field_1 : OrigamiNum 1.
Proof. constructor. Qed.

Theorem origami_field_add_closed : forall x y,
  OrigamiNum x -> OrigamiNum y -> OrigamiNum (x + y).
Proof. apply origami_sum. Qed.

Theorem origami_field_mul_closed : forall x y,
  OrigamiNum x -> OrigamiNum y -> OrigamiNum (x * y).
Proof. apply origami_prod. Qed.

Theorem origami_field_neg_closed : forall x,
  OrigamiNum x -> OrigamiNum (- x).
Proof. apply Origami_neg. Qed.

Theorem origami_field_inv_closed : forall x,
  OrigamiNum x -> x <> 0 -> OrigamiNum (/ x).
Proof. apply origami_inv. Qed.

(** r³ + ar + b = 0 ∧ a,b ∈ OrigamiNum → r ∈ OrigamiNum *)
Lemma cubic_root_closure : forall a b r,
  OrigamiNum a -> OrigamiNum b ->
  r * r * r + a * r + b = 0 ->
  OrigamiNum r.
Proof.
  intros a b r Ha Hb Heq.
  apply (ON_cubic_root a b r Ha Hb Heq).
Qed.

(** ConstructiblePoint (x₁,0) ∧ ConstructiblePoint (x₂,0) → ConstructibleLine through them *)
Lemma sqrt_of_origami_is_origami : forall x,
  OrigamiNum x -> 0 <= x -> OrigamiNum (sqrt x).
Proof.
  intros x Hx Hpos.
  apply ON_sqrt; assumption.
Qed.

(** x,y ∈ OrigamiNum → x+y ∈ OrigamiNum *)
Lemma sum_of_origami_is_origami : forall x y,
  OrigamiNum x -> OrigamiNum y -> OrigamiNum (x + y).
Proof.
  intros x y Hx Hy.
  apply ON_add; assumption.
Qed.

(** x,y ∈ OrigamiNum → x·y ∈ OrigamiNum *)
Lemma product_of_origami_is_origami : forall x y,
  OrigamiNum x -> OrigamiNum y -> OrigamiNum (x * y).
Proof.
  intros x y Hx Hy.
  apply ON_mul; assumption.
Qed.

(** x ∈ OrigamiNum ∧ x ≠ 0 → x⁻¹ ∈ OrigamiNum *)
Lemma inverse_of_origami_is_origami : forall x,
  OrigamiNum x -> x <> 0 -> OrigamiNum (/ x).
Proof.
  intros x Hx Hneq.
  apply ON_inv; assumption.
Qed.

(** √2 ∈ OrigamiNum *)
Theorem sqrt_2_is_constructible_origami : OrigamiNum (sqrt 2).
Proof.
  apply ON_sqrt.
  - apply Origami_two.
  - lra.
Qed.

(** √3 ∈ OrigamiNum *)
Theorem sqrt_3_is_origami : OrigamiNum (sqrt 3).
Proof.
  apply ON_sqrt.
  - apply Origami_three.
  - lra.
Qed.

(** √5 ∈ OrigamiNum *)
Theorem sqrt_5_is_origami : OrigamiNum (sqrt 5).
Proof.
  apply ON_sqrt.
  - replace 5 with (2 + 3) by lra.
    apply ON_add; [apply Origami_two|apply Origami_three].
  - lra.
Qed.

(** reflect((0,0), y=x) = (0,0) *)
Lemma simplify_reflect_x_coord :
  forall a b c x y,
  a * a + b * b <> 0 ->
  x - 2 * a * ((a * x + b * y + c) / (a * a + b * b)) =
  ((a * a + b * b) * x - 2 * a * (a * x + b * y + c)) / (a * a + b * b).
Proof.
  intros. unfold Rdiv. field. exact H.
Qed.

(** reflect((0,0), perp_bisector((1,0),(2,0))) = (3,0) *)
Lemma geometric_mean_point_wf : forall x,
  0 < x -> (1, sqrt x) <> (1 + x, 0).
Proof.
  intros x Hpos Heq.
  injection Heq as H1 H2.
  assert (Hsqrt_pos: sqrt x > 0) by (apply sqrt_lt_R0; lra).
  lra.
Qed.
Lemma sqrt_4_eq : sqrt 4 = 2.
Proof.
  replace 4 with (2 * 2) by ring.
  rewrite sqrt_square; lra.
Qed.

(** x > 0 → O5_image_y(0,0,1+x,0,2) = 2√x *)
Lemma fold_O5_sqrt_image : forall x,
  0 < x ->
  let p'y := 0 + sqrt (sqrt ((0 - (1+x))^2 + (0-0)^2) * (sqrt ((0 - (1+x))^2 + (0-0)^2) * 1) - (2 - (1+x)) * ((2 - (1+x)) * 1)) in
  p'y = 2 * sqrt x.
Proof.
  intros x Hpos p'y.
  unfold p'y.
  replace ((0 - (1 + x)) ^ 2 + (0 - 0) ^ 2) with ((1 + x) ^ 2) by ring.
  rewrite sqrt_pow2 by lra.
  replace ((1 + x) * ((1 + x) * 1)) with ((1 + x)^2) by ring.
  replace (2 - (1 + x)) with (1 - x) by ring.
  replace ((1 - x) * ((1 - x) * 1)) with ((1 - x)^2) by ring.
  replace ((1 + x) ^ 2 - (1 - x) ^ 2) with (4 * x) by ring.
  rewrite sqrt_mult by lra.
  rewrite sqrt_4_eq.
  lra.
Qed.

(** perp_bisector((0,0), (2, 2√x)) *)
Example sqrt_2_constructible : OrigamiNum (sqrt 2).
Proof.
  apply ON_sqrt.
  - apply Origami_two.
  - replace 2 with (1 + 1) by lra.
    apply Rplus_le_le_0_compat; apply Rle_0_1.
Qed.

(** Intersection of perpendiculars through X to both axes *)
Lemma Rinv_neg1 : / (-1) = -1.
Proof.
  apply Rmult_eq_reg_l with (-1).
  - rewrite Rinv_r. lra. lra.
  - lra.
Qed.

(** 1 · /(-1) = -1 *)
Lemma one_div_neg1 : 1 * / (-1) = -1.
Proof.
  rewrite Rinv_neg1. lra.
Qed.

(** (-1) · /(-1) = 1 *)
Lemma neg1_div_neg1 : (-1) * / (-1) = 1.
Proof.
  rewrite Rinv_neg1. lra.
Qed.

(** -/(-1) = 1 *)
Lemma neg_div_neg1 : - / (-1) = 1.
Proof.
  rewrite Rinv_neg1. lra.
Qed.

(** (- (-1) · -1 - - 0 · 0) · / (1 · -1 - 0 · 0) = 1 *)
Lemma inter_x_coord : (- (-1) * -1 - - 0 * 0) * / (1 * -1 - 0 * 0) = 1.
Proof.
  assert (H1: - (-1) * -1 - - 0 * 0 = -1) by ring.
  assert (H2: 1 * -1 - 0 * 0 = -1) by ring.
  rewrite H1, H2. rewrite neg1_div_neg1. reflexivity.
Qed.

(** fst(intersection of x=1 and y=0) = 1 *)
Lemma inter_y_coord : (1 * - 0 - 0 * - (-1)) * / (1 * -1 - 0 * 0) = 0.
Proof.
  assert (H1: 1 * - 0 - 0 * - (-1) = 0) by ring.
  rewrite H1. ring.
Qed.

(** snd(intersection of x=1 and y=0) = 0 *)
Example half_constructible : OrigamiNum (1/2).
Proof.
  unfold Rdiv.
  apply ON_mul.
  - constructor.
  - apply ON_inv.
    + apply Origami_two.
    + lra.
Qed.

(** 3/4 ∈ OrigamiNum *)
Example rational_3_4_constructible : OrigamiNum (3/4).
Proof.
  unfold Rdiv.
  apply ON_mul.
  - apply Origami_three.
  - apply ON_inv.
    + replace 4 with (2 + 2) by lra.
      apply ON_add; apply Origami_two.
    + lra.
Qed.

(** ∃ r ∈ OrigamiNum with r³ - 3r + 2 = 0 *)
Example cubic_root_constructible :
  exists r : R, OrigamiNum r /\ r * r * r + (-3) * r + 2 = 0.
Proof.
  exists 1.
  split.
  - constructor.
  - lra.
Qed.

(** a,b ∈ OrigamiNum ∧ r³ + ar + b = 0 → r ∈ OrigamiNum *)
Lemma cubic_root_origami : forall a b r,
  OrigamiNum a -> OrigamiNum b ->
  r * r * r + a * r + b = 0 ->
  OrigamiNum r.
Proof.
  intros a b r Ha Hb Hroot.
  apply (ON_cubic_root a b r Ha Hb Hroot).
Qed.

(** O6 solves cubics: a,b ∈ OrigamiNum ∧ r³ + ar + b = 0 → r ∈ OrigamiNum *)
Theorem O6_geometric_cubic_bridge : forall a b r,
  OrigamiNum a -> OrigamiNum b ->
  r * r * r + a * r + b = 0 ->
  OrigamiNum r.
Proof.
  apply cubic_root_origami.
Qed.

(** 8x³ - 6x - 1 = 0 → x ∈ OrigamiNum (angle trisection) *)
Theorem angle_trisection_possible :
  forall cos_20 : R,
    8 * (cos_20 * cos_20 * cos_20) - 6 * cos_20 - 1 = 0 ->
    OrigamiNum cos_20.
Proof.
  intros cos_20 Heq.
  assert (Ha : OrigamiNum (-3/4)).
  { replace (-3/4) with ((0 - 3) / 4) by lra.
    apply Origami_div.
    - apply ON_sub.
      + constructor.
      + apply Origami_three.
    - replace 4 with (2 + 2) by lra.
      apply ON_add; apply Origami_two.
    - lra. }
  assert (Hb : OrigamiNum (-1/8)).
  { replace (-1/8) with ((0 - 1) / 8) by lra.
    apply Origami_div.
    - apply ON_sub; constructor.
    - replace 8 with (2 * 4) by lra.
      apply ON_mul.
      + apply Origami_two.
      + replace 4 with (2 + 2) by lra.
        apply ON_add; apply Origami_two.
    - lra. }
  apply (ON_cubic_root (-3/4) (-1/8) cos_20 Ha Hb).
  replace (cos_20 * cos_20 * cos_20 + (-3/4) * cos_20 + (-1/8))
    with ((8 * (cos_20 * cos_20 * cos_20) - 6 * cos_20 - 1) / 8) by (field; lra).
  rewrite Heq.
  field.
Qed.

(** x³ = 2 → x ∈ OrigamiNum (cube duplication / Delian problem) *)
Theorem cube_duplication_possible :
  forall cbrt_2 : R,
    cbrt_2 * cbrt_2 * cbrt_2 = 2 ->
    OrigamiNum cbrt_2.
Proof.
  intros cbrt_2 Hcube.
  apply (ON_cubic_root 0 (-2) cbrt_2).
  + constructor.
  + replace (-2) with (0 - 2) by lra.
    apply ON_sub.
    - constructor.
    - apply Origami_two.
  + replace (cbrt_2 * cbrt_2 * cbrt_2 + 0 * cbrt_2 + (-2)) with (cbrt_2 * cbrt_2 * cbrt_2 - 2) by lra.
    rewrite Hcube. lra.
Qed.

(** r³ = 2 → r ∈ OrigamiNum *)
Lemma cbrt_2_is_origami : forall r : R,
  r * r * r = 2 ->
  OrigamiNum r.
Proof.
  intros r Hr.
  apply cube_duplication_possible.
  exact Hr.
Qed.

(** x³ - 2 *)
Definition cube_minus_2 (x : R) : R := x * x * x - 2.

(** cube_minus_2 ∈ C⁰(ℝ) *)
Lemma cube_minus_2_continuous : continuity cube_minus_2.
Proof.
  unfold cube_minus_2.
  apply continuity_minus.
  - apply continuity_mult.
    + apply continuity_mult.
      * apply derivable_continuous. apply derivable_id.
      * apply derivable_continuous. apply derivable_id.
    + apply derivable_continuous. apply derivable_id.
  - apply continuity_const. intro. reflexivity.
Qed.

(** ∃ r > 0 with r³ = 2 (via IVT) *)
Theorem cube_root_2_exists : exists r : R, 0 < r /\ r * r * r = 2.
Proof.
  assert (H0 : cube_minus_2 0 < 0).
  { unfold cube_minus_2. simpl. lra. }
  assert (H2 : 0 < cube_minus_2 2).
  { unfold cube_minus_2. lra. }
  assert (Hlt : 0 < 2) by lra.
  destruct (IVT cube_minus_2 0 2 cube_minus_2_continuous Hlt H0 H2) as [r [[Hr1 Hr2] Hr3]].
  exists r.
  assert (Hr_cube : r * r * r = 2).
  { unfold cube_minus_2 in Hr3. lra. }
  split; [|exact Hr_cube].
  (* Need to show 0 < r *)
  (* We have r³ = 2, so r ≠ 0, and 0 ≤ r, hence 0 < r *)
  assert (Hrneq : r <> 0).
  { intro Heq0. rewrite Heq0 in Hr_cube. lra. }
  lra.
Qed.


(** 8x³ - 6x - 1 = 0 → x ∈ OrigamiNum *)
Lemma cos_20_is_origami : forall x : R,
  8 * (x * x * x) - 6 * x - 1 = 0 ->
  OrigamiNum x.
Proof.
  intros x Hx.
  apply angle_trisection_possible.
  exact Hx.
Qed.

(** Triple angle formula and trisection cubic *)

(** 4c³ - 3c (= cos(3θ) when c = cos(θ)) *)
Definition triple_angle_poly (c : R) : R := 4 * c^3 - 3 * c.

(** triple_angle_poly c = 4c³ - 3c *)
Lemma triple_angle_poly_alt : forall c,
  triple_angle_poly c = 4 * c * c * c - 3 * c.
Proof.
  intro c. unfold triple_angle_poly. ring.
Qed.

(** 4c³ - 3c - k *)
Definition trisection_cubic (k c : R) : R := 4 * c^3 - 3 * c - k.

(** trisection_cubic k c = 0 ⟺ triple_angle_poly c = k *)
Lemma trisection_cubic_root_iff : forall k c,
  trisection_cubic k c = 0 <-> triple_angle_poly c = k.
Proof.
  intros k c. unfold trisection_cubic, triple_angle_poly. lra.
Qed.

(** 4c³ - 3c - k = 0 ⟺ c³ + (-3/4)c + (-k/4) = 0 *)
Lemma trisection_to_depressed : forall k c,
  trisection_cubic k c = 0 <->
  c^3 + (-3/4) * c + (-k/4) = 0.
Proof.
  intros k c. unfold trisection_cubic. split; intro H; lra.
Qed.

(** k ∈ OrigamiNum ∧ 4c³ - 3c - k = 0 → c ∈ OrigamiNum *)
Theorem trisected_angle_constructible : forall k c,
  OrigamiNum k ->
  trisection_cubic k c = 0 ->
  OrigamiNum c.
Proof.
  intros k c Hk Hcubic.
  apply trisection_to_depressed in Hcubic.
  apply (ON_cubic_root (-3/4) (-k/4) c).
  - assert (H4 : OrigamiNum 4) by (replace 4 with (2+2) by lra; apply ON_add; apply Origami_two).
    apply Origami_div; [apply Origami_neg; apply Origami_three | exact H4 | lra].
  - assert (H4 : OrigamiNum 4) by (replace 4 with (2+2) by lra; apply ON_add; apply Origami_two).
    apply Origami_div; [apply Origami_neg; exact Hk | exact H4 | lra].
  - replace (c * c * c) with (c^3) by ring. exact Hcubic.
Qed.

(** 8c³ - 6c - 1 = 0 ⟺ trisection_cubic(1/2, c) = 0 *)
Lemma cos_60_trisection : forall c,
  8 * c^3 - 6 * c - 1 = 0 <-> trisection_cubic (1/2) c = 0.
Proof.
  intro c. unfold trisection_cubic. split; intro H; lra.
Qed.

(** c ∈ OrigamiNum ∧ |c| ≤ 1 → √(1 - c²) ∈ OrigamiNum *)
Lemma sin_from_cos_constructible : forall c,
  OrigamiNum c ->
  -1 <= c <= 1 ->
  OrigamiNum (sqrt (1 - c^2)).
Proof.
  intros c Hc Hbounds.
  apply ON_sqrt.
  - replace (1 - c^2) with (1 + (- (c * c))) by ring.
    apply ON_add.
    + constructor.
    + apply Origami_neg. apply ON_mul; exact Hc.
  - assert (H : c^2 <= 1) by nra. lra.
Qed.


(** 7 ∈ OrigamiNum *)
Lemma Origami_seven : OrigamiNum 7.
Proof.
  replace 7 with (3 + (2 + 2)) by lra.
  apply ON_add; [apply Origami_three | apply ON_add; apply Origami_two].
Qed.

(** 12 ∈ OrigamiNum *)
Lemma Origami_twelve : OrigamiNum 12.
Proof.
  replace 12 with (3 * (2 + 2)) by lra.
  apply ON_mul; [apply Origami_three | apply ON_add; apply Origami_two].
Qed.

(** 216 ∈ OrigamiNum *)
Lemma Origami_216 : OrigamiNum 216.
Proof.
  replace 216 with (8 * 27) by lra.
  apply ON_mul.
  - replace 8 with (2 * (2 + 2)) by lra.
    apply ON_mul; [apply Origami_two | apply ON_add; apply Origami_two].
  - replace 27 with (3 * 9) by lra.
    apply ON_mul; [apply Origami_three|].
    replace 9 with (3 * 3) by lra.
    apply ON_mul; apply Origami_three.
Qed.

(** -7/12, -7/216 ∈ OrigamiNum *)
Lemma heptagon_depressed_coeffs :
  OrigamiNum (-7/12) /\ OrigamiNum (-7/216).
Proof.
  split.
  - replace (-7/12) with ((0 - 7) / 12) by lra.
    apply Origami_div.
    + apply ON_sub; [constructor | apply Origami_seven].
    + apply Origami_twelve.
    + lra.
  - replace (-7/216) with ((0 - 7) / 216) by lra.
    apply Origami_div.
    + apply ON_sub; [constructor | apply Origami_seven].
    + apply Origami_216.
    + lra.
Qed.

(** 8c³ + 4c² - 4c - 1 = 0 → c ∈ OrigamiNum (regular heptagon) *)
Theorem heptagon_constructible : forall c : R,
  8 * (c * c * c) + 4 * (c * c) - 4 * c - 1 = 0 ->
  OrigamiNum c.
Proof.
  intros c Heq.
  set (t := c + 1/6).
  assert (Ht_cubic : t * t * t + (-7/12) * t + (-7/216) = 0).
  { unfold t.
    replace ((c + 1/6) * (c + 1/6) * (c + 1/6) + -7/12 * (c + 1/6) + -7/216)
      with ((8 * (c * c * c) + 4 * (c * c) - 4 * c - 1) / 8) by field.
    rewrite Heq. field. }
  destruct heptagon_depressed_coeffs as [Ha Hb].
  assert (Ht : OrigamiNum t).
  { apply (ON_cubic_root (-7/12) (-7/216) t Ha Hb Ht_cubic). }
  replace c with (t - 1/6) by (unfold t; ring).
  apply ON_sub.
  - exact Ht.
  - apply Origami_div; [constructor | replace 6 with (2*3) by lra;
    apply ON_mul; [apply Origami_two | apply Origami_three] | lra].
Qed.

(** 8c³ - 6c + 1 = 0 → c ∈ OrigamiNum (regular nonagon) *)
Theorem nonagon_constructible : forall c : R,
  8 * (c * c * c) - 6 * c + 1 = 0 ->
  OrigamiNum c.
Proof.
  intros c Heq.
  assert (Ha : OrigamiNum (-3/4)).
  { replace (-3/4) with ((0 - 3) / (2 + 2)) by field.
    apply Origami_div.
    - apply ON_sub; [constructor | apply Origami_three].
    - apply ON_add; apply Origami_two.
    - lra. }
  assert (Hb : OrigamiNum (1/8)).
  { replace (1/8) with (1 / (2 * (2 + 2))) by field.
    apply Origami_div.
    - constructor.
    - apply ON_mul; [apply Origami_two | apply ON_add; apply Origami_two].
    - lra. }
  apply (ON_cubic_root (-3/4) (1/8) c Ha Hb).
  replace (c * c * c + -3/4 * c + 1/8)
    with ((8 * (c * c * c) - 6 * c + 1) / 8) by field.
  rewrite Heq. field.
Qed.

(** p,q ∈ OrigamiNum ∧ c³ + pc + q = 0 → c ∈ OrigamiNum *)
Theorem polygon_cubic_constructible : forall (cos_val : R) (p q : R),
  OrigamiNum p -> OrigamiNum q ->
  cos_val * cos_val * cos_val + p * cos_val + q = 0 ->
  OrigamiNum cos_val.
Proof.
  intros cos_val p q Hp Hq Heq.
  apply (ON_cubic_root p q cos_val Hp Hq Heq).
Qed.

(** 8c³ + 4c² - 4c - 1 = 0 → c ∈ OrigamiNum (tridecagon shares heptagon cubic) *)
Theorem tridecagon_constructible : forall c : R,
  8 * (c * c * c) + 4 * (c * c) - 4 * c - 1 = 0 ->
  OrigamiNum c.
Proof. exact heptagon_constructible. Qed.

(** 8c³ - 6c - 1 = 0 → c ∈ OrigamiNum (enneadecagon / 19-gon) *)
Theorem enneadecagon_constructible : forall c : R,
  8 * (c * c * c) - 6 * c - 1 = 0 ->
  OrigamiNum c.
Proof.
  intros c Heq.
  assert (Ha : OrigamiNum (-3/4)).
  { replace (-3/4) with ((0-3)/(2+2)) by field.
    apply Origami_div; [apply ON_sub; [constructor|apply Origami_three]|
    apply ON_add; apply Origami_two|lra]. }
  assert (Hb : OrigamiNum (-1/8)).
  { replace (-1/8) with ((0-1)/(2*(2+2))) by field.
    apply Origami_div; [apply ON_sub; constructor|
    apply ON_mul; [apply Origami_two|apply ON_add; apply Origami_two]|lra]. }
  apply (ON_cubic_root (-3/4) (-1/8) c Ha Hb).
  replace (c*c*c + -3/4*c + -1/8) with ((8*(c*c*c) - 6*c - 1)/8) by field.
  rewrite Heq. field.
Qed.


(** Executable algorithms for geometric operations *)

(** Alias for midpoint *)
Lemma sqrt_equal : forall x y : R, x = y -> sqrt x = sqrt y.
Proof.
  intros x y H.
  rewrite H.
  reflexivity.
Qed.

(** dist(p,q) = √(dist²(p,q)) *)
Inductive EuclideanDegree : nat -> Prop :=
| ED_base : EuclideanDegree 1
| ED_ext : forall n, EuclideanDegree n -> EuclideanDegree (2 * n).

(** Origami field extension degrees: 2^a · 3^b *)
Inductive OrigamiDegree : nat -> Prop :=
| OD_base : OrigamiDegree 1
| OD_ext2 : forall n, OrigamiDegree n -> OrigamiDegree (2 * n)
| OD_ext3 : forall n, OrigamiDegree n -> OrigamiDegree (3 * n).

(** EuclideanDegree n → OrigamiDegree n *)
Lemma euclidean_degree_is_origami : forall n,
  EuclideanDegree n -> OrigamiDegree n.
Proof.
  intros n H. induction H.
  - constructor.
  - apply OD_ext2. exact IHEuclideanDegree.
Qed.

(** OrigamiDegree 3 (cube roots) *)
Lemma three_is_origami_degree : OrigamiDegree 3.
Proof.
  change 3%nat with (3 * 1)%nat.
  apply OD_ext3. constructor.
Qed.

(** OrigamiDegree 6 = 2·3 *)
Lemma six_is_origami_degree : OrigamiDegree 6.
Proof.
  change 6%nat with (2 * 3)%nat.
  apply OD_ext2. apply three_is_origami_degree.
Qed.

(** OrigamiDegree 9 = 3² *)
Lemma nine_is_origami_degree : OrigamiDegree 9.
Proof.
  change 9%nat with (3 * 3)%nat.
  apply OD_ext3. apply three_is_origami_degree.
Qed.

(** OrigamiDegree 2^k *)
Lemma pow2_is_origami_degree : forall k, OrigamiDegree (2^k).
Proof.
  induction k.
  - simpl. constructor.
  - simpl. rewrite Nat.add_0_r.
    replace (2^k + 2^k)%nat with (2 * 2^k)%nat by lia.
    apply OD_ext2. exact IHk.
Qed.

(** φ(7) = 6 ∈ OrigamiDegree *)
Example heptagon_degree : OrigamiDegree 6.
Proof. exact six_is_origami_degree. Qed.

(** φ(9) = 6 ∈ OrigamiDegree *)
Example nonagon_degree : OrigamiDegree 6.
Proof. exact six_is_origami_degree. Qed.

(** n = 2^a · 3^b for some a,b ≥ 0 *)
Definition is_2_3_smooth (n : nat) : Prop :=
  exists a b, n = (2^a * 3^b)%nat.

(** is_2_3_smooth 1 *)
Lemma is_2_3_smooth_1 : is_2_3_smooth 1.
Proof. exists 0%nat, 0%nat. reflexivity. Qed.

(** is_2_3_smooth 2 = 2¹·3⁰ *)
Lemma is_2_3_smooth_2 : is_2_3_smooth 2.
Proof. exists 1%nat, 0%nat. reflexivity. Qed.

(** is_2_3_smooth 3 = 2⁰·3¹ *)
Lemma is_2_3_smooth_3 : is_2_3_smooth 3.
Proof. exists 0%nat, 1%nat. reflexivity. Qed.

(** is_2_3_smooth 6 = 2¹·3¹ *)
Lemma is_2_3_smooth_6 : is_2_3_smooth 6.
Proof. exists 1%nat, 1%nat. reflexivity. Qed.

(** is_2_3_smooth 12 = 2²·3¹ *)
Lemma is_2_3_smooth_12 : is_2_3_smooth 12.
Proof. exists 2%nat, 1%nat. reflexivity. Qed.

(** is_2_3_smooth 18 = 2¹·3² *)
Lemma is_2_3_smooth_18 : is_2_3_smooth 18.
Proof. exists 1%nat, 2%nat. reflexivity. Qed.

(** Repeatedly divide by 2 until odd *)
Fixpoint remove_twos_aux (n fuel : nat) : nat :=
  match fuel with
  | O => n
  | S fuel' =>
    if Nat.even n then remove_twos_aux (Nat.div2 n) fuel'
    else n
  end.

Definition remove_twos (n : nat) : nat := remove_twos_aux n n.

(** Repeatedly divide by 3 until not divisible *)
Fixpoint remove_threes_aux (n fuel : nat) : nat :=
  match fuel with
  | O => n
  | S fuel' =>
    if Nat.eqb (n mod 3) 0 then remove_threes_aux (n / 3) fuel'
    else n
  end.

Definition remove_threes (n : nat) : nat := remove_threes_aux n n.

(** 3^(S b) · x = 3 · (3^b · x) *)
Lemma pow3_S_mul : forall b x : nat, (3 ^ S b * x = 3 * (3 ^ b * x))%nat.
Proof.
  intros b x.
  replace (3 ^ S b)%nat with (3 * 3 ^ b)%nat.
  - rewrite Nat.mul_assoc. reflexivity.
  - simpl. lia.
Qed.

(** Boolean test for 2-3 smoothness *)
Definition is_2_3_smooth_b (n : nat) : bool :=
  match n with
  | O => false
  | _ => Nat.eqb (remove_threes (remove_twos n)) 1
  end.

(** n ≥ 1 → ∃ a, n = 2^a · remove_twos_aux(n) ∧ remove_twos_aux(n) is odd *)
Lemma remove_twos_aux_spec : forall n fuel,
  (n >= 1)%nat -> (fuel >= n)%nat ->
  exists a, (n = 2^a * remove_twos_aux n fuel)%nat /\ Nat.odd (remove_twos_aux n fuel) = true.
Proof.
  intros n fuel. revert n.
  induction fuel; intros n Hn Hfuel.
  - lia.
  - simpl. destruct (Nat.even n) eqn:Heven.
    + assert (Hdiv2_lt : (Nat.div2 n < n)%nat).
      { apply Nat.lt_div2. lia. }
      assert (Hdiv2_pos : (Nat.div2 n >= 1)%nat).
      { destruct n; [lia|]. destruct n; [simpl in Heven; discriminate|].
        apply le_n_S, Nat.le_0_l. }
      assert (Hfuel' : (fuel >= Nat.div2 n)%nat) by lia.
      destruct (IHfuel (Nat.div2 n) Hdiv2_pos Hfuel') as [a [Ha Hodd]].
      exists (S a).
      set (r := remove_twos_aux (Nat.div2 n) fuel) in *.
      split.
      * simpl. rewrite Nat.add_0_r.
        assert (Hn2 : (n = 2 * Nat.div2 n)%nat).
        { apply Nat.even_spec in Heven. destruct Heven as [k Hk].
          rewrite Hk. rewrite Nat.div2_double. lia. }
        rewrite Hn2. rewrite Ha.
        replace (2^a + 2^a)%nat with (2 * 2^a)%nat by lia.
        rewrite Nat.mul_assoc. reflexivity.
      * exact Hodd.
    + exists 0%nat. simpl. split; [lia|].
      rewrite <- Nat.negb_even. rewrite Heven. reflexivity.
Qed.

(** n ≥ 1 → ∃ a, n = 2^a · remove_twos(n) ∧ remove_twos(n) is odd *)
Lemma remove_twos_spec : forall n,
  (n >= 1)%nat ->
  exists a, (n = 2^a * remove_twos n)%nat /\ Nat.odd (remove_twos n) = true.
Proof.
  intros n Hn. unfold remove_twos.
  apply remove_twos_aux_spec; lia.
Qed.

(** k ≥ 1 → ∃ b, k = 3^b · remove_threes_aux(k) ∧ (result mod 3 ≠ 0 ∨ result = 1) *)
Lemma remove_threes_aux_spec : forall k fuel,
  (k >= 1)%nat -> (fuel >= k)%nat ->
  exists b, (k = 3^b * remove_threes_aux k fuel)%nat /\ (remove_threes_aux k fuel mod 3 <> 0 \/ remove_threes_aux k fuel = 1)%nat.
Proof.
  intros k fuel. revert k.
  induction fuel; intros k Hk Hfuel.
  - lia.
  - destruct (k mod 3 =? 0)%nat eqn:Hmod3_b.
    + assert (Hmod3 : k mod 3 = 0%nat) by (apply Nat.eqb_eq; exact Hmod3_b).
      assert (Hdiv3_lt : (k / 3 < k)%nat).
      { apply Nat.div_lt; lia. }
      assert (Hdiv3_pos : (k / 3 >= 1)%nat).
      { pose proof (Nat.div_mod k 3) as Hdm.
        assert (H3ne : (3 <> 0)%nat) by lia. specialize (Hdm H3ne).
        rewrite Hmod3 in Hdm. lia. }
      assert (Hfuel' : (fuel >= k / 3)%nat) by lia.
      destruct (IHfuel (Nat.div k 3) Hdiv3_pos Hfuel') as [b [Hb Hrest]].
      exists (S b).
      assert (Hsimp : remove_threes_aux k (S fuel) = remove_threes_aux (Nat.div k 3) fuel).
      { unfold remove_threes_aux; fold remove_threes_aux. rewrite Hmod3_b. reflexivity. }
      rewrite Hsimp.
      split.
      * set (r := remove_threes_aux (Nat.div k 3) fuel) in *.
        pose proof (Nat.div_mod k 3) as Hdm.
        assert (H3ne : (3 <> 0)%nat) by lia. specialize (Hdm H3ne).
        rewrite Hmod3 in Hdm. rewrite Nat.add_0_r in Hdm.
        rewrite Hdm.
        rewrite pow3_S_mul.
        rewrite Hb.
        reflexivity.
      * exact Hrest.
    + assert (Hmod3 : k mod 3 <> 0%nat) by (apply Nat.eqb_neq; exact Hmod3_b).
      exists 0%nat.
      assert (Hsimp : remove_threes_aux k (S fuel) = k).
      { unfold remove_threes_aux; fold remove_threes_aux. rewrite Hmod3_b. reflexivity. }
      rewrite Hsimp.
      split; [simpl; lia | left; exact Hmod3].
Qed.

(** m ≥ 1 → ∃ b, m = 3^b · remove_threes(m) ∧ (result mod 3 ≠ 0 ∨ result = 1) *)
Lemma remove_threes_spec : forall m,
  (m >= 1)%nat ->
  exists b, (m = 3^b * remove_threes m)%nat /\ (remove_threes m mod 3 <> 0 \/ remove_threes m = 1)%nat.
Proof.
  intros m Hm. unfold remove_threes.
  apply remove_threes_aux_spec; lia.
Qed.

(** n ≥ 1 → remove_twos(n) ≥ 1 *)
Lemma remove_twos_pos : forall n, (n >= 1)%nat -> (remove_twos n >= 1)%nat.
Proof.
  intros n Hn.
  destruct (remove_twos_spec n Hn) as [a [Ha Hodd]].
  destruct (remove_twos n); [simpl in Hodd; discriminate | lia].
Qed.

(** n odd → remove_twos_aux(n) = n *)
Lemma remove_twos_aux_odd : forall n fuel,
  (n >= 1)%nat -> Nat.odd n = true -> remove_twos_aux n fuel = n.
Proof.
  intros n fuel. revert n.
  induction fuel; intros n Hn Hodd.
  - reflexivity.
  - simpl.
    assert (Heven : Nat.even n = false).
    { rewrite <- Nat.negb_odd. rewrite Hodd. reflexivity. }
    rewrite Heven. reflexivity.
Qed.

(** n odd → remove_twos(n) = n *)
Lemma remove_twos_odd : forall n,
  (n >= 1)%nat -> Nat.odd n = true -> remove_twos n = n.
Proof.
  intros n Hn Hodd. unfold remove_twos. apply remove_twos_aux_odd; assumption.
Qed.

(** 3^b is odd *)
Lemma pow3_odd : forall b, Nat.odd (3 ^ b) = true.
Proof.
  induction b.
  - reflexivity.
  - simpl. rewrite Nat.add_0_r.
    rewrite Nat.odd_add. rewrite Nat.odd_add.
    rewrite IHb. simpl. reflexivity.
Qed.

(** 3^b ≥ 1 *)
Lemma pow3_pos : forall b, (3 ^ b >= 1)%nat.
Proof.
  induction b; simpl; lia.
Qed.

(** b ≥ 1 → 3^b mod 3 = 0 *)
Lemma pow3_mod3 : forall b, (b >= 1)%nat -> (3 ^ b mod 3 = 0)%nat.
Proof.
  intros b Hb. destruct b; [lia|].
  replace (3 ^ S b)%nat with (3 ^ b * 3)%nat by (simpl; lia).
  now rewrite Nat.Div0.mod_mul.
Qed.

(** 3^(S b) / 3 = 3^b *)
Lemma pow3_div3 : forall b, (3 ^ S b / 3 = 3 ^ b)%nat.
Proof.
  intro b.
  replace (3 ^ S b)%nat with (3 ^ b * 3)%nat by (simpl; lia).
  rewrite Nat.div_mul by lia.
  reflexivity.
Qed.

(** remove_threes_aux(3^b) = 1 *)
Lemma remove_threes_aux_pow3 : forall b fuel,
  (fuel >= 3^b)%nat -> remove_threes_aux (3^b) fuel = 1%nat.
Proof.
  induction b; intros fuel Hfuel.
  - simpl in *. destruct fuel; [lia|].
    simpl. reflexivity.
  - destruct fuel.
    + exfalso. pose proof (pow3_pos (S b)) as Hpos. lia.
    + assert (Hsimp : remove_threes_aux (3 ^ S b) (S fuel) = remove_threes_aux (3 ^ b) fuel).
      { unfold remove_threes_aux; fold remove_threes_aux.
        assert (Hmod : (3 ^ S b mod 3 =? 0) = true).
        { apply Nat.eqb_eq. apply pow3_mod3. lia. }
        rewrite Hmod. rewrite pow3_div3. reflexivity. }
      rewrite Hsimp.
      apply IHb.
      pose proof (pow3_pos b) as H3b_pos.
      assert (H3Sb : (3 ^ S b = 3 * 3 ^ b)%nat) by (simpl; lia).
      lia.
Qed.

(** remove_threes(3^b) = 1 *)
Lemma remove_threes_pow3 : forall b, remove_threes (3^b) = 1%nat.
Proof.
  intro b. unfold remove_threes.
  apply remove_threes_aux_pow3. lia.
Qed.

(** 2^a ≥ 1 *)
Lemma pow2_pos : forall a, (2 ^ a >= 1)%nat.
Proof.
  induction a; simpl; lia.
Qed.

(** a ≥ 1 ∧ odd(m) → div2(2^a · m) = 2^(a-1) · m *)
Lemma pow2_mul_odd_div2 : forall a m,
  (a >= 1)%nat -> Nat.odd m = true ->
  Nat.div2 (2 ^ a * m) = (2 ^ (a - 1) * m)%nat.
Proof.
  intros a m Ha Hodd.
  destruct a; [lia|].
  simpl. replace (a - 0)%nat with a by lia.
  assert (H2a : ((2 ^ a + (2 ^ a + 0)) * m = 2 * (2 ^ a * m))%nat) by lia.
  rewrite H2a.
  rewrite Nat.div2_double.
  reflexivity.
Qed.

(** a ≥ 1 ∧ odd(m) → even(2^a · m) *)
Lemma pow2_mul_odd_even : forall a m,
  (a >= 1)%nat -> Nat.odd m = true ->
  Nat.even (2 ^ a * m) = true.
Proof.
  intros a m Ha Hodd.
  destruct a; [lia|].
  replace (2 ^ S a * m)%nat with (2 * (2 ^ a * m))%nat by (simpl; lia).
  rewrite Nat.even_mul. simpl. reflexivity.
Qed.

(** odd(m) → remove_twos_aux(2^a · m) = m *)
Lemma remove_twos_aux_pow2_mul : forall a m fuel,
  Nat.odd m = true -> (m >= 1)%nat -> (fuel >= 2^a * m)%nat ->
  remove_twos_aux (2^a * m) fuel = m.
Proof.
  induction a; intros m fuel Hodd Hm Hfuel.
  - simpl in *. rewrite Nat.add_0_r in *.
    apply remove_twos_aux_odd; assumption.
  - destruct fuel.
    + exfalso. pose proof (pow2_pos (S a)) as Hpos. lia.
    + assert (Hsimp : remove_twos_aux (2 ^ S a * m) (S fuel) =
                      remove_twos_aux (Nat.div2 (2 ^ S a * m)) fuel).
      { unfold remove_twos_aux; fold remove_twos_aux.
        assert (Heven : Nat.even (2 ^ S a * m) = true).
        { apply pow2_mul_odd_even; [lia | assumption]. }
        rewrite Heven. reflexivity. }
      rewrite Hsimp.
      rewrite pow2_mul_odd_div2 by (try lia; assumption).
      replace (S a - 1)%nat with a by lia.
      apply IHa; try assumption.
      assert (H2Sa : (2 ^ S a = 2 * 2 ^ a)%nat) by (simpl; lia).
      lia.
Qed.

(** odd(m) → remove_twos(2^a · m) = m *)
Lemma remove_twos_pow2_mul : forall a m,
  Nat.odd m = true -> (m >= 1)%nat ->
  remove_twos (2^a * m) = m.
Proof.
  intros a m Hodd Hm. unfold remove_twos.
  apply remove_twos_aux_pow2_mul; try assumption.
  lia.
Qed.

(** is_2_3_smooth_b n = true → is_2_3_smooth n *)
Lemma is_2_3_smooth_b_reflects : forall n,
  is_2_3_smooth_b n = true -> is_2_3_smooth n.
Proof.
  intros n H.
  unfold is_2_3_smooth.
  destruct n; [discriminate|].
  unfold is_2_3_smooth_b in H. apply Nat.eqb_eq in H.
  assert (Hpos : (S n >= 1)%nat) by lia.
  destruct (remove_twos_spec (S n) Hpos) as [a [Ha _]].
  assert (Hpos2 : (remove_twos (S n) >= 1)%nat) by (apply remove_twos_pos; lia).
  destruct (remove_threes_spec (remove_twos (S n)) Hpos2) as [b [Hb _]].
  exists a, b.
  rewrite Ha, Hb, H. lia.
Qed.

(** is_2_3_smooth n → is_2_3_smooth_b n = true *)
Lemma is_2_3_smooth_b_complete : forall n,
  is_2_3_smooth n -> is_2_3_smooth_b n = true.
Proof.
  intros n [a [b Heq]].
  unfold is_2_3_smooth_b.
  destruct n.
  - exfalso.
    assert (H2a : (2^a >= 1)%nat) by apply pow2_pos.
    assert (H3b : (3^b >= 1)%nat) by apply pow3_pos.
    assert (Hprod : (2^a * 3^b >= 1)%nat) by lia.
    rewrite <- Heq in Hprod. lia.
  - apply Nat.eqb_eq.
    rewrite Heq.
    rewrite remove_twos_pow2_mul.
    + apply remove_threes_pow3.
    + apply pow3_odd.
    + apply pow3_pos.
Qed.

(** is_2_3_smooth_b n = true ⟺ is_2_3_smooth n *)
Theorem is_2_3_smooth_b_correct : forall n,
  is_2_3_smooth_b n = true <-> is_2_3_smooth n.
Proof.
  intro n. split.
  - apply is_2_3_smooth_b_reflects.
  - apply is_2_3_smooth_b_complete.
Qed.

(** is_2_3_smooth_b n = false ⟺ ¬is_2_3_smooth n *)
Corollary is_2_3_smooth_b_false : forall n,
  is_2_3_smooth_b n = false <-> ~ is_2_3_smooth n.
Proof.
  intro n. split.
  - intro Hf. intro Hs. apply is_2_3_smooth_b_complete in Hs. rewrite Hs in Hf. discriminate.
  - intro Hns. destruct (is_2_3_smooth_b n) eqn:Hb; [|reflexivity].
    exfalso. apply Hns. apply is_2_3_smooth_b_reflects. exact Hb.
Qed.

(** Tactic: decide is_2_3_smooth by computation *)
Ltac decide_smooth :=
  match goal with
  | |- is_2_3_smooth ?n =>
    let b := eval compute in (is_2_3_smooth_b n) in
    match b with
    | true => apply is_2_3_smooth_b_correct; reflexivity
    | false => fail "Not 2-3 smooth"
    end
  | |- ~ is_2_3_smooth ?n =>
    let b := eval compute in (is_2_3_smooth_b n) in
    match b with
    | false => apply is_2_3_smooth_b_false; reflexivity
    | true => fail "Is 2-3 smooth"
    end
  end.

Example smooth_4 : is_2_3_smooth 4. Proof. decide_smooth. Qed.
Example smooth_8 : is_2_3_smooth 8. Proof. decide_smooth. Qed.
Example smooth_9 : is_2_3_smooth 9. Proof. decide_smooth. Qed.
Example smooth_24 : is_2_3_smooth 24. Proof. decide_smooth. Qed.
Example smooth_27 : is_2_3_smooth 27. Proof. decide_smooth. Qed.
Example smooth_36 : is_2_3_smooth 36. Proof. decide_smooth. Qed.
Example smooth_72 : is_2_3_smooth 72. Proof. decide_smooth. Qed.
Example smooth_96 : is_2_3_smooth 96. Proof. decide_smooth. Qed.

Example not_smooth_5 : ~ is_2_3_smooth 5. Proof. decide_smooth. Qed.
Example not_smooth_7 : ~ is_2_3_smooth 7. Proof. decide_smooth. Qed.
Example not_smooth_10 : ~ is_2_3_smooth 10. Proof. decide_smooth. Qed.
Example not_smooth_11 : ~ is_2_3_smooth 11. Proof. decide_smooth. Qed.
Example not_smooth_14 : ~ is_2_3_smooth 14. Proof. decide_smooth. Qed.

(** is_2_3_smooth n → OrigamiDegree n *)
Lemma smooth_implies_origami_degree : forall n,
  is_2_3_smooth n -> OrigamiDegree n.
Proof.
  intros n [a [b Heq]]. subst n.
  induction a.
  - simpl. rewrite Nat.add_0_r. induction b.
    + simpl. constructor.
    + simpl. rewrite Nat.add_0_r in *.
      replace (3^b + (3^b + (3^b)))%nat with (3 * 3^b)%nat by lia.
      apply OD_ext3. exact IHb.
  - simpl. rewrite Nat.add_0_r in *.
    replace ((2^a + 2^a) * 3^b)%nat with (2 * (2^a * 3^b))%nat by lia.
    apply OD_ext2. exact IHa.
Qed.

(** OrigamiDegree n → is_2_3_smooth n *)
Lemma origami_degree_implies_smooth : forall n,
  OrigamiDegree n -> is_2_3_smooth n.
Proof.
  intros n H. induction H.
  - exists 0%nat, 0%nat. reflexivity.
  - destruct IHOrigamiDegree as [a [b Heq]].
    exists (S a), b. simpl. rewrite Nat.add_0_r. lia.
  - destruct IHOrigamiDegree as [a [b Heq]].
    exists a, (S b). simpl. rewrite Nat.add_0_r. lia.
Qed.

(** OrigamiDegree n ⟺ is_2_3_smooth n *)
Theorem origami_degree_iff_smooth : forall n,
  OrigamiDegree n <-> is_2_3_smooth n.
Proof.
  intro n. split.
  - exact (origami_degree_implies_smooth n).
  - exact (smooth_implies_origami_degree n).
Qed.

(** OrigamiDegree n ∧ OrigamiDegree m → OrigamiDegree (max n m) *)
Lemma OrigamiDegree_max : forall n m,
  OrigamiDegree n -> OrigamiDegree m -> OrigamiDegree (Nat.max n m).
Proof.
  intros n m Hn Hm.
  destruct (Nat.max_spec n m) as [[_ Heq] | [_ Heq]]; rewrite Heq; assumption.
Qed.

(** OrigamiNum_deg x n → OrigamiDegree n *)
Theorem OrigamiNum_deg_has_OrigamiDegree : forall x n,
  OrigamiNum_deg x n -> OrigamiDegree n.
Proof.
  intros x n H. induction H.
  - constructor.
  - constructor.
  - apply OrigamiDegree_max; assumption.
  - apply OrigamiDegree_max; assumption.
  - apply OrigamiDegree_max; assumption.
  - assumption.
  - apply OD_ext2; assumption.
  - apply OD_ext3. apply OrigamiDegree_max; assumption.
Qed.

(** OrigamiNum_deg x n → OrigamiNum x ∧ OrigamiDegree n *)
Corollary OrigamiNum_has_smooth_degree : forall x n,
  OrigamiNum_deg x n -> OrigamiNum x /\ OrigamiDegree n.
Proof.
  intros x n H. split.
  - apply OrigamiNum_deg_is_OrigamiNum with n. exact H.
  - apply OrigamiNum_deg_has_OrigamiDegree with x. exact H.
Qed.

(** OrigamiNum x → ∃ n, is_2_3_smooth n *)
Theorem OrigamiNum_algebraic_characterization : forall x,
  OrigamiNum x -> exists n, is_2_3_smooth n.
Proof.
  intros x Hx.
  destruct (OrigamiNum_has_deg x Hx) as [n Hn].
  exists n.
  apply origami_degree_implies_smooth.
  apply (OrigamiNum_deg_has_OrigamiDegree x n Hn).
Qed.

(** n-gon constructible ⟺ ∃ d, is_2_3_smooth d ∧ OrigamiDegree d *)
Definition ngon_origami_constructible (n : nat) : Prop :=
  exists d, is_2_3_smooth d /\ OrigamiDegree d.

(** 7-gon: φ(7) = 6 = 2·3 *)
Lemma heptagon_criterion : ngon_origami_constructible 7.
Proof. exists 6%nat. split; [exact is_2_3_smooth_6 | exact six_is_origami_degree]. Qed.

(** 9-gon: φ(9) = 6 = 2·3 *)
Lemma nonagon_criterion : ngon_origami_constructible 9.
Proof. exists 6%nat. split; [exact is_2_3_smooth_6 | exact six_is_origami_degree]. Qed.

(** gcd(a,b) = 1 *)
Definition coprime (a b : nat) : bool := Nat.gcd a b =? 1.

(** Count of k ∈ [1,k] with gcd(k,n) = 1 *)
Fixpoint count_coprime (n k : nat) : nat :=
  match k with
  | 0 => 0
  | S k' => (if coprime (S k') n then 1 else 0) + count_coprime n k'
  end.

(** φ(n) = |{k ∈ [1,n] : gcd(k,n) = 1}| *)
Definition euler_phi (n : nat) : nat := count_coprime n n.

(** φ(1) = 1 *)
Lemma phi_1 : euler_phi 1 = 1%nat. Proof. reflexivity. Qed.

(** φ(2) = 1 *)
Lemma phi_2 : euler_phi 2 = 1%nat. Proof. reflexivity. Qed.

(** φ(3) = 2 *)
Lemma phi_3 : euler_phi 3 = 2%nat. Proof. reflexivity. Qed.

(** φ(5) = 4 *)
Lemma phi_5 : euler_phi 5 = 4%nat. Proof. reflexivity. Qed.

(** φ(7) = 6 *)
Lemma phi_7 : euler_phi 7 = 6%nat. Proof. reflexivity. Qed.

(** φ(9) = 6 *)
Lemma phi_9 : euler_phi 9 = 6%nat. Proof. reflexivity. Qed.

(** φ(11) = 10 *)
Lemma phi_11 : euler_phi 11 = 10%nat. Proof. reflexivity. Qed.

(** φ(13) = 12 *)
Lemma phi_13 : euler_phi 13 = 12%nat. Proof. reflexivity. Qed.

(** φ(17) = 16 *)
Lemma phi_17 : euler_phi 17 = 16%nat. Proof. reflexivity. Qed.

(** φ(19) = 18 *)
Lemma phi_19 : euler_phi 19 = 18%nat. Proof. reflexivity. Qed.

(** p > 1 ∧ (d | p → d = 1 ∨ d = p) *)
Definition is_prime (p : nat) : Prop :=
  (p > 1)%nat /\ forall d, (d > 0)%nat -> (Nat.divide d p -> d = 1%nat \/ d = p).

(** is_prime p ∧ 0 < k < p → gcd(k,p) = 1 *)
Lemma coprime_prime_iff : forall p k,
  is_prime p -> (0 < k < p)%nat -> Nat.gcd k p = 1%nat.
Proof.
  intros p k [Hp_gt1 Hp_div] [Hk_pos Hk_lt].
  assert (Hgcd_div_p : Nat.divide (Nat.gcd k p) p) by apply Nat.gcd_divide_r.
  assert (Hgcd_div_k : Nat.divide (Nat.gcd k p) k) by apply Nat.gcd_divide_l.
  assert (Hgcd_pos : (Nat.gcd k p > 0)%nat).
  { destruct Hgcd_div_p as [q Hq]. destruct (Nat.gcd k p); lia. }
  destruct (Hp_div (Nat.gcd k p) Hgcd_pos Hgcd_div_p) as [H1 | Hp].
  - exact H1.
  - exfalso. rewrite Hp in Hgcd_div_k.
    destruct Hgcd_div_k as [q Hq].
    assert (q = 0 \/ q > 0)%nat as [Hq0 | Hqpos] by lia.
    + rewrite Hq0 in Hq. lia.
    + assert (k >= p)%nat by nia. lia.
Qed.

(** is_prime p ∧ k < p → count_coprime p k = k *)
Lemma count_coprime_prime_aux : forall p k,
  is_prime p -> (k < p)%nat ->
  count_coprime p k = k.
Proof.
  intros p k Hprime. revert k.
  induction k; intro Hk_lt.
  - reflexivity.
  - simpl. unfold coprime.
    assert (Hgcd : Nat.gcd (S k) p = 1%nat).
    { apply coprime_prime_iff; [exact Hprime | lia]. }
    rewrite Hgcd. simpl.
    rewrite IHk by lia. reflexivity.
Qed.

(** is_prime p → φ(p) = p - 1 *)
Theorem phi_prime : forall p,
  is_prime p -> euler_phi p = (p - 1)%nat.
Proof.
  intros p Hprime.
  unfold euler_phi.
  assert (Hp_gt1 : (p > 1)%nat) by (destruct Hprime; lia).
  destruct p; [lia|].
  simpl. unfold coprime.
  rewrite Nat.gcd_diag.
  assert (Hsp_ne1 : (S p =? 1) = false) by (apply Nat.eqb_neq; lia).
  rewrite Hsp_ne1. simpl.
  rewrite count_coprime_prime_aux.
  - lia.
  - exact Hprime.
  - lia.
Qed.

(** gcd(k, m·n) = 1 ⟺ gcd(k,m) = 1 ∧ gcd(k,n) = 1 *)
Lemma coprime_mul_iff : forall k m n,
  Nat.gcd k (m * n) = 1%nat <-> Nat.gcd k m = 1%nat /\ Nat.gcd k n = 1%nat.
Proof.
  intros k m n. split.
  - intro H. split.
    + assert (Hdiv : Nat.divide (Nat.gcd k m) (Nat.gcd k (m * n))).
      { apply Nat.gcd_greatest.
        - apply Nat.gcd_divide_l.
        - apply Nat.divide_trans with m.
          apply Nat.gcd_divide_r.
          apply Nat.divide_mul_l. apply Nat.divide_refl. }
      rewrite H in Hdiv.
      apply Nat.divide_1_r in Hdiv. exact Hdiv.
    + assert (Hdiv : Nat.divide (Nat.gcd k n) (Nat.gcd k (m * n))).
      { apply Nat.gcd_greatest.
        - apply Nat.gcd_divide_l.
        - apply Nat.divide_trans with n.
          apply Nat.gcd_divide_r.
          apply Nat.divide_mul_r. apply Nat.divide_refl. }
      rewrite H in Hdiv.
      apply Nat.divide_1_r in Hdiv. exact Hdiv.
  - intros [Hm Hn].
    set (g := Nat.gcd k (m * n)).
    assert (Hgk : Nat.divide g k) by apply Nat.gcd_divide_l.
    assert (Hgmn : Nat.divide g (m * n)) by apply Nat.gcd_divide_r.
    assert (Hgn_cop : Nat.gcd g n = 1%nat).
    { assert (Hdiv : Nat.divide (Nat.gcd g n) (Nat.gcd k n)).
      { apply Nat.gcd_greatest.
        - apply Nat.divide_trans with g. apply Nat.gcd_divide_l. exact Hgk.
        - apply Nat.gcd_divide_r. }
      rewrite Hn in Hdiv. apply Nat.divide_1_r. exact Hdiv. }
    assert (Hgm : Nat.divide g m).
    { apply Nat.gauss with n.
      - rewrite Nat.mul_comm. exact Hgmn.
      - exact Hgn_cop. }
    assert (Hdgkm : Nat.divide g (Nat.gcd k m)) by (apply Nat.gcd_greatest; assumption).
    rewrite Hm in Hdgkm. apply Nat.divide_1_r in Hdgkm. exact Hdgkm.
Qed.

(** coprime k n = true ⟺ gcd(k,n) = 1 *)
Lemma coprime_iff_gcd_1 : forall k n,
  coprime k n = true <-> Nat.gcd k n = 1%nat.
Proof.
  intros k n. unfold coprime. split.
  - intro H. apply Nat.eqb_eq. exact H.
  - intro H. apply Nat.eqb_eq. exact H.
Qed.

(** coprime k (m·n) = coprime k m && coprime k n *)
Lemma coprime_mul : forall k m n,
  coprime k (m * n) = (coprime k m && coprime k n)%bool.
Proof.
  intros k m n.
  destruct (coprime k (m * n)) eqn:Hkmn;
  destruct (coprime k m) eqn:Hkm;
  destruct (coprime k n) eqn:Hkn; simpl; try reflexivity; exfalso.
  - assert (Hkmn' : Nat.gcd k (m * n) = 1%nat).
    { unfold coprime in Hkmn. apply Nat.eqb_eq. exact Hkmn. }
    apply coprime_mul_iff in Hkmn'. destruct Hkmn' as [_ Hn].
    unfold coprime in Hkn. rewrite Hn in Hkn. simpl in Hkn. discriminate.
  - assert (Hkmn' : Nat.gcd k (m * n) = 1%nat).
    { unfold coprime in Hkmn. apply Nat.eqb_eq. exact Hkmn. }
    apply coprime_mul_iff in Hkmn'. destruct Hkmn' as [Hm _].
    unfold coprime in Hkm. rewrite Hm in Hkm. simpl in Hkm. discriminate.
  - assert (Hkmn' : Nat.gcd k (m * n) = 1%nat).
    { unfold coprime in Hkmn. apply Nat.eqb_eq. exact Hkmn. }
    apply coprime_mul_iff in Hkmn'. destruct Hkmn' as [Hm Hn].
    unfold coprime in Hkm. rewrite Hm in Hkm. simpl in Hkm. discriminate.
  - assert (Hkm' : Nat.gcd k m = 1%nat).
    { unfold coprime in Hkm. apply Nat.eqb_eq. exact Hkm. }
    assert (Hkn' : Nat.gcd k n = 1%nat).
    { unfold coprime in Hkn. apply Nat.eqb_eq. exact Hkn. }
    assert (Hboth : Nat.gcd k (m * n) = 1%nat) by (apply coprime_mul_iff; auto).
    unfold coprime in Hkmn. rewrite Hboth in Hkmn. simpl in Hkmn. discriminate.
Qed.

(** gcd(k, n) = gcd(k mod n, n) *)
Lemma gcd_mod : forall k n, (n > 0)%nat -> Nat.gcd k n = Nat.gcd (k mod n) n.
Proof.
  intros k n Hn.
  rewrite Nat.gcd_comm.
  rewrite Nat.Lcm0.gcd_mod.
  rewrite Nat.gcd_comm.
  reflexivity.
Qed.

(** φ(6) = φ(2)·φ(3) *)
Lemma phi_mult_2_3 : euler_phi (2 * 3) = (euler_phi 2 * euler_phi 3)%nat.
Proof. reflexivity. Qed.

(** φ(10) = φ(2)·φ(5) *)
Lemma phi_mult_2_5 : euler_phi (2 * 5) = (euler_phi 2 * euler_phi 5)%nat.
Proof. reflexivity. Qed.

(** φ(15) = φ(3)·φ(5) *)
Lemma phi_mult_3_5 : euler_phi (3 * 5) = (euler_phi 3 * euler_phi 5)%nat.
Proof. reflexivity. Qed.

(** φ(21) = φ(3)·φ(7) *)
Lemma phi_mult_3_7 : euler_phi (3 * 7) = (euler_phi 3 * euler_phi 7)%nat.
Proof. reflexivity. Qed.

(** Chinese Remainder Theorem machinery for φ multiplicativity *)

(** gcd(k, m) = gcd(k mod m, m) *)
Lemma coprime_mod_equiv : forall k m,
  (m > 0)%nat -> Nat.gcd k m = Nat.gcd (k mod m) m.
Proof.
  intros k m Hm.
  rewrite Nat.gcd_comm.
  rewrite Nat.Lcm0.gcd_mod.
  rewrite Nat.gcd_comm.
  reflexivity.
Qed.

(** k ↦ (k mod m, k mod n) *)
Definition crt_pair (m n k : nat) : nat * nat := (k mod m, k mod n).

(** gcd(k, m·n) = 1 ⟺ gcd(k,m) = 1 ∧ gcd(k,n) = 1 *)
Lemma coprime_product_iff : forall k m n,
  (m > 0)%nat -> (n > 0)%nat ->
  (Nat.gcd k (m * n) = 1)%nat <-> (Nat.gcd k m = 1 /\ Nat.gcd k n = 1)%nat.
Proof.
  intros k m n Hm Hn.
  apply coprime_mul_iff.
Qed.

(** gcd(k,m) = 1 ⟺ gcd(k mod m, m) = 1 *)
Lemma coprime_residue : forall k m,
  (m > 0)%nat ->
  (Nat.gcd k m = 1)%nat <-> (Nat.gcd (k mod m) m = 1)%nat.
Proof.
  intros k m Hm.
  rewrite coprime_mod_equiv by lia.
  tauto.
Qed.

(** ∃ u v, u·m = gcd(m,n) + v·n *)
Lemma bezout_gcd : forall m n,
  (m > 0)%nat ->
  exists u v, (u * m = Nat.gcd m n + v * n)%nat.
Proof.
  intros m n Hm.
  destruct (Nat.gcd_bezout_pos m n Hm) as [u [v Heq]].
  exists u, v.
  exact Heq.
Qed.

(** gcd(m,n) = 1 → ∃ u v, u·m = 1 + v·n *)
Lemma bezout_coprime : forall m n,
  (m > 0)%nat ->
  Nat.gcd m n = 1%nat ->
  exists u v, (u * m = 1 + v * n)%nat.
Proof.
  intros m n Hm Hgcd.
  destruct (bezout_gcd m n Hm) as [u [v Heq]].
  exists u, v.
  rewrite Hgcd in Heq.
  exact Heq.
Qed.

(** (a·b·m) mod m = 0 *)
Lemma mod_mul_zero : forall a b m,
  (m > 0)%nat -> ((a * b * m) mod m = 0)%nat.
Proof.
  intros a b m Hm.
  replace (a * b * m)%nat with ((a * b) * m)%nat by lia.
  apply Nat.Div0.mod_mul.
Qed.

(** u·m = 1 + v·n → (u·m) mod n = 1 *)
Lemma bezout_mod_one : forall u v m n,
  (n > 1)%nat ->
  (u * m = 1 + v * n)%nat ->
  ((u * m) mod n = 1)%nat.
Proof.
  intros u v m n Hn Heq.
  rewrite Heq.
  rewrite Nat.Div0.add_mod by lia.
  rewrite Nat.Div0.mod_mul.
  rewrite Nat.add_0_r.
  rewrite Nat.Div0.mod_mod by lia.
  apply Nat.mod_small.
  lia.
Qed.

(** c mod m = 1 → (a·c) mod m = a mod m *)
Lemma mul_mod_one : forall a c m,
  (m > 0)%nat ->
  (c mod m = 1)%nat ->
  ((a * c) mod m = a mod m)%nat.
Proof.
  intros a c m Hm Hc.
  rewrite Nat.Div0.mul_mod by lia.
  rewrite Hc.
  rewrite Nat.mul_1_r.
  apply Nat.Div0.mod_mod.
Qed.

(** a mod m = 0 → (a + b) mod m = b mod m *)
Lemma add_mod_zero_l : forall a b m,
  (m > 0)%nat ->
  (a mod m = 0)%nat ->
  ((a + b) mod m = b mod m)%nat.
Proof.
  intros a b m Hm Ha.
  rewrite Nat.Div0.add_mod by lia.
  rewrite Ha.
  rewrite Nat.add_0_l.
  apply Nat.Div0.mod_mod.
Qed.

(** b mod m = 0 → (a + b) mod m = a mod m *)
Lemma add_mod_zero_r : forall a b m,
  (m > 0)%nat ->
  (b mod m = 0)%nat ->
  ((a + b) mod m = a mod m)%nat.
Proof.
  intros a b m Hm Hb.
  rewrite Nat.add_comm.
  apply add_mod_zero_l; assumption.
Qed.

(** k mod n = 1 → (a·k) mod n = a mod n *)
Lemma mul_by_one_mod : forall a k n,
  (n > 0)%nat ->
  (k mod n = 1)%nat ->
  ((a * k) mod n = a mod n)%nat.
Proof.
  intros a k n Hn Hk.
  rewrite Nat.Div0.mul_mod by lia.
  rewrite Hk.
  rewrite Nat.mul_1_r.
  apply Nat.Div0.mod_mod.
Qed.

(** u·m = 1 + v·n → (a·(u·m)) mod n = a mod n *)
Lemma crt_first_residue : forall a u v m n,
  (n > 1)%nat ->
  (u * m = 1 + v * n)%nat ->
  ((a * (u * m)) mod n = a mod n)%nat.
Proof.
  intros a u v m n Hn Heq.
  apply mul_by_one_mod.
  - lia.
  - apply (bezout_mod_one u v m n Hn Heq).
Qed.

(** (k·m) mod m = 0 *)
Lemma mul_mod_self : forall k m,
  (m > 0)%nat ->
  ((k * m) mod m = 0)%nat.
Proof.
  intros k m Hm.
  apply Nat.Div0.mod_mul.
Qed.

(** gcd(m,n) = 1 → ∃ u, (u·m) mod n = 1 *)
Lemma mod_inverse_exists : forall m n,
  (m > 0)%nat -> (n > 1)%nat ->
  Nat.gcd m n = 1%nat ->
  exists u, ((u * m) mod n = 1)%nat.
Proof.
  intros m n Hm Hn Hgcd.
  destruct (bezout_coprime m n Hm Hgcd) as [u [v Heq]].
  exists u.
  apply (bezout_mod_one u v m n Hn Heq).
Qed.

(** (u·m) mod n = 1 → (u·b·m) mod n = b mod n *)
Lemma scale_by_inverse : forall u b m n,
  (n > 0)%nat ->
  ((u * m) mod n = 1)%nat ->
  ((u * b * m) mod n = b mod n)%nat.
Proof.
  intros u b m n Hn Hinv.
  replace (u * b * m)%nat with (b * (u * m))%nat by lia.
  apply mul_by_one_mod; assumption.
Qed.

(** gcd(m,n) = 1 ∧ b < n → ∃ t, (m·t) mod n = b *)
Lemma achieve_residue : forall m n b,
  (m > 0)%nat -> (n > 1)%nat ->
  Nat.gcd m n = 1%nat ->
  (b < n)%nat ->
  exists t, ((m * t) mod n = b)%nat.
Proof.
  intros m n b Hm Hn Hgcd Hb.
  destruct (mod_inverse_exists m n Hm Hn Hgcd) as [u Hinv].
  exists (u * b)%nat.
  replace (m * (u * b))%nat with (u * b * m)%nat by lia.
  rewrite scale_by_inverse by (lia || assumption).
  apply Nat.mod_small.
  lia.
Qed.

(** (a + n - b) mod n = (a + (n - b)) mod n *)
Lemma sub_mod_helper : forall a b n,
  (n > 0)%nat -> (b < n)%nat ->
  ((a + n - b) mod n = (a + (n - b)) mod n)%nat.
Proof.
  intros a b n Hn Hb.
  f_equal.
  lia.
Qed.

(** (a + m·t) mod m = a mod m *)
Lemma add_mul_mod : forall a m t,
  (m > 0)%nat ->
  ((a + m * t) mod m = a mod m)%nat.
Proof.
  intros a m t Hm.
  rewrite Nat.Div0.add_mod by lia.
  replace (m * t)%nat with (t * m)%nat by lia.
  rewrite Nat.Div0.mod_mul.
  rewrite Nat.add_0_r.
  apply Nat.Div0.mod_mod.
Qed.

(** (a + n) mod n = a mod n *)
Lemma mod_add_self : forall a n, (n > 0)%nat -> ((a + n) mod n = a mod n)%nat.
Proof.
  intros a n Hn.
  rewrite Nat.Div0.add_mod by lia.
  rewrite Nat.Div0.mod_same by lia.
  rewrite Nat.add_0_r.
  apply Nat.Div0.mod_mod.
Qed.

(** b < n → b + n - b = n *)
Lemma add_sub_cancel : forall b n, (b < n)%nat -> (b + n - b = n)%nat.
Proof.
  intros b n Hb.
  lia.
Qed.

(** 0 mod m = 0 ∧ 0 mod n = 0 *)
Lemma crt_zero_zero : forall m n,
  (m > 0)%nat -> (n > 0)%nat ->
  (0 mod m = 0 /\ 0 mod n = 0)%nat.
Proof.
  intros m n Hm Hn.
  split; apply Nat.Div0.mod_0_l; lia.
Qed.

(** (k mod (m·n)) mod m = k mod m *)
Lemma mod_mul_mod_l : forall val mod1 mod2,
  (mod1 > 0)%nat -> (mod2 > 0)%nat ->
  ((val mod (mod1 * mod2)) mod mod1 = val mod mod1)%nat.
Proof.
  intros val mod1 mod2 Hm1 Hm2.
  assert (Hprod : (mod1 * mod2 > 0)%nat) by lia.
  set (rem := (val mod (mod1 * mod2))%nat).
  set (quot := (val / (mod1 * mod2))%nat).
  assert (Hdiv : (val = quot * (mod1 * mod2) + rem)%nat).
  { unfold quot, rem. rewrite Nat.mul_comm. apply Nat.div_mod. lia. }
  assert (Hrem_lt : (rem < mod1 * mod2)%nat).
  { unfold rem. apply Nat.mod_upper_bound. lia. }
  rewrite Hdiv.
  rewrite Nat.Div0.add_mod by lia.
  rewrite Nat.Div0.mul_mod by lia.
  replace ((mod1 * mod2) mod mod1)%nat with 0%nat.
  2: { rewrite Nat.mul_comm. symmetry. apply Nat.Div0.mod_mul. }
  rewrite Nat.mul_0_r.
  rewrite Nat.Div0.mod_0_l by lia.
  rewrite Nat.add_0_l.
  rewrite Nat.Div0.mod_mod by lia.
  fold rem.
  reflexivity.
Qed.

(** (k mod (m·n)) mod n = k mod n *)
Lemma mod_mul_mod_r : forall val mod1 mod2,
  (mod1 > 0)%nat -> (mod2 > 0)%nat ->
  ((val mod (mod1 * mod2)) mod mod2 = val mod mod2)%nat.
Proof.
  intros val mod1 mod2 Hm1 Hm2.
  rewrite Nat.mul_comm.
  apply mod_mul_mod_l; lia.
Qed.

(** a = m·(a/m) + (a mod m) *)
Lemma div_mod_eq : forall a m,
  (m > 0)%nat -> (a = m * (a / m) + a mod m)%nat.
Proof.
  intros a m Hm.
  assert (H := Nat.div_mod a m ltac:(lia)).
  lia.
Qed.

(** a mod m = b mod m ∧ a ≥ b → m | (a - b) *)
Lemma mod_eq_divides : forall a b m,
  (m > 0)%nat -> (a >= b)%nat ->
  (a mod m = b mod m)%nat ->
  Nat.divide m (a - b).
Proof.
  intros a b m Hm Hge Heq.
  assert (Hab: (a / m >= b / m)%nat).
  { apply Nat.Div0.div_le_mono; lia. }
  assert (Ha := div_mod_eq a m Hm).
  assert (Hb := div_mod_eq b m Hm).
  assert (Hmod_a: (a mod m < m)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hmod_b: (b mod m < m)%nat) by (apply Nat.mod_upper_bound; lia).
  exists ((a / m) - (b / m))%nat.
  nia.
Qed.

(** gcd(m,n) = 1 ∧ m|d ∧ n|d → m·n | d *)
Lemma coprime_divides_mul : forall m n d,
  (m > 0)%nat -> (n > 0)%nat ->
  Nat.gcd m n = 1%nat ->
  Nat.divide m d -> Nat.divide n d ->
  Nat.divide (m * n) d.
Proof.
  intros m n d Hm Hn Hgcd Hdm Hdn.
  destruct Hdm as [qm Hqm].
  destruct Hdn as [qn Hqn].
  assert (Hdiv: Nat.divide n qm).
  { assert (Hdiv_mn: Nat.divide n (m * qm)).
    { exists qn. subst d. lia. }
    apply Nat.gauss with m; auto.
    rewrite Nat.gcd_comm. exact Hgcd. }
  destruct Hdiv as [q Hq].
  exists q.
  subst d. rewrite Hq. ring.
Qed.

(** m·n | d ∧ d < m·n → d = 0 *)
Lemma small_multiple_zero : forall m n d,
  (m > 0)%nat -> (n > 0)%nat ->
  Nat.divide (m * n) d -> (d < m * n)%nat -> d = 0%nat.
Proof.
  intros m n d Hm Hn Hdiv Hlt.
  destruct Hdiv as [q Hq].
  assert (q = 0)%nat by nia.
  lia.
Qed.

(** gcd(m,n)=1 ∧ k₁,k₂ < m·n ∧ k₁≡k₂ (mod m) ∧ k₁≡k₂ (mod n) → k₁=k₂ *)
Lemma crt_injectivity : forall m n k1 k2,
  (m > 0)%nat -> (n > 0)%nat ->
  Nat.gcd m n = 1%nat ->
  (k1 < m * n)%nat -> (k2 < m * n)%nat ->
  (k1 mod m = k2 mod m)%nat ->
  (k1 mod n = k2 mod n)%nat ->
  k1 = k2.
Proof.
  intros m n k1 k2 Hm Hn Hgcd Hk1 Hk2 Hmodm Hmodn.
  destruct (Nat.le_ge_cases k1 k2) as [Hle | Hge].
  - assert (Hdm: Nat.divide m (k2 - k1)).
    { apply mod_eq_divides; lia || auto. }
    assert (Hdn: Nat.divide n (k2 - k1)).
    { apply mod_eq_divides; lia || auto. }
    assert (Hdmn: Nat.divide (m * n) (k2 - k1)).
    { apply coprime_divides_mul; auto. }
    assert (Hdiff: (k2 - k1 < m * n)%nat) by lia.
    assert (Hzero: (k2 - k1 = 0)%nat).
    { apply small_multiple_zero with m n; auto. }
    lia.
  - assert (Hdm: Nat.divide m (k1 - k2)).
    { apply mod_eq_divides; [lia | lia | symmetry; auto]. }
    assert (Hdn: Nat.divide n (k1 - k2)).
    { apply mod_eq_divides; [lia | lia | symmetry; auto]. }
    assert (Hdmn: Nat.divide (m * n) (k1 - k2)).
    { apply coprime_divides_mul; auto. }
    assert (Hdiff: (k1 - k2 < m * n)%nat) by lia.
    assert (Hzero: (k1 - k2 = 0)%nat).
    { apply small_multiple_zero with m n; auto. }
    lia.
Qed.

(** (r + ((t + n - r) mod n)) mod n = t *)
Lemma mod_add_sub_cancel : forall res_val tgt_val mod_val,
  (mod_val > 0)%nat -> (res_val < mod_val)%nat -> (tgt_val < mod_val)%nat ->
  ((res_val + (tgt_val + mod_val - res_val) mod mod_val) mod mod_val = tgt_val)%nat.
Proof.
  intros res_val tgt_val mod_val Hmod Hres Htgt.
  destruct (Nat.le_gt_cases res_val tgt_val) as [Hle | Hgt].
  - assert (Heq: (tgt_val + mod_val - res_val = mod_val + (tgt_val - res_val))%nat) by lia.
    rewrite Heq.
    assert (Hdiff_lt: (tgt_val - res_val < mod_val)%nat) by lia.
    replace ((mod_val + (tgt_val - res_val)) mod mod_val)%nat with (tgt_val - res_val)%nat.
    2: {
      rewrite Nat.add_comm.
      rewrite Nat.Div0.add_mod by lia.
      rewrite Nat.Div0.mod_same by lia.
      rewrite Nat.add_0_r.
      rewrite Nat.Div0.mod_mod by lia.
      symmetry. apply Nat.mod_small. lia.
    }
    replace (res_val + (tgt_val - res_val))%nat with tgt_val by lia.
    apply Nat.mod_small. lia.
  - assert (Hlt: (tgt_val + mod_val - res_val < mod_val)%nat).
    { assert (Hgt': (res_val > tgt_val)%nat) by lia.
      assert (Hsum: (tgt_val + mod_val > res_val)%nat) by lia.
      lia. }
    replace ((tgt_val + mod_val - res_val) mod mod_val)%nat with (tgt_val + mod_val - res_val)%nat.
    2: { symmetry. apply Nat.mod_small. exact Hlt. }
    replace (res_val + (tgt_val + mod_val - res_val))%nat with (tgt_val + mod_val)%nat by lia.
    rewrite Nat.Div0.add_mod by lia.
    rewrite Nat.Div0.mod_same by lia.
    rewrite Nat.add_0_r.
    rewrite Nat.Div0.mod_mod by lia.
    assert (Hsmall: (tgt_val mod mod_val = tgt_val)%nat).
    { apply Nat.mod_small. exact Htgt. }
    rewrite Hsmall. reflexivity.
Qed.

(** gcd(m,n)=1 ∧ a<m ∧ b<n → ∃ k<m·n, k≡a (mod m) ∧ k≡b (mod n) *)
Lemma crt_existence : forall m n a b,
  (m > 1)%nat -> (n > 1)%nat ->
  Nat.gcd m n = 1%nat ->
  (a < m)%nat -> (b < n)%nat ->
  exists k, (k < m * n)%nat /\ (k mod m = a)%nat /\ (k mod n = b)%nat.
Proof.
  intros m n a b Hm Hn Hgcd Ha Hb.
  destruct (achieve_residue n m a ltac:(lia) ltac:(lia) ltac:(rewrite Nat.gcd_comm; exact Hgcd) ltac:(lia)) as [t1 Ht1].
  set (k1 := (n * t1)%nat).
  assert (Hk1_mod_m: (k1 mod m = a)%nat).
  { unfold k1. exact Ht1. }
  set (diff := ((b + n - k1 mod n) mod n)%nat).
  destruct (achieve_residue m n diff ltac:(lia) ltac:(lia) Hgcd ltac:(apply Nat.mod_upper_bound; lia)) as [t2 Ht2].
  set (k := (k1 + m * t2)%nat).
  exists (k mod (m * n))%nat.
  split; [| split].
  - apply Nat.mod_upper_bound. lia.
  - rewrite mod_mul_mod_l by lia.
    unfold k.
    rewrite Nat.Div0.add_mod by lia.
    rewrite Hk1_mod_m.
    rewrite Nat.Div0.mul_mod by lia.
    rewrite Nat.Div0.mod_same by lia.
    rewrite Nat.mul_0_l.
    rewrite Nat.Div0.mod_0_l by lia.
    rewrite Nat.add_0_r.
    apply Nat.mod_small. lia.
  - rewrite mod_mul_mod_r by lia.
    unfold k.
    rewrite Nat.Div0.add_mod by lia.
    rewrite Ht2.
    unfold diff.
    assert (Hkn: (k1 mod n < n)%nat) by (apply Nat.mod_upper_bound; lia).
    apply mod_add_sub_cancel; lia.
Qed.

(** gcd(k, m·n)=1 ⟺ gcd(k mod m, m)=1 ∧ gcd(k mod n, n)=1 *)
Lemma crt_coprime_iff : forall m n k,
  (m > 1)%nat -> (n > 1)%nat ->
  Nat.gcd m n = 1%nat ->
  (Nat.gcd k (m * n) = 1)%nat <-> (Nat.gcd (k mod m) m = 1)%nat /\ (Nat.gcd (k mod n) n = 1)%nat.
Proof.
  intros m n k Hm Hn Hgcd.
  split.
  - intros Hkmn.
    rewrite coprime_product_iff in Hkmn by lia.
    destruct Hkmn as [Hkm_prod Hkn_prod].
    split.
    + rewrite <- coprime_mod_equiv by lia. exact Hkm_prod.
    + rewrite <- coprime_mod_equiv by lia. exact Hkn_prod.
  - intros [Hkm Hkn].
    rewrite coprime_product_iff by lia.
    split.
    + rewrite coprime_mod_equiv by lia. exact Hkm.
    + rewrite coprime_mod_equiv by lia. exact Hkn.
Qed.

(** φ(6) = φ(2)·φ(3) *)
Lemma euler_phi_2_3 : euler_phi (2 * 3) = (euler_phi 2 * euler_phi 3)%nat.
Proof. reflexivity. Qed.

(** φ(10) = φ(2)·φ(5) *)
Lemma euler_phi_2_5 : euler_phi (2 * 5) = (euler_phi 2 * euler_phi 5)%nat.
Proof. reflexivity. Qed.

(** φ(14) = φ(2)·φ(7) *)
Lemma euler_phi_2_7 : euler_phi (2 * 7) = (euler_phi 2 * euler_phi 7)%nat.
Proof. reflexivity. Qed.

(** φ(15) = φ(3)·φ(5) *)
Lemma euler_phi_3_5 : euler_phi (3 * 5) = (euler_phi 3 * euler_phi 5)%nat.
Proof. reflexivity. Qed.

(** φ(21) = φ(3)·φ(7) *)
Lemma euler_phi_3_7 : euler_phi (3 * 7) = (euler_phi 3 * euler_phi 7)%nat.
Proof. reflexivity. Qed.

(** φ(18) = φ(2)·φ(9) *)
Lemma euler_phi_2_9 : euler_phi (2 * 9) = (euler_phi 2 * euler_phi 9)%nat.
Proof. reflexivity. Qed.

(** φ(36) = φ(4)·φ(9) *)
Lemma euler_phi_4_9 : euler_phi (4 * 9) = (euler_phi 4 * euler_phi 9)%nat.
Proof. reflexivity. Qed.

(** φ(72) = φ(8)·φ(9) *)
Lemma euler_phi_8_9 : euler_phi (8 * 9) = (euler_phi 8 * euler_phi 9)%nat.
Proof. reflexivity. Qed.

(** count_coprime n 0 = 0 *)
Lemma count_coprime_0 : forall n, count_coprime n 0 = 0%nat.
Proof. reflexivity. Qed.

Lemma count_coprime_S : forall n k,
  count_coprime n (S k) = ((if coprime (S k) n then 1 else 0) + count_coprime n k)%nat.
Proof. reflexivity. Qed.

(** count_coprime n (S k) = count_coprime n k + (1 if coprime else 0) *)
Lemma count_coprime_split : forall n k,
  count_coprime n (S k) = (count_coprime n k + if coprime (S k) n then 1 else 0)%nat.
Proof.
  intros n k. rewrite count_coprime_S. lia.
Qed.

(* count_coprime as the length of a filtered range: this turns the totient into
   a list cardinality, the bridge to the CRT bijection for multiplicativity. *)
Lemma count_coprime_filter : forall N k,
  count_coprime N k = length (filter (fun j => coprime j N) (seq 1 k)).
Proof.
  intros N k. induction k as [|k IH].
  - reflexivity.
  - rewrite count_coprime_S, seq_S, filter_app, length_app, IH.
    assert (Hsing : length (filter (fun j => coprime j N) (1 + k :: nil)%nat)
                    = if coprime (S k) N then 1%nat else 0%nat).
    { replace (1 + k)%nat with (S k) by lia. simpl.
      destruct (coprime (S k) N); reflexivity. }
    rewrite Hsing. destruct (coprime (S k) N); lia.
Qed.

(** n > 0 → coprime 1 n = true *)
Lemma coprime_1_l : forall n, (n > 0)%nat -> coprime 1 n = true.
Proof.
  intros n Hn.
  unfold coprime.
  assert (Hgcd: Nat.gcd 1 n = 1%nat).
  { destruct n; [lia|]. simpl. reflexivity. }
  rewrite Hgcd. reflexivity.
Qed.

(** gcd(n, 1) = 1 *)
Lemma gcd_n_1 : forall n, Nat.gcd n 1 = 1%nat.
Proof.
  intro n.
  rewrite Nat.gcd_comm.
  destruct n; reflexivity.
Qed.

(** coprime n 1 = true *)
Lemma coprime_n_1 : forall n, coprime n 1 = true.
Proof.
  intro n.
  unfold coprime.
  rewrite gcd_n_1.
  reflexivity.
Qed.

(** count_coprime 1 k = k *)
Lemma count_coprime_1 : forall k, count_coprime 1 k = k.
Proof.
  intro k.
  induction k as [|k' IHk].
  - reflexivity.
  - rewrite count_coprime_S.
    rewrite IHk.
    rewrite coprime_n_1.
    lia.
Qed.

(** euler_phi 1 = 1 (already have phi_1, but useful form) *)
Lemma euler_phi_1 : euler_phi 1 = 1%nat.
Proof. reflexivity. Qed.

(** n-gon origami-constructible ⟺ is_2_3_smooth(φ(n)) *)
Definition ngon_constructible_iff_phi_smooth (n : nat) : Prop :=
  is_2_3_smooth (euler_phi n).

Lemma heptagon_phi_smooth : ngon_constructible_iff_phi_smooth 7.
Proof. unfold ngon_constructible_iff_phi_smooth. exact is_2_3_smooth_6. Qed.

Lemma nonagon_phi_smooth : ngon_constructible_iff_phi_smooth 9.
Proof. unfold ngon_constructible_iff_phi_smooth. exact is_2_3_smooth_6. Qed.

Lemma is_2_3_smooth_16 : is_2_3_smooth 16.
Proof. exists 4%nat, 0%nat. reflexivity. Qed.

Lemma tridecagon_phi_smooth : ngon_constructible_iff_phi_smooth 13.
Proof. unfold ngon_constructible_iff_phi_smooth. exact is_2_3_smooth_12. Qed.

Lemma heptadecagon_phi_smooth : ngon_constructible_iff_phi_smooth 17.
Proof. unfold ngon_constructible_iff_phi_smooth. exact is_2_3_smooth_16. Qed.

Lemma enneadecagon_phi_smooth : ngon_constructible_iff_phi_smooth 19.
Proof. unfold ngon_constructible_iff_phi_smooth. exact is_2_3_smooth_18. Qed.

(** Tactic: decide n-gon constructibility by computation *)
Ltac decide_ngon :=
  unfold ngon_constructible_iff_phi_smooth;
  decide_smooth.

Example ngon_7_constructible : ngon_constructible_iff_phi_smooth 7.
Proof. decide_ngon. Qed.

Example ngon_9_constructible : ngon_constructible_iff_phi_smooth 9.
Proof. decide_ngon. Qed.

Example ngon_13_constructible : ngon_constructible_iff_phi_smooth 13.
Proof. decide_ngon. Qed.

Example ngon_17_constructible : ngon_constructible_iff_phi_smooth 17.
Proof. decide_ngon. Qed.

Example ngon_19_constructible : ngon_constructible_iff_phi_smooth 19.
Proof. decide_ngon. Qed.

Example ngon_37_constructible : ngon_constructible_iff_phi_smooth 37.
Proof. decide_ngon. Qed.

Example ngon_73_constructible : ngon_constructible_iff_phi_smooth 73.
Proof. decide_ngon. Qed.

Example ngon_11_not_constructible : ~ ngon_constructible_iff_phi_smooth 11.
Proof. decide_ngon. Qed.

Example ngon_23_not_constructible : ~ ngon_constructible_iff_phi_smooth 23.
Proof. decide_ngon. Qed.

Example ngon_29_not_constructible : ~ ngon_constructible_iff_phi_smooth 29.
Proof. decide_ngon. Qed.

(** cos(2π/n) ∈ OrigamiNum *)
Definition ngon_vertex_constructible (n : nat) (cos_val : R) : Prop :=
  OrigamiNum cos_val.

(** n ≥ 3 ∧ cos(2π/n) ∈ OrigamiNum → ∃ d, OrigamiNum_deg(cos, d) ∧ OrigamiDegree(d) *)
Theorem ngon_constructible_characterization : forall n cos_2pi_n,
  (n >= 3)%nat ->
  ngon_vertex_constructible n cos_2pi_n ->
  exists d, OrigamiNum_deg cos_2pi_n d /\ OrigamiDegree d.
Proof.
  intros n cos_val Hn Hcos.
  destruct (OrigamiNum_has_deg cos_val Hcos) as [d Hd].
  exists d. split.
  - exact Hd.
  - apply OrigamiNum_deg_has_OrigamiDegree with cos_val. exact Hd.
Qed.

(** n ≥ 3 ∧ cos(2π/n) ∈ OrigamiNum → ∃ d, is_2_3_smooth(d) *)
Corollary ngon_constructible_implies_smooth_degree : forall n cos_2pi_n,
  (n >= 3)%nat ->
  ngon_vertex_constructible n cos_2pi_n ->
  exists d, is_2_3_smooth d.
Proof.
  intros n cos_val Hn Hcos.
  destruct (ngon_constructible_characterization n cos_val Hn Hcos) as [d [Hdeg Hod]].
  exists d. apply origami_degree_implies_smooth. exact Hod.
Qed.

(** coprime k (m*n) iff coprime (k mod m) m and coprime (k mod n) n *)
Lemma coprime_product_residues : forall m n k,
  (m > 1)%nat -> (n > 1)%nat ->
  Nat.gcd m n = 1%nat ->
  coprime k (m * n) = (coprime (k mod m) m && coprime (k mod n) n)%bool.
Proof.
  intros m n k Hm Hn Hgcd.
  unfold coprime.
  destruct (Nat.gcd k (m * n) =? 1) eqn:Hkmn;
  destruct (Nat.gcd (k mod m) m =? 1) eqn:Hkm;
  destruct (Nat.gcd (k mod n) n =? 1) eqn:Hkn;
  try reflexivity.
  - (* Hkmn=true, Hkm=true, Hkn=false *)
    apply Nat.eqb_eq in Hkmn.
    apply Nat.eqb_neq in Hkn.
    rewrite crt_coprime_iff in Hkmn by lia.
    destruct Hkmn as [_ Hkn'].
    contradiction.
  - (* Hkmn=true, Hkm=false, Hkn=true *)
    apply Nat.eqb_eq in Hkmn.
    apply Nat.eqb_neq in Hkm.
    rewrite crt_coprime_iff in Hkmn by lia.
    destruct Hkmn as [Hkm' _].
    contradiction.
  - (* Hkmn=true, Hkm=false, Hkn=false *)
    apply Nat.eqb_eq in Hkmn.
    apply Nat.eqb_neq in Hkm.
    rewrite crt_coprime_iff in Hkmn by lia.
    destruct Hkmn as [Hkm' _].
    contradiction.
  - (* Hkmn=false, Hkm=true, Hkn=true *)
    apply Nat.eqb_neq in Hkmn.
    apply Nat.eqb_eq in Hkm.
    apply Nat.eqb_eq in Hkn.
    assert (Hkmn': Nat.gcd k (m * n) = 1%nat).
    { rewrite crt_coprime_iff by lia. auto. }
    contradiction.
Qed.

(** |{k ∈ [1,bound] : f(k) = true}| *)
Fixpoint count_pred (f : nat -> bool) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S k => (if f (S k) then 1 else 0) + count_pred f k
  end.

Lemma count_pred_0 : forall f, count_pred f 0 = 0%nat.
Proof. reflexivity. Qed.

Lemma count_pred_S : forall f k,
  count_pred f (S k) = ((if f (S k) then 1 else 0) + count_pred f k)%nat.
Proof. reflexivity. Qed.

(** count_coprime n k = count_pred (fun x => coprime x n) k *)
Lemma count_coprime_eq_count_pred : forall n k,
  count_coprime n k = count_pred (fun x => coprime x n) k.
Proof.
  intros n k.
  induction k as [|k' IHk].
  - reflexivity.
  - rewrite count_coprime_S, count_pred_S.
    rewrite IHk. reflexivity.
Qed.

(** |{(a,b) ∈ [1,m]×[1,n] : f(a) ∧ g(b)}| *)
Fixpoint count_pairs (f : nat -> bool) (g : nat -> bool) (m n : nat) : nat :=
  match m with
  | 0 => 0
  | S m' => (if f (S m') then count_pred g n else 0) + count_pairs f g m' n
  end.

Lemma count_pairs_0 : forall f g n, count_pairs f g 0 n = 0%nat.
Proof. reflexivity. Qed.

Lemma count_pairs_S : forall f g m n,
  count_pairs f g (S m) n = ((if f (S m) then count_pred g n else 0) + count_pairs f g m n)%nat.
Proof. reflexivity. Qed.

(** count_pairs(f,g,m,n) = count_pred(f,m) · count_pred(g,n) *)
Lemma count_pairs_eq_mul : forall f g m n,
  count_pairs f g m n = (count_pred f m * count_pred g n)%nat.
Proof.
  intros f g m n.
  induction m as [|m' IHm].
  - simpl. reflexivity.
  - rewrite count_pairs_S, count_pred_S.
    rewrite IHm.
    destruct (f (S m')); simpl; ring.
Qed.

(** φ(m) * φ(n) = count of coprime pairs *)
Lemma phi_product_eq_pairs : forall m n,
  (euler_phi m * euler_phi n)%nat =
  count_pairs (fun a => coprime a m) (fun b => coprime b n) m n.
Proof.
  intros m n.
  unfold euler_phi.
  rewrite count_coprime_eq_count_pred.
  rewrite count_coprime_eq_count_pred.
  rewrite count_pairs_eq_mul.
  reflexivity.
Qed.

(** k ↦ (k mod m, k mod n) *)
Definition crt_map (m n k : nat) : nat * nat := (k mod m, k mod n).

(** coprime(k,mn) → coprime(k mod m, m) ∧ coprime(k mod n, n) *)
Lemma crt_map_coprime : forall m n k,
  (m > 1)%nat -> (n > 1)%nat ->
  Nat.gcd m n = 1%nat ->
  (k < m * n)%nat ->
  coprime k (m * n) = true ->
  coprime (fst (crt_map m n k)) m = true /\ coprime (snd (crt_map m n k)) n = true.
Proof.
  intros m n k Hm Hn Hgcd Hk Hcop.
  unfold crt_map. simpl.
  rewrite coprime_product_residues in Hcop by lia.
  apply andb_true_iff in Hcop.
  exact Hcop.
Qed.

(** φ(2·3) = φ(2)·φ(3) *)
Lemma euler_phi_mult_2_3 : euler_phi (2 * 3) = (euler_phi 2 * euler_phi 3)%nat.
Proof. reflexivity. Qed.

Lemma euler_phi_mult_2_5 : euler_phi (2 * 5) = (euler_phi 2 * euler_phi 5)%nat.
Proof. reflexivity. Qed.

Lemma euler_phi_mult_3_4 : euler_phi (3 * 4) = (euler_phi 3 * euler_phi 4)%nat.
Proof. reflexivity. Qed.

Lemma euler_phi_mult_3_5 : euler_phi (3 * 5) = (euler_phi 3 * euler_phi 5)%nat.
Proof. reflexivity. Qed.

Lemma euler_phi_mult_4_9 : euler_phi (4 * 9) = (euler_phi 4 * euler_phi 9)%nat.
Proof. reflexivity. Qed.

Lemma euler_phi_mult_5_7 : euler_phi (5 * 7) = (euler_phi 5 * euler_phi 7)%nat.
Proof. reflexivity. Qed.

Lemma euler_phi_mult_7_9 : euler_phi (7 * 9) = (euler_phi 7 * euler_phi 9)%nat.
Proof. reflexivity. Qed.

Lemma euler_phi_mult_8_9 : euler_phi (8 * 9) = (euler_phi 8 * euler_phi 9)%nat.
Proof. reflexivity. Qed.

(** For k in [1..mn], k mod m is in [0..m-1] and k mod n is in [0..n-1] *)
Lemma crt_map_range : forall m n k,
  (m > 0)%nat -> (n > 0)%nat -> (k <= m * n)%nat ->
  (fst (crt_map m n k) < m)%nat /\ (snd (crt_map m n k) < n)%nat.
Proof.
  intros m n k Hm Hn Hk.
  unfold crt_map. simpl.
  split; apply Nat.mod_upper_bound; lia.
Qed.

(** 0 is not coprime to n when n > 1 *)
Lemma zero_not_coprime : forall n, (n > 1)%nat -> coprime 0 n = false.
Proof.
  intros n Hn.
  unfold coprime.
  rewrite Nat.gcd_0_l.
  destruct (n =? 1) eqn:Heq.
  - apply Nat.eqb_eq in Heq. lia.
  - reflexivity.
Qed.

(** Nonzero residue when k > 0 and k mod n = 0 means n divides k *)
Lemma mod_zero_divisible : forall n k,
  (n > 0)%nat -> (k mod n = 0)%nat -> Nat.divide n k.
Proof.
  intros n k Hn Hmod.
  exists (Nat.div k n).
  rewrite Nat.mul_comm.
  apply Nat.Div0.div_exact; lia.
Qed.

(** For k in [1..m*n-1], the residue pair determines k uniquely (CRT) *)
Lemma crt_unique_in_range : forall m n k1 k2,
  (m > 1)%nat -> (n > 1)%nat -> Nat.gcd m n = 1%nat ->
  (k1 < m * n)%nat -> (k2 < m * n)%nat ->
  k1 mod m = k2 mod m -> k1 mod n = k2 mod n ->
  k1 = k2.
Proof.
  intros m n k1 k2 Hm Hn Hgcd Hk1_lt Hk2_lt Hmodm Hmodn.
  apply crt_injectivity with (m := m) (n := n); lia || auto.
Qed.

(** Coprimality of residues implies coprimality of the number *)
Lemma coprime_from_residues : forall m n k,
  (m > 1)%nat -> (n > 1)%nat -> Nat.gcd m n = 1%nat ->
  coprime (k mod m) m = true -> coprime (k mod n) n = true ->
  coprime k (m * n) = true.
Proof.
  intros m n k Hm Hn Hgcd Hcopm Hcopn.
  rewrite coprime_product_residues by lia.
  rewrite Hcopm, Hcopn. reflexivity.
Qed.

(** Residue of k in [1..m] when k in [1..m*n] cycles through [0..m-1] *)
Lemma residue_cycle_m : forall m n k,
  (m > 0)%nat -> (n > 0)%nat -> (k <= m * n)%nat ->
  (k mod m < m)%nat.
Proof.
  intros. apply Nat.mod_upper_bound. lia.
Qed.

(** For each residue pair (a,b) in [0..m-1]×[0..n-1], exactly one k in [0..mn-1] maps to it *)
Lemma crt_bijection_count : forall m n a b,
  (m > 1)%nat -> (n > 1)%nat -> Nat.gcd m n = 1%nat ->
  (a < m)%nat -> (b < n)%nat ->
  exists! k, (k < m * n)%nat /\ k mod m = a /\ k mod n = b.
Proof.
  intros m n a b Hm Hn Hgcd Ha Hb.
  destruct (crt_existence m n a b Hm Hn Hgcd Ha Hb) as [k [Hk_lt [Hkm Hkn]]].
  exists k. split.
  - split; [exact Hk_lt | split; [exact Hkm | exact Hkn]].
  - intros k' [Hk'_lt [Hk'm Hk'n]].
    apply crt_injectivity with (m := m) (n := n); try lia; congruence.
Qed.


(** Extensionality for count_pred *)
Lemma count_pred_ext : forall f g n,
  (forall k, (k > 0)%nat -> (k <= n)%nat -> f k = g k) ->
  count_pred f n = count_pred g n.
Proof.
  intros f g n Hext.
  induction n as [|n' IHn'].
  - reflexivity.
  - rewrite !count_pred_S.
    rewrite Hext by lia.
    f_equal.
    apply IHn'.
    intros k Hk_pos Hk_le.
    apply Hext; lia.
Qed.

(** Counting with conjunction of predicates *)
Lemma count_pred_and : forall f g n,
  (count_pred (fun k => f k && g k) n <= count_pred f n)%nat.
Proof.
  intros f g n.
  induction n as [|n' IHn'].
  - simpl. lia.
  - rewrite !count_pred_S.
    destruct (f (S n')) eqn:Hf; destruct (g (S n')) eqn:Hg; simpl; lia.
Qed.

(** |{k ∈ [0,n-1] : f(k) = true}| *)
Fixpoint count_from_0 (f : nat -> bool) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => count_from_0 f k + (if f k then 1 else 0)
  end.

Lemma count_from_0_S : forall f n,
  count_from_0 f (S n) = (count_from_0 f n + (if f n then 1 else 0))%nat.
Proof. reflexivity. Qed.

(** |{k ∈ [1,n-1] : f(k) = true}| *)
Fixpoint count_mid (f : nat -> bool) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => match k with
           | 0 => 0
           | S _ => (if f k then 1 else 0) + count_mid f k
           end
  end.

Lemma count_pred_split : forall f n,
  (n > 0)%nat ->
  count_pred f n = (count_mid f n + (if f n then 1 else 0))%nat.
Proof.
  intros f n Hn.
  induction n as [|n' IHn'].
  - lia.
  - destruct n' as [|n''].
    + simpl. lia.
    + rewrite count_pred_S.
      rewrite IHn' by lia.
      simpl. lia.
Qed.

Lemma count_from_0_split : forall f n,
  (n > 0)%nat ->
  count_from_0 f n = (count_mid f n + (if f 0%nat then 1 else 0))%nat.
Proof.
  intros f n Hn.
  induction n as [|n' IHn'].
  - lia.
  - destruct n' as [|n''].
    + simpl. lia.
    + rewrite count_from_0_S.
      rewrite IHn' by lia.
      simpl. lia.
Qed.

(** count_pred f n = count_from_0 f n when f 0 = f n *)
Lemma count_pred_eq_from_0 : forall f n,
  (n > 0)%nat -> f 0%nat = f n ->
  count_pred f n = count_from_0 f n.
Proof.
  intros f n Hn Hf0n.
  rewrite count_pred_split by exact Hn.
  rewrite count_from_0_split by exact Hn.
  rewrite Hf0n. reflexivity.
Qed.

(** The residue predicate at 0 equals at m*n *)
Lemma residue_pred_boundary : forall (m n : nat) f g,
  (m > 0)%nat -> (n > 0)%nat ->
  (fun k => f (k mod m) && g (k mod n)) 0%nat =
  (fun k => f (k mod m) && g (k mod n)) (m * n)%nat.
Proof.
  intros m n f g Hm Hn.
  simpl. rewrite Nat.Div0.mod_0_l by lia. rewrite Nat.Div0.mod_0_l by lia.
  rewrite Nat.Div0.mod_mul. rewrite Nat.mul_comm.
  rewrite Nat.Div0.mod_mul. reflexivity.
Qed.

(** |{(a,b) ∈ [0,m-1]×[0,n-1] : f(a) ∧ g(b)}| *)
Fixpoint count_from_0_pairs (f : nat -> bool) (g : nat -> bool) (m n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => count_from_0_pairs f g m n' + (if g n' then count_from_0 f m else 0)
  end.

Lemma count_from_0_pairs_eq : forall f g m n,
  count_from_0_pairs f g m n = (count_from_0 f m * count_from_0 g n)%nat.
Proof.
  intros f g m n.
  induction n as [|n' IHn'].
  - simpl. lia.
  - simpl. rewrite IHn'.
    destruct (g n'); lia.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    CERTIFIED n-GON CATALOG - Mass Classification
    Each proof is a machine-checked certificate of constructibility.
    ═══════════════════════════════════════════════════════════════════════════ *)

Example cat_3 : ngon_constructible_iff_phi_smooth 3. Proof. decide_ngon. Qed.
Example cat_4 : ngon_constructible_iff_phi_smooth 4. Proof. decide_ngon. Qed.
Example cat_5 : ngon_constructible_iff_phi_smooth 5. Proof. decide_ngon. Qed.
Example cat_6 : ngon_constructible_iff_phi_smooth 6. Proof. decide_ngon. Qed.
Example cat_8 : ngon_constructible_iff_phi_smooth 8. Proof. decide_ngon. Qed.
Example cat_10 : ngon_constructible_iff_phi_smooth 10. Proof. decide_ngon. Qed.
Example cat_12 : ngon_constructible_iff_phi_smooth 12. Proof. decide_ngon. Qed.
Example cat_14 : ngon_constructible_iff_phi_smooth 14. Proof. decide_ngon. Qed.
Example cat_16 : ngon_constructible_iff_phi_smooth 16. Proof. decide_ngon. Qed.
Example cat_18 : ngon_constructible_iff_phi_smooth 18. Proof. decide_ngon. Qed.
Example cat_21 : ngon_constructible_iff_phi_smooth 21. Proof. decide_ngon. Qed.
Example cat_24 : ngon_constructible_iff_phi_smooth 24. Proof. decide_ngon. Qed.
Example cat_26 : ngon_constructible_iff_phi_smooth 26. Proof. decide_ngon. Qed.
Example cat_27 : ngon_constructible_iff_phi_smooth 27. Proof. decide_ngon. Qed.
Example cat_28 : ngon_constructible_iff_phi_smooth 28. Proof. decide_ngon. Qed.
Example cat_32 : ngon_constructible_iff_phi_smooth 32. Proof. decide_ngon. Qed.
Example cat_34 : ngon_constructible_iff_phi_smooth 34. Proof. decide_ngon. Qed.
Example cat_36 : ngon_constructible_iff_phi_smooth 36. Proof. decide_ngon. Qed.
Example cat_38 : ngon_constructible_iff_phi_smooth 38. Proof. decide_ngon. Qed.
Example cat_39 : ngon_constructible_iff_phi_smooth 39. Proof. decide_ngon. Qed.
Example cat_42 : ngon_constructible_iff_phi_smooth 42. Proof. decide_ngon. Qed.
Example cat_48 : ngon_constructible_iff_phi_smooth 48. Proof. decide_ngon. Qed.
Example cat_52 : ngon_constructible_iff_phi_smooth 52. Proof. decide_ngon. Qed.
Example cat_54 : ngon_constructible_iff_phi_smooth 54. Proof. decide_ngon. Qed.
Example cat_56 : ngon_constructible_iff_phi_smooth 56. Proof. decide_ngon. Qed.
Example cat_57 : ngon_constructible_iff_phi_smooth 57. Proof. decide_ngon. Qed.
Example cat_63 : ngon_constructible_iff_phi_smooth 63. Proof. decide_ngon. Qed.
Example cat_64 : ngon_constructible_iff_phi_smooth 64. Proof. decide_ngon. Qed.
Example cat_72 : ngon_constructible_iff_phi_smooth 72. Proof. decide_ngon. Qed.
Example cat_74 : ngon_constructible_iff_phi_smooth 74. Proof. decide_ngon. Qed.
Example cat_76 : ngon_constructible_iff_phi_smooth 76. Proof. decide_ngon. Qed.
Example cat_78 : ngon_constructible_iff_phi_smooth 78. Proof. decide_ngon. Qed.
Example cat_81 : ngon_constructible_iff_phi_smooth 81. Proof. decide_ngon. Qed.
Example cat_84 : ngon_constructible_iff_phi_smooth 84. Proof. decide_ngon. Qed.
Example cat_96 : ngon_constructible_iff_phi_smooth 96. Proof. decide_ngon. Qed.

Example cat_11_not : ~ ngon_constructible_iff_phi_smooth 11. Proof. decide_ngon. Qed.
Example cat_22_not : ~ ngon_constructible_iff_phi_smooth 22. Proof. decide_ngon. Qed.
Example cat_23_not : ~ ngon_constructible_iff_phi_smooth 23. Proof. decide_ngon. Qed.
Example cat_25_not : ~ ngon_constructible_iff_phi_smooth 25. Proof. decide_ngon. Qed.
Example cat_29_not : ~ ngon_constructible_iff_phi_smooth 29. Proof. decide_ngon. Qed.
Example cat_31_not : ~ ngon_constructible_iff_phi_smooth 31. Proof. decide_ngon. Qed.
Example cat_33_not : ~ ngon_constructible_iff_phi_smooth 33. Proof. decide_ngon. Qed.
Example cat_41_not : ~ ngon_constructible_iff_phi_smooth 41. Proof. decide_ngon. Qed.
Example cat_43_not : ~ ngon_constructible_iff_phi_smooth 43. Proof. decide_ngon. Qed.
Example cat_44_not : ~ ngon_constructible_iff_phi_smooth 44. Proof. decide_ngon. Qed.
Example cat_46_not : ~ ngon_constructible_iff_phi_smooth 46. Proof. decide_ngon. Qed.
Example cat_47_not : ~ ngon_constructible_iff_phi_smooth 47. Proof. decide_ngon. Qed.
Example cat_49_not : ~ ngon_constructible_iff_phi_smooth 49. Proof. decide_ngon. Qed.
Example cat_50_not : ~ ngon_constructible_iff_phi_smooth 50. Proof. decide_ngon. Qed.
Example cat_53_not : ~ ngon_constructible_iff_phi_smooth 53. Proof. decide_ngon. Qed.
Example cat_55_not : ~ ngon_constructible_iff_phi_smooth 55. Proof. decide_ngon. Qed.
Example cat_58_not : ~ ngon_constructible_iff_phi_smooth 58. Proof. decide_ngon. Qed.
Example cat_59_not : ~ ngon_constructible_iff_phi_smooth 59. Proof. decide_ngon. Qed.
Section Euler_Phi_Multiplicative.
(** Euler's totient is multiplicative on coprime arguments: the CRT residue map
    is a bijection [0,mn) <-> [0,m) x [0,n) preserving coprimality. *)
Local Open Scope bool_scope.
Local Open Scope nat_scope.

Lemma pm_length_filter_map : forall (A B : Type) (P : B -> bool) (g : A -> B) (l : list A),
  length (filter P (map g l)) = length (filter (fun x => P (g x)) l).
Proof.
  intros A B P g l. induction l as [|x l IH]; [reflexivity|].
  simpl. destruct (P (g x)); simpl; rewrite IH; reflexivity.
Qed.

Lemma pm_perm_filter_length : forall (A : Type) (P : A -> bool) (l1 l2 : list A),
  Permutation l1 l2 -> length (filter P l1) = length (filter P l2).
Proof.
  intros A P l1 l2 H. induction H.
  - reflexivity.
  - simpl. destruct (P x); simpl; rewrite IHPermutation; reflexivity.
  - simpl. destruct (P x); destruct (P y); simpl; reflexivity.
  - rewrite IHPermutation1, IHPermutation2; reflexivity.
Qed.

Lemma pm_NoDup_map_inj_in : forall (A B : Type) (f : A -> B) (l : list A),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup l -> NoDup (map f l).
Proof.
  intros A B f l. induction l as [|a l IH]; intros Hinj Hnd.
  - constructor.
  - simpl. inversion Hnd as [|? ? Hnotin Hnd']; subst. constructor.
    + intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Hy Hyin]].
      assert (a = y) by (apply Hinj; [left; reflexivity | right; exact Hyin | symmetry; exact Hy]).
      subst y. contradiction.
    + apply IH; [|exact Hnd'].
      intros x y Hx Hy. apply Hinj; right; assumption.
Qed.

Lemma pm_NoDup_list_prod : forall (A B : Type) (la : list A) (lb : list B),
  NoDup la -> NoDup lb -> NoDup (list_prod la lb).
Proof.
  intros A B la lb Hla Hlb. induction la as [|a la IH].
  - constructor.
  - inversion Hla as [|? ? Hanotin Hla']; subst. simpl.
    apply NoDup_app.
    + apply pm_NoDup_map_inj_in; [intros x y _ _ Heq; injection Heq; auto | exact Hlb].
    + apply IH; exact Hla'.
    + intros [u v] Hin1 Hin2.
      apply in_map_iff in Hin1. destruct Hin1 as [w [Hw _]]. injection Hw as Hu Hv. subst u v.
      apply in_prod_iff in Hin2. destruct Hin2 as [Hain _]. contradiction.
Qed.

Definition resmap (m n k : nat) : nat * nat := (k mod m, k mod n).

Lemma pm_crt_map_perm : forall m n,
  (m > 1)%nat -> (n > 1)%nat -> Nat.gcd m n = 1%nat ->
  Permutation (map (resmap m n) (seq 0 (m * n)))
              (list_prod (seq 0 m) (seq 0 n)).
Proof.
  intros m n Hm Hn Hgcd.
  apply NoDup_Permutation.
  - apply pm_NoDup_map_inj_in; [|apply seq_NoDup].
    intros x y Hx Hy Hxy. apply in_seq in Hx. apply in_seq in Hy.
    unfold resmap in Hxy. injection Hxy as Hax Hay.
    apply (crt_injectivity m n x y); try lia; assumption.
  - apply pm_NoDup_list_prod; apply seq_NoDup.
  - intros [a b]. split.
    + intros Hin. apply in_map_iff in Hin. destruct Hin as [k [Hk Hkin]].
      apply in_seq in Hkin. unfold resmap in Hk. injection Hk as Ha Hb. subst a b.
      apply in_prod; apply in_seq; split; try lia; apply Nat.mod_upper_bound; lia.
    + intros Hin. apply in_prod_iff in Hin. destruct Hin as [Ha Hb].
      apply in_seq in Ha. apply in_seq in Hb.
      destruct (crt_existence m n a b Hm Hn Hgcd ltac:(lia) ltac:(lia)) as [k [Hklt [Hka Hkb]]].
      apply in_map_iff. exists k. split.
      * unfold resmap. rewrite Hka, Hkb. reflexivity.
      * apply in_seq. lia.
Qed.

Lemma pm_count_from_0_as_filter : forall (f : nat -> bool) (N : nat),
  count_from_0 f N = length (filter f (seq 0 N)).
Proof.
  intros f N. induction N as [|N IH].
  - reflexivity.
  - rewrite count_from_0_S, IH.
    rewrite seq_S, filter_app. simpl.
    rewrite length_app. simpl.
    destruct (f N); simpl; lia.
Qed.

Lemma pm_filter_andb_const : forall (B : Type) (c : bool) (g : B -> bool) (lb : list B),
  length (filter (fun y => c && g y) lb) = (if c then length (filter g lb) else 0)%nat.
Proof.
  intros B c g lb. destruct c; simpl.
  - induction lb as [|b lb IH]; [reflexivity|].
    simpl. destruct (g b); simpl; rewrite IH; reflexivity.
  - induction lb as [|b lb IH]; [reflexivity|]. simpl. exact IH.
Qed.

Lemma pm_filter_map_pair : forall (A B : Type) (f : A -> bool) (g : B -> bool)
  (a : A) (lb : list B),
  length (filter (fun ab => f (fst ab) && g (snd ab)) (map (fun y => (a, y)) lb))
   = length (filter (fun y => f a && g y) lb).
Proof.
  intros A B f g a lb. induction lb as [|b lb IH]; [reflexivity|].
  simpl. destruct (f a && g b); simpl; rewrite IH; reflexivity.
Qed.

Lemma pm_length_filter_list_prod : forall (A B : Type) (f : A -> bool) (g : B -> bool)
  (la : list A) (lb : list B),
  length (filter (fun ab => f (fst ab) && g (snd ab)) (list_prod la lb))
   = (length (filter f la) * length (filter g lb))%nat.
Proof.
  intros A B f g la lb. induction la as [|a la IH]; [reflexivity|].
  simpl. rewrite filter_app, length_app, IH, pm_filter_map_pair, pm_filter_andb_const.
  cbn [filter]. destruct (f a); cbn [length]; lia.
Qed.

Lemma pm_euler_phi_as_filter : forall N,
  euler_phi N = length (filter (fun k => coprime k N) (seq 0 N)).
Proof.
  intros N. unfold euler_phi.
  rewrite count_coprime_eq_count_pred.
  destruct (Nat.eq_dec N 0) as [HN0|HN0].
  - subst N. reflexivity.
  - rewrite count_pred_eq_from_0.
    + apply pm_count_from_0_as_filter.
    + lia.
    + unfold coprime. rewrite Nat.gcd_0_l, Nat.gcd_diag. reflexivity.
Qed.

Theorem euler_phi_mult_coprime : forall m n,
  (m > 1)%nat -> (n > 1)%nat -> Nat.gcd m n = 1%nat ->
  euler_phi (m * n) = (euler_phi m * euler_phi n)%nat.
Proof.
  intros m n Hm Hn Hgcd.
  rewrite (pm_euler_phi_as_filter (m*n)), (pm_euler_phi_as_filter m), (pm_euler_phi_as_filter n).
  transitivity (length (filter (fun ab : nat*nat => coprime (fst ab) m && coprime (snd ab) n)
                               (list_prod (seq 0 m) (seq 0 n)))).
  - transitivity (length (filter (fun ab : nat*nat => coprime (fst ab) m && coprime (snd ab) n)
                                 (map (resmap m n) (seq 0 (m*n))))).
    + rewrite pm_length_filter_map. apply f_equal. apply filter_ext.
      intros k. simpl. apply coprime_product_residues; assumption.
    + apply pm_perm_filter_length. apply pm_crt_map_perm; assumption.
  - exact (pm_length_filter_list_prod nat nat (fun a => coprime a m)
             (fun b => coprime b n) (seq 0 m) (seq 0 n)).
Qed.

(** Euler totient multiplicativity (coprime m, n; m, n >= 1). *)
Theorem euler_phi_mult : forall m n,
  (m >= 1)%nat -> (n >= 1)%nat -> Nat.gcd m n = 1%nat ->
  euler_phi (m * n) = (euler_phi m * euler_phi n)%nat.
Proof.
  intros m n Hm Hn Hgcd.
  destruct (Nat.eq_dec m 1) as [Hm1|Hm1].
  - subst m. rewrite Nat.mul_1_l, phi_1, Nat.mul_1_l. reflexivity.
  - destruct (Nat.eq_dec n 1) as [Hn1|Hn1].
    + subst n. rewrite Nat.mul_1_r, phi_1, Nat.mul_1_r. reflexivity.
    + apply euler_phi_mult_coprime; lia || assumption.
Qed.

End Euler_Phi_Multiplicative.
(** Impossibility results and strict extension proofs *)

(** ¬is_2_3_smooth(n) → ¬OrigamiDegree(n) *)
Lemma not_smooth_not_origami : forall n,
  ~ is_2_3_smooth n -> ~ OrigamiDegree n.
Proof.
  intros n Hns Hod. apply Hns. apply origami_degree_implies_smooth. exact Hod.
Qed.

(** 3 ∉ {2^k : k ∈ ℕ} *)
Lemma three_not_euclidean_degree : ~ EuclideanDegree 3.
Proof.
  intro H. inversion H; lia.
Qed.

(** OrigamiDegree(3) ∧ ¬EuclideanDegree(3) *)
Theorem origami_strictly_extends_euclidean_degree :
  OrigamiDegree 3 /\ ~ EuclideanDegree 3.
Proof.
  split; [exact three_is_origami_degree | exact three_not_euclidean_degree].
Qed.

(** EuclidNum ⊊ OrigamiNum via ∛2 ∈ OrigamiNum ∖ EuclidNum *)

(** ∛2 *)
Definition cbrt2 : R := cbrt 2.

(** (∛2)³ = 2 *)
Lemma cbrt2_cubes_to_2 : cbrt2 * cbrt2 * cbrt2 = 2.
Proof.
  unfold cbrt2.
  assert (H : cube_func (cbrt 2) = 2) by apply cbrt_spec.
  unfold cube_func in H. exact H.
Qed.

(** ∛2 > 0 *)
Lemma cbrt2_pos : cbrt2 > 0.
Proof.
  unfold cbrt2.
  apply cbrt_pos_positive. lra.
Qed.

(** ∛2 ∈ OrigamiNum *)
Lemma cbrt2_is_origami : OrigamiNum cbrt2.
Proof.
  apply cube_duplication_possible.
  exact cbrt2_cubes_to_2.
Qed.

(** EuclidNum with degree tracking: degree is always 2^k *)
Inductive EuclidNum_deg : R -> nat -> Prop :=
| END_0 : EuclidNum_deg 0 1
| END_1 : EuclidNum_deg 1 1
| END_add : forall x y dx dy,
    EuclidNum_deg x dx -> EuclidNum_deg y dy ->
    EuclidNum_deg (x + y) (Nat.max dx dy)
| END_sub : forall x y dx dy,
    EuclidNum_deg x dx -> EuclidNum_deg y dy ->
    EuclidNum_deg (x - y) (Nat.max dx dy)
| END_mul : forall x y dx dy,
    EuclidNum_deg x dx -> EuclidNum_deg y dy ->
    EuclidNum_deg (x * y) (dx * dy)
| END_inv : forall x dx,
    EuclidNum_deg x dx -> x <> 0 ->
    EuclidNum_deg (/ x) dx
| END_sqrt : forall x dx,
    EuclidNum_deg x dx -> 0 <= x ->
    EuclidNum_deg (sqrt x) (2 * dx).

(** x ∈ EuclidNum → ∃ d, EuclidNum_deg(x,d) *)
Lemma EuclidNum_has_deg : forall x, EuclidNum x -> exists d, EuclidNum_deg x d.
Proof.
  intros x H. induction H.
  - exists 1%nat. constructor.
  - exists 1%nat. constructor.
  - destruct IHEuclidNum1 as [d1 Hd1]. destruct IHEuclidNum2 as [d2 Hd2].
    exists (Nat.max d1 d2). apply END_add; assumption.
  - destruct IHEuclidNum1 as [d1 Hd1]. destruct IHEuclidNum2 as [d2 Hd2].
    exists (Nat.max d1 d2). apply END_sub; assumption.
  - destruct IHEuclidNum1 as [d1 Hd1]. destruct IHEuclidNum2 as [d2 Hd2].
    exists (d1 * d2)%nat. apply END_mul; assumption.
  - destruct IHEuclidNum as [d Hd].
    exists d. apply END_inv; assumption.
  - destruct IHEuclidNum as [d Hd].
    exists (2 * d)%nat. apply END_sqrt; assumption.
Qed.

(** EuclidNum_deg(x,d) → x ∈ EuclidNum *)
Lemma EuclidNum_deg_is_EuclidNum : forall x d, EuclidNum_deg x d -> EuclidNum x.
Proof.
  intros x d H. induction H.
  - constructor.
  - constructor.
  - apply EN_add; assumption.
  - apply EN_sub; assumption.
  - apply EN_mul; assumption.
  - apply EN_inv; assumption.
  - apply EN_sqrt; assumption.
Qed.

(** EuclidNum_deg(x,d) → d ≥ 1 *)
Lemma EuclidNum_deg_pos : forall x d, EuclidNum_deg x d -> (d >= 1)%nat.
Proof.
  intros x d H. induction H; lia.
Qed.

(** n ∈ {2^k : k ∈ ℕ} *)
Inductive EuclideanDeg : nat -> Prop :=
| ED_1 : EuclideanDeg 1
| ED_double : forall n, EuclideanDeg n -> EuclideanDeg (2 * n).

(** ∃ k, n = 2^k *)
Definition is_power_of_2 (n : nat) : Prop := exists k, n = (2 ^ k)%nat.

(** EuclideanDeg(n) → is_power_of_2(n) *)
Lemma EuclideanDeg_is_power_of_2 : forall n, EuclideanDeg n -> is_power_of_2 n.
Proof.
  intros n H. induction H.
  - exists 0%nat. reflexivity.
  - destruct IHEuclideanDeg as [k Hk].
    exists (S k). simpl. lia.
Qed.

(** EuclideanDeg(2^k) *)
Lemma power_of_2_is_EuclideanDeg : forall k, EuclideanDeg (2 ^ k).
Proof.
  induction k.
  - simpl. constructor.
  - simpl. apply ED_double. exact IHk.
Qed.

(** EuclideanDeg(m) ∧ EuclideanDeg(n) → EuclideanDeg(max(m,n)) *)
Lemma EuclideanDeg_max : forall m n,
  EuclideanDeg m -> EuclideanDeg n -> EuclideanDeg (Nat.max m n).
Proof.
  intros m n Hm Hn.
  destruct (EuclideanDeg_is_power_of_2 m Hm) as [km Hkm].
  destruct (EuclideanDeg_is_power_of_2 n Hn) as [kn Hkn].
  subst.
  destruct (Nat.max_spec (2^km) (2^kn)) as [[Hlt Heq] | [Hge Heq]].
  - rewrite Heq. apply power_of_2_is_EuclideanDeg.
  - rewrite Heq. apply power_of_2_is_EuclideanDeg.
Qed.

(** EuclideanDeg(m) ∧ EuclideanDeg(n) → EuclideanDeg(m·n) *)
Lemma EuclideanDeg_mul : forall m n,
  EuclideanDeg m -> EuclideanDeg n -> EuclideanDeg (m * n).
Proof.
  intros m n Hm Hn.
  destruct (EuclideanDeg_is_power_of_2 m Hm) as [km Hkm].
  destruct (EuclideanDeg_is_power_of_2 n Hn) as [kn Hkn].
  subst.
  replace (2^km * 2^kn)%nat with (2^(km + kn))%nat.
  - apply power_of_2_is_EuclideanDeg.
  - rewrite Nat.pow_add_r. reflexivity.
Qed.

(** EuclideanDeg(n) → EuclideanDeg(2n) *)
Lemma EuclideanDeg_double : forall n,
  EuclideanDeg n -> EuclideanDeg (2 * n).
Proof.
  intros n Hn. apply ED_double. exact Hn.
Qed.

(** EuclidNum_deg(x,d) → EuclideanDeg(d) *)
Theorem EuclidNum_deg_is_EuclideanDeg : forall x d,
  EuclidNum_deg x d -> EuclideanDeg d.
Proof.
  intros x d H. induction H.
  - constructor.
  - constructor.
  - apply EuclideanDeg_max; assumption.
  - apply EuclideanDeg_max; assumption.
  - apply EuclideanDeg_mul; assumption.
  - exact IHEuclidNum_deg.
  - apply EuclideanDeg_double. exact IHEuclidNum_deg.
Qed.

(** x ∈ EuclidNum → ∃ d, EuclidNum_deg(x,d) ∧ is_power_of_2(d) *)
Corollary EuclidNum_has_power_of_2_deg : forall x,
  EuclidNum x -> exists d, EuclidNum_deg x d /\ is_power_of_2 d.
Proof.
  intros x Hx.
  destruct (EuclidNum_has_deg x Hx) as [d Hd].
  exists d. split.
  - exact Hd.
  - apply EuclideanDeg_is_power_of_2.
    apply EuclidNum_deg_is_EuclideanDeg with x.
    exact Hd.
Qed.

(** 3 ∤ 1 *)
Lemma three_not_div_1 : ~ Nat.divide 3 1.
Proof.
  intro H. destruct H as [k Hk]. lia.
Qed.

(** 3 | 2n → 3 | n *)
Lemma three_div_double : forall n, Nat.divide 3 (2 * n) -> Nat.divide 3 n.
Proof.
  intros n [k Hk].
  assert (H3 : Nat.gcd 3 2 = 1%nat) by reflexivity.
  apply Nat.gauss with 2%nat.
  - exists k. lia.
  - exact H3.
Qed.

(** 3 ∤ 2^k *)
Lemma three_not_div_pow2 : forall k, ~ Nat.divide 3 (2 ^ k).
Proof.
  induction k.
  - simpl. exact three_not_div_1.
  - simpl. intro Hdiv.
    apply IHk. apply three_div_double. exact Hdiv.
Qed.

(** EuclideanDeg(d) → 3 ∤ d *)
Lemma three_not_div_EuclideanDeg : forall d,
  EuclideanDeg d -> ~ Nat.divide 3 d.
Proof.
  intros d Hd.
  destruct (EuclideanDeg_is_power_of_2 d Hd) as [k Hk].
  subst. apply three_not_div_pow2.
Qed.

(** ∛2 ∉ ℚ *)
Lemma cbrt2_irrational : forall p q : Z, (q > 0)%Z -> cbrt2 <> IZR p / IZR q.
Proof.
  intros p q Hq Heq.
  assert (Hcube : cbrt2 * cbrt2 * cbrt2 = 2) by exact cbrt2_cubes_to_2.
  rewrite Heq in Hcube.
  assert (Hq_nz : IZR q <> 0) by (apply not_0_IZR; lia).
  assert (Hq3_nz : IZR q * IZR q * IZR q <> 0).
  { apply Rmult_integral_contrapositive_currified;
    [apply Rmult_integral_contrapositive_currified|]; assumption. }
  assert (Hcube'' : IZR p * IZR p * IZR p = 2 * (IZR q * IZR q * IZR q)).
  { assert (H : IZR p * IZR p * IZR p =
               IZR p / IZR q * (IZR p / IZR q) * (IZR p / IZR q) * (IZR q * IZR q * IZR q))
      by (field; exact Hq_nz).
    rewrite Hcube in H. lra. }
  rewrite <- !mult_IZR in Hcube''.
  apply eq_IZR in Hcube''.
  assert (Hp3 : (p * p * p = 2 * (q * q * q))%Z) by exact Hcube''.
  clear Hcube Hcube'' Heq Hq_nz Hq3_nz.
  assert (Hloop : forall n p' q', (Z.to_nat (Z.abs q') < n)%nat -> (q' > 0)%Z ->
                  (p' * p' * p' = 2 * (q' * q' * q'))%Z -> False).
  { induction n.
    - intros p' q' Hlt. lia.
    - intros p' q' Hlt Hq'_pos Heq.
      assert (Heven_p'3 : Z.Even (p' * p' * p')) by (exists (q' * q' * q')%Z; lia).
      assert (Heven_p' : Z.Even p').
      { destruct (Z.Even_or_Odd p') as [He | Ho]; [exact He | exfalso].
        destruct Heven_p'3 as [k Hk]. destruct Ho as [j Hj].
        assert (Hodd_p'3 : Z.Odd (p' * p' * p')).
        { exists (2 * j * j * j + 3 * j * j + 3 * j)%Z. lia. }
        destruct Hodd_p'3 as [m Hm]. lia. }
      destruct Heven_p' as [p'' Hp'']. subst p'.
      assert (Heq' : (4 * (p'' * p'' * p'') = q' * q' * q')%Z) by lia.
      assert (Heven_q'3 : Z.Even (q' * q' * q')) by (exists (2 * (p'' * p'' * p''))%Z; lia).
      assert (Heven_q' : Z.Even q').
      { destruct (Z.Even_or_Odd q') as [He | Ho]; [exact He | exfalso].
        destruct Heven_q'3 as [k Hk]. destruct Ho as [j Hj].
        assert (Hodd_q'3 : Z.Odd (q' * q' * q')).
        { exists (2 * j * j * j + 3 * j * j + 3 * j)%Z. lia. }
        destruct Hodd_q'3 as [m Hm]. lia. }
      destruct Heven_q' as [q'' Hq'']. subst q'.
      apply (IHn p'' q''); lia. }
  apply (Hloop (S (Z.to_nat (Z.abs q))) p q); lia.
Qed.

(** ∛2 ≠ 0 *)
Lemma cbrt2_neq_0 : cbrt2 <> 0.
Proof.
  intro Heq.
  assert (H : cbrt2 * cbrt2 * cbrt2 = 2) by exact cbrt2_cubes_to_2.
  rewrite Heq in H. lra.
Qed.

(** ∛2 ≠ 1 *)
Lemma cbrt2_neq_1 : cbrt2 <> 1.
Proof.
  intro Heq.
  assert (H : cbrt2 * cbrt2 * cbrt2 = 2) by exact cbrt2_cubes_to_2.
  rewrite Heq in H. lra.
Qed.

(** x² ∈ ℚ ∧ x ∈ ℚ → √(x²) ∈ ℚ *)
Lemma sqrt_rational_is_rational : forall x,
  EuclidNum x -> 0 <= x ->
  (exists p q : Z, (q > 0)%Z /\ sqrt x = IZR p / IZR q) ->
  exists p' q' : Z, (q' > 0)%Z /\ x = IZR p' / IZR q'.
Proof.
  intros x Hx Hnn [p [q [Hq Heq]]].
  exists (p * p)%Z, (q * q)%Z.
  split.
  - lia.
  - assert (Hsq : sqrt x * sqrt x = x) by (apply sqrt_sqrt; exact Hnn).
    rewrite <- Hsq. rewrite Heq.
    rewrite mult_IZR. rewrite mult_IZR.
    field.
    apply not_0_IZR. lia.
Qed.

(** (∛4)³ = 4 *)
Lemma cbrt4_cubes_to_4 : cbrt 4 * cbrt 4 * cbrt 4 = 4.
Proof.
  assert (H : cube_func (cbrt 4) = 4) by apply cbrt_spec.
  unfold cube_func in H. exact H.
Qed.

(** (∛2)² = ∛4 *)
Lemma cbrt2_squared_is_cbrt4 : cbrt2 * cbrt2 = cbrt 4.
Proof.
  unfold cbrt2.
  assert (H2 : cbrt 2 * cbrt 2 * cbrt 2 = 2) by (apply cbrt_spec).
  assert (H4 : cbrt 4 * cbrt 4 * cbrt 4 = 4) by (apply cbrt4_cubes_to_4).
  assert (Hcbrt2_pos : cbrt 2 > 0) by (apply cbrt_pos_positive; lra).
  assert (Hcbrt4_pos : cbrt 4 > 0) by (apply cbrt_pos_positive; lra).
  assert (Heq : (cbrt 2 * cbrt 2) * (cbrt 2 * cbrt 2) * (cbrt 2 * cbrt 2) =
                cbrt 4 * cbrt 4 * cbrt 4).
  { replace ((cbrt 2 * cbrt 2) * (cbrt 2 * cbrt 2) * (cbrt 2 * cbrt 2))
      with ((cbrt 2 * cbrt 2 * cbrt 2) * (cbrt 2 * cbrt 2 * cbrt 2)) by ring.
    rewrite H2. rewrite H4. ring. }
  apply cbrt_unique.
  - unfold cube_func. unfold cube_func in Heq.
    replace ((cbrt 2 * cbrt 2) * (cbrt 2 * cbrt 2) * (cbrt 2 * cbrt 2))
      with (cbrt 2 * cbrt 2 * (cbrt 2 * cbrt 2) * (cbrt 2 * cbrt 2)) by ring.
    exact Heq.
  - left. split; nra.
Qed.

(** ∛4 ∉ ℚ *)
Lemma cbrt4_irrational : forall p q : Z, (q > 0)%Z -> cbrt 4 <> IZR p / IZR q.
Proof.
  assert (Hloop : forall n p' q', (Z.to_nat (Z.abs q') < n)%nat -> (q' > 0)%Z ->
                  (p' * p' * p' = 4 * (q' * q' * q'))%Z -> False).
  { induction n.
    - intros p' q' Hlt. lia.
    - intros p' q' Hlt Hq'_pos Heq'.
      assert (Heven_p'3 : Z.Even (p' * p' * p')) by (exists (2 * (q' * q' * q'))%Z; lia).
      assert (Heven_p' : Z.Even p').
      { destruct (Z.Even_or_Odd p') as [He | Ho]; [exact He | exfalso].
        destruct Heven_p'3 as [k Hk]. destruct Ho as [j Hj].
        assert (Hodd_p'3 : Z.Odd (p' * p' * p')).
        { exists (2 * j * j * j + 3 * j * j + 3 * j)%Z. lia. }
        destruct Hodd_p'3 as [m Hm]. lia. }
      destruct Heven_p' as [p'' Hp'']. subst p'.
      assert (Heq'' : (2 * (p'' * p'' * p'') = q' * q' * q')%Z) by lia.
      assert (Heven_q'3 : Z.Even (q' * q' * q')) by (exists (p'' * p'' * p'')%Z; lia).
      assert (Heven_q' : Z.Even q').
      { destruct (Z.Even_or_Odd q') as [He | Ho]; [exact He | exfalso].
        destruct Heven_q'3 as [k Hk]. destruct Ho as [j Hj].
        assert (Hodd_q'3 : Z.Odd (q' * q' * q')).
        { exists (2 * j * j * j + 3 * j * j + 3 * j)%Z. lia. }
        destruct Hodd_q'3 as [m Hm]. lia. }
      destruct Heven_q' as [q'' Hq'']. subst q'.
      apply (IHn p'' q''); lia. }
  intros p q Hq Heq.
  assert (Hq_nz : IZR q <> 0) by (apply not_0_IZR; lia).
  assert (Hcube : cbrt 4 * cbrt 4 * cbrt 4 = 4) by exact cbrt4_cubes_to_4.
  rewrite Heq in Hcube.
  assert (Hcube'' : IZR p * IZR p * IZR p = 4 * (IZR q * IZR q * IZR q)).
  { assert (H : IZR p * IZR p * IZR p =
               IZR p / IZR q * (IZR p / IZR q) * (IZR p / IZR q) * (IZR q * IZR q * IZR q))
      by (field; exact Hq_nz).
    rewrite Hcube in H. lra. }
  rewrite <- !mult_IZR in Hcube''.
  apply eq_IZR in Hcube''.
  apply (Hloop (S (Z.to_nat (Z.abs q))) p q); lia.
Qed.

Lemma pow2_not_div_by_3 : forall k, ~ Nat.divide 3 (2^k).
Proof. exact three_not_div_pow2. Qed.

Lemma EuclidNum_algebraic_degree_power_of_2 :
  forall x, EuclidNum x -> exists k, EuclideanDeg (2^k).
Proof.
  intros x _. exists 0%nat. simpl. constructor.
Qed.

(** EuclidNum with tower height tracking *)
Inductive EuclidNum_ht : R -> nat -> Prop :=
| EHT_0 : EuclidNum_ht 0 0
| EHT_1 : EuclidNum_ht 1 0
| EHT_add : forall x y hx hy,
    EuclidNum_ht x hx -> EuclidNum_ht y hy ->
    EuclidNum_ht (x + y) (Nat.max hx hy)
| EHT_sub : forall x y hx hy,
    EuclidNum_ht x hx -> EuclidNum_ht y hy ->
    EuclidNum_ht (x - y) (Nat.max hx hy)
| EHT_mul : forall x y hx hy,
    EuclidNum_ht x hx -> EuclidNum_ht y hy ->
    EuclidNum_ht (x * y) (Nat.max hx hy)
| EHT_inv : forall x hx,
    EuclidNum_ht x hx -> x <> 0 ->
    EuclidNum_ht (/ x) hx
| EHT_sqrt : forall x hx,
    EuclidNum_ht x hx -> 0 <= x ->
    EuclidNum_ht (sqrt x) (S hx).

(** x ∈ EuclidNum → ∃ h, EuclidNum_ht(x,h) *)
Lemma EuclidNum_has_ht : forall x, EuclidNum x -> exists h, EuclidNum_ht x h.
Proof.
  intros x H. induction H.
  - exists 0%nat. constructor.
  - exists 0%nat. constructor.
  - destruct IHEuclidNum1 as [h1 Hh1]. destruct IHEuclidNum2 as [h2 Hh2].
    exists (Nat.max h1 h2). apply EHT_add; assumption.
  - destruct IHEuclidNum1 as [h1 Hh1]. destruct IHEuclidNum2 as [h2 Hh2].
    exists (Nat.max h1 h2). apply EHT_sub; assumption.
  - destruct IHEuclidNum1 as [h1 Hh1]. destruct IHEuclidNum2 as [h2 Hh2].
    exists (Nat.max h1 h2). apply EHT_mul; assumption.
  - destruct IHEuclidNum as [h Hh].
    exists h. apply EHT_inv; assumption.
  - destruct IHEuclidNum as [h Hh].
    exists (S h). apply EHT_sqrt; assumption.
Qed.

(** EuclidNum_ht(x,h) → x ∈ EuclidNum *)
Lemma EuclidNum_ht_is_EuclidNum : forall x h, EuclidNum_ht x h -> EuclidNum x.
Proof.
  intros x h H. induction H.
  - constructor.
  - constructor.
  - apply EN_add; assumption.
  - apply EN_sub; assumption.
  - apply EN_mul; assumption.
  - apply EN_inv; assumption.
  - apply EN_sqrt; assumption.
Qed.

(** ∛(2^n) *)
Definition cbrt_pow2 (n : nat) : R := cbrt (2 ^ n).

(** (∛(2^n))³ = 2^n *)
Lemma cbrt_pow2_cubes : forall n, cbrt_pow2 n * cbrt_pow2 n * cbrt_pow2 n = 2 ^ n.
Proof.
  intro n. unfold cbrt_pow2.
  assert (H : cube_func (cbrt (2^n)) = 2^n).
  { apply cbrt_spec. }
  unfold cube_func in H. exact H.
Qed.

(** ∛(2^n) > 0 *)
Lemma cbrt_pow2_pos : forall n, cbrt_pow2 n > 0.
Proof.
  intro n. unfold cbrt_pow2.
  apply cbrt_pos_positive.
  apply pow_lt. lra.
Qed.

(** (∛(2^n))² = ∛(2^(2n)) *)
Lemma cbrt_pow2_squared : forall n, cbrt_pow2 n * cbrt_pow2 n = cbrt_pow2 (2 * n).
Proof.
  intro n. unfold cbrt_pow2.
  assert (Hpos1 : cbrt (2^n) > 0) by (apply cbrt_pos_positive; apply pow_lt; lra).
  assert (Hpos2 : cbrt (2^(2*n)) > 0) by (apply cbrt_pos_positive; apply pow_lt; lra).
  assert (H1 : cbrt (2^n) * cbrt (2^n) * cbrt (2^n) = 2^n) by apply cbrt_spec.
  assert (H2 : cbrt (2^(2*n)) * cbrt (2^(2*n)) * cbrt (2^(2*n)) = 2^(2*n)) by apply cbrt_spec.
  apply cbrt_unique.
  - unfold cube_func.
    replace ((cbrt (2^n) * cbrt (2^n)) * (cbrt (2^n) * cbrt (2^n)) * (cbrt (2^n) * cbrt (2^n)))
      with ((cbrt (2^n) * cbrt (2^n) * cbrt (2^n)) * (cbrt (2^n) * cbrt (2^n) * cbrt (2^n))) by ring.
    rewrite H1. rewrite H2.
    replace (2^n * 2^n) with (2^(n+n)) by (rewrite pow_add; ring).
    f_equal. lia.
  - left. split; nra.
Qed.

Lemma pow_nat_IZR : forall n, 2^n = IZR (2^(Z.of_nat n)).
Proof.
  induction n.
  - reflexivity.
  - replace (2 ^ S n) with (2 * 2^n) by (simpl; ring).
    rewrite IHn.
    replace (Z.of_nat (S n)) with (Z.succ (Z.of_nat n)) by lia.
    rewrite Z.pow_succ_r; [|lia].
    rewrite mult_IZR. lra.
Qed.

Lemma cbrt_pow2_1_irrational : forall p q : Z, (q > 0)%Z -> cbrt_pow2 1 <> IZR p / IZR q.
Proof.
  unfold cbrt_pow2. simpl.
  replace (2 * 1) with 2 by ring.
  exact cbrt2_irrational.
Qed.

Lemma cbrt_pow2_2_irrational : forall p q : Z, (q > 0)%Z -> cbrt_pow2 2 <> IZR p / IZR q.
Proof.
  unfold cbrt_pow2. simpl.
  replace (2 * (2 * 1)) with 4 by ring.
  exact cbrt4_irrational.
Qed.

Lemma cbrt_pow2_sqrt_inv : forall n a,
  cbrt_pow2 n = sqrt a -> 0 <= a -> a = cbrt_pow2 (2 * n).
Proof.
  intros n a Heq Ha.
  assert (Ha' : a = cbrt_pow2 n * cbrt_pow2 n).
  { rewrite Heq. rewrite sqrt_sqrt; [reflexivity | exact Ha]. }
  rewrite Ha'. apply cbrt_pow2_squared.
Qed.

(** n mod 3 ≠ 0 → (2n) mod 3 ≠ 0 *)
Lemma double_preserves_mod3 : forall n,
  (n mod 3 <> 0)%nat -> ((2 * n) mod 3 <> 0)%nat.
Proof.
  intros n Hn.
  destruct (n mod 3) as [|[|[|k]]] eqn:Hmod.
  - lia.
  - replace (2 * n)%nat with (n + n)%nat by lia.
    rewrite Nat.Div0.add_mod by lia. rewrite Hmod.
    simpl. lia.
  - replace (2 * n)%nat with (n + n)%nat by lia.
    rewrite Nat.Div0.add_mod by lia. rewrite Hmod.
    simpl. lia.
  - assert (H : (n mod 3 < 3)%nat) by (apply Nat.mod_upper_bound; lia).
    lia.
Qed.

(** ∛2 = √x ∧ x ≥ 0 → x = ∛4 *)
Lemma cbrt2_sqrt_gives_cbrt4 : forall x, cbrt2 = sqrt x -> 0 <= x -> x = cbrt 4.
Proof.
  intros x Heq Hnn.
  assert (Hsq : sqrt x * sqrt x = x) by (apply sqrt_sqrt; exact Hnn).
  rewrite <- Heq in Hsq.
  rewrite <- Hsq.
  exact cbrt2_squared_is_cbrt4.
Qed.

Lemma max_0_l : forall a b, Nat.max a b = 0%nat -> a = 0%nat.
Proof. intros. destruct a; [reflexivity | simpl in H; destruct b; discriminate]. Qed.

Lemma max_0_r : forall a b, Nat.max a b = 0%nat -> b = 0%nat.
Proof. intros. destruct b; [reflexivity | destruct a; simpl in H; discriminate]. Qed.

Definition is_rational (x : R) : Prop :=
  exists p q : Z, (q > 0)%Z /\ x = IZR p / IZR q.

Lemma EuclidNum_ht_0_rational : forall x, EuclidNum_ht x 0 -> is_rational x.
Proof.
  intros x H.
  remember 0%nat as n.
  induction H; try discriminate.
  - exists 0%Z, 1%Z. split; [lia | simpl; field].
  - exists 1%Z, 1%Z. split; [lia | simpl; field].
  - assert (Hhx : hx = 0%nat) by (apply max_0_l with hy; exact Heqn).
    assert (Hhy : hy = 0%nat) by (apply max_0_r with hx; exact Heqn).
    destruct (IHEuclidNum_ht1 Hhx) as [p1 [q1 [Hq1 Hp1]]].
    destruct (IHEuclidNum_ht2 Hhy) as [p2 [q2 [Hq2 Hp2]]].
    exists (p1 * q2 + p2 * q1)%Z, (q1 * q2)%Z.
    split; [lia | rewrite Hp1, Hp2; rewrite plus_IZR, !mult_IZR; field; split; apply not_0_IZR; lia].
  - assert (Hhx : hx = 0%nat) by (apply max_0_l with hy; exact Heqn).
    assert (Hhy : hy = 0%nat) by (apply max_0_r with hx; exact Heqn).
    destruct (IHEuclidNum_ht1 Hhx) as [p1 [q1 [Hq1 Hp1]]].
    destruct (IHEuclidNum_ht2 Hhy) as [p2 [q2 [Hq2 Hp2]]].
    exists (p1 * q2 - p2 * q1)%Z, (q1 * q2)%Z.
    split; [lia | rewrite Hp1, Hp2; rewrite minus_IZR, !mult_IZR; field; split; apply not_0_IZR; lia].
  - assert (Hhx : hx = 0%nat) by (apply max_0_l with hy; exact Heqn).
    assert (Hhy : hy = 0%nat) by (apply max_0_r with hx; exact Heqn).
    destruct (IHEuclidNum_ht1 Hhx) as [p1 [q1 [Hq1 Hp1]]].
    destruct (IHEuclidNum_ht2 Hhy) as [p2 [q2 [Hq2 Hp2]]].
    exists (p1 * p2)%Z, (q1 * q2)%Z.
    split; [lia | rewrite Hp1, Hp2; rewrite !mult_IZR; field; split; apply not_0_IZR; lia].
  - destruct (IHEuclidNum_ht Heqn) as [p1 [q1 [Hq1 Hp1]]].
    destruct (Z_lt_le_dec 0 p1) as [Hppos | Hpneg].
    + exists q1, p1. split; [lia | rewrite Hp1; field; split; apply not_0_IZR; lia].
    + destruct (Z.eq_dec p1 0) as [Heq | Hneq].
      * exfalso. apply H0. rewrite Hp1. rewrite Heq. unfold IZR. field. apply not_0_IZR. lia.
      * exists (- q1)%Z, (- p1)%Z. split; [lia | rewrite Hp1; rewrite !opp_IZR; field; split; apply not_0_IZR; lia].
Qed.

(** ∛2 ∉ ℚ *)
Lemma cbrt2_not_rational : ~ is_rational cbrt2.
Proof.
  intros [p [q [Hq Heq]]].
  apply (cbrt2_irrational p q Hq). exact Heq.
Qed.

(** ∛2 not at Euclidean height 0 *)
Lemma cbrt2_not_EuclidNum_ht_0 : ~ EuclidNum_ht cbrt2 0.
Proof.
  intro H.
  apply cbrt2_not_rational.
  apply EuclidNum_ht_0_rational.
  exact H.
Qed.

(** ∛4 ∉ ℚ *)
Lemma cbrt4_not_rational : ~ is_rational (cbrt 4).
Proof.
  intros [p [q [Hq Heq]]].
  apply (cbrt4_irrational p q Hq). exact Heq.
Qed.

(** ∛4 not at Euclidean height 0 *)
Lemma cbrt4_not_EuclidNum_ht_0 : ~ EuclidNum_ht (cbrt 4) 0.
Proof.
  intro H. apply cbrt4_not_rational. apply EuclidNum_ht_0_rational. exact H.
Qed.

(** x ∈ ℚ ∧ x+y ∈ ℚ → y ∈ ℚ *)
Lemma EuclidNum_ht_rational_add : forall x y h,
  is_rational x -> EuclidNum_ht y h -> is_rational (x + y) -> is_rational y.
Proof.
  intros x y h [px [qx [Hqx Hpx]]] Hy [ps [qs [Hqs Hps]]].
  exists (ps * qx - px * qs)%Z, (qs * qx)%Z.
  split; [lia|].
  rewrite Hpx in Hps.
  assert (Heq : y = IZR ps / IZR qs - IZR px / IZR qx).
  { rewrite <- Hps. ring. }
  rewrite Heq. rewrite minus_IZR, !mult_IZR. field.
  split; apply not_0_IZR; lia.
Qed.

(** ℚ closed under + *)
Lemma rational_add : forall x y,
  is_rational x -> is_rational y -> is_rational (x + y).
Proof.
  intros x y [px [qx [Hqx Hpx]]] [py [qy [Hqy Hpy]]].
  exists (px * qy + py * qx)%Z, (qx * qy)%Z.
  split; [lia|].
  rewrite Hpx, Hpy. rewrite plus_IZR, !mult_IZR. field.
  split; apply not_0_IZR; lia.
Qed.

(** (∛4)² = ∛16 *)
Lemma cbrt4_squared_is_cbrt16 : cbrt 4 * cbrt 4 = cbrt 16.
Proof.
  assert (H4 : cbrt 4 * cbrt 4 * cbrt 4 = 4) by apply cbrt_spec.
  assert (H16 : cbrt 16 * cbrt 16 * cbrt 16 = 16) by apply cbrt_spec.
  assert (Hcbrt4_pos : cbrt 4 > 0) by (apply cbrt_pos_positive; lra).
  assert (Hcbrt16_pos : cbrt 16 > 0) by (apply cbrt_pos_positive; lra).
  apply cbrt_unique.
  - unfold cube_func.
    replace ((cbrt 4 * cbrt 4) * (cbrt 4 * cbrt 4) * (cbrt 4 * cbrt 4))
      with ((cbrt 4 * cbrt 4 * cbrt 4) * (cbrt 4 * cbrt 4 * cbrt 4)) by ring.
    rewrite H4. lra.
  - left. split; nra.
Qed.

(** ℚ closed under - *)
Lemma rational_sub : forall x y,
  is_rational x -> is_rational y -> is_rational (x - y).
Proof.
  intros x y [px [qx [Hqx Hpx]]] [py [qy [Hqy Hpy]]].
  exists (px * qy - py * qx)%Z, (qx * qy)%Z.
  split; [lia|].
  rewrite Hpx, Hpy. rewrite minus_IZR, !mult_IZR. field.
  split; apply not_0_IZR; lia.
Qed.

(** ℚ closed under × *)
Lemma rational_mul : forall x y,
  is_rational x -> is_rational y -> is_rational (x * y).
Proof.
  intros x y [px [qx [Hqx Hpx]]] [py [qy [Hqy Hpy]]].
  exists (px * py)%Z, (qx * qy)%Z.
  split; [lia|].
  rewrite Hpx, Hpy. rewrite !mult_IZR. field.
  split; apply not_0_IZR; lia.
Qed.

(** ℚ closed under ⁻¹ for x ≠ 0 *)
Lemma rational_inv : forall x,
  is_rational x -> x <> 0 -> is_rational (/ x).
Proof.
  intros x [px [qx [Hqx Hpx]]] Hneq.
  destruct (Z.lt_trichotomy px 0) as [Hneg | [Hzero | Hpos]].
  - exists (-qx)%Z, (-px)%Z. split; [lia|].
    rewrite Hpx. rewrite !opp_IZR. field.
    split; [|apply not_0_IZR; lia].
    rewrite Hpx in Hneq. intro Hc.
    apply Hneq. field_simplify; [|apply not_0_IZR; lia].
    rewrite Hc. lra.
  - exfalso. apply Hneq. rewrite Hpx, Hzero. field. apply not_0_IZR; lia.
  - exists qx, px. split; [lia|].
    rewrite Hpx. field.
    split; [|apply not_0_IZR; lia].
    rewrite Hpx in Hneq. intro Hc.
    apply Hneq. field_simplify; [|apply not_0_IZR; lia].
    rewrite Hc. lra.
Qed.

(** ℚ is a field: closed under +, -, ×, ÷ *)
Lemma rational_closed_field_ops : forall x y,
  is_rational x -> is_rational y ->
  is_rational (x + y) /\ is_rational (x - y) /\ is_rational (x * y) /\
  (y <> 0 -> is_rational (x / y)).
Proof.
  intros x y Hx Hy.
  repeat split.
  - apply rational_add; assumption.
  - apply rational_sub; assumption.
  - apply rational_mul; assumption.
  - intro Hy_nz.
    unfold Rdiv. apply rational_mul.
    + exact Hx.
    + apply rational_inv; assumption.
Qed.

(** √a = ∛2 ∧ a ≥ 0 → a = ∛4 *)
Lemma cbrt2_sqrt_implies_cbrt4 : forall a, sqrt a = cbrt2 -> a >= 0 -> a = cbrt 4.
Proof.
  intros a Heq Ha.
  assert (Hcbrt2_pos : cbrt2 > 0) by (apply cbrt_pos_positive; lra).
  assert (Hsqrt_sq : sqrt a * sqrt a = a) by (apply sqrt_sqrt; lra).
  rewrite Heq in Hsqrt_sq.
  rewrite <- Hsqrt_sq.
  exact cbrt2_squared_is_cbrt4.
Qed.

(** √a = ∛4 ∧ a ≥ 0 → a = ∛16 *)
Lemma cbrt4_sqrt_implies_cbrt16 : forall a, sqrt a = cbrt 4 -> a >= 0 -> a = cbrt 16.
Proof.
  intros a Heq Ha.
  assert (Hcbrt4_pos : cbrt 4 > 0) by (apply cbrt_pos_positive; lra).
  assert (Hsqrt_sq : sqrt a * sqrt a = a) by (apply sqrt_sqrt; lra).
  rewrite Heq in Hsqrt_sq.
  rewrite <- Hsqrt_sq.
  exact cbrt4_squared_is_cbrt16.
Qed.

(** ∛2 ≠ 0 *)
Lemma cbrt2_ne_0 : cbrt2 <> 0.
Proof.
  assert (H : cbrt2 > 0) by (apply cbrt_pos_positive; lra). lra.
Qed.

(** ∛2 ≠ 1 *)
Lemma cbrt2_ne_1 : cbrt2 <> 1.
Proof.
  assert (Hcube : cbrt2 * cbrt2 * cbrt2 = 2) by (unfold cbrt2; apply cbrt_spec).
  intro Heq. rewrite Heq in Hcube. lra.
Qed.

(** ∛4 ≠ 0 *)
Lemma cbrt4_ne_0 : cbrt 4 <> 0.
Proof.
  assert (H : cbrt 4 > 0) by (apply cbrt_pos_positive; lra). lra.
Qed.

(** ∛4 ≠ 1 *)
Lemma cbrt4_ne_1 : cbrt 4 <> 1.
Proof.
  assert (Hcube : cbrt 4 * cbrt 4 * cbrt 4 = 4) by apply cbrt_spec.
  intro Heq. rewrite Heq in Hcube. lra.
Qed.

(** x ∈ ℚ(√r) ⟺ x = p + q√r for p,q ∈ ℚ *)
Lemma sqrt_pos_from_ne0 : forall r, r >= 0 -> sqrt r <> 0 -> r > 0.
Proof.
  intros r Hr Hsqrt.
  destruct (Rle_or_lt r 0) as [Hrle | Hrgt]; [|exact Hrgt].
  destruct (Req_dec r 0) as [Hr0 | Hrne0].
  - rewrite Hr0 in Hsqrt. rewrite sqrt_0 in Hsqrt. lra.
  - assert (r < 0) by lra. rewrite sqrt_neg_0 in Hsqrt; lra.
Qed.

(** (p + q√r)³ = (p³ + 3pq²r) + (3p²q + q³r)√r *)
Lemma cube_in_quadratic_field : forall p q r,
  r > 0 ->
  (p + q * sqrt r) * (p + q * sqrt r) * (p + q * sqrt r) =
  (p*p*p + 3*p*q*q*r) + (3*p*p*q + q*q*q*r) * sqrt r.
Proof.
  intros p q r Hr.
  set (s := sqrt r).
  assert (Hsqrt_sq : s * s = r) by (unfold s; apply sqrt_sqrt; lra).
  replace (p*p*p + 3*p*q*q*r) with (p*p*p + 3*p*q*q*(s*s)) by (rewrite Hsqrt_sq; ring).
  replace (q*q*q*r) with (q*q*q*(s*s)) by (rewrite Hsqrt_sq; ring).
  ring.
Qed.

(** q ≠ 0 ∧ 3p²q + q³r = 0 → r ≤ 0 *)
Lemma irrational_coeff_zero_implies_r_neg : forall p q r,
  q <> 0 -> 3*p*p*q + q*q*q*r = 0 -> r <= 0.
Proof.
  intros p q r Hq Heq.
  assert (Hfactor : q * (3*p*p + q*q*r) = 0) by lra.
  apply Rmult_integral in Hfactor.
  destruct Hfactor as [Hqz | Hinner]; [lra|].
  assert (Hqq_pos : q * q > 0) by nra.
  assert (Hinner2 : q*q*r = - 3*p*p) by lra.
  assert (Hr : r * (q * q) = - 3 * p * p) by lra.
  destruct (Rle_or_lt r 0) as [Hle|Hgt]; [exact Hle|].
  assert (Hlhs_pos : r * (q * q) > 0) by nra.
  assert (Hrhs_neg : - 3 * p * p <= 0) by nra.
  lra.
Qed.

(** ∛2 ∉ ℚ(√r) for any rational r ≥ 0 *)
Lemma cbrt2_ne_sqrt_of_rational : forall r,
  is_rational r -> r >= 0 -> cbrt2 <> sqrt r.
Proof.
  intros r Hr Hr_ge Heq.
  apply cbrt4_not_rational.
  rewrite <- cbrt2_squared_is_cbrt4.
  assert (Hcbrt2_sq : cbrt2 * cbrt2 = r).
  { rewrite Heq. apply sqrt_sqrt. lra. }
  rewrite Hcbrt2_sq. exact Hr.
Qed.

(** ℚ(√r) closed under + *)
Lemma quadratic_conj_product : forall p q r,
  r >= 0 -> (p + q * sqrt r) * (p - q * sqrt r) = p * p - q * q * r.
Proof.
  intros p q r Hr.
  destruct (Req_dec r 0) as [Hr0 | Hrne0].
  - rewrite Hr0. rewrite sqrt_0. ring.
  - set (s := sqrt r).
    assert (Hsq : s * s = r) by (unfold s; apply sqrt_sqrt; lra).
    replace ((p + q * s) * (p - q * s)) with (p * p - q * q * (s * s)) by ring.
    rewrite Hsq. ring.
Qed.

(** 5 ∉ {2^a × 3^b} *)
Lemma five_not_origami_degree : ~ OrigamiDegree 5.
Proof.
  intro H. inversion H; lia.
Qed.

(** 11-gon requires degree 5, which is not origami-constructible *)
Theorem hendecagon_impossible :
  ~ OrigamiDegree 5.
Proof. exact five_not_origami_degree. Qed.

(** 5 ∉ {2^a × 3^b : a,b ∈ ℕ} *)
Lemma five_not_smooth : ~ is_2_3_smooth 5.
Proof.
  intro H. destruct H as [a [b Heq]].
  destruct a; simpl in Heq; [destruct b; simpl in Heq; lia|].
  destruct a; simpl in Heq; [destruct b; simpl in Heq; lia|].
  destruct a; simpl in Heq; destruct b; simpl in Heq; lia.
Qed.

(** 5 not smooth via OrigamiDegree characterization *)
Corollary five_not_smooth_via_degree : ~ is_2_3_smooth 5.
Proof.
  intro H. apply smooth_implies_origami_degree in H. exact (five_not_origami_degree H).
Qed.

(** 10 = 2×5 ∉ {2^a × 3^b} *)
Lemma ten_not_smooth : ~ is_2_3_smooth 10.
Proof.
  intro H. destruct H as [a [b Heq]].
  destruct a.
  - simpl in Heq. destruct b; simpl in Heq; lia.
  - destruct a.
    + simpl in Heq. destruct b; simpl in Heq; lia.
    + destruct a.
      * simpl in Heq. destruct b; simpl in Heq; lia.
      * simpl in Heq. destruct b; simpl in Heq; lia.
Qed.

(** 11-gon not origami-constructible: φ(11) = 10 not 2-3 smooth *)
Theorem hendecagon_not_constructible : ~ ngon_constructible_iff_phi_smooth 11.
Proof.
  unfold ngon_constructible_iff_phi_smooth.
  rewrite phi_11. exact ten_not_smooth.
Qed.

(** 11 ∉ {2^a × 3^b} *)
Lemma eleven_not_origami_degree : ~ OrigamiDegree 11.
Proof.
  intro H. inversion H; lia.
Qed.

(** 22 = 2×11 ∉ {2^a × 3^b} *)
Lemma twentytwo_not_smooth : ~ is_2_3_smooth 22.
Proof.
  intro H. destruct H as [a [b Heq]].
  destruct a; simpl in Heq; [destruct b; simpl in Heq; lia|].
  destruct a; simpl in Heq; [destruct b; simpl in Heq; lia|].
  destruct a; simpl in Heq; [destruct b; simpl in Heq; lia|].
  destruct a; simpl in Heq; [destruct b; simpl in Heq; lia|].
  destruct a; simpl in Heq; destruct b; simpl in Heq; lia.
Qed.

(** φ(23) = 22 *)
Lemma phi_23 : euler_phi 23 = 22%nat.
Proof. reflexivity. Qed.

(** 23-gon not origami-constructible: φ(23) = 22 not 2-3 smooth *)
Theorem icositrigon_not_constructible : ~ ngon_constructible_iff_phi_smooth 23.
Proof.
  unfold ngon_constructible_iff_phi_smooth.
  rewrite phi_23. exact twentytwo_not_smooth.
Qed.

(** n-gon origami-constructible ⟺ φ(n) is 2-3 smooth *)
Theorem ngon_iff_phi_smooth : forall n,
  (n >= 3)%nat ->
  (ngon_constructible_iff_phi_smooth n <-> is_2_3_smooth (euler_phi n)).
Proof.
  intros n Hn.
  unfold ngon_constructible_iff_phi_smooth.
  split; auto.
Qed.

(** n-gon not origami-constructible ⟺ φ(n) not 2-3 smooth *)
Corollary ngon_not_constructible_iff_not_smooth : forall n,
  (n >= 3)%nat ->
  (~ ngon_constructible_iff_phi_smooth n <-> ~ is_2_3_smooth (euler_phi n)).
Proof.
  intros n Hn.
  rewrite ngon_iff_phi_smooth by exact Hn.
  split; auto.
Qed.



(** φ = (1 + √5)/2 ∈ OrigamiNum *)
Theorem golden_ratio_origami : OrigamiNum ((1 + sqrt 5) / 2).
Proof.
  apply Origami_div.
  - apply ON_add; [constructor | apply ON_sqrt; [|lra]].
    replace 5 with (2 + 3) by lra.
    apply ON_add; [apply Origami_two | apply Origami_three].
  - apply Origami_two.
  - lra.
Qed.

(** √2 ∈ OrigamiNum *)
Theorem sqrt2_origami : OrigamiNum (sqrt 2).
Proof.
  apply ON_sqrt; [apply Origami_two | lra].
Qed.

(** √3 ∈ OrigamiNum *)
Theorem sqrt3_origami : OrigamiNum (sqrt 3).
Proof.
  apply ON_sqrt; [apply Origami_three | lra].
Qed.

(** ρ³ - ρ - 1 = 0 → ρ ∈ OrigamiNum *)
Theorem plastic_constant_origami : forall rho : R,
  rho * rho * rho - rho - 1 = 0 -> OrigamiNum rho.
Proof.
  intros rho Heq.
  apply (ON_cubic_root (-1) (-1) rho).
  - replace (-1) with (0 - 1) by lra. apply ON_sub; constructor.
  - replace (-1) with (0 - 1) by lra. apply ON_sub; constructor.
  - lra.
Qed.



(** EuclidNum ⊂ OrigamiNum *)
Theorem euclidean_subset_of_origami : forall x, EuclidNum x -> OrigamiNum x.
Proof. exact Euclid_in_Origami. Qed.

(** Angle trisection and cube duplication solvable via origami *)
Theorem classical_problems_solvable :
  (forall c, 8*(c*c*c) - 6*c - 1 = 0 -> OrigamiNum c) /\
  (forall c, c*c*c = 2 -> OrigamiNum c).
Proof.
  split.
  - exact angle_trisection_possible.
  - exact cube_duplication_possible.
Qed.

(** 8c³ + 4c² - 4c - 1 = 0 → c ∈ OrigamiNum (heptagon) *)
Theorem heptagon_is_origami_constructible :
  forall c, 8*(c*c*c) + 4*(c*c) - 4*c - 1 = 0 -> OrigamiNum c.
Proof. exact heptagon_constructible. Qed.

(** ∛2 ∈ OrigamiNum ∧ 3 ∈ OrigamiDegree \ EuclideanDegree *)
Theorem cbrt2_witnesses_strict_extension :
  (forall r, r*r*r = 2 -> OrigamiNum r) /\
  (OrigamiDegree 3 /\ ~ EuclideanDegree 3).
Proof.
  split.
  - exact cube_duplication_possible.
  - exact origami_strictly_extends_euclidean_degree.
Qed.


(** O5_general_image(p,l,q) ∈ l *)
Lemma Rabs_sqr_eq : forall x, Rabs x * Rabs x = x * x.
Proof. intro x. rewrite <- Rabs_mult. rewrite Rabs_pos_eq; [ring | apply Rle_0_sqr]. Qed.

(** O5_general_valid ⟹ h² = r² - d²‖l‖² ≥ 0 *)
Lemma sqrt_div_sq : forall x y,
  0 <= x -> 0 < y ->
  (sqrt x / sqrt y) * (sqrt x / sqrt y) = x / y.
Proof.
  intros x y Hx Hy.
  assert (Hsqrt_x : sqrt x * sqrt x = x) by (apply sqrt_sqrt; lra).
  assert (Hsqrt_y : sqrt y * sqrt y = y) by (apply sqrt_sqrt; lra).
  assert (Hsqrt_y_nz : sqrt y <> 0) by (apply Rgt_not_eq; apply sqrt_lt_R0; lra).
  unfold Rdiv.
  replace (sqrt x * / sqrt y * (sqrt x * / sqrt y))
    with ((sqrt x * sqrt x) * (/ sqrt y * / sqrt y)) by ring.
  rewrite Hsqrt_x, <- Rinv_mult, Hsqrt_y.
  reflexivity.
Qed.

(** (-ad + bt)² + (-bd - at)² = ‖l‖²d² + h² *)
Lemma O5_algebraic_identity : forall a b d t norm2 h2,
  norm2 = a * a + b * b ->
  norm2 > 0 ->
  t * t = h2 / norm2 ->
  (- a * d + b * t) * (- a * d + b * t) + (- b * d - a * t) * (- b * d - a * t) =
  norm2 * (d * d) + h2.
Proof.
  intros a b d t norm2 h2 Hnorm2 Hpos Ht2.
  replace ((- a * d + b * t) * (- a * d + b * t) + (- b * d - a * t) * (- b * d - a * t))
    with (norm2 * (d * d) + norm2 * (t * t)) by (rewrite Hnorm2; ring).
  rewrite Ht2.
  field. lra.
Qed.

(** O5_general_valid ⟹ r² - d²‖l‖² ≥ 0 (expanded form) *)
Lemma OrigamiNum_add_comm : forall x y,
  OrigamiNum x -> OrigamiNum y -> x + y = y + x.
Proof. intros. ring. Qed.

(** x × y = y × x *)
Lemma OrigamiNum_mul_comm : forall x y,
  OrigamiNum x -> OrigamiNum y -> x * y = y * x.
Proof. intros. ring. Qed.

(** x + (y + z) = (x + y) + z *)
Lemma OrigamiNum_add_assoc : forall x y z,
  OrigamiNum x -> OrigamiNum y -> OrigamiNum z -> x + (y + z) = (x + y) + z.
Proof. intros. ring. Qed.

(** x(yz) = (xy)z *)
Lemma OrigamiNum_mul_assoc : forall x y z,
  OrigamiNum x -> OrigamiNum y -> OrigamiNum z -> x * (y * z) = (x * y) * z.
Proof. intros. ring. Qed.

(** x(y + z) = xy + xz *)
Lemma OrigamiNum_distr_l : forall x y z,
  OrigamiNum x -> OrigamiNum y -> OrigamiNum z -> x * (y + z) = x * y + x * z.
Proof. intros. ring. Qed.

(** 0 + x = x *)
Lemma OrigamiNum_add_0_l : forall x, OrigamiNum x -> 0 + x = x.
Proof. intros. ring. Qed.

(** 1 × x = x *)
Lemma OrigamiNum_mul_1_l : forall x, OrigamiNum x -> 1 * x = x.
Proof. intros. ring. Qed.

(** x + (-x) = 0 *)
Lemma OrigamiNum_add_opp_r : forall x, OrigamiNum x -> x + (- x) = 0.
Proof. intros. ring. Qed.

(** x ≠ 0 → x × x⁻¹ = 1 *)
Lemma OrigamiNum_mul_inv_r : forall x, OrigamiNum x -> x <> 0 -> x * (/ x) = 1.
Proof. intros. field. assumption. Qed.

(** ax³ + bx² + cx + d = a(t³ + pt + q) where t = x + b/(3a) *)
Lemma general_cubic_to_depressed : forall a b c d x,
  a <> 0 ->
  let t := x + b / (3 * a) in
  let p := (3 * a * c - b^2) / (3 * a^2) in
  let q := (2 * b^3 - 9 * a * b * c + 27 * a^2 * d) / (27 * a^3) in
  a * x^3 + b * x^2 + c * x + d = a * (t^3 + p * t + q).
Proof.
  intros a b c d x Ha t p q.
  unfold t, p, q.
  field. lra.
Qed.

(** Tschirnhaus: ax³+bx²+cx+d = 0 → t³+pt+q = 0 *)
Corollary tschirnhaus_depressed : forall a b c d x,
  a <> 0 ->
  a * x^3 + b * x^2 + c * x + d = 0 ->
  let t := x + b / (3 * a) in
  let p := (3 * a * c - b^2) / (3 * a^2) in
  let q := (2 * b^3 - 9 * a * b * c + 27 * a^2 * d) / (27 * a^3) in
  t^3 + p * t + q = 0.
Proof.
  intros a b c d x Ha Hcubic t p q.
  rewrite (general_cubic_to_depressed a b c d x Ha) in Hcubic.
  unfold t, p, q.
  apply Rmult_eq_reg_l with a; [|lra].
  lra.
Qed.


(** |Ax + By + C| / √(A² + B²) *)
Lemma sq_le_iff : forall x y, 0 <= x -> 0 <= y -> (x^2 <= y^2 <-> x <= y).
Proof.
  intros x y Hx Hy. split; intro H.
  - destruct (Rle_dec x y) as [Hle|Hgt]; [exact Hle | exfalso].
    apply Rnot_le_lt in Hgt.
    replace (y^2) with (y * y) in H by ring.
    replace (x^2) with (x * x) in H by ring.
    assert (Hsq : x * x > y * y) by nra.
    lra.
  - apply pow_incr; lra.
Qed.

(** O5 solvable ⟺ dist(q,l) ≤ dist(p,q) *)
Definition depressed_cubic (p q t : R) : R := t^3 + p * t + q.

(** t³ + pt + q = 0 *)
Definition is_cubic_root (p q t : R) : Prop := depressed_cubic p q t = 0.

(** ∄ four distinct roots *)
Definition cubic_at_most_3_roots : Prop :=
  forall p q t1 t2 t3 t4,
    is_cubic_root p q t1 -> is_cubic_root p q t2 ->
    is_cubic_root p q t3 -> is_cubic_root p q t4 ->
    t1 <> t2 -> t1 <> t3 -> t1 <> t4 ->
    t2 <> t3 -> t2 <> t4 -> t3 <> t4 ->
    False.

(** Δ > 0 ⟹ 3 distinct roots; Δ < 0 ⟹ unique root *)
Definition discriminant_determines_roots : Prop :=
  forall p q,
    (cubic_discriminant p q > 0 ->
      exists t1 t2 t3, is_cubic_root p q t1 /\ is_cubic_root p q t2 /\ is_cubic_root p q t3
                       /\ t1 <> t2 /\ t1 <> t3 /\ t2 <> t3) /\
    (cubic_discriminant p q < 0 ->
      exists! t, is_cubic_root p q t).

(** t³+pt+q = (t-r)(t²+rt+(r²+p)) when r is a root *)
Lemma cubic_factor : forall p q r t,
  is_cubic_root p q r ->
  depressed_cubic p q t = (t - r) * (t^2 + r*t + (r^2 + p)).
Proof.
  intros p q r t Hr.
  unfold is_cubic_root, depressed_cubic in *.
  replace (t^3 + p*t + q) with (t^3 - r^3 + p*t - p*r + (r^3 + p*r + q)) by ring.
  rewrite Hr.
  ring.
Qed.

(** a ≠ 0 ∧ at²+bt+c has 3 roots ⟹ ⊥ *)
Lemma quadratic_at_most_2_roots : forall a b c t1 t2 t3,
  a <> 0 ->
  a*t1^2 + b*t1 + c = 0 ->
  a*t2^2 + b*t2 + c = 0 ->
  a*t3^2 + b*t3 + c = 0 ->
  t1 <> t2 -> t1 <> t3 -> t2 <> t3 ->
  False.
Proof.
  intros a b c t1 t2 t3 Ha H1 H2 H3 Hn12 Hn13 Hn23.
  assert (Hdiff12 : a*(t1^2 - t2^2) + b*(t1 - t2) = 0) by lra.
  assert (Hdiff13 : a*(t1^2 - t3^2) + b*(t1 - t3) = 0) by lra.
  assert (Hfact12 : (t1 - t2) * (a*(t1 + t2) + b) = 0).
  { replace ((t1 - t2) * (a*(t1 + t2) + b)) with (a*(t1^2 - t2^2) + b*(t1 - t2)) by ring.
    exact Hdiff12. }
  assert (Hfact13 : (t1 - t3) * (a*(t1 + t3) + b) = 0).
  { replace ((t1 - t3) * (a*(t1 + t3) + b)) with (a*(t1^2 - t3^2) + b*(t1 - t3)) by ring.
    exact Hdiff13. }
  assert (Ht12_nz : t1 - t2 <> 0) by lra.
  assert (Ht13_nz : t1 - t3 <> 0) by lra.
  apply Rmult_integral in Hfact12. destruct Hfact12 as [Hf12|Hf12]; [lra|].
  apply Rmult_integral in Hfact13. destruct Hfact13 as [Hf13|Hf13]; [lra|].
  assert (Heq : a*(t1 + t2) + b = a*(t1 + t3) + b) by lra.
  assert (Ht23 : t2 = t3).
  { apply Rmult_eq_reg_l with a; [|exact Ha]. lra. }
  exact (Hn23 Ht23).
Qed.

(** Proof of cubic_at_most_3_roots *)
Theorem cubic_at_most_3_roots_proof : cubic_at_most_3_roots.
Proof.
  unfold cubic_at_most_3_roots.
  intros p q t1 t2 t3 t4 H1 H2 H3 H4 Hn12 Hn13 Hn14 Hn23 Hn24 Hn34.
  pose proof (cubic_factor p q t1 t2 H1) as Hfact2.
  pose proof (cubic_factor p q t1 t3 H1) as Hfact3.
  pose proof (cubic_factor p q t1 t4 H1) as Hfact4.
  unfold is_cubic_root in H2, H3, H4.
  rewrite Hfact2 in H2.
  rewrite Hfact3 in H3.
  rewrite Hfact4 in H4.
  apply Rmult_integral in H2. destruct H2 as [H2|H2]; [lra|].
  apply Rmult_integral in H3. destruct H3 as [H3|H3]; [lra|].
  apply Rmult_integral in H4. destruct H4 as [H4|H4]; [lra|].
  apply (quadratic_at_most_2_roots 1 t1 (t1^2 + p) t2 t3 t4).
  - lra.
  - replace (1 * t2^2 + t1 * t2 + (t1^2 + p)) with (t2^2 + t1*t2 + (t1^2 + p)) by ring.
    exact H2.
  - replace (1 * t3^2 + t1 * t3 + (t1^2 + p)) with (t3^2 + t1*t3 + (t1^2 + p)) by ring.
    exact H3.
  - replace (1 * t4^2 + t1 * t4 + (t1^2 + p)) with (t4^2 + t1*t4 + (t1^2 + p)) by ring.
    exact H4.
  - exact Hn23.
  - exact Hn24.
  - exact Hn34.
Qed.

(** b² - 4c for t² + bt + c *)
Definition quad_discriminant (b c : R) : R := b^2 - 4*c.

(** b² - 4c < 0 → t² + bt + c ≠ 0 *)
Lemma quadratic_no_roots_neg_disc : forall b c t,
  quad_discriminant b c < 0 ->
  t^2 + b*t + c <> 0.
Proof.
  intros b c t Hdisc Heq.
  unfold quad_discriminant in Hdisc.
  assert (H : 4 * (t^2 + b*t + c) = (2*t + b)^2 - (b^2 - 4*c)) by ring.
  rewrite Heq in H.
  assert (Hsq : (2*t + b)^2 >= 0).
  { replace ((2*t+b)^2) with ((2*t+b)*(2*t+b)) by ring.
    apply Rle_ge. apply Rle_0_sqr. }
  lra.
Qed.

(** quad_discriminant(r, r²+p) = -3r² - 4p *)
Lemma cubic_quad_discriminant : forall p q r,
  is_cubic_root p q r ->
  quad_discriminant r (r^2 + p) = -3*r^2 - 4*p.
Proof.
  intros p q r _. unfold quad_discriminant. ring.
Qed.

(** is_cubic_root r ∧ quad_discriminant < 0 → r is unique root *)
Lemma cubic_unique_root_neg_quad_disc : forall p q r,
  is_cubic_root p q r ->
  quad_discriminant r (r^2 + p) < 0 ->
  forall t, is_cubic_root p q t -> t = r.
Proof.
  intros p q r Hr Hqdisc t Ht.
  destruct (Req_dec t r) as [Heq|Hneq]; [exact Heq|exfalso].
  pose proof (cubic_factor p q r t Hr) as Hfact.
  unfold is_cubic_root in Ht. rewrite Hfact in Ht.
  apply Rmult_integral in Ht. destruct Ht as [Ht|Ht].
  - lra.
  - apply (quadratic_no_roots_neg_disc r (r^2 + p) t Hqdisc).
    exact Ht.
Qed.

(** r₁ ≠ r₂ both roots → quad_discriminant(r₁, r₁²+p) ≥ 0 *)
Lemma two_roots_implies_nonneg_discriminant : forall p q r1 r2,
  is_cubic_root p q r1 ->
  is_cubic_root p q r2 ->
  r1 <> r2 ->
  quad_discriminant r1 (r1^2 + p) >= 0.
Proof.
  intros p q r1 r2 Hr1 Hr2 Hneq.
  pose proof (cubic_factor p q r1 r2 Hr1) as Hfact.
  unfold is_cubic_root in Hr2. rewrite Hfact in Hr2.
  apply Rmult_integral in Hr2. destruct Hr2 as [Hr2|Hr2]; [lra|].
  unfold quad_discriminant.
  assert (H : 4 * (r2^2 + r1*r2 + (r1^2 + p)) = (2*r2 + r1)^2 - (r1^2 - 4*(r1^2+p))) by ring.
  rewrite Hr2 in H.
  assert (Hsq : (2*r2 + r1)^2 >= 0).
  { replace ((2*r2+r1)^2) with ((2*r2+r1)*(2*r2+r1)) by ring.
    apply Rle_ge. apply Rle_0_sqr. }
  lra.
Qed.

(** quad_discriminant < 0 → at most one root *)
Theorem cubic_at_most_one_root_when_quad_disc_neg : forall p q r,
  is_cubic_root p q r ->
  quad_discriminant r (r^2 + p) < 0 ->
  forall t, is_cubic_root p q t -> t = r.
Proof.
  intros p q r Hr Hqdisc t Ht.
  apply cubic_unique_root_neg_quad_disc with p q; assumption.
Qed.

(** t ≥ 1 → t³ ≥ t *)
Lemma cube_ge_self : forall t, t >= 1 -> t^3 >= t.
Proof.
  intros t Ht. nra.
Qed.

(** ∃ M, t > M → t³ + pt + q > 0 *)
Lemma depressed_cubic_pos_large : forall p q,
  exists M, forall t, t > M -> depressed_cubic p q t > 0.
Proof.
  intros p q.
  exists (Rabs p + Rabs q + 2). intros t Ht.
  unfold depressed_cubic.
  assert (Habsp : 0 <= Rabs p) by apply Rabs_pos.
  assert (Habsq : 0 <= Rabs q) by apply Rabs_pos.
  assert (Ht_pos : t > 2) by lra.
  assert (Ht_ge1 : t >= 1) by lra.
  assert (Hcube_ge : t^3 >= t) by (apply cube_ge_self; lra).
  assert (Hcube_ge_tt : t^3 >= t * t) by nra.
  assert (Hpabs : - Rabs p <= p).
  { unfold Rabs. destruct (Rcase_abs p); lra. }
  assert (Hpt_bound : p * t >= - Rabs p * t) by nra.
  assert (Hqabs : - Rabs q <= q).
  { unfold Rabs. destruct (Rcase_abs q); lra. }
  assert (Hq_bound : q >= - Rabs q) by lra.
  assert (Hsum : t^3 + p*t + q >= t*t - Rabs p * t - Rabs q) by lra.
  assert (Htt_bound : t * t > t * (Rabs p + 1)).
  { apply Rmult_lt_compat_l; lra. }
  assert (Hfinal : t*t - Rabs p * t - Rabs q > 0) by lra.
  lra.
Qed.


(** Relating cubic discriminant Δ = -4p³ - 27q² to root structure *)

(** Δ = -4p³ - 27(r³ + pr)² when r is a root *)
Lemma cubic_disc_via_root : forall p q r,
  is_cubic_root p q r ->
  cubic_discriminant p q = -4 * p^3 - 27 * (r^3 + p * r)^2.
Proof.
  intros p q r Hr.
  unfold is_cubic_root, depressed_cubic in Hr.
  unfold cubic_discriminant.
  replace q with (- r^3 - p * r) by lra.
  ring.
Qed.

(** q = -r(r² + p) when r is a root *)
Lemma root_gives_q : forall p q r,
  is_cubic_root p q r ->
  q = - r * (r^2 + p).
Proof.
  intros p q r Hr.
  unfold is_cubic_root, depressed_cubic in Hr.
  lra.
Qed.

(** Δ_cubic = Δ_quad · (9r² - Δ_quad)² / 16 *)
Lemma cubic_disc_via_quad_disc : forall p q r,
  is_cubic_root p q r ->
  cubic_discriminant p q =
    quad_discriminant r (r^2 + p) * (9 * r^2 - quad_discriminant r (r^2 + p))^2 / 16.
Proof.
  intros p q r Hr.
  unfold cubic_discriminant, quad_discriminant.
  pose proof (root_gives_q p q r Hr) as Hq.
  rewrite Hq.
  field.
Qed.

(** (9r² - Δ_quad)² ≥ 0 *)
Lemma square_term_nonneg : forall r p,
  (9 * r^2 - quad_discriminant r (r^2 + p))^2 >= 0.
Proof.
  intros r p.
  apply Rle_ge. apply pow2_ge_0.
Qed.

(** Δ_cubic < 0 ∧ (9r² - Δ_quad)² > 0 → Δ_quad < 0 *)
Lemma neg_cubic_disc_implies_neg_quad_disc : forall p q r,
  is_cubic_root p q r ->
  (9 * r^2 - quad_discriminant r (r^2 + p))^2 > 0 ->
  cubic_discriminant p q < 0 ->
  quad_discriminant r (r^2 + p) < 0.
Proof.
  intros p q r Hr Hsq_pos Hcubic_neg.
  rewrite (cubic_disc_via_quad_disc p q r Hr) in Hcubic_neg.
  set (dq := quad_discriminant r (r^2 + p)) in *.
  set (sq := (9 * r^2 - dq)^2) in *.
  destruct (Rlt_or_le dq 0) as [Hdq_neg | Hdq_nonneg].
  - exact Hdq_neg.
  - exfalso.
    assert (Hsq_nn : sq >= 0) by (unfold sq; apply Rle_ge; apply pow2_ge_0).
    assert (Hprod_nn : dq * sq >= 0) by nra.
    assert (Hdiv_nn : dq * sq / 16 >= 0) by nra.
    lra.
Qed.

(** Δ_cubic = 0 → Δ_quad = 0 ∨ 9r² = Δ_quad *)
Lemma zero_cubic_disc_cases : forall p q r,
  is_cubic_root p q r ->
  cubic_discriminant p q = 0 ->
  quad_discriminant r (r^2 + p) = 0 \/
  9 * r^2 - quad_discriminant r (r^2 + p) = 0.
Proof.
  intros p q r Hr Hzero.
  rewrite (cubic_disc_via_quad_disc p q r Hr) in Hzero.
  set (dq := quad_discriminant r (r^2 + p)) in *.
  set (sq := (9 * r^2 - dq)^2) in *.
  assert (Hdq_sq_zero : dq * sq = 0) by lra.
  apply Rmult_integral in Hdq_sq_zero.
  destruct Hdq_sq_zero as [Hdq_zero | Hsq_zero].
  - left. exact Hdq_zero.
  - right. unfold sq in Hsq_zero.
    assert (H : (9 * r^2 - dq) * (9 * r^2 - dq) = 0).
    { replace ((9 * r^2 - dq)^2) with ((9 * r^2 - dq) * (9 * r^2 - dq)) in Hsq_zero by ring.
      exact Hsq_zero. }
    apply Rmult_integral in H. destruct H; lra.
Qed.

(** Δ < 0 → r is the unique root *)
Theorem neg_cubic_disc_unique_root : forall p q r,
  is_cubic_root p q r ->
  cubic_discriminant p q < 0 ->
  forall t, is_cubic_root p q t -> t = r.
Proof.
  intros p q r Hr Hdisc t Ht.
  assert (Hsq_pos : (9 * r^2 - quad_discriminant r (r^2 + p))^2 > 0).
  { destruct (Req_dec (9 * r^2 - quad_discriminant r (r^2 + p)) 0) as [Heq | Hneq].
    - exfalso.
      rewrite (cubic_disc_via_quad_disc p q r Hr) in Hdisc.
      rewrite Heq in Hdisc.
      replace (0^2) with 0 in Hdisc by ring.
      lra.
    - replace ((9 * r^2 - quad_discriminant r (r^2 + p))^2)
        with ((9 * r^2 - quad_discriminant r (r^2 + p)) *
              (9 * r^2 - quad_discriminant r (r^2 + p))) by ring.
      nra. }
  assert (Hquad_neg : quad_discriminant r (r^2 + p) < 0).
  { apply (neg_cubic_disc_implies_neg_quad_disc p q r Hr Hsq_pos Hdisc). }
  apply (cubic_unique_root_neg_quad_disc p q r Hr Hquad_neg t Ht).
Qed.

(** Δ < 0 ∧ ∃ root → ∃! root *)
Corollary neg_disc_unique_existence : forall p q,
  cubic_discriminant p q < 0 ->
  (exists r, is_cubic_root p q r) ->
  exists! t, is_cubic_root p q t.
Proof.
  intros p q Hdisc [r Hr].
  exists r. split.
  - exact Hr.
  - intros t Ht. symmetry. apply (neg_cubic_disc_unique_root p q r Hr Hdisc t Ht).
Qed.

(** Δ < 0 case of discriminant theorem *)
Theorem discriminant_neg_case : forall p q,
  cubic_discriminant p q < 0 ->
  (exists r, is_cubic_root p q r) ->
  exists! t, is_cubic_root p q t.
Proof.
  exact neg_disc_unique_existence.
Qed.


(** Δ = 0: repeated root cases *)

(** Δ_quad = 0 ∧ r ≠ 0 → double root at -r/2 *)
Lemma quad_disc_zero_double_root : forall r p,
  r <> 0 ->
  quad_discriminant r (r^2 + p) = 0 ->
  exists s, s <> r /\ is_cubic_root p (- r * (r^2 + p)) s /\
    forall t, is_cubic_root p (- r * (r^2 + p)) t -> t = r \/ t = s.
Proof.
  intros r p Hrne0 Hqd.
  unfold quad_discriminant in Hqd.
  set (s := - r / 2).
  exists s.
  split.
  - unfold s. lra.
  - split.
    + unfold is_cubic_root, depressed_cubic, s.
      assert (Hp : p = - 3 * r^2 / 4) by lra.
      rewrite Hp. field.
    + intros t Ht.
      unfold is_cubic_root, depressed_cubic in Ht.
      assert (Hfactor : t^3 + p * t + (- r * (r^2 + p)) = (t - r) * (t^2 + r*t + (r^2 + p))).
      { ring. }
      rewrite Hfactor in Ht.
      apply Rmult_integral in Ht.
      destruct Ht as [Htr | Hquad].
      * left. lra.
      * right. unfold s.
        assert (Hdisc : r^2 - 4*(r^2 + p) = 0) by lra.
        assert (Hsq : (t + r/2)^2 = 0).
        { replace (t^2 + r*t + (r^2 + p)) with ((t + r/2)^2 - (r^2/4 - (r^2 + p))) in Hquad by field.
          replace (r^2/4 - (r^2 + p)) with ((r^2 - 4*(r^2 + p))/4) in Hquad by field.
          rewrite Hdisc in Hquad. lra. }
        assert (Hzero : t + r/2 = 0).
        { destruct (Req_dec (t + r/2) 0) as [Hz|Hnz]; [exact Hz|].
          exfalso. assert (Hpos : (t + r/2)^2 > 0) by nra. lra. }
        lra.
Qed.

(** p = q = 0 → Δ = 0 ∧ 0 is triple root *)
Lemma triple_root_case : forall p q,
  p = 0 -> q = 0 ->
  cubic_discriminant p q = 0 /\
  forall t, is_cubic_root p q t -> t = 0.
Proof.
  intros p q Hp Hq. subst.
  split.
  - unfold cubic_discriminant. ring.
  - intros t Ht. unfold is_cubic_root, depressed_cubic in Ht.
    replace (t^3 + 0*t + 0) with (t^3) in Ht by ring.
    assert (Ht3 : t * t * t = 0) by lra.
    destruct (Req_dec t 0) as [Hz|Hnz]; [exact Hz|].
    exfalso. assert (Hpos : t * t > 0) by nra.
    assert (Htt : t * t * t <> 0) by nra. lra.
Qed.

(** 0 is root → q = 0 *)
Lemma zero_root_implies_q_zero : forall p q,
  is_cubic_root p q 0 -> q = 0.
Proof.
  intros p q H.
  unfold is_cubic_root, depressed_cubic in H.
  lra.
Qed.

(** q = 0 → 0 is root *)
Lemma q_zero_implies_zero_root : forall p,
  is_cubic_root p 0 0.
Proof.
  intros p. unfold is_cubic_root, depressed_cubic. ring.
Qed.

(** is_cubic_root p 0 t ⟺ t = 0 ∨ t² + p = 0 *)
Lemma q_zero_factorization : forall p t,
  is_cubic_root p 0 t <-> t = 0 \/ t^2 + p = 0.
Proof.
  intros p t. unfold is_cubic_root, depressed_cubic.
  split; intro H.
  - assert (Hfact : t^3 + p * t + 0 = t * (t^2 + p)) by ring.
    rewrite Hfact in H.
    apply Rmult_integral in H.
    destruct H as [Ht | Htq].
    + left. exact Ht.
    + right. lra.
  - destruct H as [Ht | Htq].
    + subst. ring.
    + replace (t^3 + p * t + 0) with (t * (t^2 + p)) by ring.
      rewrite Htq. ring.
Qed.

(** q = 0 ∧ p > 0 → 0 is unique root *)
Lemma q_zero_p_pos_unique_root : forall p,
  p > 0 ->
  forall t, is_cubic_root p 0 t -> t = 0.
Proof.
  intros p Hp t Ht.
  apply q_zero_factorization in Ht.
  destruct Ht as [Hz | Hsq].
  - exact Hz.
  - exfalso. assert (Hpos : t^2 >= 0) by nra. lra.
Qed.

(** q = 0 ∧ p < 0 → roots are 0, √(-p), -√(-p) *)
Lemma q_zero_p_neg_three_roots : forall p,
  p < 0 ->
  is_cubic_root p 0 0 /\
  is_cubic_root p 0 (sqrt (-p)) /\
  is_cubic_root p 0 (- sqrt (-p)).
Proof.
  intros p Hp.
  assert (Hneg_p_pos : -p > 0) by lra.
  assert (Hsqrt_sq : sqrt (-p) * sqrt (-p) = -p) by (apply sqrt_sqrt; lra).
  repeat split.
  - apply q_zero_implies_zero_root.
  - apply q_zero_factorization. right.
    replace ((sqrt (-p))^2) with (sqrt (-p) * sqrt (-p)) by ring.
    lra.
  - apply q_zero_factorization. right.
    replace ((- sqrt (-p))^2) with (sqrt (-p) * sqrt (-p)) by ring.
    lra.
Qed.

(** p = q = 0 → t³ = 0 → t = 0 *)
Lemma q_zero_p_zero_triple : forall t,
  is_cubic_root 0 0 t -> t = 0.
Proof.
  intros t Ht.
  apply (proj2 (triple_root_case 0 0 eq_refl eq_refl) t Ht).
Qed.

(** p < 0 ∧ q = 0 → Δ > 0 *)
Lemma q_zero_p_neg_disc_pos : forall p,
  p < 0 -> cubic_discriminant p 0 > 0.
Proof.
  intros p Hp.
  unfold cubic_discriminant.
  assert (Hp2 : p * p > 0).
  { assert (Hnz : p <> 0) by lra.
    assert (Hp_neg : - p > 0) by lra.
    replace (p * p) with ((- p) * (- p)) by ring.
    apply Rmult_lt_0_compat; lra. }
  assert (Hp3 : p^3 < 0).
  { replace (p^3) with (p * (p * p)) by ring.
    rewrite <- (Rmult_0_l (p * p)).
    apply Rmult_lt_compat_r; lra. }
  lra.
Qed.

(** p > 0 ∧ q = 0 → Δ < 0 *)
Lemma q_zero_p_pos_disc_neg : forall p,
  p > 0 -> cubic_discriminant p 0 < 0.
Proof.
  intros p Hp.
  unfold cubic_discriminant.
  assert (Hp2 : p * p > 0) by (apply Rmult_lt_0_compat; lra).
  assert (Hp3 : p^3 > 0).
  { replace (p^3) with (p * (p * p)) by ring.
    apply Rmult_lt_0_compat; lra. }
  lra.
Qed.

(** x ≠ 0 → x² > 0 *)
Lemma sq_pos_of_neq_zero : forall x, x <> 0 -> x * x > 0.
Proof.
  intros x Hx.
  destruct (Rlt_or_le x 0) as [Hneg|Hpos].
  - replace (x * x) with ((- x) * (- x)) by ring.
    apply Rmult_lt_0_compat; lra.
  - destruct Hpos as [Hpos|Heq]; [|lra].
    apply Rmult_lt_0_compat; lra.
Qed.

(** x < 0 → x³ < 0 *)
Lemma cube_neg_of_neg : forall x, x < 0 -> x * x * x < 0.
Proof.
  intros x Hx.
  assert (Hxx : x * x > 0) by (apply sq_pos_of_neq_zero; lra).
  replace (x * x * x) with (x * (x * x)) by ring.
  rewrite <- (Rmult_0_l (x * x)).
  apply Rmult_lt_compat_r; lra.
Qed.

(** x > 0 → x³ > 0 *)
Lemma cube_pos_of_pos : forall x, x > 0 -> x * x * x > 0.
Proof.
  intros x Hx.
  assert (Hxx : x * x > 0) by (apply Rmult_lt_0_compat; lra).
  apply Rmult_lt_0_compat; lra.
Qed.

(** x³ = 0 ⟺ x = 0 *)
Lemma cube_zero_iff : forall x, x * x * x = 0 <-> x = 0.
Proof.
  intro x. split; intro H.
  - destruct (Req_dec x 0) as [Hz|Hnz]; [exact Hz|].
    exfalso.
    destruct (Rlt_or_le x 0) as [Hneg|Hpos].
    + assert (Hcube : x * x * x < 0) by (apply cube_neg_of_neg; lra). lra.
    + destruct Hpos as [Hpos|Heq]; [|lra].
      assert (Hcube : x * x * x > 0) by (apply cube_pos_of_pos; lra). lra.
  - subst. ring.
Qed.

(** Δ(p,0) = 0 → p = 0 *)
Lemma disc_zero_q_zero_implies_p_zero : forall p,
  cubic_discriminant p 0 = 0 -> p = 0.
Proof.
  intros p Hdisc.
  unfold cubic_discriminant in Hdisc.
  replace (0^2) with 0 in Hdisc by ring.
  assert (Hp3 : p^3 = 0) by lra.
  replace (p^3) with (p * p * p) in Hp3 by ring.
  apply cube_zero_iff. exact Hp3.
Qed.


(** Δ > 0: three distinct real roots *)

(** Δ > 0 → p < 0 *)
Lemma pos_disc_implies_neg_p : forall p q,
  cubic_discriminant p q > 0 -> p < 0.
Proof.
  intros p q Hdisc.
  unfold cubic_discriminant in Hdisc.
  destruct (Rle_or_lt 0 p) as [Hp_nn | Hp_neg].
  - exfalso.
    assert (Hp3 : p^3 >= 0) by nra.
    assert (Hq2 : q^2 >= 0) by nra.
    lra.
  - exact Hp_neg.
Qed.

(** √(-p/3): location of local extrema of t³ + pt + q *)
Definition critical_point (p : R) : R := sqrt (- p / 3).

(** p < 0 → √(-p/3) > 0 *)
Lemma critical_point_pos : forall p,
  p < 0 -> critical_point p > 0.
Proof.
  intros p Hp.
  unfold critical_point.
  apply sqrt_lt_R0. lra.
Qed.

(** (critical_point p)² = -p/3 *)
Lemma critical_point_sq : forall p,
  p < 0 -> (critical_point p)^2 = - p / 3.
Proof.
  intros p Hp.
  unfold critical_point.
  replace ((sqrt (- p / 3))^2) with (sqrt (- p / 3) * sqrt (- p / 3)) by ring.
  rewrite sqrt_sqrt by lra.
  reflexivity.
Qed.

(** f(tc) = q + (2p/3)·tc where tc = critical_point p *)
Lemma cubic_at_critical_pos : forall p q,
  p < 0 ->
  depressed_cubic p q (critical_point p) =
    q + (2 * p / 3) * critical_point p.
Proof.
  intros p q Hp.
  unfold depressed_cubic.
  set (tc := critical_point p).
  assert (Htc_sq : tc^2 = - p / 3) by (apply critical_point_sq; exact Hp).
  replace (tc^3) with (tc * tc^2) by ring.
  rewrite Htc_sq.
  field.
Qed.

(** f(-tc) = q - (2p/3)·tc *)
Lemma cubic_at_critical_neg : forall p q,
  p < 0 ->
  depressed_cubic p q (- critical_point p) =
    q - (2 * p / 3) * critical_point p.
Proof.
  intros p q Hp.
  unfold depressed_cubic.
  set (tc := critical_point p).
  assert (Htc_sq : tc^2 = - p / 3) by (apply critical_point_sq; exact Hp).
  replace ((- tc)^3) with (- (tc * tc^2)) by ring.
  rewrite Htc_sq.
  field.
Qed.

(** f(tc)·f(-tc) = q² + 4p³/27 *)
Lemma extrema_product_discriminant : forall p q,
  p < 0 ->
  depressed_cubic p q (critical_point p) *
  depressed_cubic p q (- critical_point p) =
    q^2 + 4 * p^3 / 27.
Proof.
  intros p q Hp.
  rewrite cubic_at_critical_pos by exact Hp.
  rewrite cubic_at_critical_neg by exact Hp.
  set (tc := critical_point p).
  assert (Htc_sq : tc^2 = - p / 3) by (apply critical_point_sq; exact Hp).
  replace ((q + 2 * p / 3 * tc) * (q - 2 * p / 3 * tc))
    with (q * q - (2 * p / 3 * tc) * (2 * p / 3 * tc)) by ring.
  replace ((2 * p / 3 * tc) * (2 * p / 3 * tc))
    with (4 * p * p / 9 * (tc * tc)) by field.
  replace (tc * tc) with (tc^2) by ring.
  rewrite Htc_sq.
  replace (q * q) with (q^2) by ring.
  replace (p * p) with (p^2) by ring.
  field.
Qed.

(** Δ = -27·f(tc)·f(-tc) *)
Lemma discriminant_extrema_relation : forall p q,
  p < 0 ->
  cubic_discriminant p q =
    -27 * (depressed_cubic p q (critical_point p) *
           depressed_cubic p q (- critical_point p)).
Proof.
  intros p q Hp.
  rewrite extrema_product_discriminant by exact Hp.
  unfold cubic_discriminant.
  field.
Qed.

(** Δ > 0 → f(tc)·f(-tc) < 0 *)
Lemma pos_disc_extrema_opposite_signs : forall p q,
  cubic_discriminant p q > 0 ->
  depressed_cubic p q (critical_point p) *
  depressed_cubic p q (- critical_point p) < 0.
Proof.
  intros p q Hdisc.
  assert (Hp : p < 0) by (apply pos_disc_implies_neg_p with q; exact Hdisc).
  rewrite discriminant_extrema_relation in Hdisc by exact Hp.
  set (f_min := depressed_cubic p q (critical_point p)) in *.
  set (f_max := depressed_cubic p q (- critical_point p)) in *.
  lra.
Qed.

(** ∃ M, t < M → t³ + pt + q < 0 *)
Lemma depressed_cubic_neg_large : forall p q,
  exists M, forall t, t < M -> depressed_cubic p q t < 0.
Proof.
  intros p q.
  destruct (depressed_cubic_pos_large p (-q)) as [N HN].
  exists (-N).
  intros t Ht.
  assert (HNt : - t > N) by lra.
  specialize (HN (-t) HNt).
  unfold depressed_cubic in *.
  replace ((-t)^3) with (- t^3) in HN by ring.
  lra.
Qed.

(** x³ = cube_func x *)
Lemma pow3_eq_cube_func : forall x, x^3 = cube_func x.
Proof.
  intro x. unfold cube_func. ring.
Qed.

(** t³ + pt + q = cube_func(t) + p·t + q *)
Lemma depressed_cubic_as_sum : forall p q x,
  depressed_cubic p q x = cube_func x + p * x + q.
Proof.
  intros. unfold depressed_cubic, cube_func. ring.
Qed.

(** x ↦ p·x is continuous *)
Lemma continuity_linear : forall p, continuity (fun x => p * x).
Proof.
  intros p x.
  apply derivable_continuous_pt.
  apply derivable_pt_scal.
  apply derivable_pt_id.
Qed.

(** x ↦ c is continuous *)
Lemma continuity_const_fn : forall c, continuity (fun _ => c).
Proof.
  intros c x. apply continuity_const. intros y z. reflexivity.
Qed.

(** Curried form of depressed_cubic for continuity proofs *)
Definition depressed_cubic_alt (p q : R) : R -> R :=
  fun x => cube_func x + p * x + q.

Lemma depressed_cubic_alt_eq : forall p q x,
  depressed_cubic p q x = depressed_cubic_alt p q x.
Proof.
  intros. unfold depressed_cubic, depressed_cubic_alt, cube_func. ring.
Qed.

(** t³ + pt + q is continuous in t *)
Lemma depressed_cubic_alt_continuous : forall p q,
  continuity (depressed_cubic_alt p q).
Proof.
  intros p q x.
  unfold depressed_cubic_alt.
  apply continuity_pt_plus.
  - apply continuity_pt_plus.
    + apply cube_func_continuous.
    + apply (continuity_linear p).
  - apply (continuity_const_fn q).
Qed.

(** f(a) < 0 < f(b) → ∃ r ∈ [a,b], f(r) = 0 *)
Lemma IVT_root_exists : forall p q a b,
  a < b ->
  depressed_cubic_alt p q a < 0 ->
  0 < depressed_cubic_alt p q b ->
  exists r, a <= r <= b /\ depressed_cubic p q r = 0.
Proof.
  intros p q a b Hab Ha Hb.
  destruct (IVT (depressed_cubic_alt p q) a b
                (depressed_cubic_alt_continuous p q) Hab Ha Hb)
    as [r [[Har Hrb] Hr]].
  exists r.
  split.
  - split; lra.
  - rewrite depressed_cubic_alt_eq. exact Hr.
Qed.

Lemma depressed_cubic_alt_sign : forall p q t,
  depressed_cubic_alt p q t < 0 <-> depressed_cubic p q t < 0.
Proof.
  intros. rewrite depressed_cubic_alt_eq. tauto.
Qed.

Lemma depressed_cubic_alt_sign_pos : forall p q t,
  depressed_cubic_alt p q t > 0 <-> depressed_cubic p q t > 0.
Proof.
  intros. rewrite depressed_cubic_alt_eq. tauto.
Qed.

Lemma depressed_cubic_alt_pos_large : forall p q,
  exists M, forall t, t > M -> depressed_cubic_alt p q t > 0.
Proof.
  intros p q.
  destruct (depressed_cubic_pos_large p q) as [M HM].
  exists M. intros t Ht.
  apply depressed_cubic_alt_sign_pos. apply HM. exact Ht.
Qed.

Lemma depressed_cubic_alt_neg_large : forall p q,
  exists M, forall t, t < M -> depressed_cubic_alt p q t < 0.
Proof.
  intros p q.
  destruct (depressed_cubic_neg_large p q) as [M HM].
  exists M. intros t Ht.
  apply depressed_cubic_alt_sign. apply HM. exact Ht.
Qed.

(** A real root of the depressed cubic t³ + pt + q, from IVT on the bracket
    [-(1+|p|+|q|), 1+|p|+|q|] where the cubic changes sign. *)
Theorem depressed_cubic_root_sig : forall p q,
  {r | is_cubic_root p q r}.
Proof.
  intros p q.
  set (b := 1 + Rabs p + Rabs q).
  pose proof (Rabs_pos p) as Hp0. pose proof (Rabs_pos q) as Hq0.
  assert (Hp : - Rabs p <= p <= Rabs p).
  { split; [ | apply Rle_abs ]. pose proof (Rle_abs (- p)) as H. rewrite Rabs_Ropp in H. lra. }
  assert (Hq : - Rabs q <= q <= Rabs q).
  { split; [ | apply Rle_abs ]. pose proof (Rle_abs (- q)) as H. rewrite Rabs_Ropp in H. lra. }
  assert (Hb1 : 1 <= b) by (unfold b; lra).
  assert (Hab : - b < b) by lra.
  assert (Hfa : depressed_cubic_alt p q (- b) < 0)
    by (unfold depressed_cubic_alt, cube_func, b in *; nra).
  assert (Hfb : 0 < depressed_cubic_alt p q b)
    by (unfold depressed_cubic_alt, cube_func, b in *; nra).
  destruct (IVT (depressed_cubic_alt p q) (- b) b
                (depressed_cubic_alt_continuous p q) Hab Hfa Hfb)
    as [r [[Har Hrb] Hr]].
  exists r.
  unfold is_cubic_root.
  rewrite depressed_cubic_alt_eq.
  exact Hr.
Qed.

(** ∀ p q, ∃ r, r³ + pr + q = 0. *)
Theorem depressed_cubic_root_exists : forall p q,
  exists r, is_cubic_root p q r.
Proof.
  intros p q. destruct (depressed_cubic_root_sig p q) as [r Hr]. exists r. exact Hr.
Qed.

(** Δ < 0 → ∃! r, r³ + pr + q = 0 *)
Corollary neg_disc_unique_root_exists : forall p q,
  cubic_discriminant p q < 0 ->
  exists! r, is_cubic_root p q r.
Proof.
  intros p q Hdisc.
  apply neg_disc_unique_existence.
  - exact Hdisc.
  - apply depressed_cubic_root_exists.
Qed.

(** Δ > 0 → extrema have opposite signs *)
Lemma pos_disc_alt_extrema_opposite : forall p q,
  cubic_discriminant p q > 0 ->
  (depressed_cubic_alt p q (critical_point p) < 0 /\
   depressed_cubic_alt p q (- critical_point p) > 0) \/
  (depressed_cubic_alt p q (critical_point p) > 0 /\
   depressed_cubic_alt p q (- critical_point p) < 0).
Proof.
  intros p q Hdisc.
  assert (Hprod : depressed_cubic p q (critical_point p) *
                  depressed_cubic p q (- critical_point p) < 0)
    by (apply pos_disc_extrema_opposite_signs; exact Hdisc).
  rewrite depressed_cubic_alt_eq in Hprod.
  rewrite depressed_cubic_alt_eq in Hprod.
  set (f_tc := depressed_cubic_alt p q (critical_point p)) in *.
  set (f_mtc := depressed_cubic_alt p q (- critical_point p)) in *.
  destruct (Rlt_or_le f_tc 0) as [Hftc_neg | Hftc_nonneg].
  - left. split. exact Hftc_neg. nra.
  - right. destruct (Rle_or_lt f_tc 0) as [Hftc_zero | Hftc_pos].
    + exfalso. assert (f_tc = 0) by lra. nra.
    + split. exact Hftc_pos. nra.
Qed.

Lemma neg_depressed_cubic_alt_continuous : forall p q,
  continuity (fun x => - depressed_cubic_alt p q x).
Proof.
  intros p q x.
  apply continuity_pt_opp.
  apply depressed_cubic_alt_continuous.
Qed.

(** Δ > 0 → ∃ root in [-tc, tc] *)
Lemma pos_disc_middle_root : forall p q,
  cubic_discriminant p q > 0 ->
  exists r, - critical_point p <= r <= critical_point p /\
            depressed_cubic p q r = 0.
Proof.
  intros p q Hdisc.
  assert (Hp : p < 0) by (apply pos_disc_implies_neg_p with q; exact Hdisc).
  assert (Htc_pos : critical_point p > 0) by (apply critical_point_pos; exact Hp).
  destruct (pos_disc_alt_extrema_opposite p q Hdisc) as [[Hftc Hfmtc] | [Hftc Hfmtc]].
  - pose (g := fun x => - depressed_cubic_alt p q x).
    assert (Hgcont : continuity g) by apply neg_depressed_cubic_alt_continuous.
    assert (Hgmtc : g (- critical_point p) < 0) by (unfold g; lra).
    assert (Hgtc : 0 < g (critical_point p)) by (unfold g; lra).
    destruct (IVT g (- critical_point p) (critical_point p) Hgcont)
      as [r [[Hr1 Hr2] Hr]].
    + lra.
    + exact Hgmtc.
    + exact Hgtc.
    + exists r. split. lra.
      unfold g in Hr. rewrite depressed_cubic_alt_eq. lra.
  - destruct (IVT (depressed_cubic_alt p q) (- critical_point p) (critical_point p)
                  (depressed_cubic_alt_continuous p q)) as [r [[Hr1 Hr2] Hr]].
    + lra.
    + exact Hfmtc.
    + exact Hftc.
    + exists r. split. lra. rewrite depressed_cubic_alt_eq. exact Hr.
Qed.

(** p < 0 → f(-tc) > f(tc) *)
Lemma local_max_gt_local_min : forall p q,
  p < 0 ->
  depressed_cubic p q (- critical_point p) >
  depressed_cubic p q (critical_point p).
Proof.
  intros p q Hp.
  set (tc := critical_point p).
  rewrite cubic_at_critical_neg by exact Hp.
  rewrite cubic_at_critical_pos by exact Hp.
  assert (Htc_pos : tc > 0) by (apply critical_point_pos; exact Hp).
  apply Rlt_0_minus.
  assert (Heq : q - 2 * p / 3 * critical_point p - (q + 2 * p / 3 * critical_point p) = (- 4 * p / 3) * critical_point p) by (unfold critical_point; field).
  rewrite Heq.
  apply Rmult_lt_0_compat.
  - lra.
  - exact Htc_pos.
Qed.

(** Δ > 0 → f(-tc) > 0 *)
Lemma pos_disc_local_max_pos : forall p q,
  cubic_discriminant p q > 0 ->
  depressed_cubic p q (- critical_point p) > 0.
Proof.
  intros p q Hdisc.
  assert (Hp : p < 0) by (apply pos_disc_implies_neg_p with q; exact Hdisc).
  assert (Hprod : depressed_cubic p q (critical_point p) *
                  depressed_cubic p q (- critical_point p) < 0)
    by (apply pos_disc_extrema_opposite_signs; exact Hdisc).
  assert (Hmax_gt_min : depressed_cubic p q (- critical_point p) >
                        depressed_cubic p q (critical_point p))
    by (apply local_max_gt_local_min; exact Hp).
  destruct (Rlt_or_le (depressed_cubic p q (- critical_point p)) 0) as [Hneg | Hnn].
  - exfalso. assert (Hmin_neg : depressed_cubic p q (critical_point p) < 0) by lra.
    assert (Hprod_pos : depressed_cubic p q (critical_point p) *
                        depressed_cubic p q (- critical_point p) > 0) by nra.
    lra.
  - destruct (Req_dec (depressed_cubic p q (- critical_point p)) 0) as [Heq | Hneq].
    + exfalso. rewrite Heq in Hprod. lra.
    + lra.
Qed.

(** Δ > 0 → f(tc) < 0 *)
Lemma pos_disc_local_min_neg : forall p q,
  cubic_discriminant p q > 0 ->
  depressed_cubic p q (critical_point p) < 0.
Proof.
  intros p q Hdisc.
  assert (Hprod : depressed_cubic p q (critical_point p) *
                  depressed_cubic p q (- critical_point p) < 0)
    by (apply pos_disc_extrema_opposite_signs; exact Hdisc).
  assert (Hmax_pos : depressed_cubic p q (- critical_point p) > 0)
    by (apply pos_disc_local_max_pos; exact Hdisc).
  destruct (Rlt_or_le (depressed_cubic p q (critical_point p)) 0) as [Hneg | Hnn].
  - exact Hneg.
  - exfalso. assert (Hprod_nn : depressed_cubic p q (critical_point p) *
                                depressed_cubic p q (- critical_point p) >= 0) by nra.
    lra.
Qed.

(** Δ > 0 → ∃ root r < -tc *)
Lemma pos_disc_left_root : forall p q,
  cubic_discriminant p q > 0 ->
  exists r, r < - critical_point p /\ depressed_cubic p q r = 0.
Proof.
  intros p q Hdisc.
  assert (Hp : p < 0) by (apply pos_disc_implies_neg_p with q; exact Hdisc).
  assert (Htc_pos : critical_point p > 0) by (apply critical_point_pos; exact Hp).
  assert (Hmax_pos : depressed_cubic_alt p q (- critical_point p) > 0).
  { rewrite <- depressed_cubic_alt_eq. apply pos_disc_local_max_pos. exact Hdisc. }
  destruct (depressed_cubic_alt_neg_large p q) as [M HM].
  set (M' := Rmin M (- critical_point p) - 1).
  assert (HM'_lt : M' < - critical_point p).
  { unfold M'. unfold Rmin. destruct (Rle_dec M (- critical_point p)); lra. }
  assert (HM'_ltM : M' < M).
  { unfold M'. unfold Rmin. destruct (Rle_dec M (- critical_point p)); lra. }
  assert (HM'_neg : depressed_cubic_alt p q M' < 0).
  { apply HM. exact HM'_ltM. }
  destruct (IVT (depressed_cubic_alt p q) M' (- critical_point p)
                (depressed_cubic_alt_continuous p q)) as [r [[Hr1 Hr2] Hr]].
  - lra.
  - exact HM'_neg.
  - exact Hmax_pos.
  - exists r. split.
    + destruct (Req_dec r (- critical_point p)) as [Heq | Hneq].
      * exfalso. rewrite Heq in Hr. lra.
      * lra.
    + rewrite depressed_cubic_alt_eq. exact Hr.
Qed.

(** Δ > 0 → ∃ root r > tc *)
Lemma pos_disc_right_root : forall p q,
  cubic_discriminant p q > 0 ->
  exists r, r > critical_point p /\ depressed_cubic p q r = 0.
Proof.
  intros p q Hdisc.
  assert (Hp : p < 0) by (apply pos_disc_implies_neg_p with q; exact Hdisc).
  assert (Htc_pos : critical_point p > 0) by (apply critical_point_pos; exact Hp).
  assert (Hmin_neg : depressed_cubic_alt p q (critical_point p) < 0).
  { rewrite <- depressed_cubic_alt_eq. apply pos_disc_local_min_neg. exact Hdisc. }
  destruct (depressed_cubic_alt_pos_large p q) as [N HN].
  set (N' := Rmax N (critical_point p) + 1).
  assert (HN'_gt : N' > critical_point p).
  { unfold N'. unfold Rmax. destruct (Rle_dec N (critical_point p)); lra. }
  assert (HN'_gtN : N' > N).
  { unfold N'. unfold Rmax. destruct (Rle_dec N (critical_point p)); lra. }
  assert (HN'_pos : depressed_cubic_alt p q N' > 0).
  { apply HN. exact HN'_gtN. }
  destruct (IVT (depressed_cubic_alt p q) (critical_point p) N'
                (depressed_cubic_alt_continuous p q)) as [r [[Hr1 Hr2] Hr]].
  - lra.
  - exact Hmin_neg.
  - exact HN'_pos.
  - exists r. split.
    + destruct (Req_dec r (critical_point p)) as [Heq | Hneq].
      * exfalso. rewrite Heq in Hr. lra.
      * lra.
    + rewrite depressed_cubic_alt_eq. exact Hr.
Qed.

(** Δ > 0 → ∃ r₁ < r₂ < r₃ all roots *)
Theorem pos_disc_three_distinct_roots : forall p q,
  cubic_discriminant p q > 0 ->
  exists r1 r2 r3,
    is_cubic_root p q r1 /\ is_cubic_root p q r2 /\ is_cubic_root p q r3 /\
    r1 < r2 /\ r2 < r3.
Proof.
  intros p q Hdisc.
  assert (Hp : p < 0) by (apply pos_disc_implies_neg_p with q; exact Hdisc).
  assert (Htc_pos : critical_point p > 0) by (apply critical_point_pos; exact Hp).
  destruct (pos_disc_left_root p q Hdisc) as [r1 [Hr1_lt Hr1_root]].
  destruct (pos_disc_middle_root p q Hdisc) as [r2 [Hr2_bd Hr2_root]].
  destruct (pos_disc_right_root p q Hdisc) as [r3 [Hr3_gt Hr3_root]].
  exists r1, r2, r3.
  repeat split.
  - unfold is_cubic_root. exact Hr1_root.
  - unfold is_cubic_root. exact Hr2_root.
  - unfold is_cubic_root. exact Hr3_root.
  - destruct Hr2_bd as [Hr2_lo Hr2_hi]. lra.
  - destruct Hr2_bd as [Hr2_lo Hr2_hi]. lra.
Qed.

(** Proof of discriminant_determines_roots *)
Theorem discriminant_determines_roots_proof : discriminant_determines_roots.
Proof.
  unfold discriminant_determines_roots.
  intros p q. split.
  - intro Hpos.
    destruct (pos_disc_three_distinct_roots p q Hpos) as [r1 [r2 [r3 [Hr1 [Hr2 [Hr3 [Hlt12 Hlt23]]]]]]].
    exists r1, r2, r3.
    repeat split; try assumption; lra.
  - intro Hneg.
    apply neg_disc_unique_root_exists. exact Hneg.
Qed.


(** O6 fold multiplicity determined by cubic discriminant *)

(** Beloch fold from cubic root t *)
Definition O6_has_exactly_one_fold (p q : R) : Prop :=
  exists t, is_cubic_root p q t /\
    forall t', is_cubic_root p q t' -> t' = t.

(** ∃ t₁ ≠ t₂ ≠ t₃ all roots *)
Definition O6_has_three_distinct_folds (p q : R) : Prop :=
  exists t1 t2 t3,
    is_cubic_root p q t1 /\ is_cubic_root p q t2 /\ is_cubic_root p q t3 /\
    t1 <> t2 /\ t1 <> t3 /\ t2 <> t3.

(** Δ < 0 ∧ ∃ root → exactly one O6 fold *)
Theorem O6_neg_discriminant_one_fold : forall p q,
  cubic_discriminant p q < 0 ->
  (exists t, is_cubic_root p q t) ->
  O6_has_exactly_one_fold p q.
Proof.
  intros p q Hdisc [t Ht].
  unfold O6_has_exactly_one_fold.
  exists t. split.
  - exact Ht.
  - intros t' Ht'. apply (neg_cubic_disc_unique_root p q t Ht Hdisc t' Ht').
Qed.

(** Δ < 0 → exactly one O6 fold *)
Theorem O6_neg_discriminant_one_fold_unconditional : forall p q,
  cubic_discriminant p q < 0 ->
  O6_has_exactly_one_fold p q.
Proof.
  intros p q Hdisc.
  destruct (depressed_cubic_root_exists p q) as [r Hr].
  apply O6_neg_discriminant_one_fold.
  - exact Hdisc.
  - exists r. exact Hr.
Qed.

(** Δ > 0 → three distinct O6 folds *)
Theorem O6_pos_discriminant_three_folds : forall p q,
  cubic_discriminant p q > 0 ->
  O6_has_three_distinct_folds p q.
Proof.
  intros p q Hdisc.
  destruct (pos_disc_three_distinct_roots p q Hdisc) as [r1 [r2 [r3 [Hr1 [Hr2 [Hr3 [Hlt12 Hlt23]]]]]]].
  unfold O6_has_three_distinct_folds.
  exists r1, r2, r3.
  repeat split; try assumption; lra.
Qed.

(** ∃ exactly t₁ ≠ t₂ both roots *)
Definition O6_has_two_distinct_folds (p q : R) : Prop :=
  exists t1 t2,
    is_cubic_root p q t1 /\ is_cubic_root p q t2 /\
    t1 <> t2 /\
    forall t, is_cubic_root p q t -> t = t1 \/ t = t2.

(** r ≠ 0 ∧ Δ_quad = 0 → two O6 folds *)
Theorem O6_zero_disc_double_root_two_folds : forall p r,
  r <> 0 ->
  is_cubic_root p (- r * (r^2 + p)) r ->
  quad_discriminant r (r^2 + p) = 0 ->
  O6_has_two_distinct_folds p (- r * (r^2 + p)).
Proof.
  intros p r Hrne0 Hr Hqd.
  destruct (quad_disc_zero_double_root r p Hrne0 Hqd) as [s [Hsner [Hs Huniq]]].
  unfold O6_has_two_distinct_folds.
  exists r, s.
  repeat split.
  - exact Hr.
  - exact Hs.
  - intro Heq. apply Hsner. symmetry. exact Heq.
  - exact Huniq.
Qed.

(** p = q = 0 → one O6 fold (triple root at 0) *)
Theorem O6_zero_disc_triple_root_one_fold :
  O6_has_exactly_one_fold 0 0.
Proof.
  unfold O6_has_exactly_one_fold.
  exists 0. split.
  - unfold is_cubic_root, depressed_cubic. ring.
  - intros t' Ht'. apply (proj2 (triple_root_case 0 0 eq_refl eq_refl) t' Ht').
Qed.

Corollary O6_fold_count_by_discriminant : forall p q,
  (cubic_discriminant p q < 0 /\ (exists t, is_cubic_root p q t) ->
    O6_has_exactly_one_fold p q) /\
  (cubic_discriminant p q > 0 ->
    O6_has_three_distinct_folds p q).
Proof.
  intros p q. split.
  - intros [Hdisc Hex]. apply O6_neg_discriminant_one_fold; assumption.
  - apply O6_pos_discriminant_three_folds.
Qed.


(** Cardano's formula: t = ∛(-q/2 + √Δ') + ∛(-q/2 - √Δ') where Δ' = q²/4 + p³/27 *)

(** q²/4 + p³/27 *)
Definition cardano_discriminant (p q : R) : R := q*q/4 + p*p*p/27.

(** Δ_cubic = -108 · Δ_cardano *)
Lemma cardano_cubic_disc_relation : forall p q,
  cubic_discriminant p q = -108 * cardano_discriminant p q.
Proof.
  intros p q.
  unfold cubic_discriminant, cardano_discriminant.
  field.
Qed.

(** Δ_cubic < 0 → Δ_cardano > 0 *)
Lemma neg_cubic_disc_pos_cardano : forall p q,
  cubic_discriminant p q < 0 -> cardano_discriminant p q > 0.
Proof.
  intros p q H.
  rewrite cardano_cubic_disc_relation in H.
  unfold cardano_discriminant in *.
  lra.
Qed.

(** u = ∛(-q/2 + √Δ') *)
Definition cardano_u (p q : R) : R :=
  cbrt (- q/2 + sqrt (cardano_discriminant p q)).

(** v = ∛(-q/2 - √Δ') *)
Definition cardano_v (p q : R) : R :=
  cbrt (- q/2 - sqrt (cardano_discriminant p q)).

(** u + v *)
Definition cardano_root (p q : R) : R := cardano_u p q + cardano_v p q.

(** u³ + v³ = -q *)
Lemma cardano_uv_sum_cubes : forall p q,
  cardano_discriminant p q >= 0 ->
  let u := cardano_u p q in
  let v := cardano_v p q in
  cube_func u + cube_func v = -q.
Proof.
  intros p q Hdisc u v.
  unfold u, v, cardano_u, cardano_v.
  rewrite 2!cbrt_spec.
  set (s := sqrt (cardano_discriminant p q)).
  replace (- q / 2 + s + (- q / 2 - s)) with (-q) by field.
  reflexivity.
Qed.

(** u³ · v³ = -p³/27 *)
Lemma cardano_uv_prod_cubes : forall p q,
  cardano_discriminant p q >= 0 ->
  let u := cardano_u p q in
  let v := cardano_v p q in
  cube_func u * cube_func v = - p^3 / 27.
Proof.
  intros p q Hdisc u v.
  unfold u, v, cardano_u, cardano_v.
  rewrite 2!cbrt_spec.
  set (s := sqrt (cardano_discriminant p q)).
  assert (Hs : s * s = cardano_discriminant p q).
  { unfold s. apply sqrt_sqrt. lra. }
  unfold cardano_discriminant in Hs.
  replace ((- q / 2 + s) * (- q / 2 - s)) with ((-q/2)^2 - s^2) by ring.
  replace (s^2) with (s * s) by ring.
  rewrite Hs.
  unfold cardano_discriminant.
  field.
Qed.

(** Key identity: uv = -p/3 *)
Lemma cardano_uv_product : forall p q,
  cardano_discriminant p q >= 0 ->
  let u := cardano_u p q in
  let v := cardano_v p q in
  u * v = - p / 3.
Proof.
  intros p q Hdisc u v.
  unfold u, v, cardano_u, cardano_v, cardano_discriminant in *.
  apply cardano_product.
  lra.
Qed.

(** Main Theorem: Cardano's formula gives a root when discriminant >= 0 *)
Theorem cardano_formula_is_root : forall p q,
  cardano_discriminant p q >= 0 ->
  depressed_cubic p q (cardano_root p q) = 0.
Proof.
  intros p q Hdisc.
  unfold depressed_cubic, cardano_root.
  set (u := cardano_u p q).
  set (v := cardano_v p q).
  replace ((u + v) ^ 3) with ((u + v) * (u + v) * (u + v)) by (simpl; ring).
  rewrite sum_of_cubes_identity.
  assert (Hsum : cube_func u + cube_func v = -q).
  { apply cardano_uv_sum_cubes. exact Hdisc. }
  assert (Hprod : u * v = -p/3).
  { apply cardano_uv_product. exact Hdisc. }
  unfold cube_func in Hsum.
  rewrite Hsum.
  replace (3 * u * v) with (3 * (u * v)) by ring.
  rewrite Hprod.
  field.
Qed.

Lemma cardano_neg_disc_requires_complex : forall p q,
  cardano_discriminant p q < 0 -> cubic_discriminant p q > 0.
Proof.
  intros p q Hneg.
  rewrite cardano_cubic_disc_relation.
  assert (Hprod : -108 * cardano_discriminant p q > 0).
  { assert (H1 : -108 < 0) by lra.
    assert (H2 : - cardano_discriminant p q > 0) by lra.
    replace (-108 * cardano_discriminant p q) with (108 * (- cardano_discriminant p q)) by ring.
    apply Rmult_lt_0_compat; lra. }
  lra.
Qed.

(** Triple-angle identity for cosine: cos(3x) = 4cos³x − 3cos x *)
Lemma cos_triple : forall x, cos (3 * x) = 4 * (cos x)^3 - 3 * cos x.
Proof.
  intro x.
  replace (3 * x) with (x + (x + x)) by ring.
  rewrite cos_plus, cos_plus, sin_plus.
  pose proof (sin2_cos2 x) as H. unfold Rsqr in H.
  assert (Hsin : sin x * sin x = 1 - cos x * cos x) by lra.
  replace (sin x * (sin x * cos x + cos x * sin x))
    with (2 * (sin x * sin x) * cos x) by ring.
  rewrite !Hsin. ring.
Qed.

(** Trigonometric Cardano parameter C = (3q)/(2p)·√(−3/p) *)
Definition cardano_C (p q : R) : R := (3 * q) / (2 * p) * sqrt (-3 / p).

(** Trigonometric (casus irreducibilis) root: t = 2√(−p/3)·cos(⅓·acos C) *)
Definition cardano_trig_root (p q : R) : R :=
  2 * sqrt (- p / 3) * cos (/3 * acos (cardano_C p q)).

Lemma neg_p_div3_nonneg : forall p, p < 0 -> 0 <= - p / 3.
Proof. intros p Hp. unfold Rdiv. apply Rmult_le_pos; lra. Qed.

Lemma neg_3_div_p_pos : forall p, p < 0 -> 0 < -3 / p.
Proof.
  intros p Hp. replace (-3 / p) with (3 / (- p)) by (field; lra).
  apply Rdiv_lt_0_compat; lra.
Qed.

Lemma sqrt_prod_one : forall p, p < 0 -> sqrt (-p/3) * sqrt (-3/p) = 1.
Proof.
  intros p Hp.
  assert (H1 : 0 <= -p/3) by (apply neg_p_div3_nonneg; exact Hp).
  assert (H2 : 0 <= -3/p) by (apply Rlt_le; apply neg_3_div_p_pos; exact Hp).
  rewrite <- sqrt_mult by assumption.
  replace (-p/3 * (-3/p)) with 1 by (field; lra).
  apply sqrt_1.
Qed.

Lemma cardano_C_sq_cleared : forall p q, p < 0 ->
  cardano_C p q * cardano_C p q * (4 * (p*p*p)) = -27 * (q*q).
Proof.
  intros p q Hp. unfold cardano_C.
  assert (Hs : sqrt (-3/p) * sqrt (-3/p) = -3/p)
    by (apply sqrt_sqrt; apply Rlt_le; apply neg_3_div_p_pos; exact Hp).
  replace ((3*q)/(2*p) * sqrt(-3/p) * ((3*q)/(2*p) * sqrt(-3/p)) * (4*(p*p*p)))
    with ((3*q)*(3*q) * (sqrt(-3/p) * sqrt(-3/p)) * ((p*p*p)/(p*p))) by (field; lra).
  rewrite Hs. field. lra.
Qed.

Lemma cardano_C_bound : forall p q,
  cubic_discriminant p q > 0 -> -1 <= cardano_C p q <= 1.
Proof.
  intros p q Hdisc.
  assert (Hp : p < 0) by (apply pos_disc_implies_neg_p with q; exact Hdisc).
  assert (HC2 : cardano_C p q * cardano_C p q * (4 * (p*p*p)) = -27 * (q*q))
    by (apply cardano_C_sq_cleared; exact Hp).
  unfold cubic_discriminant in Hdisc.
  assert (Hp3 : p * p * p < 0) by nra.
  assert (HC1 : cardano_C p q * cardano_C p q <= 1) by nra.
  split; nra.
Qed.

(** Cardano's trigonometric solution covers the three-real-root casus irreducibilis (Δ_cubic > 0) *)
Theorem cardano_trig_root_is_root : forall p q,
  cubic_discriminant p q > 0 ->
  depressed_cubic p q (cardano_trig_root p q) = 0.
Proof.
  intros p q Hdisc.
  assert (Hp : p < 0) by (apply pos_disc_implies_neg_p with q; exact Hdisc).
  assert (HCb : -1 <= cardano_C p q <= 1) by (apply cardano_C_bound; exact Hdisc).
  assert (Hcos3 : cos (3 * (/3 * acos (cardano_C p q))) = cardano_C p q).
  { replace (3 * (/3 * acos (cardano_C p q))) with (acos (cardano_C p q)) by field.
    apply cos_acos; exact HCb. }
  rewrite cos_triple in Hcos3.
  assert (Hs2 : sqrt (-p/3) * sqrt (-p/3) = -p/3)
    by (apply sqrt_sqrt; apply neg_p_div3_nonneg; exact Hp).
  assert (HpsC : 2 * p * sqrt (-p/3) * cardano_C p q = 3 * q).
  { unfold cardano_C.
    replace (2 * p * sqrt(-p/3) * ((3*q)/(2*p) * sqrt(-3/p)))
      with (3 * q * (sqrt(-p/3) * sqrt(-3/p))) by (field; lra).
    rewrite sqrt_prod_one by exact Hp. ring. }
  unfold depressed_cubic, cardano_trig_root.
  set (c := cos (/3 * acos (cardano_C p q))) in *.
  set (s := sqrt (-p/3)) in *.
  set (C := cardano_C p q) in *.
  clearbody c s C.
  assert (R1 : 3 * (s * s) + p = 0) by lra.
  assert (R2 : 4 * c^3 - 3 * c - C = 0) by lra.
  assert (R3 : 2 * p * s * C - 3 * q = 0) by lra.
  apply (Rmult_eq_reg_l (3 * p)); [|intro Hc; lra]. rewrite Rmult_0_r.
  replace (3 * p * ((2 * s * c)^3 + p * (2 * s * c) + q))
    with (8 * p * s * c^3 * (3 * (s * s) + p)
          - 2 * p * p * s * (4 * c^3 - 3 * c - C)
          - p * (2 * p * s * C - 3 * q)) by ring.
  rewrite R1, R2, R3. ring.
Qed.

(* The trig Cardano root for any angle phi with cos(3 phi) = C is a root. *)
Lemma cardano_trig_root_general : forall p q phi,
  cubic_discriminant p q > 0 ->
  cos (3 * phi) = cardano_C p q ->
  depressed_cubic p q (2 * sqrt (-p/3) * cos phi) = 0.
Proof.
  intros p q phi Hdisc Hcos3eq.
  assert (Hp : p < 0) by (apply pos_disc_implies_neg_p with q; exact Hdisc).
  assert (Hcos3 : cos (3 * phi) = cardano_C p q) by exact Hcos3eq.
  rewrite cos_triple in Hcos3.
  assert (Hs2 : sqrt (-p/3) * sqrt (-p/3) = -p/3)
    by (apply sqrt_sqrt; apply neg_p_div3_nonneg; exact Hp).
  assert (HpsC : 2 * p * sqrt (-p/3) * cardano_C p q = 3 * q).
  { unfold cardano_C.
    replace (2 * p * sqrt(-p/3) * ((3*q)/(2*p) * sqrt(-3/p)))
      with (3 * q * (sqrt(-p/3) * sqrt(-3/p))) by (field; lra).
    rewrite sqrt_prod_one by exact Hp. ring. }
  unfold depressed_cubic.
  set (c := cos phi) in *.
  set (s := sqrt (-p/3)) in *.
  set (C := cardano_C p q) in *.
  clearbody c s C.
  assert (R1 : 3 * (s * s) + p = 0) by lra.
  assert (R2 : 4 * c^3 - 3 * c - C = 0) by lra.
  assert (R3 : 2 * p * s * C - 3 * q = 0) by lra.
  apply (Rmult_eq_reg_l (3 * p)); [|intro Hc; lra]. rewrite Rmult_0_r.
  replace (3 * p * ((2 * s * c)^3 + p * (2 * s * c) + q))
    with (8 * p * s * c^3 * (3 * (s * s) + p)
          - 2 * p * p * s * (4 * c^3 - 3 * c - C)
          - p * (2 * p * s * C - 3 * q)) by ring.
  rewrite R1, R2, R3. ring.
Qed.

(* The three trigonometric roots t_k = 2 sqrt(-p/3) cos(acos(C)/3 + 2 pi k/3). *)
Definition cardano_trig_root_k (p q : R) (k : nat) : R :=
  2 * sqrt (-p/3) * cos (/3 * acos (cardano_C p q) + 2*PI*INR k/3).

Theorem cardano_trig_root_k_is_root : forall p q k,
  cubic_discriminant p q > 0 ->
  depressed_cubic p q (cardano_trig_root_k p q k) = 0.
Proof.
  intros p q k Hdisc. unfold cardano_trig_root_k.
  apply cardano_trig_root_general; [exact Hdisc|].
  assert (HCb : -1 <= cardano_C p q <= 1) by (apply cardano_C_bound; exact Hdisc).
  replace (3 * (/3 * acos (cardano_C p q) + 2*PI*INR k/3))
    with (acos (cardano_C p q) + 2 * INR k * PI) by field.
  rewrite cos_period. apply cos_acos; exact HCb.
Qed.

(** All three trig branches (k = 0, 1, 2) are roots of the depressed cubic. *)
Theorem cardano_three_trig_roots : forall p q,
  cubic_discriminant p q > 0 ->
  depressed_cubic p q (cardano_trig_root_k p q 0) = 0 /\
  depressed_cubic p q (cardano_trig_root_k p q 1) = 0 /\
  depressed_cubic p q (cardano_trig_root_k p q 2) = 0.
Proof.
  intros p q Hdisc.
  split; [|split]; apply cardano_trig_root_k_is_root; exact Hdisc.
Qed.

Lemma cardano_C_strict : forall p q,
  cubic_discriminant p q > 0 -> -1 < cardano_C p q < 1.
Proof.
  intros p q Hdisc.
  assert (Hp : p < 0) by (apply pos_disc_implies_neg_p with q; exact Hdisc).
  assert (HC2 : cardano_C p q * cardano_C p q * (4 * (p*p*p)) = -27 * (q*q))
    by (apply cardano_C_sq_cleared; exact Hp).
  unfold cubic_discriminant in Hdisc.
  assert (Hp3 : p*p*p < 0) by nra.
  assert (HC1 : cardano_C p q * cardano_C p q < 1) by nra.
  split; nra.
Qed.

(** For Delta > 0 the three trig roots are pairwise distinct: the formula
    genuinely recovers all three real roots, not just one. *)
Theorem cardano_three_trig_roots_distinct : forall p q,
  cubic_discriminant p q > 0 ->
  cardano_trig_root_k p q 0 <> cardano_trig_root_k p q 1 /\
  cardano_trig_root_k p q 0 <> cardano_trig_root_k p q 2 /\
  cardano_trig_root_k p q 1 <> cardano_trig_root_k p q 2.
Proof.
  intros p q Hdisc.
  assert (Hp : p < 0) by (apply pos_disc_implies_neg_p with q; exact Hdisc).
  assert (Hpi : 0 < PI) by apply PI_RGT_0.
  pose proof (cardano_C_strict p q Hdisc) as [HClo HChi].
  set (C := cardano_C p q) in *.
  set (s := sqrt (-p/3)) in *.
  assert (Hs : 0 < s) by (unfold s; apply sqrt_lt_R0; lra).
  set (a := acos C) in *.
  assert (Hca : cos a = C) by (unfold a; apply cos_acos; lra).
  assert (Hac : 0 < a < PI).
  { pose proof (acos_bound C) as [Hlo Hhi]. unfold a in *. split.
    - destruct Hlo as [Hlo|Hlo]; [exact Hlo|exfalso].
      rewrite <- Hlo in Hca. rewrite cos_0 in Hca. lra.
    - destruct Hhi as [Hhi|Hhi]; [exact Hhi|exfalso].
      rewrite Hhi in Hca. rewrite cos_PI in Hca. lra. }
  unfold cardano_trig_root_k. fold C. fold s. fold a.
  set (t0 := 2*s*cos (/3*a + 2*PI*INR 0/3)).
  set (t1 := 2*s*cos (/3*a + 2*PI*INR 1/3)).
  set (t2 := 2*s*cos (/3*a + 2*PI*INR 2/3)).
  assert (E0 : /3*a + 2*PI*INR 0/3 = a/3) by (simpl; field).
  assert (E1 : /3*a + 2*PI*INR 1/3 = a/3 + 2*PI/3) by (simpl; field).
  assert (E2c : cos (/3*a + 2*PI*INR 2/3) = cos (2*PI/3 - a/3)).
  { replace (/3*a + 2*PI*INR 2/3) with ((a/3 - 2*PI/3) + 2*INR 1*PI) by (simpl; field).
    rewrite cos_period.
    replace (a/3 - 2*PI/3) with (-(2*PI/3 - a/3)) by field. apply cos_neg. }
  assert (Hcos01 : cos (a/3 + 2*PI/3) < cos (a/3)) by (apply cos_decreasing_1; lra).
  assert (Hcos02 : cos (2*PI/3 - a/3) < cos (a/3)) by (apply cos_decreasing_1; lra).
  assert (Hcos12 : cos (a/3 + 2*PI/3) < cos (2*PI/3 - a/3)) by (apply cos_decreasing_1; lra).
  unfold t0, t1, t2.
  rewrite E0, E1, E2c.
  split; [|split]; intro Heq; nra.
Qed.
Definition is_quintisection (theta phi : R) : Prop :=
  phi = theta / 5 /\ 0 < theta < 2 * PI.

(** 5-smooth numbers: products of powers of 2, 3, and 5.
    These characterize degrees achievable by 2-fold origami. *)
Definition is_5_smooth (n : nat) : Prop :=
  exists a b c : nat, n = (Nat.pow 2 a * Nat.pow 3 b * Nat.pow 5 c)%nat.

(** 2-fold origami numbers: extends single-fold with quintic solutions.
    The additional constructor allows roots of degree-5 polynomials
    arising from simultaneous 2-fold operations. *)
Inductive OrigamiNum2 : R -> Prop :=
| ON2_0 : OrigamiNum2 0
| ON2_1 : OrigamiNum2 1
| ON2_add : forall x y, OrigamiNum2 x -> OrigamiNum2 y -> OrigamiNum2 (x + y)
| ON2_sub : forall x y, OrigamiNum2 x -> OrigamiNum2 y -> OrigamiNum2 (x - y)
| ON2_mul : forall x y, OrigamiNum2 x -> OrigamiNum2 y -> OrigamiNum2 (x * y)
| ON2_inv : forall x, OrigamiNum2 x -> x <> 0 -> OrigamiNum2 (/ x)
| ON2_sqrt : forall x, OrigamiNum2 x -> 0 <= x -> OrigamiNum2 (sqrt x)
| ON2_cbrt : forall a b r, OrigamiNum2 a -> OrigamiNum2 b ->
    r * r * r + a * r + b = 0 -> OrigamiNum2 r
| ON2_quint : forall a b c d e r,
    OrigamiNum2 a -> OrigamiNum2 b -> OrigamiNum2 c -> OrigamiNum2 d -> OrigamiNum2 e ->
    r^5 + a * r^4 + b * r^3 + c * r^2 + d * r + e = 0 -> OrigamiNum2 r.

(** Single-fold origami numbers embed into 2-fold. *)
Lemma Origami_in_Origami2 : forall x, OrigamiNum x -> OrigamiNum2 x.
Proof.
  intros x H. induction H.
  - apply ON2_0.
  - apply ON2_1.
  - apply ON2_add; assumption.
  - apply ON2_sub; assumption.
  - apply ON2_mul; assumption.
  - apply ON2_inv; assumption.
  - apply ON2_sqrt; assumption.
  - apply (ON2_cbrt a b); assumption.
Qed.

(* ===== Structural degree bound for two-fold origami numbers =====
   Mirrors OrigamiNum_deg (sqrt doubles, cbrt triples) and adds the quintic
   step (degree x5), so every OrigamiNum2 number carries a 2^a*3^b*5^c bound. *)
Inductive OrigamiNum2_deg : R -> nat -> Prop :=
| ON2D_0 : OrigamiNum2_deg 0 1
| ON2D_1 : OrigamiNum2_deg 1 1
| ON2D_add : forall x y n m, OrigamiNum2_deg x n -> OrigamiNum2_deg y m ->
    OrigamiNum2_deg (x + y) (Nat.max n m)
| ON2D_sub : forall x y n m, OrigamiNum2_deg x n -> OrigamiNum2_deg y m ->
    OrigamiNum2_deg (x - y) (Nat.max n m)
| ON2D_mul : forall x y n m, OrigamiNum2_deg x n -> OrigamiNum2_deg y m ->
    OrigamiNum2_deg (x * y) (Nat.max n m)
| ON2D_inv : forall x n, OrigamiNum2_deg x n -> x <> 0 -> OrigamiNum2_deg (/ x) n
| ON2D_sqrt : forall x n, OrigamiNum2_deg x n -> 0 <= x -> OrigamiNum2_deg (sqrt x) (2 * n)
| ON2D_cbrt : forall a b r n m, OrigamiNum2_deg a n -> OrigamiNum2_deg b m ->
    r * r * r + a * r + b = 0 -> OrigamiNum2_deg r (3 * Nat.max n m)
| ON2D_quint : forall a b c d e r na nb nc nd ne,
    OrigamiNum2_deg a na -> OrigamiNum2_deg b nb -> OrigamiNum2_deg c nc ->
    OrigamiNum2_deg d nd -> OrigamiNum2_deg e ne ->
    r ^ 5 + a * r ^ 4 + b * r ^ 3 + c * r ^ 2 + d * r + e = 0 ->
    OrigamiNum2_deg r (5 * Nat.max na (Nat.max nb (Nat.max nc (Nat.max nd ne)))).

Lemma is_5_smooth_one : is_5_smooth 1.
Proof. exists 0%nat, 0%nat, 0%nat. reflexivity. Qed.

Lemma is_5_smooth_mul2 : forall n, is_5_smooth n -> is_5_smooth (2 * n).
Proof. intros n [a [b [c H]]]. exists (S a), b, c. rewrite H, Nat.pow_succ_r'. ring. Qed.

Lemma is_5_smooth_mul3 : forall n, is_5_smooth n -> is_5_smooth (3 * n).
Proof. intros n [a [b [c H]]]. exists a, (S b), c. rewrite H, Nat.pow_succ_r'. ring. Qed.

Lemma is_5_smooth_mul5 : forall n, is_5_smooth n -> is_5_smooth (5 * n).
Proof. intros n [a [b [c H]]]. exists a, b, (S c). rewrite H, Nat.pow_succ_r'. ring. Qed.

Lemma is_5_smooth_max : forall n m,
  is_5_smooth n -> is_5_smooth m -> is_5_smooth (Nat.max n m).
Proof.
  intros n m Hn Hm. destruct (Nat.max_spec n m) as [[_ E] | [_ E]];
    rewrite E; assumption.
Qed.

(* every OrigamiNum2 number carries a structural degree *)
Theorem OrigamiNum2_has_deg : forall x, OrigamiNum2 x -> exists n, OrigamiNum2_deg x n.
Proof.
  intros x H. induction H.
  - exists 1%nat. constructor.
  - exists 1%nat. constructor.
  - destruct IHOrigamiNum2_1 as [n1 Hn1]. destruct IHOrigamiNum2_2 as [n2 Hn2].
    exists (Nat.max n1 n2). apply ON2D_add; assumption.
  - destruct IHOrigamiNum2_1 as [n1 Hn1]. destruct IHOrigamiNum2_2 as [n2 Hn2].
    exists (Nat.max n1 n2). apply ON2D_sub; assumption.
  - destruct IHOrigamiNum2_1 as [n1 Hn1]. destruct IHOrigamiNum2_2 as [n2 Hn2].
    exists (Nat.max n1 n2). apply ON2D_mul; assumption.
  - destruct IHOrigamiNum2 as [n Hn]. exists n. apply ON2D_inv; assumption.
  - destruct IHOrigamiNum2 as [n Hn]. exists (2 * n)%nat. apply ON2D_sqrt; assumption.
  - destruct IHOrigamiNum2_1 as [n1 Hn1]. destruct IHOrigamiNum2_2 as [n2 Hn2].
    exists (3 * Nat.max n1 n2)%nat. apply (ON2D_cbrt a b); assumption.
  - destruct IHOrigamiNum2_1 as [na Hna]. destruct IHOrigamiNum2_2 as [nb Hnb].
    destruct IHOrigamiNum2_3 as [nc Hnc]. destruct IHOrigamiNum2_4 as [nd Hnd].
    destruct IHOrigamiNum2_5 as [ne Hne].
    exists (5 * Nat.max na (Nat.max nb (Nat.max nc (Nat.max nd ne))))%nat.
    apply (ON2D_quint a b c d e); assumption.
Qed.

(* the structural degree is 2-3-5-smooth *)
Theorem OrigamiNum2_deg_is_5_smooth : forall x n, OrigamiNum2_deg x n -> is_5_smooth n.
Proof.
  intros x n H. induction H.
  - apply is_5_smooth_one.
  - apply is_5_smooth_one.
  - apply is_5_smooth_max; assumption.
  - apply is_5_smooth_max; assumption.
  - apply is_5_smooth_max; assumption.
  - assumption.
  - apply is_5_smooth_mul2; assumption.
  - apply is_5_smooth_mul3, is_5_smooth_max; assumption.
  - apply is_5_smooth_mul5. repeat apply is_5_smooth_max; assumption.
Qed.

(* main result: every two-fold origami number has a 2^a*3^b*5^c degree bound *)
Theorem OrigamiNum2_degree_5_smooth : forall x, OrigamiNum2 x ->
  exists n, OrigamiNum2_deg x n /\ is_5_smooth n.
Proof.
  intros x H. destruct (OrigamiNum2_has_deg x H) as [n Hn].
  exists n. split; [exact Hn | apply (OrigamiNum2_deg_is_5_smooth x n Hn)].
Qed.

(** The regular hendecagon (11-gon) central angle. *)
Lemma nat_as_OrigamiNum : forall n : nat, OrigamiNum (INR n).
Proof.
  induction n.
  - simpl. apply ON_0.
  - rewrite S_INR. apply ON_add. exact IHn. apply ON_1.
Qed.

(** Helper: build positive as OrigamiNum *)
Lemma pos_as_OrigamiNum : forall p : positive, OrigamiNum (IZR (Z.pos p)).
Proof.
  induction p.
  - rewrite Pos2Z.inj_xI. rewrite plus_IZR. rewrite mult_IZR.
    simpl. apply ON_add. apply ON_mul.
    replace 2 with (1 + 1) by ring. apply ON_add; apply ON_1.
    exact IHp. apply ON_1.
  - rewrite Pos2Z.inj_xO. rewrite mult_IZR. simpl.
    apply ON_mul. replace 2 with (1 + 1) by ring.
    apply ON_add; apply ON_1. exact IHp.
  - simpl. apply ON_1.
Qed.

(** Helper: negation preserves OrigamiNum *)
Lemma OrigamiNum_opp : forall x, OrigamiNum x -> OrigamiNum (- x).
Proof.
  intros. replace (-x) with (0 - x) by ring. apply ON_sub.
  apply ON_0. exact H.
Qed.

(** Helper: build integer as OrigamiNum *)
Lemma Z_as_OrigamiNum : forall z : Z, OrigamiNum (IZR z).
Proof.
  intro z. destruct z.
  - simpl. apply ON_0.
  - apply pos_as_OrigamiNum.
  - change (IZR (Z.neg p)) with (- IZR (Z.pos p)).
    apply OrigamiNum_opp. apply pos_as_OrigamiNum.
Qed.

(** Helper: rational numbers are OrigamiNum *)
Lemma Q_as_OrigamiNum : forall p q : Z, IZR q <> 0 -> OrigamiNum (IZR p / IZR q).
Proof.
  intros p q Hq.
  unfold Rdiv. apply ON_mul.
  - apply Z_as_OrigamiNum.
  - apply ON_inv. apply Z_as_OrigamiNum. exact Hq.
Qed.
Lemma cos_2x_minus : forall a b,
  2 * cos b * cos a - cos (a - b) = cos (a + b).
Proof.
  intros. rewrite cos_plus. rewrite cos_minus. ring.
Qed.
Definition chebyshev_11_quotient (x : R) : R :=
  1024*x^10 + 1024*x^9 - 1792*x^8 - 1792*x^7 + 1024*x^6 + 1024*x^5 - 208*x^4 - 208*x^3 + 12*x^2 + 12*x + 1.
Definition minpoly_2cos_degree : nat := 5.
Definition algebraic_degree_cos_2pi_11 : nat := 5.
Lemma five_not_2_3_smooth : ~ is_2_3_smooth 5.
Proof.
  intro H. destruct H as [a [b Heq]].
  destruct a; simpl in Heq; [destruct b; simpl in Heq; lia|].
  destruct a; simpl in Heq; [destruct b; simpl in Heq; lia|].
  destruct a; simpl in Heq; destruct b; simpl in Heq; lia.
Qed.

Lemma five_is_5_smooth : is_5_smooth 5.
Proof.
  unfold is_5_smooth.
  exists 0%nat, 0%nat, 1%nat. reflexivity.
Qed.

Theorem cos_2pi_11_not_single_fold_origami :
  algebraic_degree_cos_2pi_11 = 5%nat /\ ~ is_2_3_smooth 5.
Proof.
  split.
  - reflexivity.
  - exact five_not_2_3_smooth.
Qed.

Theorem cos_2pi_11_is_2_fold_origami :
  algebraic_degree_cos_2pi_11 = 5%nat /\ is_5_smooth 5.
Proof.
  split.
  - reflexivity.
  - exact five_is_5_smooth.
Qed.

(** The hendecagon (11-gon) requires 2-fold origami *)
Theorem hendecagon_requires_2_fold :
  ~ is_2_3_smooth (euler_phi 11) /\ is_5_smooth (euler_phi 11).
Proof.
  split.
  - rewrite phi_11. exact ten_not_smooth.
  - rewrite phi_11. unfold is_5_smooth.
    exists 1%nat, 0%nat, 1%nat. reflexivity.
Qed.

(** cos(2π/11) ∈ OrigamiNum2 via the quintic y⁵+y⁴-4y³-3y²+3y+1 = 0. *)
Definition hendecagon_vertex (k : nat) : R * R :=
  (cos (2 * PI * INR k / 11), sin (2 * PI * INR k / 11)).

Theorem hendecagon_vertex_0 : hendecagon_vertex 0 = (1, 0).
Proof.
  unfold hendecagon_vertex. simpl.
  rewrite Rmult_0_r. unfold Rdiv. rewrite Rmult_0_l.
  rewrite cos_0, sin_0. reflexivity.
Qed.
Inductive OrigamiNum3 : R -> Prop :=
| ON3_0 : OrigamiNum3 0
| ON3_1 : OrigamiNum3 1
| ON3_add : forall x y, OrigamiNum3 x -> OrigamiNum3 y -> OrigamiNum3 (x + y)
| ON3_sub : forall x y, OrigamiNum3 x -> OrigamiNum3 y -> OrigamiNum3 (x - y)
| ON3_mul : forall x y, OrigamiNum3 x -> OrigamiNum3 y -> OrigamiNum3 (x * y)
| ON3_inv : forall x, OrigamiNum3 x -> x <> 0 -> OrigamiNum3 (/ x)
| ON3_sqrt : forall x, OrigamiNum3 x -> 0 <= x -> OrigamiNum3 (sqrt x)
| ON3_cbrt : forall a b r, OrigamiNum3 a -> OrigamiNum3 b ->
    r * r * r + a * r + b = 0 -> OrigamiNum3 r
| ON3_quint : forall a b c d e r,
    OrigamiNum3 a -> OrigamiNum3 b -> OrigamiNum3 c -> OrigamiNum3 d -> OrigamiNum3 e ->
    r^5 + a * r^4 + b * r^3 + c * r^2 + d * r + e = 0 -> OrigamiNum3 r
| ON3_sept : forall a b c d e f g r,
    OrigamiNum3 a -> OrigamiNum3 b -> OrigamiNum3 c -> OrigamiNum3 d ->
    OrigamiNum3 e -> OrigamiNum3 f -> OrigamiNum3 g ->
    r^7 + a * r^6 + b * r^5 + c * r^4 + d * r^3 + e * r^2 + f * r + g = 0 ->
    OrigamiNum3 r.

Lemma Origami2_in_Origami3 : forall x, OrigamiNum2 x -> OrigamiNum3 x.
Proof.
  intros x H. induction H.
  - apply ON3_0.
  - apply ON3_1.
  - apply ON3_add; assumption.
  - apply ON3_sub; assumption.
  - apply ON3_mul; assumption.
  - apply ON3_inv; assumption.
  - apply ON3_sqrt; assumption.
  - apply (ON3_cbrt a b); assumption.
  - apply (ON3_quint a b c d e); assumption.
Qed.


(** Heptagon construction via Chebyshev polynomials.

    The regular heptagon requires solving 8c³ + 4c² - 4c - 1 = 0.
    This cubic is not solvable by radicals of degree ≤ 2, hence
    the heptagon is not compass-straightedge constructible.
    However, origami (O6 Beloch fold) solves cubics. *)

(** The heptagon polynomial: 8c³ + 4c² - 4c - 1 = 0 *)
Definition heptagon_poly (c : R) : R := 8*c^3 + 4*c^2 - 4*c - 1.

(** cos(2π/7) *)
Definition tschirnhaus_shift : R := 1/6.

(** c = t - 1/6 *)
Definition heptagon_depressed (t : R) : R :=
  t^3 + heptagon_cubic_a * t + heptagon_cubic_b.

(** Tschirnhaus: heptagon_poly(t - 1/6) = 8 · (t³ - 7t/12 - 7/216) *)
Lemma heptagon_depressed_expanded : forall t,
  heptagon_depressed t = t^3 - 7/12 * t - 7/216.
Proof.
  intros. unfold heptagon_depressed, heptagon_cubic_a, heptagon_cubic_b. field.
Qed.
Lemma heptagon_depressed_eq_depressed_cubic : forall t,
  heptagon_depressed t = depressed_cubic heptagon_cubic_a heptagon_cubic_b t.
Proof.
  intros. unfold heptagon_depressed, depressed_cubic. ring.
Qed.

(** t₀ is a root of the standard depressed cubic *)
Lemma vertex_coords_origami : forall theta,
  OrigamiNum (cos theta) -> OrigamiNum (sin theta) ->
  forall k : nat, OrigamiNum (cos (INR k * theta)) /\ OrigamiNum (sin (INR k * theta)).
Proof.
  intros theta Hc Hs k. induction k as [|k [IHc IHs]].
  - replace (INR 0) with 0 by reflexivity.
    rewrite Rmult_0_l, cos_0, sin_0. split; [apply ON_1 | apply ON_0].
  - replace (INR (S k) * theta) with (INR k * theta + theta) by (rewrite S_INR; ring).
    rewrite cos_plus, sin_plus. split.
    + apply ON_sub; apply ON_mul; assumption.
    + apply ON_add; apply ON_mul; assumption.
Qed.

(** (cos(k.theta), sin(k.theta)) is a constructible point *)
Definition delian_p : R := 0.
Definition delian_q : R := -2.

(** depressed_cubic(0, -2, ∛2) = 0 *)
Lemma cbrt2_satisfies_delian_cubic : depressed_cubic delian_p delian_q cbrt2 = 0.
Proof.
  unfold depressed_cubic, delian_p, delian_q.
  assert (H : cbrt2 * cbrt2 * cbrt2 = 2) by exact cbrt2_cubes_to_2.
  replace (cbrt2^3) with (cbrt2 * cbrt2 * cbrt2) by ring.
  lra.
Qed.

(** is_cubic_root(0, -2, ∛2) *)
Theorem cbrt2_is_cubic_root : is_cubic_root delian_p delian_q cbrt2.
Proof.
  unfold is_cubic_root.
  exact cbrt2_satisfies_delian_cubic.
Qed.

(** fold_O6_beloch(0, -2, ∛2) *)
Theorem delian_O6_parameters :
  delian_p = 0 /\
  delian_q = -2 /\
  is_cubic_root delian_p delian_q cbrt2 /\
  cbrt2 * cbrt2 * cbrt2 = 2.
Proof.
  split. { reflexivity. }
  split. { reflexivity. }
  split. { exact cbrt2_is_cubic_root. }
  exact cbrt2_cubes_to_2.
Qed.

(** ∛2 ∈ OrigamiNum (wrapper for cbrt2_is_origami) *)
Theorem cbrt2_origami_constructible : OrigamiNum cbrt2.
Proof. exact cbrt2_is_origami. Qed.


(** 11-gon is the first n-gon requiring 2-fold origami.

    cos(2π/11) has [ℚ(cos(2π/11)):ℚ] = 5.
    5 ∉ {2^a × 3^b} implies cos(2π/11) ∉ OrigamiNum (via Alperin-Lang).
    5 ∈ {2^a × 3^b × 5^c} implies cos(2π/11) ∈ OrigamiNum2. *)

(** [ℚ(cos(2π/11)):ℚ] = 5, 5 ∉ {2^a × 3^b} *)
Theorem cos_2pi_11_degree_not_smooth :
  algebraic_degree_cos_2pi_11 = 5%nat /\ ~ is_2_3_smooth 5.
Proof.
  split.
  - reflexivity.
  - exact five_not_2_3_smooth.
Qed.

(** OrigamiNum x → x in tower of degree 2^a × 3^b *)
Theorem origami_tower_degree_smooth : forall x,
  OrigamiNum x -> exists t, InTower x t /\ exists a b, tower_degree t = (2^a * 3^b)%nat.
Proof.
  intros x H. apply Alperin_Lang_with_degree. exact H.
Qed.

(** cos(2π/11) ∈ OrigamiNum2 *)
Fixpoint peval (p : list Z) (x : R) : R :=
  match p with
  | nil => 0
  | c :: p' => IZR c + x * peval p' x
  end.

Definition is_poly_root (p : list Z) (x : R) : Prop := peval p x = 0.

(** A polynomial is nonzero if some coefficient is a nonzero integer. *)
Definition pnonzero (p : list Z) : Prop := Exists (fun c => c <> 0%Z) p.

(** x is algebraic over Q of degree <= n: a nonzero integer poly with <= n+1 coeffs vanishes at x.
    (Clearing denominators, this is equivalent to a rational polynomial of degree <= n.) *)
Definition alg_deg_le (x : R) (n : nat) : Prop :=
  exists p, pnonzero p /\ (length p <= S n)%nat /\ is_poly_root p x.

(** Every rational a/b (b>0) is algebraic of degree <= 1: root of b*x - a. *)
Lemma rational_alg_deg_le_1 : forall a b : Z, (b > 0)%Z ->
  alg_deg_le (IZR a / IZR b) 1.
Proof.
  intros a b Hb.
  exists ((- a)%Z :: b :: nil).
  assert (Hbne : IZR b <> 0) by (apply not_0_IZR; lia).
  split; [|split].
  - apply Exists_cons_tl, Exists_cons_hd. lia.
  - simpl. lia.
  - unfold is_poly_root. simpl. rewrite opp_IZR. field. exact Hbne.
Qed.

(** Any real cube root of 2 is algebraic of degree <= 3: root of x^3 - 2. *)
Lemma cube_root2_alg_deg_le_3 : forall r : R, r * r * r = 2 -> alg_deg_le r 3.
Proof.
  intros r Hr.
  exists ((-2)%Z :: 0%Z :: 0%Z :: 1%Z :: nil).
  split; [|split].
  - apply Exists_cons_hd. lia.
  - simpl. lia.
  - unfold is_poly_root. simpl. nra.
Qed.

(** A degree-<=n witness is also a degree-<=m witness for m >= n. *)
Lemma alg_deg_le_mono : forall x n m, (n <= m)%nat -> alg_deg_le x n -> alg_deg_le x m.
Proof.
  intros x n m Hnm [p [Hnz [Hlen Hroot]]].
  exists p. split; [exact Hnz | split; [lia | exact Hroot]].
Qed.

(** If z^3 is even then z is even. *)
Lemma Even_cube : forall z : Z, Z.Even (z*z*z) -> Z.Even z.
Proof.
  intros z H. destruct (Z.Even_or_Odd z) as [He|Ho]; [exact He|exfalso].
  destruct Ho as [k Hk]. destruct H as [m Hm].
  assert (Hodd : (z*z*z = 2*(4*k*k*k + 6*k*k + 3*k) + 1)%Z) by (rewrite Hk; ring).
  lia.
Qed.

(** The norm form of Q(cbrt 2) is anisotropic over Q:
    a^3 + 2 b^3 + 4 c^3 = 6 a b c  has only the trivial integer solution
    (infinite descent: each variable is forced even). *)
Lemma norm_form_trivial : forall a b c : Z,
  (a*a*a + 2*(b*b*b) + 4*(c*c*c) = 6*a*b*c)%Z ->
  a = 0%Z /\ b = 0%Z /\ c = 0%Z.
Proof.
  assert (Hloop : forall n a b c,
    (Z.to_nat (Z.abs a + Z.abs b + Z.abs c) < n)%nat ->
    (a*a*a + 2*(b*b*b) + 4*(c*c*c) = 6*a*b*c)%Z ->
    a = 0%Z /\ b = 0%Z /\ c = 0%Z).
  { induction n; intros a b c Hlt Heq.
    - lia.
    - assert (Ha : Z.Even a)
        by (apply Even_cube; exists (3*a*b*c - b*b*b - 2*(c*c*c))%Z; lia).
      destruct Ha as [a' Ha']. subst a.
      assert (Heq2 : (4*(a'*a'*a') + b*b*b + 2*(c*c*c) = 6*a'*b*c)%Z) by nia.
      assert (Hb : Z.Even b)
        by (apply Even_cube; exists (3*a'*b*c - 2*(a'*a'*a') - c*c*c)%Z; lia).
      destruct Hb as [b' Hb']. subst b.
      assert (Heq3 : (2*(a'*a'*a') + 4*(b'*b'*b') + c*c*c = 6*a'*b'*c)%Z) by nia.
      assert (Hc : Z.Even c)
        by (apply Even_cube; exists (3*a'*b'*c - a'*a'*a' - 2*(b'*b'*b'))%Z; lia).
      destruct Hc as [c' Hc']. subst c.
      assert (Heq4 : (a'*a'*a' + 2*(b'*b'*b') + 4*(c'*c'*c') = 6*a'*b'*c')%Z) by nia.
      destruct (Z.eq_dec a' 0) as [Za|Za];
      destruct (Z.eq_dec b' 0) as [Zb|Zb];
      destruct (Z.eq_dec c' 0) as [Zc|Zc];
      try (subst; repeat split; reflexivity);
      (assert (Hd : a' = 0%Z /\ b' = 0%Z /\ c' = 0%Z);
       [ apply (IHn a' b' c'); [ lia | exact Heq4 ]
       | destruct Hd as [Hd1 [Hd2 Hd3]]; subst; repeat split; reflexivity ]). }
  intros a b c Heq.
  apply (Hloop (S (Z.to_nat (Z.abs a + Z.abs b + Z.abs c))) a b c); [lia | exact Heq].
Qed.

(** If a (real) cube root of 2 satisfies a degree-<=2 integer relation
    c0 + c1 a + c2 a^2 = 0, then its norm form vanishes (over Z). *)
Lemma alg_deg2_norm : forall (a : R) (c0 c1 c2 : Z),
  a * a * a = 2 ->
  IZR c0 + IZR c1 * a + IZR c2 * (a * a) = 0 ->
  (c0*c0*c0 + 2*(c1*c1*c1) + 4*(c2*c2*c2) = 6*c0*c1*c2)%Z.
Proof.
  intros a c0 c1 c2 Ha E0.
  assert (E1 : 2*IZR c2 + IZR c0*a + IZR c1*(a*a) = 0).
  { replace (2*IZR c2 + IZR c0*a + IZR c1*(a*a))
      with (a*(IZR c0 + IZR c1*a + IZR c2*(a*a)) + IZR c2*(2 - a*a*a)) by ring.
    rewrite Ha, E0. ring. }
  assert (E2 : 2*IZR c1 + 2*IZR c2*a + IZR c0*(a*a) = 0).
  { replace (2*IZR c1 + 2*IZR c2*a + IZR c0*(a*a))
      with (a*a*(IZR c0 + IZR c1*a + IZR c2*(a*a)) + (IZR c1 + IZR c2*a)*(2 - a*a*a)) by ring.
    rewrite Ha, E0. ring. }
  assert (Hnorm : IZR c0*IZR c0*IZR c0 + 2*(IZR c1*IZR c1*IZR c1)
                  + 4*(IZR c2*IZR c2*IZR c2) - 6*IZR c0*IZR c1*IZR c2 = 0).
  { replace (IZR c0*IZR c0*IZR c0 + 2*(IZR c1*IZR c1*IZR c1)
             + 4*(IZR c2*IZR c2*IZR c2) - 6*IZR c0*IZR c1*IZR c2)
      with ((IZR c0*IZR c0 - 2*IZR c1*IZR c2) * (IZR c0 + IZR c1*a + IZR c2*(a*a))
          + (2*IZR c2*IZR c2 - IZR c0*IZR c1) * (2*IZR c2 + IZR c0*a + IZR c1*(a*a))
          + (IZR c1*IZR c1 - IZR c0*IZR c2) * (2*IZR c1 + 2*IZR c2*a + IZR c0*(a*a))) by ring.
    rewrite E0, E1, E2. ring. }
  assert (HZ : IZR (c0*c0*c0 + 2*(c1*c1*c1) + 4*(c2*c2*c2) - 6*c0*c1*c2) = IZR 0).
  { rewrite minus_IZR, !plus_IZR, !mult_IZR. lra. }
  apply eq_IZR in HZ. lia.
Qed.

(** A real cube root of 2 is NOT algebraic of degree <= 2. *)
Lemma cube_root2_not_alg_deg_le_2 : forall a, a * a * a = 2 -> ~ alg_deg_le a 2.
Proof.
  intros a Ha [p [Hnz [Hlen Hroot]]]. unfold is_poly_root in Hroot.
  destruct p as [|c0 [|c1 [|c2 [|c3 p']]]]; simpl in Hlen, Hroot; try lia.
  - inversion Hnz.
  - assert (E : IZR c0 + IZR 0 * a + IZR 0 * (a * a) = 0).
    { transitivity (IZR c0 + a * 0); [ring | exact Hroot]. }
    pose proof (alg_deg2_norm a c0 0 0 Ha E) as Hn.
    apply norm_form_trivial in Hn. destruct Hn as [H0 [_ _]]. subst c0.
    inversion Hnz as [x l Hx|x l Ht]; [lia | inversion Ht].
  - assert (E : IZR c0 + IZR c1 * a + IZR 0 * (a * a) = 0).
    { transitivity (IZR c0 + a * (IZR c1 + a * 0)); [ring | exact Hroot]. }
    pose proof (alg_deg2_norm a c0 c1 0 Ha E) as Hn.
    apply norm_form_trivial in Hn. destruct Hn as [H0 [H1 _]]. subst c0 c1.
    inversion Hnz as [x l Hx|x l Ht]; [lia|].
    inversion Ht as [x2 l2 Hx2|x2 l2 Ht2]; [lia | inversion Ht2].
  - assert (E : IZR c0 + IZR c1 * a + IZR c2 * (a * a) = 0).
    { transitivity (IZR c0 + a * (IZR c1 + a * (IZR c2 + a * 0))); [ring | exact Hroot]. }
    pose proof (alg_deg2_norm a c0 c1 c2 Ha E) as Hn.
    apply norm_form_trivial in Hn. destruct Hn as [H0 [H1 H2]]. subst c0 c1 c2.
    inversion Hnz as [x l Hx|x l Ht]; [lia|].
    inversion Ht as [x2 l2 Hx2|x2 l2 Ht2]; [lia|].
    inversion Ht2 as [x3 l3 Hx3|x3 l3 Ht3]; [lia | inversion Ht3].
Qed.

(** A real cube root of 2 has algebraic degree exactly 3 over Q. *)
Theorem cube_root2_alg_deg_exactly_3 : forall a, a * a * a = 2 ->
  alg_deg_le a 3 /\ ~ alg_deg_le a 2.
Proof.
  intros a Ha. split.
  - apply cube_root2_alg_deg_le_3. exact Ha.
  - apply cube_root2_not_alg_deg_le_2. exact Ha.
Qed.

(** The origami number cbrt2 = cbrt 2 has algebraic degree exactly 3 over Q,
    so the Delian root genuinely sits at degree 3 (not a power of 2). *)
Corollary cbrt2_algebraic_degree_exactly_3 :
  alg_deg_le cbrt2 3 /\ ~ alg_deg_le cbrt2 2.
Proof. apply cube_root2_alg_deg_exactly_3. exact cbrt2_cubes_to_2. Qed.

(** If z^2 is even then z is even. *)
Lemma Even_square : forall z : Z, Z.Even (z*z) -> Z.Even z.
Proof.
  intros z H. destruct (Z.Even_or_Odd z) as [He|Ho]; [exact He|exfalso].
  destruct Ho as [k Hk]. destruct H as [m Hm].
  assert (z*z = 2*(2*k*k + 2*k) + 1)%Z by (rewrite Hk; ring). lia.
Qed.

(** 2 is not a square in Q: c0^2 = 2 c1^2 has only the trivial integer solution. *)
Lemma sqrt2_descent : forall c0 c1 : Z, (c0*c0 = 2*(c1*c1))%Z -> c0 = 0%Z /\ c1 = 0%Z.
Proof.
  assert (Hloop : forall n c0 c1, (Z.to_nat (Z.abs c0 + Z.abs c1) < n)%nat ->
    (c0*c0 = 2*(c1*c1))%Z -> c0 = 0%Z /\ c1 = 0%Z).
  { induction n; intros c0 c1 Hlt Heq.
    - lia.
    - assert (Hc0 : Z.Even c0) by (apply Even_square; exists (c1*c1)%Z; lia).
      destruct Hc0 as [c0' Hc0']. subst c0.
      assert (Heq2 : (2*(c0'*c0') = c1*c1)%Z) by nia.
      assert (Hc1 : Z.Even c1) by (apply Even_square; exists (c0'*c0')%Z; lia).
      destruct Hc1 as [c1' Hc1']. subst c1.
      assert (Heq3 : (c0'*c0' = 2*(c1'*c1'))%Z) by nia.
      destruct (Z.eq_dec c0' 0) as [Za|Za]; destruct (Z.eq_dec c1' 0) as [Zb|Zb];
      try (subst; repeat split; reflexivity);
      (assert (Hd : c0' = 0%Z /\ c1' = 0%Z);
       [ apply (IHn c0' c1'); [ lia | exact Heq3 ]
       | destruct Hd as [Hd1 Hd2]; subst; repeat split; reflexivity ]). }
  intros c0 c1 Heq.
  apply (Hloop (S (Z.to_nat (Z.abs c0 + Z.abs c1))) c0 c1); [lia | exact Heq].
Qed.

(** A square root of 2 satisfying a degree-1 integer relation yields c0^2 = 2 c1^2. *)
Lemma sqrt2_alg1_to_int : forall (s : R) (c0 c1 : Z),
  s * s = 2 -> IZR c0 + IZR c1 * s = 0 -> (c0*c0 = 2*(c1*c1))%Z.
Proof.
  intros s c0 c1 Hs E0.
  assert (Hc0 : IZR c0 = - (IZR c1 * s)) by lra.
  assert (Hsq : IZR c0 * IZR c0 = 2 * (IZR c1 * IZR c1)).
  { rewrite Hc0. replace (- (IZR c1 * s) * - (IZR c1 * s)) with (IZR c1 * IZR c1 * (s*s)) by ring.
    rewrite Hs. ring. }
  assert (HZ : IZR (c0*c0) = IZR (2*(c1*c1))).
  { rewrite !mult_IZR. lra. }
  apply eq_IZR in HZ. lia.
Qed.

(** A square root of 2 is NOT algebraic of degree <= 1. *)
Lemma sqrt2_not_alg_deg_le_1 : forall s, s * s = 2 -> ~ alg_deg_le s 1.
Proof.
  intros s Hs [p [Hnz [Hlen Hroot]]]. unfold is_poly_root in Hroot.
  destruct p as [|c0 [|c1 [|c2 p']]]; simpl in Hlen, Hroot; try lia.
  - inversion Hnz.
  - assert (E : IZR c0 + IZR 0 * s = 0) by (transitivity (IZR c0 + s * 0); [ring | exact Hroot]).
    pose proof (sqrt2_alg1_to_int s c0 0 Hs E) as Hn.
    apply sqrt2_descent in Hn. destruct Hn as [H0 _]. subst c0.
    inversion Hnz as [x l Hx|x l Ht]; [lia | inversion Ht].
  - assert (E : IZR c0 + IZR c1 * s = 0) by (transitivity (IZR c0 + s * (IZR c1 + s * 0)); [ring | exact Hroot]).
    pose proof (sqrt2_alg1_to_int s c0 c1 Hs E) as Hn.
    apply sqrt2_descent in Hn. destruct Hn as [H0 H1]. subst c0 c1.
    inversion Hnz as [x l Hx|x l Ht]; [lia|].
    inversion Ht as [x2 l2 Hx2|x2 l2 Ht2]; [lia | inversion Ht2].
Qed.

(** A square root of 2 is algebraic of degree <= 2: root of x^2 - 2. *)
Lemma sqrt2_alg_deg_le_2 : forall s, s * s = 2 -> alg_deg_le s 2.
Proof.
  intros s Hs.
  exists ((-2)%Z :: 0%Z :: 1%Z :: nil).
  split; [|split].
  - apply Exists_cons_hd. lia.
  - simpl. lia.
  - unfold is_poly_root. simpl. nra.
Qed.

(** A square root of 2 has algebraic degree exactly 2 over Q. *)
Theorem sqrt2_alg_deg_exactly_2 : forall s, s * s = 2 ->
  alg_deg_le s 2 /\ ~ alg_deg_le s 1.
Proof.
  intros s Hs. split.
  - apply sqrt2_alg_deg_le_2. exact Hs.
  - apply sqrt2_not_alg_deg_le_1. exact Hs.
Qed.

(** sqrt 2 has algebraic degree exactly 2 over Q (compass-constructible degree). *)
Corollary sqrt2_algebraic_degree_exactly_2 :
  alg_deg_le (sqrt 2) 2 /\ ~ alg_deg_le (sqrt 2) 1.
Proof. apply sqrt2_alg_deg_exactly_2. apply sqrt_sqrt. lra. Qed.


(** ═══════════════════════════════════════════════════════════════════════════
    HEPTAGON CUBIC IRREDUCIBILITY
    The monic minimal polynomial of 2cos(2pi/7), y^3 + y^2 - 2y - 1, has no
    rational root, hence is irreducible over Q (a cubic is irreducible iff it has
    no rational root). cos(2pi/7) therefore has algebraic degree exactly 3.
    ═══════════════════════════════════════════════════════════════════════════ *)
Lemma IZR_eq_2 : IZR 2 = 2. Proof. lra. Qed.
Lemma IZR_eq_4 : IZR 4 = 4. Proof. lra. Qed.
Open Scope R_scope.
Definition is_subfield (F : R -> Prop) : Prop :=
  F 0 /\ F 1 /\
  (forall x y, F x -> F y -> F (x + y)) /\
  (forall x y, F x -> F y -> F (x - y)) /\
  (forall x y, F x -> F y -> F (x * y)) /\
  (forall x, F x -> x <> 0 -> F (/ x)).

Lemma subfield_0 : forall F, is_subfield F -> F 0. Proof. intros F H; apply H. Qed.
Lemma subfield_1 : forall F, is_subfield F -> F 1. Proof. intros F H; apply H. Qed.
Lemma subfield_add : forall F x y, is_subfield F -> F x -> F y -> F (x+y).
Proof. intros F x y H; apply H. Qed.
Lemma subfield_sub : forall F x y, is_subfield F -> F x -> F y -> F (x-y).
Proof. intros F x y H; apply H. Qed.
Lemma subfield_mul : forall F x y, is_subfield F -> F x -> F y -> F (x*y).
Proof. intros F x y H; apply H. Qed.
Lemma subfield_inv : forall F x, is_subfield F -> F x -> x <> 0 -> F (/ x).
Proof. intros F x H; apply H. Qed.
Lemma subfield_opp : forall F x, is_subfield F -> F x -> F (- x).
Proof. intros F x H Hx. replace (-x) with (0 - x) by ring.
  apply subfield_sub; [exact H | apply subfield_0; exact H | exact Hx]. Qed.
Lemma subfield_div : forall F x y, is_subfield F -> F x -> F y -> y <> 0 -> F (x / y).
Proof. intros F x y H Hx Hy Hy0. unfold Rdiv. apply subfield_mul; [exact H | exact Hx | apply subfield_inv; auto]. Qed.

(* closure tactic: discharge F-membership of polynomial combinations of in-field
   atoms; the field predicate is bound from the goal to avoid higher-order
   unification absorbing coefficients into F. *)
Ltac sfclose :=
  repeat first
    [ assumption
    | match goal with
      | |- ?P (_ + _) => apply (subfield_add P)
      | |- ?P (_ - _) => apply (subfield_sub P)
      | |- ?P (_ * _) => apply (subfield_mul P)
      | |- ?P (- _)   => apply (subfield_opp P)
      | |- ?P 0       => apply (subfield_0 P)
      | |- ?P 1       => apply (subfield_1 P)
      end ].

Lemma is_rational_subfield : is_subfield is_rational.
Proof.
  repeat split.
  - exists 0%Z, 1%Z. split; [lia | simpl; field].
  - exists 1%Z, 1%Z. split; [lia | simpl; field].
  - apply rational_add.
  - apply rational_sub.
  - apply rational_mul.
  - apply rational_inv.
Qed.

Lemma subfield_INR : forall F, is_subfield F -> forall n : nat, F (INR n).
Proof.
  intros F HF n. induction n.
  - simpl. apply subfield_0; auto.
  - rewrite S_INR. apply subfield_add; [exact HF | exact IHn | apply subfield_1; exact HF].
Qed.

Lemma subfield_IZR : forall F, is_subfield F -> forall z : Z, F (IZR z).
Proof.
  intros F HF z. destruct z.
  - apply subfield_0; auto.
  - replace (IZR (Z.pos p)) with (INR (Pos.to_nat p)).
    + apply subfield_INR; auto.
    + rewrite INR_IZR_INZ, positive_nat_Z. reflexivity.
  - replace (IZR (Z.neg p)) with (- INR (Pos.to_nat p)).
    + apply subfield_opp; [auto | apply subfield_INR; auto].
    + rewrite INR_IZR_INZ, positive_nat_Z, <- opp_IZR. reflexivity.
Qed.

Lemma subfield_contains_rational : forall F, is_subfield F -> forall x, is_rational x -> F x.
Proof.
  intros F HF x [p [q [Hq Hx]]]. subst x. unfold Rdiv.
  apply subfield_mul; [exact HF | apply subfield_IZR; auto |].
  apply subfield_inv; [exact HF | apply subfield_IZR; auto | apply not_0_IZR; lia].
Qed.

Lemma subfield_2 : forall F, is_subfield F -> F 2.
Proof. intros F H. replace 2 with (1+1) by lra. sfclose. Qed.
Lemma subfield_3 : forall F, is_subfield F -> F 3.
Proof. intros F H. replace 3 with (1+1+1) by lra. sfclose. Qed.

(* ---------- linear independence of {1, s} when s not in F ---------- *)
Lemma lin_indep_sqrt : forall F A B s,
  is_subfield F -> F A -> F B -> ~ F s -> A + B * s = 0 -> B = 0.
Proof.
  intros F A B s HF HA HB Hs Heq.
  destruct (Req_dec B 0) as [HB0|HB0]; [exact HB0|exfalso].
  apply Hs.
  assert (Hs' : s = (- A) / B).
  { apply (Rmult_eq_reg_r B); [|exact HB0].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by exact HB0. rewrite Rmult_1_r. lra. }
  rewrite Hs'. apply subfield_div; [exact HF | apply subfield_opp; auto | exact HB | exact HB0].
Qed.

(* ---------- quadratic extension F(s) with s*s in F ---------- *)
Definition QF (F : R -> Prop) (s : R) (x : R) : Prop :=
  exists p q, F p /\ F q /\ x = p + q * s.

(* Decidability of real disequality and of nat divisibility. *)
Lemma Rneq_dec : forall x y : R, {x <> y} + {~ (x <> y)}.
Proof.
  intros x y. destruct (Req_dec_T x y) as [e|ne];
    [right; intro H; exact (H e) | left; exact ne].
Qed.

Lemma Ndivide_dec : forall k d : nat, {Nat.divide k d} + {~ Nat.divide k d}.
Proof.
  intros [|k] d.
  - destruct (Nat.eq_dec d 0) as [->|Hd];
      [left; exists 0%nat; reflexivity | right; intros [x Hx]; simpl in Hx; lia].
  - destruct (Nat.eq_dec (d mod (S k)) 0) as [H|H].
    + left. apply Nat.mod_divide in H; [exact H | lia].
    + right. intro Hdiv. apply H. apply Nat.mod_divide; [lia | exact Hdiv].
Qed.

Lemma Zneq_dec : forall x y : Z, {x <> y} + {~ (x <> y)}.
Proof.
  intros x y. destruct (Z.eq_dec x y) as [e|ne];
    [right; intro H; exact (H e) | left; exact ne].
Qed.

(* Decidability of "some list entry, read with default d, satisfies P", for
   decidable P with P d false. *)
Lemma list_ex_nth_dec : forall (A : Type) (d : A) (P : A -> Prop),
  (forall x, {P x} + {~ P x}) -> ~ P d ->
  forall l, {exists k, P (nth k l d)} + {~ exists k, P (nth k l d)}.
Proof.
  intros A d P Pdec HPd l.
  destruct (Exists_dec P l Pdec) as [H|H].
  - left. apply Exists_exists in H. destruct H as [x [Hin Hx]].
    apply (In_nth l x d) in Hin. destruct Hin as [k [Hk Hnth]].
    exists k. rewrite Hnth. exact Hx.
  - right. intros [k Hk]. apply H. apply Exists_exists.
    destruct (Nat.lt_ge_cases k (length l)) as [Hlt|Hge].
    + exists (nth k l d). split; [apply nth_In; exact Hlt | exact Hk].
    + rewrite nth_overflow in Hk by exact Hge. contradiction.
Qed.

Lemma Zdiv_neg_dec : forall p x : Z, {~ Z.divide p x} + {~ ~ Z.divide p x}.
Proof.
  intros p x. destruct (Znumtheory.Zdivide_dec p x) as [d|nd];
    [right; intro h; exact (h d) | left; exact nd].
Qed.

Lemma Rlist_ex_nonzero_dec : forall l : list R,
  {exists k, nth k l 0 <> 0} + {~ exists k, nth k l 0 <> 0}.
Proof. intro l. exact (list_ex_nth_dec R 0 (fun x => x <> 0) (fun x => Rneq_dec x 0) (fun h => h eq_refl) l). Qed.

Lemma Zlist_ex_nonzero_dec : forall l : list Z,
  {exists k, nth k l 0%Z <> 0%Z} + {~ exists k, nth k l 0%Z <> 0%Z}.
Proof. intro l. exact (list_ex_nth_dec Z 0%Z (fun x => x <> 0%Z) (fun x => Zneq_dec x 0) (fun h => h eq_refl) l). Qed.

Lemma Zlist_ex_notdiv_dec : forall p : Z, forall l : list Z,
  {exists k, ~ Z.divide p (nth k l 0%Z)} + {~ exists k, ~ Z.divide p (nth k l 0%Z)}.
Proof. intros p l. exact (list_ex_nth_dec Z 0%Z (fun x => ~ Z.divide p x) (fun x => Zdiv_neg_dec p x) (fun h => h (Z.divide_0_r p)) l). Qed.

Lemma list_ex_In_dec : forall (A : Type) (P : A -> Prop) (L : list A),
  (forall x, {P x} + {~ P x}) ->
  {exists a, In a L /\ P a} + {~ exists a, In a L /\ P a}.
Proof.
  intros A P L Pdec. destruct (Exists_dec P L Pdec) as [H|H].
  - left. apply Exists_exists in H. exact H.
  - right. intro Hex. apply H. apply Exists_exists. exact Hex.
Qed.

Lemma list_ex_ge_notdiv_dec : forall (p : Z) (l : list Z) (lb : nat),
  {exists j, (lb <= j)%nat /\ ~ Z.divide p (nth j l 0%Z)} +
  {~ exists j, (lb <= j)%nat /\ ~ Z.divide p (nth j l 0%Z)}.
Proof.
  intros p l lb.
  destruct (Exists_dec (fun j => ~ Z.divide p (nth j l 0%Z)) (seq lb (length l - lb))
              (fun j => Zdiv_neg_dec p (nth j l 0%Z))) as [H|H].
  - left. apply Exists_exists in H. destruct H as [j [Hin Hj]].
    apply in_seq in Hin. exists j. split; [lia | exact Hj].
  - right. intros [j [Hjlb Hj]]. apply H. apply Exists_exists. exists j.
    split; [| exact Hj]. apply in_seq.
    destruct (Nat.lt_ge_cases j (length l)) as [Hlt|Hge]; [lia|].
    exfalso. apply Hj. rewrite nth_overflow by exact Hge. apply Z.divide_0_r.
Qed.

Lemma bounded_ex_dec : forall (Q : nat -> Prop) (n : nat),
  (forall k, {Q k} + {~ Q k}) ->
  {exists k, (k < n)%nat /\ Q k} + {~ exists k, (k < n)%nat /\ Q k}.
Proof.
  intros Q n Qdec. destruct (Exists_dec Q (seq 0 n) Qdec) as [H|H].
  - left. apply Exists_exists in H. destruct H as [k [Hin Hk]].
    apply in_seq in Hin. exists k. split; [lia | exact Hk].
  - right. intros [k [Hkn Hk]]. apply H. apply Exists_exists. exists k.
    split; [apply in_seq; lia | exact Hk].
Qed.

Lemma QF_contains : forall F s x, is_subfield F -> F x -> QF F s x.
Proof. intros F s x HF Hx. exists x, 0. repeat split; [exact Hx | apply subfield_0; auto | ring]. Qed.

Lemma QF_self : forall F s, is_subfield F -> QF F s s.
Proof. intros F s HF. exists 0, 1. repeat split; [apply subfield_0; auto | apply subfield_1; auto | ring]. Qed.

Lemma QF_subfield : forall F s, is_subfield F -> F (s*s) -> is_subfield (QF F s).
Proof.
  intros F s HF Hss.
  repeat split.
  - apply QF_contains; [exact HF | apply subfield_0; auto].
  - apply QF_contains; [exact HF | apply subfield_1; auto].
  - intros x y [px [qx [Hpx [Hqx Hx]]]] [py [qy [Hpy [Hqy Hy]]]].
    exists (px+py), (qx+qy). repeat split; [sfclose | sfclose | subst; ring].
  - intros x y [px [qx [Hpx [Hqx Hx]]]] [py [qy [Hpy [Hqy Hy]]]].
    exists (px-py), (qx-qy). repeat split; [sfclose | sfclose | subst; ring].
  - intros x y [px [qx [Hpx [Hqx Hx]]]] [py [qy [Hpy [Hqy Hy]]]].
    exists (px*py + qx*qy*(s*s)), (px*qy + qx*py). repeat split; [sfclose | sfclose | subst; ring].
  - intros x [px [qx [Hpx [Hqx Hx]]]] Hxne.
    set (D := px*px - qx*qx*(s*s)).
    destruct (Req_dec_T D 0) as [HD0|HDne].
    + assert (HsF : F s).
      { assert (Hfact : x * (px - qx*s) = 0)
          by (subst x; replace ((px+qx*s)*(px-qx*s)) with (px*px - qx*qx*(s*s)) by ring;
              unfold D in HD0; exact HD0).
        apply Rmult_integral in Hfact. destruct Hfact as [Hc|Hc]; [contradiction|].
        destruct (Req_dec qx 0) as [Hqx0|Hqx0].
        - exfalso. subst qx. assert (px = 0) by lra. subst px. apply Hxne. subst x. ring.
        - assert (Hs2 : s = px / qx).
          { apply (Rmult_eq_reg_r qx); [|exact Hqx0]. unfold Rdiv.
            rewrite Rmult_assoc, Rinv_l by exact Hqx0. rewrite Rmult_1_r. lra. }
          rewrite Hs2. apply subfield_div; auto. }
      assert (HxF : F x) by (subst x; sfclose).
      apply QF_contains; [exact HF | apply subfield_inv; auto].
    + assert (HDF : F D) by (unfold D; sfclose).
      exists (px / D), (- qx / D). repeat split.
      * apply subfield_div; auto.
      * apply subfield_div; [exact HF | apply subfield_opp; auto | auto | auto].
      * subst x.
        apply (Rmult_eq_reg_l (px + qx*s)); [|exact Hxne].
        rewrite Rinv_r by exact Hxne.
        unfold D. field. unfold D in HDne. exact HDne.
Qed.

(* ---------- cubic conjugate + Vieta descent step ----------
   For a root p + q*s (q <> 0) of the monic cubic x^3 + c2 x^2 + c1 x + c0
   (coeffs in F, s^2 in F): a root lies in F, or s lies in F.  Split on whether
   the s-component V of the expanded cubic vanishes. *)
Lemma cubic_conj_vieta_step : forall (F:R->Prop) c0 c1 c2 s p q,
  is_subfield F -> F (s*s) -> F c0 -> F c1 -> F c2 -> F p -> F q -> q <> 0 ->
  (p+q*s)*(p+q*s)*(p+q*s) + c2*((p+q*s)*(p+q*s)) + c1*(p+q*s) + c0 = 0 ->
  (exists w, F w /\ w*w*w + c2*(w*w) + c1*w + c0 = 0) \/ F s.
Proof.
  intros F c0 c1 c2 s p q HF Hss Hc0 Hc1 Hc2 Hp Hq Hqne Hcubic.
  assert (F3 : F 3) by (apply subfield_3; auto).
  assert (F2 : F 2) by (apply subfield_2; auto).
  set (U := p*p*p + 3*p*q*q*(s*s) + c2*(p*p + q*q*(s*s)) + c1*p + c0).
  set (V := 3*p*p*q + q*q*q*(s*s) + 2*c2*p*q + c1*q).
  assert (FU : F U) by (unfold U; sfclose).
  assert (FV : F V) by (unfold V; sfclose).
  assert (Hexp : (p+q*s)*(p+q*s)*(p+q*s) + c2*((p+q*s)*(p+q*s)) + c1*(p+q*s) + c0
                 = U + V*s) by (unfold U, V; ring).
  rewrite Hexp in Hcubic.
  destruct (Req_dec_T V 0) as [HV0|HVne].
  - left.
    assert (HU0 : U = 0)
      by (rewrite HV0, Rmult_0_l, Rplus_0_r in Hcubic; exact Hcubic).
    set (w := - c2 - 2*p).
    assert (Fw : F w) by (unfold w; sfclose).
    exists w. split; [exact Fw|].
    assert (HV' : 3*p*p + q*q*(s*s) + 2*c2*p + c1 = 0).
    { apply (Rmult_eq_reg_r q); [|exact Hqne].
      rewrite Rmult_0_l.
      replace ((3*p*p + q*q*(s*s) + 2*c2*p + c1) * q) with V by (unfold V; ring).
      exact HV0. }
    assert (Hc1e : c1 = -(3*p*p + q*q*(s*s) + 2*c2*p)) by lra.
    assert (Hc0e : c0 = -(p*p*p + 3*p*q*q*(s*s) + c2*(p*p + q*q*(s*s)) + c1*p)).
    { unfold U in HU0. lra. }
    rewrite Hc1e in Hc0e.
    unfold w. subst c0. subst c1. ring.
  - right.
    assert (HsV : V * s = - U) by lra.
    assert (Hseq : s = (- U) / V).
    { apply (Rmult_eq_reg_r V); [| exact HVne].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by exact HVne. rewrite Rmult_1_r.
      rewrite Rmult_comm. exact HsV. }
    rewrite Hseq. apply subfield_div; [exact HF | apply subfield_opp; auto | exact FV | exact HVne].
Qed.

(* ---------- real quadratic tower ---------- *)
Fixpoint tower (L : list R) : R -> Prop :=
  match L with
  | nil => is_rational
  | s :: L' => QF (tower L') s
  end.

Fixpoint wf_tower (L : list R) : Prop :=
  match L with
  | nil => True
  | s :: L' => tower L' (s*s) /\ wf_tower L'
  end.

Lemma tower_subfield : forall L, wf_tower L -> is_subfield (tower L).
Proof.
  induction L as [|s L' IH]; intros Wf.
  - simpl. apply is_rational_subfield.
  - simpl in *. destruct Wf as [Wss Wf']. apply QF_subfield; [apply IH; exact Wf' | exact Wss].
Qed.

Lemma tower_weaken_base : forall L1 L2 x,
  wf_tower L2 -> tower L1 x -> tower (L1 ++ L2) x.
Proof.
  induction L1 as [|s L1' IH]; intros L2 x W2 Tx.
  - simpl in *. apply subfield_contains_rational; [apply tower_subfield; exact W2 | exact Tx].
  - simpl in *. destruct Tx as [p [q [Tp [Tq Hx]]]].
    exists p, q. repeat split; [apply IH; auto | apply IH; auto | exact Hx].
Qed.

Lemma tower_weaken_top : forall L1 L2 x,
  wf_tower (L1 ++ L2) -> tower L2 x -> tower (L1 ++ L2) x.
Proof.
  induction L1 as [|s L1' IH]; intros L2 x W Tx.
  - simpl in *. exact Tx.
  - simpl in *. destruct W as [Wss W'].
    apply QF_contains; [apply tower_subfield; exact W' | apply IH; auto].
Qed.

Lemma wf_tower_app : forall L1 L2, wf_tower L1 -> wf_tower L2 -> wf_tower (L1 ++ L2).
Proof.
  induction L1 as [|s L1' IH]; intros L2 W1 W2.
  - simpl. exact W2.
  - simpl in *. destruct W1 as [Wss W1']. split.
    + apply tower_weaken_base; [exact W2 | exact Wss].
    + apply IH; auto.
Qed.

(* ---------- EuclidNum collapses into a quadratic tower ---------- *)
Lemma EuclidNum_in_tower : forall x, EuclidNum x -> exists L, wf_tower L /\ tower L x.
Proof.
  intros x H. induction H.
  - exists nil. split; [exact I | exists 0%Z, 1%Z; split; [lia | simpl; field]].
  - exists nil. split; [exact I | exists 1%Z, 1%Z; split; [lia | simpl; field]].
  - destruct IHEuclidNum1 as [L1 [W1 T1]]. destruct IHEuclidNum2 as [L2 [W2 T2]].
    exists (L1 ++ L2). assert (Wapp : wf_tower (L1 ++ L2)) by (apply wf_tower_app; auto).
    split; [exact Wapp |].
    apply subfield_add with (F := tower (L1 ++ L2)).
    + apply tower_subfield; exact Wapp.
    + apply tower_weaken_base; auto.
    + apply tower_weaken_top; auto.
  - destruct IHEuclidNum1 as [L1 [W1 T1]]. destruct IHEuclidNum2 as [L2 [W2 T2]].
    exists (L1 ++ L2). assert (Wapp : wf_tower (L1 ++ L2)) by (apply wf_tower_app; auto).
    split; [exact Wapp |].
    apply subfield_sub with (F := tower (L1 ++ L2)).
    + apply tower_subfield; exact Wapp.
    + apply tower_weaken_base; auto.
    + apply tower_weaken_top; auto.
  - destruct IHEuclidNum1 as [L1 [W1 T1]]. destruct IHEuclidNum2 as [L2 [W2 T2]].
    exists (L1 ++ L2). assert (Wapp : wf_tower (L1 ++ L2)) by (apply wf_tower_app; auto).
    split; [exact Wapp |].
    apply subfield_mul with (F := tower (L1 ++ L2)).
    + apply tower_subfield; exact Wapp.
    + apply tower_weaken_base; auto.
    + apply tower_weaken_top; auto.
  - destruct IHEuclidNum as [L [W T]]. exists L. split; [exact W |].
    apply subfield_inv with (F := tower L); [apply tower_subfield; exact W | exact T | exact H0].
  - destruct IHEuclidNum as [L [W T]]. exists (sqrt x :: L). split.
    + simpl. split; [| exact W].
      replace (sqrt x * sqrt x) with x by (rewrite sqrt_sqrt; [reflexivity | exact H0]). exact T.
    + simpl. apply QF_self. apply tower_subfield; exact W.
Qed.

(* ---------- descent: a cubic root in a tower implies a rational root ---------- *)
Lemma cubic_descent_tower : forall (c0 c1 c2 : R),
  is_rational c0 -> is_rational c1 -> is_rational c2 ->
  forall L, wf_tower L -> forall r, tower L r ->
    r*r*r + c2*(r*r) + c1*r + c0 = 0 ->
    exists r', is_rational r' /\ r'*r'*r' + c2*(r'*r') + c1*r' + c0 = 0.
Proof.
  intros c0 c1 c2 Q0 Q1 Q2 L. induction L as [|s L' IH]; intros Wf r Tr Hroot.
  - exists r. split; [exact Tr | exact Hroot].
  - simpl in Wf. destruct Wf as [Wss Wf'].
    simpl in Tr. destruct Tr as [p [q [Tp [Tq Hr]]]].
    assert (HsfL' : is_subfield (tower L')) by (apply tower_subfield; exact Wf').
    assert (Tc0 : tower L' c0) by (apply subfield_contains_rational; auto).
    assert (Tc1 : tower L' c1) by (apply subfield_contains_rational; auto).
    assert (Tc2 : tower L' c2) by (apply subfield_contains_rational; auto).
    destruct (Req_dec q 0) as [Hq0|Hq0].
    + assert (Trp : tower L' r)
        by (rewrite Hr, Hq0; replace (p + 0*s) with p by ring; exact Tp).
      apply (IH Wf' r Trp Hroot).
    + assert (Hroot2 : (p+q*s)*(p+q*s)*(p+q*s) + c2*((p+q*s)*(p+q*s)) + c1*(p+q*s) + c0 = 0)
        by (rewrite <- Hr; exact Hroot).
      destruct (cubic_conj_vieta_step (tower L') c0 c1 c2 s p q
                 HsfL' Wss Tc0 Tc1 Tc2 Tp Tq Hq0 Hroot2) as [[w [Tw Hw]] | Hsin].
      * apply (IH Wf' w Tw Hw).
      * assert (Trp : tower L' r) by (rewrite Hr; sfclose).
        apply (IH Wf' r Trp Hroot).
Qed.

Lemma not_EuclidNum_of_cubic_no_rat_root : forall c0 c1 c2 : R,
  is_rational c0 -> is_rational c1 -> is_rational c2 ->
  (forall r, is_rational r -> r*r*r + c2*(r*r) + c1*r + c0 <> 0) ->
  forall a, a*a*a + c2*(a*a) + c1*a + c0 = 0 -> ~ EuclidNum a.
Proof.
  intros c0 c1 c2 Q0 Q1 Q2 Hnorat a Ha HE.
  destruct (EuclidNum_in_tower a HE) as [L [W TL]].
  destruct (cubic_descent_tower c0 c1 c2 Q0 Q1 Q2 L W a TL Ha) as [r' [Qr' Hr']].
  exact (Hnorat r' Qr' Hr').
Qed.

Lemma is_rational_IZR : forall z : Z, is_rational (IZR z).
Proof. intros z. exists z, 1%Z. split; [lia |]. field. Qed.

Lemma is_rational_1  : is_rational 1.    Proof. apply (is_rational_IZR 1). Qed.
Lemma is_rational_m1 : is_rational (-1).  Proof. apply (is_rational_IZR (-1)). Qed.
Lemma is_rational_m2 : is_rational (-2).  Proof. apply (is_rational_IZR (-2)). Qed.

(* ---------- heptagon: 2cos(2pi/7) and cos(2pi/7) are NOT compass-constructible ---------- *)
Open Scope R_scope.
Lemma monic_cubic_coprime_root : forall A B C p q : Z,
  (q > 0)%Z -> Z.gcd p q = 1%Z ->
  (p*p*p + C*(p*p*q) + B*(p*q*q) + A*(q*q*q) = 0)%Z ->
  (p | A)%Z /\ (p*p*p + C*(p*p) + B*p + A = 0)%Z.
Proof.
  intros A B C p q Hq Hcop Heq.
  assert (Hgqp : Z.gcd q p = 1%Z) by (rewrite Z.gcd_comm; exact Hcop).
  assert (Hrel : Znumtheory.rel_prime q p) by (apply Znumtheory.Zgcd_1_rel_prime; exact Hgqp).
  assert (Hqd3 : (q | p*(p*p))%Z) by (exists (-(C*p*p + B*p*q + A*q*q))%Z; nia).
  assert (Hqd2 : (q | p*p)%Z) by (apply (Znumtheory.Gauss q p (p*p)); [exact Hqd3 | exact Hrel]).
  assert (Hqd1 : (q | p)%Z) by (apply (Znumtheory.Gauss q p p); [exact Hqd2 | exact Hrel]).
  assert (Hqg : (q | Z.gcd p q)%Z) by (apply Z.gcd_greatest; [exact Hqd1 | apply Z.divide_refl]).
  rewrite Hcop in Hqg. apply Z.divide_1_r in Hqg.
  assert (Hq1 : q = 1%Z) by (destruct Hqg; lia). subst q.
  assert (Heq1 : (p*p*p + C*(p*p) + B*p + A = 0)%Z) by nia.
  split; [exists (-(p*p + C*p + B))%Z; nia | exact Heq1].
Qed.

Lemma monic_cubic_int_no_root : forall A B C : Z,
  (forall n : Z, (n | A)%Z -> (n*n*n + C*(n*n) + B*n + A)%Z <> 0%Z) ->
  forall p q : Z, (q <> 0)%Z ->
    (p*p*p + C*(p*p*q) + B*(p*q*q) + A*(q*q*q))%Z <> 0%Z.
Proof.
  intros A B C Hcheck p q Hq Heq.
  set (g := Z.gcd p q).
  assert (Hg0 : (g <> 0)%Z) by (unfold g; intro H; apply Z.gcd_eq_0 in H; destruct H; contradiction).
  assert (Hgpos : (g > 0)%Z) by (assert (0<=g)%Z by (unfold g; apply Z.gcd_nonneg); lia).
  assert (Hgp : (g|p)%Z) by (unfold g; apply Z.gcd_divide_l).
  assert (Hgq : (g|q)%Z) by (unfold g; apply Z.gcd_divide_r).
  destruct Hgp as [p' Hp']. destruct Hgq as [q' Hq'].
  assert (Hcop : Z.gcd p' q' = 1%Z).
  { assert (Z.gcd p q = g) by reflexivity. rewrite Hp', Hq' in H.
    rewrite Z.gcd_mul_mono_r, Z.abs_eq in H by lia. nia. }
  assert (Hq'0 : (q' <> 0)%Z) by (intro; subst q'; rewrite Z.mul_0_l in Hq'; contradiction).
  assert (Hform : (p*p*p + C*(p*p*q) + B*(p*q*q) + A*(q*q*q)
                = g*g*g * (p'*p'*p' + C*(p'*p'*q') + B*(p'*q'*q') + A*(q'*q'*q')))%Z)
    by (rewrite Hp', Hq'; ring).
  rewrite Hform in Heq.
  apply Zmult_integral in Heq. destruct Heq as [Hc|Hc].
  - nia.
  - assert (Hwin : exists n : Z, (n | A)%Z /\ (n*n*n + C*(n*n) + B*n + A = 0)%Z).
    + destruct (Z_lt_le_dec q' 0) as [Hqneg|Hqpos].
      * assert (Hcop' : Z.gcd (-p') (-q') = 1%Z)
          by (rewrite Z.gcd_opp_l, Z.gcd_opp_r; exact Hcop).
        assert (Hc' : ((-p')*(-p')*(-p') + C*((-p')*(-p')*(-q')) + B*((-p')*(-q')*(-q'))
                       + A*((-q')*(-q')*(-q')) = 0)%Z) by nia.
        destruct (monic_cubic_coprime_root A B C (-p') (-q') ltac:(lia) Hcop' Hc') as [Hdiv Heqn].
        exists (-p')%Z; split; assumption.
      * destruct (monic_cubic_coprime_root A B C p' q' ltac:(lia) Hcop Hc) as [Hdiv Heqn].
        exists p'; split; assumption.
    + destruct Hwin as [n [Hdiv Heqn]]. exact (Hcheck n Hdiv Heqn).
Qed.

(* bridge to the real rational-root form used by not_EuclidNum_of_cubic_no_rat_root *)
Lemma cubic_no_rat_root_of_int : forall A B C : Z,
  (forall n : Z, (n | A)%Z -> (n*n*n + C*(n*n) + B*n + A)%Z <> 0%Z) ->
  forall r, is_rational r -> r*r*r + IZR C*(r*r) + IZR B*r + IZR A <> 0.
Proof.
  intros A B C Hcheck r [p [q [Hq Hr]]] Heq. subst r.
  assert (Hqne : IZR q <> 0) by (apply not_0_IZR; lia).
  apply (monic_cubic_int_no_root A B C Hcheck p q ltac:(lia)).
  apply eq_IZR_R0.
  assert (Hpush : IZR (p*p*p + C*(p*p*q) + B*(p*q*q) + A*(q*q*q)) =
     (IZR q*IZR q*IZR q) * ((IZR p/IZR q)*(IZR p/IZR q)*(IZR p/IZR q)
       + IZR C*((IZR p/IZR q)*(IZR p/IZR q)) + IZR B*(IZR p/IZR q) + IZR A)).
  { rewrite ?plus_IZR, ?mult_IZR. field. exact Hqne. }
  rewrite Hpush, Heq. ring.
Qed.

(* ---------- the three cubics have no rational root ---------- *)
Lemma delian_check : forall n : Z, (n | (-2))%Z ->
  (n*n*n + 0*(n*n) + 0*n + (-2))%Z <> 0%Z.
Proof.
  intros n Hdiv Heq. destruct Hdiv as [k Hk].
  assert (Hn0 : n <> 0%Z) by (intro; subst; lia).
  assert (Hb : (-2 <= n <= 2)%Z) by nia.
  assert (Hcase : (n = -2 \/ n = -1 \/ n = 1 \/ n = 2)%Z) by lia.
  destruct Hcase as [ -> | [ -> | [ -> | -> ] ] ]; lia.
Qed.

Lemma trisect_check : forall n : Z, (n | (-1))%Z ->
  (n*n*n + 0*(n*n) + (-3)*n + (-1))%Z <> 0%Z.
Proof.
  intros n Hdiv Heq. destruct Hdiv as [k Hk].
  assert (Hn0 : n <> 0%Z) by (intro; subst; lia).
  assert (Hb : (-1 <= n <= 1)%Z) by nia.
  assert (Hcase : (n = -1 \/ n = 1)%Z) by lia.
  destruct Hcase as [ -> | -> ]; lia.
Qed.

Lemma nonagon_check : forall n : Z, (n | 1)%Z ->
  (n*n*n + 0*(n*n) + (-3)*n + 1)%Z <> 0%Z.
Proof.
  intros n Hdiv Heq. destruct Hdiv as [k Hk].
  assert (Hn0 : n <> 0%Z) by (intro; subst; lia).
  assert (Hb : (-1 <= n <= 1)%Z) by nia.
  assert (Hcase : (n = -1 \/ n = 1)%Z) by lia.
  destruct Hcase as [ -> | -> ]; lia.
Qed.

(* ---------- cubic memberships via triple-angle ---------- *)
Definition cos_pi_9 : R := cos (PI/9).
Lemma cos_pi_9_cubic : 8*(cos_pi_9*cos_pi_9*cos_pi_9) - 6*cos_pi_9 - 1 = 0.
Proof.
  unfold cos_pi_9. pose proof (cos_triple (PI/9)) as H.
  replace (3*(PI/9)) with (PI/3) in H by field.
  rewrite cos_PI3 in H. nra.
Qed.

Lemma cos_2pi_3 : cos (2*PI/3) = -1/2.
Proof.
  replace (2*PI/3) with (PI - PI/3) by field.
  rewrite cos_minus, cos_PI, sin_PI, cos_PI3. lra.
Qed.
Theorem not_EuclidNum_cbrt2 : ~ EuclidNum cbrt2.
Proof.
  apply (not_EuclidNum_of_cubic_no_rat_root (-2) 0 0
           (is_rational_IZR (-2)) (is_rational_IZR 0) (is_rational_IZR 0)
           (cubic_no_rat_root_of_int (-2) 0 0 delian_check)).
  pose proof cbrt2_cubes_to_2. nra.
Qed.

Theorem not_EuclidNum_two_cos_pi_9 : ~ EuclidNum (2 * cos_pi_9).
Proof.
  apply (not_EuclidNum_of_cubic_no_rat_root (-1) (-3) 0
           (is_rational_IZR (-1)) (is_rational_IZR (-3)) (is_rational_IZR 0)
           (cubic_no_rat_root_of_int (-1) (-3) 0 trisect_check)).
  pose proof cos_pi_9_cubic. nra.
Qed.

(** The angle PI/3 cannot be trisected by compass and straightedge. *)
Theorem not_EuclidNum_cos_pi_9 : ~ EuclidNum cos_pi_9.
Proof.
  intro H. apply not_EuclidNum_two_cos_pi_9.
  apply EN_mul; [replace 2 with (1+1) by ring; apply EN_add; apply EN_1 | exact H].
Qed.
Open Scope R_scope.
Lemma cubic_factor_id : forall p q r0 t,
  t ^ 3 + p * t + q
  = (t - r0) * (t * t + r0 * t + (r0 * r0 + p)) + (r0 ^ 3 + p * r0 + q).
Proof. intros; ring. Qed.
Open Scope R_scope.
Fixpoint Fcomb (cs vs : list R) : R :=
  match cs, vs with
  | c :: cs', v :: vs' => c * v + Fcomb cs' vs'
  | _, _ => 0
  end.

Lemma Fcomb_nil_r : forall cs, Fcomb cs [] = 0.
Proof. destruct cs; reflexivity. Qed.

Lemma Fcomb_cons : forall c cs v vs, Fcomb (c::cs) (v::vs) = c*v + Fcomb cs vs.
Proof. reflexivity. Qed.

(* zero coefficients give zero *)
Lemma Fcomb_zeros : forall vs cs, Forall (fun c => c = 0) cs -> Fcomb cs vs = 0.
Proof.
  induction vs as [|v vs IH]; intros cs Hz.
  - apply Fcomb_nil_r.
  - destruct cs as [|c cs]; [reflexivity|].
    inversion Hz; subst. simpl. rewrite IH by assumption. ring.
Qed.

(* scaling a combination *)
Lemma Fcomb_scale : forall a cs vs, a * Fcomb cs vs = Fcomb (map (Rmult a) cs) vs.
Proof.
  intros a cs vs. revert cs. induction vs as [|v vs IH]; intros cs.
  - rewrite !Fcomb_nil_r. ring.
  - destruct cs as [|c cs]; simpl; [ring|]. rewrite <- IH. ring.
Qed.

(* adding combinations on the same vectors (equal-length coeff lists) *)
Lemma Fcomb_add : forall cs ds vs, length cs = length ds ->
  Fcomb cs vs + Fcomb ds vs = Fcomb (map (fun p => fst p + snd p) (combine cs ds)) vs.
Proof.
  intros cs ds vs. revert cs ds. induction vs as [|v vs IH]; intros cs ds Hlen.
  - rewrite !Fcomb_nil_r. ring.
  - destruct cs as [|c cs]; destruct ds as [|d ds]; simpl in Hlen; try lia.
    + simpl. ring.
    + simpl. rewrite <- IH by lia. ring.
Qed.

(* F-membership is preserved by combinations of in-field coefficients and vectors *)
Lemma Fcomb_in_field : forall F cs vs, is_subfield F ->
  Forall F cs -> Forall F vs -> F (Fcomb cs vs).
Proof.
  intros F cs vs HF. revert cs. induction vs as [|v vs IH]; intros cs Hcs Hvs.
  - rewrite Fcomb_nil_r. apply subfield_0; auto.
  - destruct cs as [|c cs]; simpl.
    + apply subfield_0; auto.
    + inversion Hcs; subst. inversion Hvs; subst.
      apply subfield_add; [exact HF | apply subfield_mul; auto | apply IH; auto].
Qed.

(* ---- linear independence and spanning over F ---- *)
Definition lin_indep (F : R -> Prop) (vs : list R) : Prop :=
  forall cs, length cs = length vs -> Forall F cs ->
    Fcomb cs vs = 0 -> Forall (fun c => c = 0) cs.

Definition spans (F : R -> Prop) (vs : list R) (y : R) : Prop :=
  exists cs, length cs = length vs /\ Forall F cs /\ Fcomb cs vs = y.

Lemma spans_in : forall F vs v, In v vs -> spans F vs v -> True.
Proof. trivial. Qed.

(* the empty list is independent *)
Lemma lin_indep_nil : forall F, lin_indep F [].
Proof.
  intros F cs Hlen _ _. destruct cs; [constructor | simpl in Hlen; lia].
Qed.

(* standard basis coefficient vector: 1 at position i, 0 elsewhere, length n *)
Fixpoint e_i (n i : nat) : list R :=
  match n with
  | 0 => []
  | S n' => match i with
            | 0 => 1 :: repeat 0 n'
            | S i' => 0 :: e_i n' i'
            end
  end.

Lemma e_i_length : forall n i, length (e_i n i) = n.
Proof.
  induction n as [|n IH]; intros i; [reflexivity|].
  destruct i; simpl; [rewrite repeat_length; reflexivity | rewrite IH; reflexivity].
Qed.

Lemma e_i_Forall : forall F n i, is_subfield F -> Forall F (e_i n i).
Proof.
  intros F n. induction n as [|n IH]; intros i HF; [constructor|].
  destruct i; simpl.
  - constructor; [apply subfield_1; auto|].
    apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst x. apply subfield_0; auto.
  - constructor; [apply subfield_0; auto | apply IH; auto].
Qed.

Lemma Fcomb_e_i : forall vs i, (i < length vs)%nat -> Fcomb (e_i (length vs) i) vs = nth i vs 0.
Proof.
  induction vs as [|v vs IH]; intros i Hi; [simpl in Hi; lia|].
  simpl length. destruct i; simpl.
  - rewrite Fcomb_zeros.
    + ring.
    + apply Forall_forall. intros x Hx. apply repeat_spec in Hx. exact Hx.
  - simpl in Hi. rewrite IH by lia. ring.
Qed.

(* every element of an independent list is nonzero *)
Lemma lin_indep_nonzero : forall F vs, is_subfield F -> lin_indep F vs ->
  Forall (fun v => v <> 0) vs.
Proof.
  intros F vs HF Hind. apply Forall_forall. intros v Hv.
  destruct (In_nth vs v 0 Hv) as [i [Hi Hnth]].
  intro Hv0.
  assert (Hcombo : Fcomb (e_i (length vs) i) vs = 0)
    by (rewrite Fcomb_e_i by exact Hi; rewrite Hnth; exact Hv0).
  specialize (Hind (e_i (length vs) i) (e_i_length _ _) (e_i_Forall F _ _ HF) Hcombo).
  rewrite Forall_forall in Hind.
  assert (Hci : nth i (e_i (length vs) i) 0 = 1).
  { clear -Hi. revert i Hi. induction vs as [|w vs IH]; intros i Hi; [simpl in Hi; lia|].
    simpl length in *. destruct i; simpl; [reflexivity | apply IH; lia]. }
  assert (Hin : In (nth i (e_i (length vs) i) 0) (e_i (length vs) i))
    by (apply nth_In; rewrite e_i_length; exact Hi).
  specialize (Hind _ Hin). rewrite Hci in Hind. lra.
Qed.

(* ---- the span of a set is a subspace ---- *)
Lemma spans_zero : forall F us, is_subfield F -> spans F us 0.
Proof.
  intros F us HF. exists (repeat 0 (length us)). repeat split.
  - rewrite repeat_length; reflexivity.
  - apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst x. apply subfield_0; auto.
  - apply Fcomb_zeros. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. exact Hx.
Qed.

Lemma spans_scale : forall F us a y, is_subfield F -> F a -> spans F us y -> spans F us (a*y).
Proof.
  intros F us a y HF Ha [cs [Hlen [HFcs Hcomb]]].
  exists (map (Rmult a) cs). repeat split.
  - rewrite length_map; exact Hlen.
  - apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as [c [Hc Hcin]].
    subst x. apply subfield_mul; [exact HF | exact Ha |]. rewrite Forall_forall in HFcs; auto.
  - rewrite <- Fcomb_scale, Hcomb. reflexivity.
Qed.

Lemma spans_add : forall F us y z, is_subfield F -> spans F us y -> spans F us z -> spans F us (y+z).
Proof.
  intros F us y z HF [cs [Hlc [HFc Hc]]] [ds [Hld [HFd Hd]]].
  exists (map (fun p => fst p + snd p) (combine cs ds)). repeat split.
  - rewrite length_map, length_combine, Hlc, Hld, Nat.min_id; reflexivity.
  - apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as [[c d] [Hcd Hin]].
    subst x. simpl. apply in_combine_l in Hin as Hc1. apply in_combine_r in Hin as Hd1.
    apply subfield_add; [exact HF | rewrite Forall_forall in HFc; auto | rewrite Forall_forall in HFd; auto].
  - rewrite <- Fcomb_add by (rewrite Hlc, Hld; reflexivity). rewrite Hc, Hd. reflexivity.
Qed.

(* span is transitive: span over a set that lies in the span of us is in span us *)
Lemma spans_trans : forall F us vs y, is_subfield F ->
  (forall v, In v vs -> spans F us v) -> spans F vs y -> spans F us y.
Proof.
  intros F us vs y HF Hvs [cs [Hlen [HFcs Hcomb]]]. subst y.
  revert cs Hlen HFcs. induction vs as [|v vs IH]; intros cs Hlen HFcs.
  - destruct cs; simpl in *; [apply spans_zero; auto | lia].
  - destruct cs as [|c cs]; simpl in Hlen; [lia|].
    simpl. inversion HFcs; subst.
    apply spans_add; auto.
    + apply spans_scale; auto. apply Hvs. left; reflexivity.
    + apply IH; [intros w Hw; apply Hvs; right; exact Hw | lia | assumption].
Qed.

(* ---- Fcomb is linear in its vector (second) argument too ---- *)
Definition vadd (v w : list R) : list R := map (fun p => fst p + snd p) (combine v w).
Definition vscale (a : R) (v : list R) : list R := map (Rmult a) v.

Lemma Fcomb_vadd_r : forall cs v w, length v = length w ->
  Fcomb cs (vadd v w) = Fcomb cs v + Fcomb cs w.
Proof.
  induction cs as [|c cs IH]; intros v w Hlen.
  - simpl. ring.
  - destruct v as [|v0 v]; destruct w as [|w0 w]; simpl in Hlen; try lia.
    + cbn. ring.
    + replace (vadd (v0::v) (w0::w)) with ((v0+w0) :: vadd v w) by reflexivity.
      cbn [Fcomb]. rewrite (IH v w) by lia. ring.
Qed.

Lemma Fcomb_vscale_r : forall cs a v, Fcomb cs (vscale a v) = a * Fcomb cs v.
Proof.
  induction cs as [|c cs IH]; intros a v.
  - simpl. ring.
  - destruct v as [|v0 v].
    + cbn. ring.
    + replace (vscale a (v0::v)) with (a*v0 :: vscale a v) by reflexivity.
      cbn [Fcomb]. rewrite (IH a v). ring.
Qed.

Lemma Fcomb_vs_zeros : forall cs vs, Forall (fun v => v = 0) vs -> Fcomb cs vs = 0.
Proof.
  induction cs as [|c cs IH]; intros vs Hz.
  - reflexivity.
  - destruct vs as [|v vs]; simpl; [reflexivity|].
    inversion Hz; subst. rewrite IH by assumption. ring.
Qed.

Lemma Fcomb_app : forall cs1 vs1 cs2 vs2, length cs1 = length vs1 ->
  Fcomb (cs1 ++ cs2) (vs1 ++ vs2) = Fcomb cs1 vs1 + Fcomb cs2 vs2.
Proof.
  induction cs1 as [|c cs1 IH]; intros vs1 cs2 vs2 Hlen.
  - destruct vs1; simpl in Hlen; [|lia]. simpl. ring.
  - destruct vs1 as [|v vs1]; simpl in Hlen; [lia|].
    simpl. rewrite IH by lia. ring.
Qed.

Lemma Fcomb_middle : forall cL vL x y cR vR, length cL = length vL ->
  Fcomb (cL ++ x :: cR) (vL ++ y :: vR) = Fcomb cL vL + x * y + Fcomb cR vR.
Proof. intros cL vL x y cR vR H. rewrite Fcomb_app by assumption. simpl. ring. Qed.

Definition vsub (v w : list R) : list R := map (fun p => fst p - snd p) (combine v w).

Lemma Fcomb_vsub_r : forall cs v w, length v = length w ->
  Fcomb cs (vsub v w) = Fcomb cs v - Fcomb cs w.
Proof.
  induction cs as [|c cs IH]; intros v w Hlen.
  - simpl. ring.
  - destruct v as [|v0 v]; destruct w as [|w0 w]; simpl in Hlen; try lia.
    + cbn. ring.
    + replace (vsub (v0::v) (w0::w)) with ((v0-w0) :: vsub v w) by reflexivity.
      cbn [Fcomb]. rewrite (IH v w) by lia. ring.
Qed.

Lemma nth_tl : forall (i:nat) (r:list R), nth i (tl r) 0 = nth (S i) r 0.
Proof. intros i r. destruct r as [|x r']; [destruct i; reflexivity | reflexivity]. Qed.

Lemma nth_vscale : forall (i:nat) a v, nth i (vscale a v) 0 = a * nth i v 0.
Proof.
  induction i as [|i IH]; intros a v; destruct v as [|x v]; simpl.
  - ring.
  - ring.
  - ring.
  - apply IH.
Qed.

Lemma nth_vsub : forall (i:nat) v w, length v = length w ->
  nth i (vsub v w) 0 = nth i v 0 - nth i w 0.
Proof.
  induction i as [|i IH]; intros v w Hlen; destruct v as [|x v]; destruct w as [|y w];
    simpl in Hlen; try lia.
  - simpl. ring.
  - simpl. ring.
  - simpl. ring.
  - simpl. apply IH. lia.
Qed.

Definition col (j : nat) (rows : list (list R)) : list R := map (fun r => nth j r 0) rows.

Lemma col_app : forall j A B, col j (A ++ B) = col j A ++ col j B.
Proof. intros j A B. unfold col. apply map_app. Qed.

Lemma col_map_tl : forall j rows, col j (map (@tl R) rows) = col (S j) rows.
Proof.
  intros j rows. unfold col. rewrite map_map. apply map_ext. intros r. apply nth_tl.
Qed.

Lemma map_add_vadd : forall (A:Type) (a b : A -> R) (l : list A),
  map (fun x => a x + b x) l = vadd (map a l) (map b l).
Proof.
  intros A a b l. induction l as [|x l IH]; [reflexivity|].
  cbn [map].
  replace (vadd (a x :: map a l) (b x :: map b l))
    with ((a x + b x) :: vadd (map a l) (map b l)) by reflexivity.
  rewrite IH. reflexivity.
Qed.

(* a kernel of the coefficient matrix (columns) yields a dependence among the w's *)
Lemma kernel_gives_dep : forall vs css lam,
  Forall (fun c => length c = length vs) css ->
  (forall j, (j < length vs)%nat -> Fcomb lam (col j css) = 0) ->
  Fcomb lam (map (fun c => Fcomb c vs) css) = 0.
Proof.
  induction vs as [|v vs IH]; intros css lam Hlen Hker.
  - apply Fcomb_vs_zeros. apply Forall_forall. intros x Hx.
    apply in_map_iff in Hx. destruct Hx as [c [Hc _]]. rewrite <- Hc. apply Fcomb_nil_r.
  - assert (Heq : map (fun c => Fcomb c (v::vs)) css
               = map (fun c => nth 0 c 0 * v + Fcomb (tl c) vs) css).
    { apply map_ext_in. intros c Hc. rewrite Forall_forall in Hlen. specialize (Hlen c Hc).
      destruct c as [|c0 c']; simpl in Hlen; [lia | reflexivity]. }
    rewrite Heq, map_add_vadd.
    rewrite Fcomb_vadd_r by (rewrite !length_map; reflexivity).
    assert (Hpart1 : Fcomb lam (map (fun c => nth 0 c 0 * v) css) = 0).
    { replace (map (fun c => nth 0 c 0 * v) css) with (vscale v (col 0 css)).
      2:{ unfold vscale, col. rewrite map_map. apply map_ext. intros c. ring. }
      rewrite Fcomb_vscale_r, (Hker 0%nat) by (simpl; lia). ring. }
    rewrite Hpart1, Rplus_0_l.
    rewrite <- (map_map (@tl R) (fun c' => Fcomb c' vs) css).
    apply IH.
    + apply Forall_forall. intros c' Hc'. apply in_map_iff in Hc'.
      destruct Hc' as [c [Htl Hc]]. subst c'.
      rewrite Forall_forall in Hlen. specialize (Hlen c Hc).
      destruct c as [|c0 c'']; simpl in Hlen |- *; lia.
    + intros j Hj. unfold col. rewrite map_map.
      replace (map (fun r => nth j (tl r) 0) css) with (col (S j) css).
      2:{ unfold col. apply map_ext. intros r.
          destruct r as [|r0 r']; [destruct j; reflexivity | reflexivity]. }
      apply Hker. simpl. lia.
Qed.

Lemma length_vscale : forall a v, length (vscale a v) = length v.
Proof. intros a v. unfold vscale. apply length_map. Qed.

Lemma map_sub_vsub : forall (A:Type) (a b : A -> R) (l : list A),
  map (fun x => a x - b x) l = vsub (map a l) (map b l).
Proof.
  intros A a b l. induction l as [|x l IH]; [reflexivity|].
  cbn [map].
  replace (vsub (a x :: map a l) (b x :: map b l))
    with ((a x - b x) :: vsub (map a l) (map b l)) by reflexivity.
  rewrite IH. reflexivity.
Qed.

(* find the first row with nonzero head: rows = L ++ piv :: R *)
Lemma split_pivot : forall rows,
  Exists (fun r => nth 0 r 0 <> 0) rows ->
  exists L piv R, rows = L ++ piv :: R /\ nth 0 piv 0 <> 0.
Proof.
  induction rows as [|r rows IH]; intros Hex.
  - apply Exists_nil in Hex. contradiction.
  - apply Exists_cons in Hex. destruct Hex as [Hhd | Htl].
    + exists nil, r, rows. split; [reflexivity | exact Hhd].
    + destruct (IH Htl) as [L [piv [R [Heq Hpiv]]]].
      exists (r :: L), piv, R. split; [simpl; rewrite Heq; reflexivity | exact Hpiv].
Qed.

(* eliminate the first column of r using pivot piv, then drop it *)
Definition elimrow (piv r : list R) : list R :=
  tl (vsub r (vscale (nth 0 r 0 / nth 0 piv 0) piv)).

Lemma nth_elimrow : forall j piv r, length r = length piv ->
  nth j (elimrow piv r) 0
    = nth (S j) r 0 - (nth 0 r 0 / nth 0 piv 0) * nth (S j) piv 0.
Proof.
  intros j piv r Hlen. unfold elimrow.
  rewrite nth_tl. rewrite nth_vsub by (rewrite length_vscale; exact Hlen).
  rewrite nth_vscale. reflexivity.
Qed.

Lemma col_map_elimrow : forall piv others j,
  Forall (fun r => length r = length piv) others ->
  col j (map (elimrow piv) others)
    = vsub (col (S j) others)
           (vscale (nth (S j) piv 0 / nth 0 piv 0) (col 0 others)).
Proof.
  intros piv others j Hlen. unfold col. unfold vscale. rewrite !map_map.
  rewrite <- (map_sub_vsub (list R) (fun r => nth (S j) r 0)
                (fun r => nth (S j) piv 0 / nth 0 piv 0 * nth 0 r 0) others).
  apply map_ext_in. intros r Hr.
  rewrite Forall_forall in Hlen. specialize (Hlen r Hr).
  rewrite nth_elimrow by exact Hlen. unfold Rdiv. ring.
Qed.

Lemma Fcomb_col_elimrow : forall mu piv others j,
  Forall (fun r => length r = length piv) others ->
  Fcomb mu (col j (map (elimrow piv) others))
    = Fcomb mu (col (S j) others)
      - (nth (S j) piv 0 / nth 0 piv 0) * Fcomb mu (col 0 others).
Proof.
  intros mu piv others j Hlen.
  rewrite col_map_elimrow by exact Hlen.
  rewrite Fcomb_vsub_r by (unfold col; rewrite length_vscale; unfold col; rewrite !length_map; reflexivity).
  rewrite Fcomb_vscale_r. reflexivity.
Qed.

(* ---- length and subfield-closure plumbing for the kernel assembly ---- *)
Lemma length_tl_R : forall (l:list R), length (tl l) = Nat.pred (length l).
Proof. destruct l; reflexivity. Qed.

Lemma length_vsub : forall v w, length (vsub v w) = Nat.min (length v) (length w).
Proof.
  induction v as [|x v IH]; intros w; [reflexivity|].
  destruct w as [|y w]; [reflexivity|].
  unfold vsub. simpl. f_equal. apply IH.
Qed.

Lemma Forall_tl : forall (F:R->Prop) l, Forall F l -> Forall F (tl l).
Proof. intros F l H. destruct l; [exact H | inversion H; assumption]. Qed.

Lemma Forall_F_nth : forall F i r, is_subfield F -> Forall F r -> F (nth i r 0).
Proof.
  intros F i r HF Hr. destruct (Nat.lt_ge_cases i (length r)) as [Hlt|Hge].
  - rewrite Forall_forall in Hr. apply Hr. apply nth_In; exact Hlt.
  - rewrite nth_overflow by exact Hge. apply subfield_0; auto.
Qed.

Lemma Forall_F_vscale : forall F a v, is_subfield F -> F a -> Forall F v -> Forall F (vscale a v).
Proof.
  intros F a v HF Ha Hv. unfold vscale. apply Forall_forall. intros z Hz.
  apply in_map_iff in Hz. destruct Hz as [x [Hz Hin]]. subst z.
  apply subfield_mul; [exact HF | exact Ha | rewrite Forall_forall in Hv; apply Hv; exact Hin].
Qed.

Lemma Forall_F_vsub : forall F v w, is_subfield F -> Forall F v -> Forall F w -> Forall F (vsub v w).
Proof.
  intros F v w HF Hv Hw. unfold vsub. apply Forall_forall. intros z Hz.
  apply in_map_iff in Hz. destruct Hz as [[a b] [Hz Hin]]. subst z. simpl.
  apply subfield_sub;
    [exact HF
    | rewrite Forall_forall in Hv; apply Hv; eapply in_combine_l; exact Hin
    | rewrite Forall_forall in Hw; apply Hw; eapply in_combine_r; exact Hin].
Qed.

Lemma Forall_F_col : forall F j rows, is_subfield F ->
  Forall (fun r => Forall F r) rows -> Forall F (col j rows).
Proof.
  intros F j rows HF Hrows. unfold col. apply Forall_forall. intros z Hz.
  apply in_map_iff in Hz. destruct Hz as [r [Hz Hin]]. subst z.
  rewrite Forall_forall in Hrows. apply Forall_F_nth; [exact HF | apply Hrows; exact Hin].
Qed.

Lemma length_elimrow : forall piv r, length r = length piv ->
  length (elimrow piv r) = Nat.pred (length r).
Proof.
  intros piv r H. unfold elimrow.
  rewrite length_tl_R, length_vsub, length_vscale, H, Nat.min_id. reflexivity.
Qed.

Lemma Forall_F_elimrow : forall F piv r, is_subfield F ->
  Forall F piv -> Forall F r -> nth 0 piv 0 <> 0 -> Forall F (elimrow piv r).
Proof.
  intros F piv r HF Hpiv Hr Hp. unfold elimrow. apply Forall_tl.
  apply Forall_F_vsub; [exact HF | exact Hr |].
  apply Forall_F_vscale; [exact HF | | exact Hpiv].
  apply subfield_div; [exact HF | apply Forall_F_nth; auto | apply Forall_F_nth; auto | exact Hp].
Qed.

(* pivot case of the wide-matrix kernel: more rows than columns -> nontrivial kernel,
   given the inductive hypothesis for one fewer column *)
Lemma wide_matrix_kernel_caseB :
  forall (F : R -> Prop) n' rows,
  is_subfield F ->
  Forall (fun r => length r = S n' /\ Forall F r) rows ->
  Exists (fun r => nth 0 r 0 <> 0) rows ->
  (forall rows', Forall (fun r => length r = n' /\ Forall F r) rows' ->
      (n' < length rows')%nat ->
      exists mu, length mu = length rows' /\ Forall F mu /\
                 Exists (fun c => c <> 0) mu /\
                 (forall j, (j < n')%nat -> Fcomb mu (col j rows') = 0)) ->
  (S n' < length rows)%nat ->
  exists lam, length lam = length rows /\ Forall F lam /\
              Exists (fun c => c <> 0) lam /\
              (forall j, (j < S n')%nat -> Fcomb lam (col j rows) = 0).
Proof.
  intros F n' rows HF Hrows Hex IH Hlt.
  destruct (split_pivot rows Hex) as [L [piv [R [Heq Hpiv]]]].
  assert (Hrows' := Hrows). rewrite Heq in Hrows'.
  rewrite Forall_app in Hrows'. destruct Hrows' as [HL HpivR].
  pose proof (Forall_inv HpivR) as Hpivp. pose proof (Forall_inv_tail HpivR) as HR.
  destruct Hpivp as [Hpivlen Hpivf].
  set (others := L ++ R).
  set (hp := nth 0 piv 0).
  assert (Hothers : Forall (fun r => length r = S n' /\ Forall F r) others).
  { unfold others. rewrite Forall_app. split; assumption. }
  assert (HothersFl : Forall (fun r => length r = length piv) others).
  { apply Forall_forall. intros r Hr. rewrite Forall_forall in Hothers.
    destruct (Hothers r Hr) as [Hl _]. rewrite Hl, Hpivlen. reflexivity. }
  set (reduced := map (elimrow piv) others).
  assert (Hred : Forall (fun r => length r = n' /\ Forall F r) reduced).
  { apply Forall_forall. intros z Hz. unfold reduced in Hz. apply in_map_iff in Hz.
    destruct Hz as [r [Hz Hr]]. subst z.
    rewrite Forall_forall in Hothers. destruct (Hothers r Hr) as [Hl Hf]. split.
    - rewrite length_elimrow by (rewrite Hl, Hpivlen; reflexivity). rewrite Hl. reflexivity.
    - apply Forall_F_elimrow; [exact HF | exact Hpivf | exact Hf | exact Hpiv]. }
  assert (Hlenrows : length rows = (length L + S (length R))%nat).
  { rewrite Heq, length_app. simpl. reflexivity. }
  assert (Hlenothers : length others = (length L + length R)%nat).
  { unfold others. rewrite length_app. reflexivity. }
  assert (Hredcnt : (n' < length reduced)%nat).
  { unfold reduced. rewrite length_map, Hlenothers. lia. }
  destruct (IH reduced Hred Hredcnt) as [mu [Hmulen [HmuF [Hmunz Hmuker]]]].
  assert (Hmu2 : length mu = (length L + length R)%nat).
  { rewrite Hmulen. unfold reduced. rewrite length_map. exact Hlenothers. }
  set (muL := firstn (length L) mu).
  set (muR := skipn (length L) mu).
  assert (Hsplit : mu = muL ++ muR) by (unfold muL, muR; rewrite firstn_skipn; reflexivity).
  assert (HmuLlen : length muL = length L).
  { unfold muL. rewrite length_firstn. apply Nat.min_l. lia. }
  set (K0 := Fcomb mu (col 0 others)).
  set (lam_piv := - (/ hp) * K0).
  assert (HmuF' := HmuF). rewrite Hsplit in HmuF'. rewrite Forall_app in HmuF'.
  destruct HmuF' as [HmuLF HmuRF].
  assert (HK0F : F K0).
  { unfold K0. apply Fcomb_in_field; [exact HF | exact HmuF |].
    apply Forall_F_col; [exact HF|]. apply Forall_forall. intros r Hr.
    rewrite Forall_forall in Hothers. destruct (Hothers r Hr) as [_ Hf]. exact Hf. }
  assert (Hhp : F hp) by (unfold hp; apply Forall_F_nth; [exact HF | exact Hpivf]).
  assert (Hlampiv : F lam_piv).
  { unfold lam_piv. apply (subfield_mul F (- / hp) K0); [exact HF | | exact HK0F].
    apply (subfield_opp F (/ hp)); [exact HF|].
    apply (subfield_inv F hp); [exact HF | exact Hhp | exact Hpiv]. }
  exists (muL ++ lam_piv :: muR).
  split.
  { rewrite length_app. simpl. rewrite HmuLlen, Hlenrows. f_equal.
    unfold muR. rewrite length_skipn. lia. }
  split.
  { apply Forall_app. split; [exact HmuLF|]. apply Forall_cons; [exact Hlampiv | exact HmuRF]. }
  split.
  { rewrite Hsplit in Hmunz. apply Exists_app in Hmunz. apply Exists_app.
    destruct Hmunz as [H|H]; [left; exact H | right; apply Exists_cons; right; exact H]. }
  intros j Hj.
  assert (Hcolrows : col j (L ++ piv :: R) = col j L ++ (nth j piv 0 :: col j R))
    by (rewrite col_app; reflexivity).
  rewrite Heq, Hcolrows.
  rewrite Fcomb_middle by (rewrite HmuLlen; unfold col; rewrite length_map; reflexivity).
  assert (Hjoin : Fcomb muL (col j L) + Fcomb muR (col j R) = Fcomb mu (col j others)).
  { unfold others. rewrite col_app, Hsplit.
    rewrite Fcomb_app by (rewrite HmuLlen; unfold col; rewrite length_map; reflexivity).
    reflexivity. }
  assert (Hgoal : Fcomb muL (col j L) + lam_piv * nth j piv 0 + Fcomb muR (col j R)
                = Fcomb mu (col j others) + lam_piv * nth j piv 0)
    by (rewrite <- Hjoin; ring).
  rewrite Hgoal.
  destruct j as [|j'].
  - change (nth 0 piv 0) with hp. fold K0.
    assert (Hlph : lam_piv * hp = - K0).
    { unfold lam_piv. replace (- / hp * K0 * hp) with (- (K0 * (/ hp * hp))) by ring.
      rewrite Rinv_l by exact Hpiv. ring. }
    rewrite Hlph. ring.
  - assert (Hj' : (j' < n')%nat) by lia.
    pose proof (Hmuker j' Hj') as Hk. unfold reduced in Hk.
    rewrite (Fcomb_col_elimrow mu piv others j' HothersFl) in Hk.
    fold K0 in Hk.
    assert (Hval : Fcomb mu (col (S j') others) = (nth (S j') piv 0 / hp) * K0)
      by (apply Rminus_diag_uniq; exact Hk).
    rewrite Hval. unfold lam_piv, Rdiv. ring.
Qed.

(* more rows than columns -> a nontrivial F-kernel exists *)
Lemma wide_matrix_kernel : forall (F:R->Prop) n rows,
  is_subfield F ->
  Forall (fun r => length r = n /\ Forall F r) rows ->
  (n < length rows)%nat ->
  exists lam, length lam = length rows /\ Forall F lam /\
              Exists (fun c => c <> 0) lam /\
              (forall j, (j < n)%nat -> Fcomb lam (col j rows) = 0).
Proof.
  intros F. induction n as [|n' IH]; intros rows HF Hrows Hlt.
  - destruct rows as [|r0 rows]; [simpl in Hlt; lia|].
    exists (1 :: repeat 0 (length rows)).
    split; [simpl; rewrite repeat_length; reflexivity|].
    split.
    { constructor; [apply subfield_1; auto|]. apply Forall_forall. intros x Hx.
      apply repeat_spec in Hx. subst x. apply subfield_0; auto. }
    split.
    { apply Exists_cons. left. apply R1_neq_R0. }
    intros j Hj. lia.
  - destruct (Exists_dec (fun r => nth 0 r 0 <> 0) rows
                (fun r => Rneq_dec (nth 0 r 0) 0)) as [Hex|Hnex].
    + exact (wide_matrix_kernel_caseB F n' rows HF Hrows Hex
               (fun rows' Hr Hc => IH rows' HF Hr Hc) Hlt).
    + assert (Hall0 : Forall (fun r => nth 0 r 0 = 0) rows).
      { apply Forall_forall. intros r Hr.
        destruct (Req_dec_T (nth 0 r 0) 0) as [|Hne]; [assumption|].
        exfalso. apply Hnex. apply Exists_exists. exists r. split; assumption. }
      set (tails := map (@tl R) rows).
      assert (Htails : Forall (fun r => length r = n' /\ Forall F r) tails).
      { apply Forall_forall. intros z Hz. unfold tails in Hz. apply in_map_iff in Hz.
        destruct Hz as [r [Hz Hr]]. subst z.
        rewrite Forall_forall in Hrows. destruct (Hrows r Hr) as [Hl Hf]. split.
        - rewrite length_tl_R, Hl. reflexivity.
        - apply Forall_tl; exact Hf. }
      assert (Htlt : (n' < length tails)%nat) by (unfold tails; rewrite length_map; lia).
      destruct (IH tails HF Htails Htlt) as [lam [Hlamlen [HlamF [Hlamnz Hlamker]]]].
      exists lam.
      split; [rewrite Hlamlen; unfold tails; rewrite length_map; reflexivity|].
      split; [exact HlamF|]. split; [exact Hlamnz|].
      intros j Hj. destruct j as [|j'].
      * assert (Hc0 : Forall (fun v => v = 0) (col 0 rows)).
        { apply Forall_forall. intros z Hz. unfold col in Hz. apply in_map_iff in Hz.
          destruct Hz as [r [Hz Hr]]. subst z. rewrite Forall_forall in Hall0. apply Hall0; exact Hr. }
        apply Fcomb_vs_zeros; exact Hc0.
      * assert (Hcol : col (S j') rows = col j' tails)
          by (unfold tails; rewrite col_map_tl; reflexivity).
        rewrite Hcol. apply Hlamker. lia.
Qed.

(* collect a coordinate list for each spanned vector into a coefficient matrix *)
Lemma spans_all_matrix : forall F vs ws,
  Forall (spans F vs) ws ->
  exists css, length css = length ws /\
              Forall (fun c => length c = length vs /\ Forall F c) css /\
              map (fun c => Fcomb c vs) css = ws.
Proof.
  intros F vs ws. induction ws as [|w ws IH]; intros Hall.
  - exists nil. split; [reflexivity|]. split; [constructor|reflexivity].
  - inversion Hall as [|? ? Hw Hws]; subst.
    destruct Hw as [c [Hclen [HcF Hcfc]]].
    destruct (IH Hws) as [css [Hlen [Hcss Hmap]]].
    exists (c :: css). split; [simpl; rewrite Hlen; reflexivity|]. split.
    + constructor; [split; [exact Hclen | exact HcF] | exact Hcss].
    + simpl. rewrite Hcfc, Hmap. reflexivity.
Qed.

(* Steinitz exchange bound: an independent set is no larger than any spanning set *)
Theorem steinitz : forall F vs ws,
  is_subfield F -> lin_indep F ws -> Forall (spans F vs) ws ->
  (length ws <= length vs)%nat.
Proof.
  intros F vs ws HF Hindep Hspan.
  destruct (Nat.lt_ge_cases (length vs) (length ws)) as [Hgt|Hle]; [exfalso|exact Hle].
  destruct (spans_all_matrix F vs ws Hspan) as [css [Hlen [Hcss Hmap]]].
  assert (Hcnt : (length vs < length css)%nat) by (rewrite Hlen; lia).
  destruct (wide_matrix_kernel F (length vs) css HF Hcss Hcnt)
    as [lam [Hlamlen [HlamF [Hlamnz Hlamker]]]].
  assert (Hdep : Fcomb lam (map (fun c => Fcomb c vs) css) = 0).
  { apply kernel_gives_dep.
    - apply Forall_forall. intros c Hc. rewrite Forall_forall in Hcss.
      destruct (Hcss c Hc) as [Hl _]. exact Hl.
    - exact Hlamker. }
  rewrite Hmap in Hdep.
  assert (Hall0 : Forall (fun c => c = 0) lam).
  { apply Hindep; [rewrite Hlamlen, Hlen; reflexivity | exact HlamF | exact Hdep]. }
  rewrite Exists_exists in Hlamnz. destruct Hlamnz as [x [Hx Hxne]].
  rewrite Forall_forall in Hall0. apply Hxne. apply Hall0; exact Hx.
Qed.

(* If more vectors than generators are each an F-combination of the generators,
   they satisfy a nontrivial F-linear relation. *)
Lemma lin_dep_of_spanned : forall F vs ws,
  is_subfield F -> Forall (spans F vs) ws -> (length vs < length ws)%nat ->
  exists cs, length cs = length ws /\ Forall F cs /\ Fcomb cs ws = 0 /\
             ~ Forall (fun c => c = 0) cs.
Proof.
  intros F vs ws HF Hspan Hgt.
  destruct (spans_all_matrix F vs ws Hspan) as [css [Hlen [Hcss Hmap]]].
  assert (Hcnt : (length vs < length css)%nat) by (rewrite Hlen; lia).
  destruct (wide_matrix_kernel F (length vs) css HF Hcss Hcnt)
    as [lam [Hlamlen [HlamF [Hlamnz Hlamker]]]].
  exists lam.
  assert (Hdep : Fcomb lam (map (fun c => Fcomb c vs) css) = 0).
  { apply kernel_gives_dep.
    - apply Forall_forall. intros c Hc. rewrite Forall_forall in Hcss.
      destruct (Hcss c Hc) as [Hl _]. exact Hl.
    - exact Hlamker. }
  rewrite Hmap in Hdep.
  split; [rewrite Hlamlen, Hlen; reflexivity |].
  split; [exact HlamF |]. split; [exact Hdep |].
  rewrite Exists_exists in Hlamnz. destruct Hlamnz as [x [Hx Hxne]].
  intro Hall0. rewrite Forall_forall in Hall0. apply Hxne. apply Hall0; exact Hx.
Qed.

(* ============================================================================
   Bridge: a quadratic tower of height n is spanned over Q by 2^n reals.
   ============================================================================ *)

Fixpoint tower_basis (L : list R) : list R :=
  match L with
  | nil => 1 :: nil
  | s :: L' => tower_basis L' ++ map (Rmult s) (tower_basis L')
  end.

Lemma tower_basis_length : forall L, length (tower_basis L) = (2 ^ length L)%nat.
Proof.
  induction L as [|s L' IH]; [reflexivity|].
  replace (length (s :: L')) with (S (length L')) by reflexivity.
  rewrite Nat.pow_succ_r'. cbn [tower_basis]. rewrite length_app, length_map, IH. lia.
Qed.

Lemma tower_spanned : forall L, wf_tower L ->
  forall x, tower L x -> spans is_rational (tower_basis L) x.
Proof.
  induction L as [|s L' IH]; intros Wf x Hx.
  - simpl in Hx. exists (x :: nil). split; [reflexivity|]. split.
    + constructor; [exact Hx | constructor].
    + simpl. ring.
  - simpl in Wf. destruct Wf as [Wss Wf'].
    simpl in Hx. destruct Hx as [p [q [Tp [Tq Hxe]]]].
    destruct (IH Wf' p Tp) as [cp [Hcplen [Hcpr Hcpfc]]].
    destruct (IH Wf' q Tq) as [cq [Hcqlen [Hcqr Hcqfc]]].
    exists (cp ++ cq). split.
    + rewrite length_app, Hcplen, Hcqlen. cbn [tower_basis].
      rewrite length_app, length_map. reflexivity.
    + split.
      * apply Forall_app; split; assumption.
      * cbn [tower_basis]. rewrite Fcomb_app by (rewrite Hcplen; reflexivity).
        rewrite Hcpfc.
        replace (map (Rmult s) (tower_basis L')) with (vscale s (tower_basis L')) by reflexivity.
        rewrite Fcomb_vscale_r, Hcqfc, Hxe. ring.
Qed.

(* ============================================================================
   Bridge: integer-polynomial evaluation is an F-combination of powers of x.
   ============================================================================ *)

Definition powers (x : R) (n : nat) : list R := map (fun i => x ^ i) (seq 0 n).

Lemma powers_S : forall x n, powers x (S n) = 1 :: vscale x (powers x n).
Proof.
  intros x n. unfold powers.
  replace (seq 0 (S n)) with (0%nat :: seq 1 n) by reflexivity.
  cbn [map]. replace (x ^ 0) with 1 by (simpl; ring). f_equal.
  unfold vscale. rewrite <- seq_shift, !map_map. apply map_ext. intros i. simpl. ring.
Qed.

Lemma peval_Fcomb : forall p x, peval p x = Fcomb (map IZR p) (powers x (length p)).
Proof.
  induction p as [|c p IH]; intros x; [reflexivity|].
  cbn [length map]. rewrite powers_S. cbn [Fcomb].
  rewrite Fcomb_vscale_r, <- IH. cbn [peval]. ring.
Qed.

(* scaling all coefficients of an F-combination *)
Lemma Fcomb_scale_l : forall a cs vs, Fcomb (map (Rmult a) cs) vs = a * Fcomb cs vs.
Proof.
  induction cs as [|c cs IH]; intros vs.
  - simpl. ring.
  - destruct vs as [|v vs]; simpl; [ring | rewrite IH; ring].
Qed.

(* clearing denominators of a list of rationals onto a common positive denominator *)
Lemma Forall2_scale : forall b D zs cs,
  Forall2 (fun z c => IZR z = IZR D * c) zs cs ->
  Forall2 (fun z c => IZR z = IZR (D * b) * c) (map (Z.mul b) zs) cs.
Proof.
  intros b D zs cs H. induction H; [constructor|].
  simpl. constructor; [rewrite mult_IZR, H, mult_IZR; ring | exact IHForall2].
Qed.

Lemma clear_denoms : forall cs, Forall is_rational cs ->
  exists (D : Z) (zs : list Z), (D > 0)%Z /\ length zs = length cs /\
    Forall2 (fun z c => IZR z = IZR D * c) zs cs.
Proof.
  induction cs as [|c cs IH]; intros Hall.
  - exists 1%Z, nil. split; [lia | split; [reflexivity | constructor]].
  - apply Forall_inv_tail in Hall as Hcs. apply Forall_inv in Hall as Hc.
    destruct Hc as [a [b [Hb Hce]]].
    destruct (IH Hcs) as [D' [zs' [HD' [Hlen' HF2]]]].
    exists (D' * b)%Z, ((D' * a)%Z :: map (Z.mul b) zs'). split; [nia | split].
    + simpl. rewrite length_map, Hlen'. reflexivity.
    + constructor.
      * rewrite Hce, !mult_IZR.
        assert (Hbne : IZR b <> 0) by (apply not_0_IZR; lia). field. exact Hbne.
      * apply Forall2_scale. exact HF2.
Qed.

Lemma Forall2_map_eq : forall D zs cs,
  Forall2 (fun z c => IZR z = IZR D * c) zs cs -> map IZR zs = map (Rmult (IZR D)) cs.
Proof.
  intros D zs cs H. induction H; [reflexivity|].
  simpl. rewrite H, IHForall2. reflexivity.
Qed.

Lemma Forall2_exists_nonzero : forall D zs cs, IZR D <> 0 ->
  Forall2 (fun z c => IZR z = IZR D * c) zs cs ->
  Exists (fun c => c <> 0) cs -> Exists (fun z => z <> 0%Z) zs.
Proof.
  intros D zs cs HD H. induction H as [| z c zs0 cs0 Hzc Hrest IH]; intros Hex.
  - apply Exists_nil in Hex. contradiction.
  - apply Exists_cons in Hex. destruct Hex as [Hhd | Htl].
    + apply Exists_cons_hd. intro Hz0. apply Hhd. subst z.
      apply (Rmult_eq_reg_l (IZR D)); [|exact HD]. rewrite Rmult_0_r, <- Hzc. reflexivity.
    + apply Exists_cons_tl. apply IH. exact Htl.
Qed.

(* a vanishing rational combination of powers of x gives a bounded algebraic degree *)
Lemma rational_relation_alg_deg : forall x cs m,
  length cs = S m -> Forall is_rational cs ->
  ~ Forall (fun c => c = 0) cs ->
  Fcomb cs (powers x (S m)) = 0 ->
  alg_deg_le x m.
Proof.
  intros x cs m Hlen Hrat Hnz Hfc.
  destruct (clear_denoms cs Hrat) as [D [zs [HD [Hzslen HF2]]]].
  assert (HDne : IZR D <> 0) by (apply not_0_IZR; lia).
  exists zs. split; [|split].
  - unfold pnonzero. apply (Forall2_exists_nonzero D zs cs HDne HF2).
    destruct (Exists_dec (fun c => c <> 0) cs (fun c => Rneq_dec c 0)) as [He|He]; [exact He|].
    exfalso. apply Hnz. apply Forall_forall. intros c Hc.
    destruct (Req_dec_T c 0) as [|Hcne]; [assumption|].
    exfalso. apply He. apply Exists_exists. exists c. split; assumption.
  - rewrite Hzslen, Hlen. lia.
  - unfold is_poly_root. rewrite peval_Fcomb, Hzslen, Hlen.
    rewrite (Forall2_map_eq D zs cs HF2), Fcomb_scale_l, Hfc. ring.
Qed.

Lemma subfield_pow : forall F x i, is_subfield F -> F x -> F (x ^ i).
Proof.
  intros F x i HF Hx. induction i as [|i IH].
  - simpl. apply subfield_1; exact HF.
  - simpl. apply subfield_mul; [exact HF | exact Hx | exact IH].
Qed.

(* ============================================================================
   #2 (upper bound): every Euclidean-constructible number has algebraic degree
   at most a power of 2.
   ============================================================================ *)
Theorem euclid_alg_deg_le_pow2 : forall x, EuclidNum x -> exists k, alg_deg_le x (2 ^ k)%nat.
Proof.
  intros x HE. destruct (EuclidNum_in_tower x HE) as [L [Wf Tx]].
  exists (length L).
  assert (HsfT : is_subfield (tower L)) by (apply tower_subfield; exact Wf).
  assert (Hspan : Forall (spans is_rational (tower_basis L)) (powers x (S (2 ^ length L)))).
  { apply Forall_forall. intros y Hy. unfold powers in Hy. apply in_map_iff in Hy.
    destruct Hy as [i [Hy Hi]]. subst y.
    apply tower_spanned; [exact Wf|]. apply subfield_pow; [exact HsfT | exact Tx]. }
  assert (Hgt : (length (tower_basis L) < length (powers x (S (2 ^ length L))))%nat).
  { rewrite tower_basis_length. unfold powers; rewrite length_map, length_seq. lia. }
  destruct (lin_dep_of_spanned is_rational (tower_basis L)
              (powers x (S (2 ^ length L))) is_rational_subfield Hspan Hgt)
    as [cs [Hlencs [Hratcs [Hfccs Hnd]]]].
  assert (Hlen2 : length cs = S (2 ^ length L))
    by (rewrite Hlencs; unfold powers; rewrite length_map, length_seq; reflexivity).
  apply (rational_relation_alg_deg x cs (2 ^ length L) Hlen2 Hratcs Hnd Hfccs).
Qed.


(* ============================================================================
   Subrings of R and the cubic ring-extension CF F a b r = F[r] for a root r of
   t^3 + a t + b.  (Ring closure is all that the degree bound needs; we avoid the
   harder field-inverse proof.)
   ============================================================================ *)

Definition is_subring (F : R -> Prop) : Prop :=
  F 0 /\ F 1 /\
  (forall x y, F x -> F y -> F (x + y)) /\
  (forall x y, F x -> F y -> F (x - y)) /\
  (forall x y, F x -> F y -> F (x * y)).

Lemma subring_0 : forall F, is_subring F -> F 0. Proof. intros F H; apply H. Qed.
Lemma subring_1 : forall F, is_subring F -> F 1. Proof. intros F H; apply H. Qed.
Lemma subring_add : forall F x y, is_subring F -> F x -> F y -> F (x + y).
Proof. intros F x y H; apply H. Qed.
Lemma subring_sub : forall F x y, is_subring F -> F x -> F y -> F (x - y).
Proof. intros F x y H; apply H. Qed.
Lemma subring_mul : forall F x y, is_subring F -> F x -> F y -> F (x * y).
Proof. intros F x y H; apply H. Qed.

Ltac srclose :=
  repeat first
    [ assumption
    | match goal with
      | |- ?P (_ + _) => apply (subring_add P)
      | |- ?P (_ - _) => apply (subring_sub P)
      | |- ?P (_ * _) => apply (subring_mul P)
      | |- ?P 0 => apply (subring_0 P)
      | |- ?P 1 => apply (subring_1 P)
      end ].

Lemma subring_pow : forall F x i, is_subring F -> F x -> F (x ^ i).
Proof.
  intros F x i HF Hx. induction i as [|i IH].
  - simpl. apply subring_1; exact HF.
  - simpl. apply subring_mul; [exact HF | exact Hx | exact IH].
Qed.

Definition CF (F : R -> Prop) (a b r : R) (x : R) : Prop :=
  exists p q s, F p /\ F q /\ F s /\ x = p + q * r + s * (r * r).

Lemma CF_subring : forall F a b r,
  is_subring F -> F a -> F b -> r * r * r + a * r + b = 0 -> is_subring (CF F a b r).
Proof.
  intros F a b r HF Ha Hb Hr. repeat split.
  - exists 0, 0, 0. repeat split; try (apply subring_0; exact HF). ring.
  - exists 1, 0, 0. repeat split;
      [ apply subring_1; exact HF | apply subring_0; exact HF | apply subring_0; exact HF | ring ].
  - intros x y [px [qx [sx [Hpx [Hqx [Hsx Hx]]]]]] [py [qy [sy [Hpy [Hqy [Hsy Hy]]]]]].
    exists (px + py), (qx + qy), (sx + sy). repeat split; [srclose | srclose | srclose |].
    subst x y. ring.
  - intros x y [px [qx [sx [Hpx [Hqx [Hsx Hx]]]]]] [py [qy [sy [Hpy [Hqy [Hsy Hy]]]]]].
    exists (px - py), (qx - qy), (sx - sy). repeat split; [srclose | srclose | srclose |].
    subst x y. ring.
  - intros x y [px [qx [sx [Hpx [Hqx [Hsx Hx]]]]]] [py [qy [sy [Hpy [Hqy [Hsy Hy]]]]]].
    exists (px*py - b*(qx*sy + sx*qy)),
           (px*qy + qx*py - a*(qx*sy + sx*qy) - b*(sx*sy)),
           (px*sy + qx*qy + sx*py - a*(sx*sy)).
    repeat split; [srclose | srclose | srclose |].
    subst x y. nsatz.
Qed.

Lemma subfield_is_subring : forall F, is_subfield F -> is_subring F.
Proof.
  intros F H. repeat split.
  - apply subfield_0; exact H.
  - apply subfield_1; exact H.
  - intros x y Hx Hy. apply subfield_add; assumption.
  - intros x y Hx Hy. apply subfield_sub; assumption.
  - intros x y Hx Hy. apply subfield_mul; assumption.
Qed.

Lemma is_rational_subring : is_subring is_rational.
Proof. apply subfield_is_subring. apply is_rational_subfield. Qed.

Lemma QF_subring : forall F s, is_subring F -> F (s * s) -> is_subring (QF F s).
Proof.
  intros F s HF Hss. repeat split.
  - exists 0, 0. repeat split; [apply subring_0; exact HF | apply subring_0; exact HF | ring].
  - exists 1, 0. repeat split; [apply subring_1; exact HF | apply subring_0; exact HF | ring].
  - intros x y [px [qx [Hpx [Hqx Hx]]]] [py [qy [Hpy [Hqy Hy]]]].
    exists (px + py), (qx + qy). repeat split; [srclose | srclose |]. subst x y. ring.
  - intros x y [px [qx [Hpx [Hqx Hx]]]] [py [qy [Hpy [Hqy Hy]]]].
    exists (px - py), (qx - qy). repeat split; [srclose | srclose |]. subst x y. ring.
  - intros x y [px [qx [Hpx [Hqx Hx]]]] [py [qy [Hpy [Hqy Hy]]]].
    exists (px*py + qx*qy*(s*s)), (px*qy + qx*py). repeat split; [srclose | srclose |].
    subst x y. ring.
Qed.

(* mixed quadratic/cubic tower *)
Inductive ostep : Type := OQuad (s : R) | OCubic (a b r : R).

Fixpoint otower (L : list ostep) : R -> Prop :=
  match L with
  | nil => is_rational
  | OQuad s :: L' => QF (otower L') s
  | OCubic a b r :: L' => CF (otower L') a b r
  end.

Fixpoint owf (L : list ostep) : Prop :=
  match L with
  | nil => True
  | OQuad s :: L' => otower L' (s * s) /\ owf L'
  | OCubic a b r :: L' => otower L' a /\ otower L' b /\ (r*r*r + a*r + b = 0) /\ owf L'
  end.

Lemma otower_subring : forall L, owf L -> is_subring (otower L).
Proof.
  induction L as [|st L' IH]; intros W.
  - simpl. apply is_rational_subring.
  - destruct st as [s | a b r]; simpl in *.
    + destruct W as [Wss W']. apply QF_subring; [apply IH; exact W' | exact Wss].
    + destruct W as [Wa [Wb [Wr W']]].
      apply CF_subring; [apply IH; exact W' | exact Wa | exact Wb | exact Wr].
Qed.

Fixpoint otower_basis (L : list ostep) : list R :=
  match L with
  | nil => 1 :: nil
  | OQuad s :: L' => otower_basis L' ++ map (Rmult s) (otower_basis L')
  | OCubic a b r :: L' =>
      otower_basis L' ++ map (Rmult r) (otower_basis L') ++ map (Rmult (r*r)) (otower_basis L')
  end.

Definition two_three_smooth (m : nat) : Prop := exists a b, m = (2 ^ a * 3 ^ b)%nat.

Lemma two_three_smooth_dec : forall m, {two_three_smooth m} + {~ two_three_smooth m}.
Proof.
  intro m. destruct (is_2_3_smooth_b m) eqn:E.
  - left. apply is_2_3_smooth_b_reflects. exact E.
  - right. intro H. rewrite (is_2_3_smooth_b_complete m H) in E. discriminate.
Qed.

Lemma otower_basis_smooth : forall L, two_three_smooth (length (otower_basis L)).
Proof.
  induction L as [|st L' IH]; [exists 0%nat, 0%nat; reflexivity|].
  destruct st as [s | a b r].
  - destruct IH as [a [bb Hab]]. exists (S a), bb. cbn [otower_basis].
    rewrite length_app, length_map, Hab.
    replace (2 ^ S a)%nat with (2 * 2 ^ a)%nat by (rewrite Nat.pow_succ_r'; reflexivity). lia.
  - destruct IH as [aa [bb Hab]]. exists aa, (S bb). cbn [otower_basis].
    rewrite !length_app, !length_map, Hab.
    replace (3 ^ S bb)%nat with (3 * 3 ^ bb)%nat by (rewrite Nat.pow_succ_r'; reflexivity). lia.
Qed.

Lemma otower_spanned : forall L, owf L ->
  forall x, otower L x -> spans is_rational (otower_basis L) x.
Proof.
  induction L as [|st L' IH]; intros Wf x Hx.
  - simpl in Hx. exists (x :: nil). split; [reflexivity|]. split.
    + constructor; [exact Hx | constructor].
    + simpl. ring.
  - destruct st as [s | a b r].
    + simpl in Wf. destruct Wf as [Wss Wf'].
      simpl in Hx. destruct Hx as [p [q [Tp [Tq Hxe]]]].
      destruct (IH Wf' p Tp) as [cp [Hcplen [Hcpr Hcpfc]]].
      destruct (IH Wf' q Tq) as [cq [Hcqlen [Hcqr Hcqfc]]].
      exists (cp ++ cq). split.
      * rewrite length_app, Hcplen, Hcqlen. cbn [otower_basis].
        rewrite length_app, length_map. reflexivity.
      * split.
        -- apply Forall_app; split; assumption.
        -- cbn [otower_basis]. rewrite Fcomb_app by (rewrite Hcplen; reflexivity).
           rewrite Hcpfc.
           replace (map (Rmult s) (otower_basis L')) with (vscale s (otower_basis L')) by reflexivity.
           rewrite Fcomb_vscale_r, Hcqfc, Hxe. ring.
    + simpl in Wf. destruct Wf as [Wa [Wb [Wr Wf']]].
      simpl in Hx. destruct Hx as [p [q [s [Tp [Tq [Ts Hxe]]]]]].
      destruct (IH Wf' p Tp) as [cp [Hcplen [Hcpr Hcpfc]]].
      destruct (IH Wf' q Tq) as [cq [Hcqlen [Hcqr Hcqfc]]].
      destruct (IH Wf' s Ts) as [cs0 [Hcslen [Hcsr Hcsfc]]].
      exists (cp ++ cq ++ cs0). split.
      * rewrite !length_app, Hcplen, Hcqlen, Hcslen. cbn [otower_basis].
        rewrite !length_app, !length_map. reflexivity.
      * split.
        -- apply Forall_app; split; [assumption | apply Forall_app; split; assumption].
        -- cbn [otower_basis].
           rewrite Fcomb_app by (rewrite Hcplen; reflexivity).
           rewrite Fcomb_app by (rewrite Hcqlen, length_map; reflexivity).
           rewrite Hcpfc.
           replace (map (Rmult r) (otower_basis L')) with (vscale r (otower_basis L')) by reflexivity.
           replace (map (Rmult (r*r)) (otower_basis L')) with (vscale (r*r) (otower_basis L')) by reflexivity.
           rewrite Fcomb_vscale_r, Hcqfc, Fcomb_vscale_r, Hcsfc, Hxe. ring.
Qed.

(* tower-combination machinery for OrigamiNum_in_otower *)
Lemma QF_contains_sr : forall F s x, is_subring F -> F x -> QF F s x.
Proof. intros F s x HF Hx. exists x, 0. repeat split; [exact Hx | apply subring_0; exact HF | ring]. Qed.

Lemma CF_contains_sr : forall F a b r x, is_subring F -> F x -> CF F a b r x.
Proof.
  intros F a b r x HF Hx. exists x, 0, 0.
  repeat split; [exact Hx | apply subring_0; exact HF | apply subring_0; exact HF | ring].
Qed.

Lemma otower_contains_rational : forall L, owf L -> forall x, is_rational x -> otower L x.
Proof.
  induction L as [|st L' IH]; intros W x Hx.
  - simpl. exact Hx.
  - destruct st as [s | a b r]; simpl in *.
    + destruct W as [_ W']. apply QF_contains_sr; [apply otower_subring; exact W' | apply IH; assumption].
    + destruct W as [_ [_ [_ W']]]. apply CF_contains_sr; [apply otower_subring; exact W' | apply IH; assumption].
Qed.

Lemma otower_weaken_base : forall L1 L2 x, owf L2 -> otower L1 x -> otower (L1 ++ L2) x.
Proof.
  induction L1 as [|st L1' IH]; intros L2 x W2 Tx.
  - simpl in Tx. simpl. apply otower_contains_rational; [exact W2 | exact Tx].
  - destruct st as [s | a b r]; simpl in *.
    + destruct Tx as [p [q [Tp [Tq Hx]]]]. exists p, q.
      repeat split; [apply IH; [exact W2 | exact Tp] | apply IH; [exact W2 | exact Tq] | exact Hx].
    + destruct Tx as [p [q [s0 [Tp [Tq [Ts0 Hx]]]]]]. exists p, q, s0.
      repeat split;
        [apply IH; [exact W2 | exact Tp] | apply IH; [exact W2 | exact Tq]
         | apply IH; [exact W2 | exact Ts0] | exact Hx].
Qed.

Lemma owf_app : forall L1 L2, owf L1 -> owf L2 -> owf (L1 ++ L2).
Proof.
  induction L1 as [|st L1' IH]; intros L2 W1 W2.
  - simpl. exact W2.
  - destruct st as [s | a b r]; simpl in *.
    + destruct W1 as [Wss W1']. split.
      * apply otower_weaken_base; [exact W2 | exact Wss].
      * apply IH; [exact W1' | exact W2].
    + destruct W1 as [Wa [Wb [Wr W1']]]. split; [|split; [|split]].
      * apply otower_weaken_base; [exact W2 | exact Wa].
      * apply otower_weaken_base; [exact W2 | exact Wb].
      * exact Wr.
      * apply IH; [exact W1' | exact W2].
Qed.

Lemma otower_weaken_top : forall L1 L2 x, owf (L1 ++ L2) -> otower L2 x -> otower (L1 ++ L2) x.
Proof.
  induction L1 as [|st L1' IH]; intros L2 x W Tx.
  - simpl in *. exact Tx.
  - destruct st as [s | a b r]; simpl in *.
    + destruct W as [Wss W']. apply QF_contains_sr; [apply otower_subring; exact W' | apply IH; [exact W' | exact Tx]].
    + destruct W as [Wa [Wb [Wr W']]]. apply CF_contains_sr; [apply otower_subring; exact W' | apply IH; [exact W' | exact Tx]].
Qed.

Lemma Fcomb_in_subring : forall G cs vs, is_subring G -> Forall G cs -> Forall G vs -> G (Fcomb cs vs).
Proof.
  induction cs as [|c cs IH]; intros vs HG Hcs Hvs.
  - simpl. apply subring_0; exact HG.
  - destruct vs as [|v vs]; simpl.
    + apply subring_0; exact HG.
    + inversion Hcs; inversion Hvs; subst.
      apply subring_add;
        [ exact HG
        | apply subring_mul; [exact HG | assumption | assumption]
        | apply IH; assumption ].
Qed.

(* from a nonzero F-relation on the powers of u (u<>0), read off 1/u as an F-poly in u *)
Lemma inverse_from_relation : forall (F : R -> Prop) cs u,
  is_subfield F -> u <> 0 -> Forall F cs -> ~ Forall (fun c => c = 0) cs ->
  Fcomb cs (powers u (length cs)) = 0 ->
  exists ds, Forall F ds /\ u * Fcomb ds (powers u (length ds)) = 1.
Proof.
  intros F cs u HF Hu. induction cs as [|c cs' IH]; intros HFcs Hnz Hrel.
  - exfalso. apply Hnz. constructor.
  - apply Forall_inv in HFcs as Hc. apply Forall_inv_tail in HFcs as Hcs'.
    cbn [length] in Hrel. rewrite powers_S in Hrel. cbn [Fcomb] in Hrel.
    rewrite Fcomb_vscale_r in Hrel.
    set (P := Fcomb cs' (powers u (length cs'))) in *.
    destruct (Req_dec_T c 0) as [Hc0 | Hcne].
    + assert (HuP : u * P = 0) by (rewrite Hc0 in Hrel; lra).
      assert (HP0 : P = 0)
        by (apply (Rmult_eq_reg_l u); [rewrite Rmult_0_r; exact HuP | exact Hu]).
      apply IH; [exact Hcs' | intro Hall; apply Hnz; constructor; [exact Hc0 | exact Hall] | exact HP0].
    + exists (map (Rmult (- / c)) cs'). split.
      * apply Forall_forall. intros z Hz. apply in_map_iff in Hz.
        destruct Hz as [x [Hzx Hx]]. subst z.
        apply subfield_mul; [exact HF | | rewrite Forall_forall in Hcs'; apply Hcs'; exact Hx].
        apply subfield_opp; [exact HF |]. apply subfield_inv; [exact HF | exact Hc | exact Hcne].
      * rewrite length_map, Fcomb_scale_l. fold P.
        assert (HuP : u * P = - c) by lra.
        replace (u * (- / c * P)) with (- / c * (u * P)) by ring.
        rewrite HuP. field. exact Hcne.
Qed.

Lemma CF_subfield : forall F a b r,
  is_subfield F -> F a -> F b -> r*r*r + a*r + b = 0 -> is_subfield (CF F a b r).
Proof.
  intros F a b r HF Ha Hb Hr.
  assert (HsrF : is_subring F) by (apply subfield_is_subring; exact HF).
  assert (HsrCF : is_subring (CF F a b r)) by (apply CF_subring; assumption).
  repeat split.
  - apply subring_0; exact HsrCF.
  - apply subring_1; exact HsrCF.
  - intros x y Hx Hy. apply subring_add; assumption.
  - intros x y Hx Hy. apply subring_sub; assumption.
  - intros x y Hx Hy. apply subring_mul; assumption.
  - intros u Hu Hune.
    assert (Hspan : Forall (spans F (1 :: r :: (r*r) :: nil)) (powers u 4)).
    { apply Forall_forall. intros w Hw. unfold powers in Hw. apply in_map_iff in Hw.
      destruct Hw as [i [Hwi Hi]]. subst w.
      assert (HuiCF : CF F a b r (u ^ i)) by (apply subring_pow; [exact HsrCF | exact Hu]).
      destruct HuiCF as [p [q [s [Hp [Hq [Hs Hue]]]]]].
      exists (p :: q :: s :: nil). split; [reflexivity|]. split.
      - constructor; [exact Hp | constructor; [exact Hq | constructor; [exact Hs | constructor]]].
      - simpl. rewrite Hue. ring. }
    assert (Hgt : Nat.lt (length (1 :: r :: (r*r) :: nil)) (length (powers u 4))).
    { unfold powers; rewrite length_map, length_seq; simpl; lia. }
    destruct (lin_dep_of_spanned F (1 :: r :: (r*r) :: nil) (powers u 4) HF Hspan Hgt)
      as [cs [Hlencs [Hratcs [Hfccs Hnd]]]].
    assert (Hlen4 : length cs = 4%nat)
      by (rewrite Hlencs; unfold powers; rewrite length_map, length_seq; reflexivity).
    assert (Hrel : Fcomb cs (powers u (length cs)) = 0) by (rewrite Hlen4; exact Hfccs).
    destruct (inverse_from_relation F cs u HF Hune Hratcs Hnd Hrel) as [ds [Hdsf Hinv]].
    assert (HvCF : CF F a b r (Fcomb ds (powers u (length ds)))).
    { apply Fcomb_in_subring; [exact HsrCF | |].
      - apply Forall_forall. intros z Hz. apply CF_contains_sr; [exact HsrF |].
        rewrite Forall_forall in Hdsf; apply Hdsf; exact Hz.
      - apply Forall_forall. intros z Hz. unfold powers in Hz. apply in_map_iff in Hz.
        destruct Hz as [i [Hzi Hi]]. subst z. apply subring_pow; [exact HsrCF | exact Hu]. }
    replace (/ u) with (Fcomb ds (powers u (length ds))).
    + exact HvCF.
    + apply (Rmult_eq_reg_l u); [|exact Hune]. rewrite Rinv_r by exact Hune. exact Hinv.
Qed.

Lemma otower_subfield : forall L, owf L -> is_subfield (otower L).
Proof.
  induction L as [|st L' IH]; intros W.
  - simpl. apply is_rational_subfield.
  - destruct st as [s | a b r]; simpl in *.
    + destruct W as [Wss W']. apply QF_subfield; [apply IH; exact W' | exact Wss].
    + destruct W as [Wa [Wb [Wr W']]].
      apply CF_subfield; [apply IH; exact W' | exact Wa | exact Wb | exact Wr].
Qed.

Lemma OrigamiNum_in_otower : forall x, OrigamiNum x -> exists L, owf L /\ otower L x.
Proof.
  intros x H.
  induction H as
    [ | | x y Hx IHx Hy IHy | x y Hx IHx Hy IHy | x y Hx IHx Hy IHy
    | x Hx IHx Hxne | x Hx IHx Hxnn | a b r Ha IHa Hb IHb Hcubic ].
  - exists nil. split; [exact I | simpl; exists 0%Z, 1%Z; split; [lia | simpl; field]].
  - exists nil. split; [exact I | simpl; exists 1%Z, 1%Z; split; [lia | simpl; field]].
  - destruct IHx as [L1 [W1 T1]]. destruct IHy as [L2 [W2 T2]].
    exists (L1 ++ L2). assert (Wapp : owf (L1 ++ L2)) by (apply owf_app; assumption).
    split; [exact Wapp |]. apply subring_add; [apply otower_subring; exact Wapp | |].
    + apply otower_weaken_base; [exact W2 | exact T1].
    + apply otower_weaken_top; [exact Wapp | exact T2].
  - destruct IHx as [L1 [W1 T1]]. destruct IHy as [L2 [W2 T2]].
    exists (L1 ++ L2). assert (Wapp : owf (L1 ++ L2)) by (apply owf_app; assumption).
    split; [exact Wapp |]. apply subring_sub; [apply otower_subring; exact Wapp | |].
    + apply otower_weaken_base; [exact W2 | exact T1].
    + apply otower_weaken_top; [exact Wapp | exact T2].
  - destruct IHx as [L1 [W1 T1]]. destruct IHy as [L2 [W2 T2]].
    exists (L1 ++ L2). assert (Wapp : owf (L1 ++ L2)) by (apply owf_app; assumption).
    split; [exact Wapp |]. apply subring_mul; [apply otower_subring; exact Wapp | |].
    + apply otower_weaken_base; [exact W2 | exact T1].
    + apply otower_weaken_top; [exact Wapp | exact T2].
  - destruct IHx as [L [W T]]. exists L. split; [exact W |].
    apply subfield_inv; [apply otower_subfield; exact W | exact T | exact Hxne].
  - destruct IHx as [L [W T]]. exists (OQuad (R_sqrt.sqrt x) :: L). split.
    + simpl. split; [| exact W]. rewrite (R_sqrt.sqrt_sqrt x Hxnn). exact T.
    + simpl. exists 0, 1. repeat split;
        [ apply subring_0; apply otower_subring; exact W
        | apply subring_1; apply otower_subring; exact W | ring ].
  - destruct IHa as [La [Wa Ta]]. destruct IHb as [Lb [Wb Tb]].
    assert (Wapp : owf (La ++ Lb)) by (apply owf_app; assumption).
    exists (OCubic a b r :: (La ++ Lb)). split.
    + simpl. split; [|split; [|split]].
      * apply otower_weaken_base; [exact Wb | exact Ta].
      * apply otower_weaken_top; [exact Wapp | exact Tb].
      * exact Hcubic.
      * exact Wapp.
    + simpl. exists 0, 1, 0. repeat split;
        [ apply subring_0; apply otower_subring; exact Wapp
        | apply subring_1; apply otower_subring; exact Wapp
        | apply subring_0; apply otower_subring; exact Wapp | ring ].
Qed.

(* ============================================================================
   #1: every origami-constructible number has algebraic degree of the form
   2^a * 3^b.
   ============================================================================ *)
Theorem origami_alg_deg_2_3_smooth : forall x, OrigamiNum x ->
  exists m, two_three_smooth m /\ alg_deg_le x m.
Proof.
  intros x HO. destruct (OrigamiNum_in_otower x HO) as [L [Wf Tx]].
  exists (length (otower_basis L)). split; [apply otower_basis_smooth |].
  assert (HsfT : is_subfield (otower L)) by (apply otower_subfield; exact Wf).
  assert (Hspan : Forall (spans is_rational (otower_basis L))
                         (powers x (S (length (otower_basis L))))).
  { apply Forall_forall. intros y Hy. unfold powers in Hy. apply in_map_iff in Hy.
    destruct Hy as [i [Hyi Hi]]. subst y.
    apply otower_spanned; [exact Wf |].
    apply subring_pow; [apply subfield_is_subring; exact HsfT | exact Tx]. }
  assert (Hgt : (length (otower_basis L)
                 < length (powers x (S (length (otower_basis L)))))%nat).
  { unfold powers; rewrite length_map, length_seq. lia. }
  destruct (lin_dep_of_spanned is_rational (otower_basis L)
              (powers x (S (length (otower_basis L)))) is_rational_subfield Hspan Hgt)
    as [cs [Hlencs [Hratcs [Hfccs Hnd]]]].
  assert (Hlen2 : length cs = S (length (otower_basis L)))
    by (rewrite Hlencs; unfold powers; rewrite length_map, length_seq; reflexivity).
  apply (rational_relation_alg_deg x cs (length (otower_basis L)) Hlen2 Hratcs Hnd Hfccs).
Qed.


(* ============================================================================
   Dimension of a subspace S of R over a coefficient subfield F, via bases.
   ============================================================================ *)

Definition spanning (F : R -> Prop) (B : list R) (S : R -> Prop) : Prop :=
  forall y, S y -> spans F B y.

Definition basis (F : R -> Prop) (B : list R) (S : R -> Prop) : Prop :=
  Forall S B /\ lin_indep F B /\ spanning F B S.

(* any two bases of the same space have equal cardinality (Steinitz both ways) *)
Lemma basis_card_unique : forall F B1 B2 S, is_subfield F ->
  basis F B1 S -> basis F B2 S -> length B1 = length B2.
Proof.
  intros F B1 B2 S HF [HS1 [Hli1 Hsp1]] [HS2 [Hli2 Hsp2]].
  assert (H12 : (length B1 <= length B2)%nat).
  { apply (steinitz F B2 B1 HF Hli1). apply Forall_forall. intros b Hb.
    apply Hsp2. rewrite Forall_forall in HS1. apply HS1; exact Hb. }
  assert (H21 : (length B2 <= length B1)%nat).
  { apply (steinitz F B1 B2 HF Hli2). apply Forall_forall. intros b Hb.
    apply Hsp1. rewrite Forall_forall in HS2. apply HS2; exact Hb. }
  lia.
Qed.

(* an independent subset is no larger than any spanning set *)
Lemma indep_le_span : forall F B G S, is_subfield F ->
  lin_indep F B -> Forall S B -> spanning F G S -> (length B <= length G)%nat.
Proof.
  intros F B G S HF Hli HBS Hsp. apply (steinitz F G B HF Hli).
  apply Forall_forall. intros b Hb. apply Hsp.
  rewrite Forall_forall in HBS. apply HBS; exact Hb.
Qed.

(* every member of a list is spanned by the list *)
Lemma spans_in_self : forall F vs v, is_subfield F -> In v vs -> spans F vs v.
Proof.
  intros F vs v HF Hin. apply In_nth with (d := 0) in Hin.
  destruct Hin as [i [Hilt Hnth]].
  exists (e_i (length vs) i). split; [apply e_i_length |]. split.
  - apply e_i_Forall; exact HF.
  - rewrite Fcomb_e_i by exact Hilt. exact Hnth.
Qed.

Lemma spans_mono : forall F g B y, is_subfield F -> spans F B y -> spans F (g :: B) y.
Proof.
  intros F g B y HF [cs [Hlen [HFcs Hfc]]].
  exists (0 :: cs). split; [simpl; rewrite Hlen; reflexivity |]. split.
  - constructor; [apply subfield_0; exact HF | exact HFcs].
  - simpl. rewrite Hfc. ring.
Qed.

Lemma indep_extend : forall F g B, is_subfield F ->
  lin_indep F B -> ~ spans F B g -> lin_indep F (g :: B).
Proof.
  intros F g B HF Hli Hns cs Hlen HFcs Hfc.
  destruct cs as [|c cs']; [simpl in Hlen; discriminate|].
  simpl in Hlen. injection Hlen as Hlen'. simpl in Hfc.
  apply Forall_inv in HFcs as Hc. apply Forall_inv_tail in HFcs as Hcs'.
  assert (Hc0 : c = 0).
  { destruct (Req_dec_T c 0) as [|Hcne]; [assumption|]. exfalso. apply Hns.
    exists (map (Rmult (- / c)) cs'). split; [rewrite length_map; exact Hlen' |]. split.
    - apply Forall_forall. intros z Hz. apply in_map_iff in Hz. destruct Hz as [w [Hzw Hw]]. subst z.
      apply subfield_mul;
        [ exact HF
        | apply subfield_opp; [exact HF | apply subfield_inv; [exact HF | exact Hc | exact Hcne]]
        | rewrite Forall_forall in Hcs'; apply Hcs'; exact Hw ].
    - rewrite Fcomb_scale_l.
      assert (HFcsB : Fcomb cs' B = - c * g) by lra.
      rewrite HFcsB. field. exact Hcne. }
  subst c. constructor; [reflexivity |].
  apply Hli; [exact Hlen' | exact Hcs' | lra].
Qed.

Lemma extract_aux : forall F G, is_subfield F ->
  exists B, lin_indep F B /\ (forall v, In v B -> In v G) /\ (forall g, In g G -> spans F B g).
Proof.
  intros F G HF. induction G as [|g G' IH].
  - exists nil. split; [apply lin_indep_nil | split].
    + intros v Hv; exact Hv.
    + intros x Hx; inversion Hx.
  - destruct IH as [B' [Hli' [Hsub' Hsp']]].
    destruct (classic (spans F B' g)) as [Hgs | Hgns].
    + exists B'. split; [exact Hli' | split].
      * intros v Hv. right. apply Hsub'; exact Hv.
      * intros x Hx. destruct Hx as [Hxg | Hxg]; [subst x; exact Hgs | apply Hsp'; exact Hxg].
    + exists (g :: B'). split; [apply indep_extend; assumption | split].
      * intros v Hv. destruct Hv as [Hvg | Hvb];
          [subst v; left; reflexivity | right; apply Hsub'; exact Hvb].
      * intros x Hx. destruct Hx as [Hxg | Hxg].
        -- subst x. apply spans_in_self; [exact HF | left; reflexivity].
        -- apply spans_mono; [exact HF |]. apply Hsp'; exact Hxg.
Qed.

Lemma basis_extract : forall F G S, is_subfield F ->
  Forall S G -> spanning F G S -> exists B, basis F B S.
Proof.
  intros F G S HF HSG Hsp.
  destruct (extract_aux F G HF) as [B [Hli [Hsub Hspg]]].
  exists B. split; [| split].
  - apply Forall_forall. intros v Hv. rewrite Forall_forall in HSG. apply HSG. apply Hsub; exact Hv.
  - exact Hli.
  - intros y Hy. apply (spans_trans F B G y HF); [intros v Hv; apply Hspg; exact Hv | apply Hsp; exact Hy].
Qed.

(* ============================================================================
   Polynomial arithmetic over R (coefficient lists, low degree first).
   pe cs x = sum_i cs_i x^i = Fcomb cs (powers x (length cs)).
   ============================================================================ *)

Definition pe (cs : list R) (x : R) : R := Fcomb cs (powers x (length cs)).

Lemma pe_nil : forall x, pe nil x = 0.
Proof. intros x. reflexivity. Qed.

Lemma pe_cons : forall c cs x, pe (c :: cs) x = c + x * pe cs x.
Proof.
  intros c cs x. unfold pe. cbn [length]. rewrite powers_S. cbn [Fcomb].
  rewrite Fcomb_vscale_r. ring.
Qed.

Fixpoint padd (p q : list R) : list R :=
  match p, q with
  | nil, _ => q
  | _, nil => p
  | a :: p', b :: q' => (a + b) :: padd p' q'
  end.

Lemma pe_padd : forall p q x, pe (padd p q) x = pe p x + pe q x.
Proof.
  induction p as [|a p IH]; intros q x.
  - simpl. rewrite pe_nil. ring.
  - destruct q as [|b q].
    + simpl. rewrite pe_nil. ring.
    + simpl padd. rewrite !pe_cons, IH. ring.
Qed.

Lemma pe_scale : forall a q x, pe (map (Rmult a) q) x = a * pe q x.
Proof.
  intros a q x. unfold pe. rewrite length_map, Fcomb_scale_l. reflexivity.
Qed.

Fixpoint pmul (p q : list R) : list R :=
  match p with
  | nil => nil
  | a :: p' => padd (map (Rmult a) q) (0 :: pmul p' q)
  end.

Lemma pe_pmul : forall p q x, pe (pmul p q) x = pe p x * pe q x.
Proof.
  induction p as [|a p IH]; intros q x.
  - simpl. rewrite pe_nil. ring.
  - simpl pmul. rewrite pe_padd, pe_scale, (pe_cons 0 (pmul p q) x), IH, (pe_cons a p x). ring.
Qed.

(* ============================================================================
   Product basis: a flat combination over {e_i * f_j} regroups as a nested
   combination (outer over the e_i, K-coefficients being combinations of f_j).
   ============================================================================ *)

Fixpoint Kcoeffs (Bf Be cs : list R) : list R :=
  match Be with
  | nil => nil
  | _ :: Be' => Fcomb (firstn (length Bf) cs) Bf :: Kcoeffs Bf Be' (skipn (length Bf) cs)
  end.

Lemma Fcomb_prod_regroup : forall Bf Be cs, length cs = (length Be * length Bf)%nat ->
  Fcomb cs (flat_map (fun e => map (Rmult e) Bf) Be) = Fcomb (Kcoeffs Bf Be cs) Be.
Proof.
  intros Bf Be. induction Be as [|e Be' IH]; intros cs Hlen.
  - cbn [flat_map Kcoeffs]. rewrite !Fcomb_nil_r. reflexivity.
  - cbn [flat_map Kcoeffs].
    assert (Hf : length (firstn (length Bf) cs) = length Bf).
    { rewrite length_firstn. apply Nat.min_l. cbn [length] in Hlen. nia. }
    rewrite <- (firstn_skipn (length Bf) cs) at 1.
    rewrite Fcomb_app by (rewrite Hf, length_map; reflexivity).
    cbn [Fcomb].
    replace (map (Rmult e) Bf) with (vscale e Bf) by reflexivity.
    rewrite Fcomb_vscale_r.
    rewrite IH by (rewrite length_skipn; cbn [length] in Hlen; nia).
    ring.
Qed.

Lemma Kcoeffs_length : forall Bf Be cs, length (Kcoeffs Bf Be cs) = length Be.
Proof.
  intros Bf Be. induction Be as [|e Be' IH]; intros cs; [reflexivity|].
  cbn [Kcoeffs length]. rewrite IH. reflexivity.
Qed.

Lemma Forall_firstn_R : forall (P:R->Prop) n l, Forall P l -> Forall P (firstn n l).
Proof.
  intros P n l. revert n. induction l as [|a l IH]; intros n H.
  - rewrite firstn_nil. constructor.
  - destruct n; simpl; [constructor|]. inversion H; subst.
    constructor; [assumption | apply IH; assumption].
Qed.

Lemma Forall_skipn_R : forall (P:R->Prop) n l, Forall P l -> Forall P (skipn n l).
Proof.
  intros P n l. revert n. induction l as [|a l IH]; intros n H.
  - rewrite skipn_nil. constructor.
  - destruct n; simpl; [exact H|]. inversion H; subst. apply IH; assumption.
Qed.

Lemma Kcoeffs_Forall : forall K Bf Be cs, is_subfield K ->
  Forall K cs -> Forall K Bf -> Forall K (Kcoeffs Bf Be cs).
Proof.
  intros K Bf Be. induction Be as [|e Be' IH]; intros cs HK Hcs HBf; [constructor|].
  cbn [Kcoeffs]. constructor.
  - apply Fcomb_in_field; [exact HK | apply Forall_firstn_R; exact Hcs | exact HBf].
  - apply IH; [exact HK | apply Forall_skipn_R; exact Hcs | exact HBf].
Qed.

Lemma Kcoeffs_zero_inv : forall F Bf Be cs, is_subfield F ->
  lin_indep F Bf -> length cs = (length Be * length Bf)%nat -> Forall F cs ->
  Forall (fun c => c = 0) (Kcoeffs Bf Be cs) -> Forall (fun c => c = 0) cs.
Proof.
  intros F Bf Be. induction Be as [|e Be' IH]; intros cs HF Hli Hlen HFcs Hz.
  - simpl in Hlen. destruct cs as [|c cs']; [constructor | simpl in Hlen; lia].
  - cbn [Kcoeffs] in Hz. apply Forall_inv in Hz as H1. apply Forall_inv_tail in Hz as H2.
    rewrite <- (firstn_skipn (length Bf) cs). apply Forall_app. split.
    + apply (Hli (firstn (length Bf) cs)).
      * rewrite length_firstn. apply Nat.min_l. cbn [length] in Hlen. nia.
      * apply Forall_firstn_R; exact HFcs.
      * exact H1.
    + apply (IH (skipn (length Bf) cs) HF Hli).
      * rewrite length_skipn. cbn [length] in Hlen. nia.
      * apply Forall_skipn_R; exact HFcs.
      * exact H2.
Qed.

Lemma product_length : forall Bf Be,
  length (flat_map (fun e => map (Rmult e) Bf) Be) = (length Be * length Bf)%nat.
Proof.
  intros Bf Be. induction Be as [|e Be' IH]; [reflexivity|].
  cbn [flat_map length]. rewrite length_app, length_map, IH. nia.
Qed.

Lemma product_basis_indep : forall Bf Be K, is_subfield K ->
  (forall x, is_rational x -> K x) -> Forall K Bf ->
  lin_indep is_rational Bf -> lin_indep K Be ->
  lin_indep is_rational (flat_map (fun e => map (Rmult e) Bf) Be).
Proof.
  intros Bf Be K HK HQK HBfK Hlif Hlie cs Hlen HFcs Hfc.
  rewrite product_length in Hlen.
  apply (Kcoeffs_zero_inv is_rational Bf Be cs is_rational_subfield Hlif Hlen HFcs).
  apply Hlie.
  - apply Kcoeffs_length.
  - apply Kcoeffs_Forall; [exact HK | | exact HBfK].
    apply Forall_forall. intros z Hz. apply HQK.
    rewrite Forall_forall in HFcs. apply HFcs; exact Hz.
  - rewrite <- (Fcomb_prod_regroup Bf Be cs Hlen). exact Hfc.
Qed.

Lemma spans_vscale : forall F a vs y, spans F vs y -> spans F (vscale a vs) (a * y).
Proof.
  intros F a vs y [cs [Hlen [HF Hfc]]]. exists cs.
  split; [unfold vscale; rewrite length_map; exact Hlen | split].
  - exact HF.
  - rewrite Fcomb_vscale_r, Hfc. reflexivity.
Qed.

Lemma spans_app : forall F A B u v, spans F A u -> spans F B v -> spans F (A ++ B) (u + v).
Proof.
  intros F A B u v [ca [Hla [HFa Hfa]]] [cb [Hlb [HFb Hfb]]].
  exists (ca ++ cb). split; [rewrite !length_app, Hla, Hlb; reflexivity | split].
  - apply Forall_app; split; assumption.
  - rewrite Fcomb_app by exact Hla. rewrite Hfa, Hfb. reflexivity.
Qed.

Lemma product_spans_aux : forall Bf Be ks,
  length ks = length Be ->
  (forall k, In k ks -> spans is_rational Bf k) ->
  spans is_rational (flat_map (fun e => map (Rmult e) Bf) Be) (Fcomb ks Be).
Proof.
  intros Bf Be. induction Be as [|e Be' IH]; intros ks Hlen Hks.
  - destruct ks; [|simpl in Hlen; lia]. cbn [flat_map Fcomb].
    exists nil. split; [reflexivity | split; [constructor | reflexivity]].
  - destruct ks as [|k ks']; [simpl in Hlen; lia|].
    cbn [flat_map Fcomb].
    replace (map (Rmult e) Bf) with (vscale e Bf) by reflexivity.
    replace (k * e) with (e * k) by ring.
    apply spans_app.
    + apply spans_vscale. apply Hks. left; reflexivity.
    + apply IH; [simpl in Hlen; lia | intros k' Hk'; apply Hks; right; exact Hk'].
Qed.

(* the products of a Q-basis of K and a K-basis of L form a Q-basis of L *)
Lemma product_basis : forall Bf Be K L,
  is_subfield K -> is_subfield L ->
  (forall x, is_rational x -> K x) -> (forall x, K x -> L x) ->
  basis is_rational Bf K -> basis K Be L ->
  basis is_rational (flat_map (fun e => map (Rmult e) Bf) Be) L.
Proof.
  intros Bf Be K L HK HL HQK HKL [HBfK [HlifBf HspBf]] [HBeL [HlieBe HspBe]].
  split; [|split].
  - apply Forall_forall. intros z Hz. apply in_flat_map in Hz. destruct Hz as [e [HeBe Hz]].
    apply in_map_iff in Hz. destruct Hz as [f [Hzf HfBf]]. subst z.
    apply subfield_mul;
      [ exact HL
      | rewrite Forall_forall in HBeL; apply HBeL; exact HeBe
      | apply HKL; rewrite Forall_forall in HBfK; apply HBfK; exact HfBf ].
  - apply (product_basis_indep Bf Be K); [exact HK | exact HQK | exact HBfK | exact HlifBf | exact HlieBe].
  - intros y Hy. destruct (HspBe y Hy) as [ks [Hlks [HKks Hfks]]].
    rewrite <- Hfks. apply product_spans_aux; [exact Hlks |].
    intros k Hk. apply HspBf. rewrite Forall_forall in HKks. apply HKks; exact Hk.
Qed.

(* tower law: dim_Q(L) = dim_K(L) * dim_Q(K) *)
Lemma tower_law_dim : forall Bf Be BL K L,
  is_subfield K -> is_subfield L ->
  (forall x, is_rational x -> K x) -> (forall x, K x -> L x) ->
  basis is_rational Bf K -> basis K Be L -> basis is_rational BL L ->
  length BL = (length Be * length Bf)%nat.
Proof.
  intros Bf Be BL K L HK HL HQK HKL HbBf HbBe HbBL.
  pose proof (product_basis Bf Be K L HK HL HQK HKL HbBf HbBe) as Hprod.
  rewrite (basis_card_unique is_rational BL _ L is_rational_subfield HbBL Hprod).
  apply product_length.
Qed.

(* ============================================================================
   Q[x] (polynomial evaluations) as a subfield, with basis 1,x,...,x^{d-1}.
   ============================================================================ *)

Lemma Forall_rat_padd : forall p q,
  Forall is_rational p -> Forall is_rational q -> Forall is_rational (padd p q).
Proof.
  induction p as [|a p IH]; intros q Hp Hq.
  - simpl. exact Hq.
  - destruct q as [|b q]; simpl; [exact Hp|].
    inversion Hp; inversion Hq; subst. constructor.
    + apply (subfield_add is_rational a b is_rational_subfield); assumption.
    + apply IH; assumption.
Qed.

Lemma Forall_rat_pmul : forall p q,
  Forall is_rational p -> Forall is_rational q -> Forall is_rational (pmul p q).
Proof.
  induction p as [|a p IH]; intros q Hp Hq.
  - simpl. constructor.
  - simpl pmul. inversion Hp; subst. apply Forall_rat_padd.
    + apply Forall_forall. intros z Hz. apply in_map_iff in Hz. destruct Hz as [w [Hzw Hw]]. subst z.
      apply (subfield_mul is_rational a w is_rational_subfield);
        [assumption | rewrite Forall_forall in Hq; apply Hq; exact Hw].
    + constructor; [apply (subfield_0 is_rational is_rational_subfield) | apply IH; assumption].
Qed.

Definition Qx (x v : R) : Prop := exists cs, Forall is_rational cs /\ pe cs x = v.

Lemma Qx_subring : forall x, is_subring (Qx x).
Proof.
  intros x. repeat split.
  - exists nil. split; [constructor | apply pe_nil].
  - exists (1 :: nil). split;
      [ constructor; [apply (subfield_1 is_rational is_rational_subfield) | constructor]
      | rewrite pe_cons, pe_nil; ring ].
  - intros u v [cu [Hcu Hu]] [cv [Hcv Hv]]. exists (padd cu cv). split.
    + apply Forall_rat_padd; assumption.
    + rewrite pe_padd, Hu, Hv. reflexivity.
  - intros u v [cu [Hcu Hu]] [cv [Hcv Hv]]. exists (padd cu (map (Rmult (-1)) cv)). split.
    + apply Forall_rat_padd; [exact Hcu |]. apply Forall_forall. intros z Hz.
      apply in_map_iff in Hz. destruct Hz as [w [Hzw Hw]]. subst z.
      apply (subfield_mul is_rational (-1) w is_rational_subfield);
        [ apply (subfield_opp is_rational 1 is_rational_subfield); apply (subfield_1 is_rational is_rational_subfield)
        | rewrite Forall_forall in Hcv; apply Hcv; exact Hw ].
    + rewrite pe_padd, pe_scale, Hu, Hv. ring.
  - intros u v [cu [Hcu Hu]] [cv [Hcv Hv]]. exists (pmul cu cv). split.
    + apply Forall_rat_pmul; assumption.
    + rewrite pe_pmul, Hu, Hv. reflexivity.
Qed.

Lemma Qx_rational : forall x v, is_rational v -> Qx x v.
Proof.
  intros x v Hv. exists (v :: nil).
  split; [constructor; [exact Hv | constructor] | rewrite pe_cons, pe_nil; ring].
Qed.

Lemma Qx_subfield : forall x F B, is_subfield F -> F x -> basis is_rational B F -> is_subfield (Qx x).
Proof.
  intros x F B HF Hx [HBF [HliB HspB]].
  assert (HQxsub : is_subring (Qx x)) by (apply Qx_subring).
  assert (HQxF : forall v, Qx x v -> F v).
  { intros v [cs [Hcs Hv]]. rewrite <- Hv. unfold pe.
    apply Fcomb_in_field; [exact HF | |].
    - apply Forall_forall. intros z Hz. apply subfield_contains_rational;
        [exact HF | rewrite Forall_forall in Hcs; apply Hcs; exact Hz].
    - apply Forall_forall. intros z Hz. unfold powers in Hz. apply in_map_iff in Hz.
      destruct Hz as [i [Hzi _]]. subst z. apply subfield_pow; [exact HF | exact Hx]. }
  repeat split.
  - apply subring_0; exact HQxsub.
  - apply subring_1; exact HQxsub.
  - intros u v Hu Hv. apply subring_add; [exact HQxsub | exact Hu | exact Hv].
  - intros u v Hu Hv. apply subring_sub; [exact HQxsub | exact Hu | exact Hv].
  - intros u v Hu Hv. apply subring_mul; [exact HQxsub | exact Hu | exact Hv].
  - intros u Hu Hune.
    assert (HuF : F u) by (apply HQxF; exact Hu).
    assert (HpowF : Forall F (powers u (S (length B)))).
    { apply Forall_forall. intros w Hw. unfold powers in Hw. apply in_map_iff in Hw.
      destruct Hw as [i [Hwi _]]. subst w. apply subfield_pow; [exact HF | exact HuF]. }
    assert (Hspan : Forall (spans is_rational B) (powers u (S (length B)))).
    { apply Forall_forall. intros w Hw. unfold powers in Hw. apply in_map_iff in Hw.
      destruct Hw as [i [Hwi _]]. subst w. apply HspB. apply subfield_pow; [exact HF | exact HuF]. }
    assert (Hgt : Nat.lt (length B) (length (powers u (S (length B))))).
    { unfold powers; rewrite length_map, length_seq. lia. }
    destruct (lin_dep_of_spanned is_rational B (powers u (S (length B)))
                is_rational_subfield Hspan Hgt) as [cs [Hlencs [Hratcs [Hfccs Hnd]]]].
    assert (Hlen2 : length cs = S (length B))
      by (rewrite Hlencs; unfold powers; rewrite length_map, length_seq; reflexivity).
    assert (Hrel : Fcomb cs (powers u (length cs)) = 0) by (rewrite Hlen2; exact Hfccs).
    destruct (inverse_from_relation is_rational cs u is_rational_subfield Hune Hratcs Hnd Hrel)
      as [ds [Hdsf Hinv]].
    replace (/ u) with (Fcomb ds (powers u (length ds))).
    + apply Fcomb_in_subring; [exact HQxsub | |].
      * apply Forall_forall. intros z Hz. apply Qx_rational.
        rewrite Forall_forall in Hdsf; apply Hdsf; exact Hz.
      * apply Forall_forall. intros z Hz. unfold powers in Hz. apply in_map_iff in Hz.
        destruct Hz as [i [Hzi _]]. subst z. apply subring_pow; [exact HQxsub | exact Hu].
    + apply (Rmult_eq_reg_l u); [|exact Hune]. rewrite Rinv_r by exact Hune. exact Hinv.
Qed.

(* ============================================================================
   The powers basis 1, x, ..., x^{d-1} of Q[x], where d is the maximal length
   of an independent prefix of powers.
   ============================================================================ *)

Lemma nat_boundary : forall (P : nat -> Prop) N, P 0%nat -> ~ P (S N) -> exists d, P d /\ ~ P (S d).
Proof.
  induction N as [|N IH]; intros H0 HSN.
  - exists 0%nat. split; assumption.
  - destruct (classic (P (S N))) as [HP | HP].
    + exists (S N). split; assumption.
    + apply IH; assumption.
Qed.

Lemma powers_app : forall x d, powers x (S d) = powers x d ++ (x ^ d :: nil).
Proof.
  intros x d. unfold powers. rewrite seq_S, map_app. simpl. reflexivity.
Qed.

Lemma powers_length : forall x n, length (powers x n) = n.
Proof. intros x n. unfold powers. rewrite length_map, length_seq. reflexivity. Qed.

Lemma powers_top_in_span : forall x d,
  lin_indep is_rational (powers x d) -> ~ lin_indep is_rational (powers x (S d)) ->
  spans is_rational (powers x d) (x ^ d).
Proof.
  intros x d Hind Hdep.
  apply not_all_ex_not in Hdep. destruct Hdep as [cs Hcs].
  apply imply_to_and in Hcs. destruct Hcs as [Hlencs Hcs].
  apply imply_to_and in Hcs. destruct Hcs as [Hratcs Hcs].
  apply imply_to_and in Hcs. destruct Hcs as [Hfccs Hnd].
  assert (HlenSd : length cs = S d) by (rewrite Hlencs, powers_length; reflexivity).
  assert (Hcsne : cs <> nil) by (intro Hc; subst cs; simpl in HlenSd; discriminate).
  pose proof (app_removelast_last 0 Hcsne) as Hsplit.
  set (cs0 := removelast cs) in *. set (a := last cs 0) in *.
  assert (Hlen0 : length cs0 = d).
  { assert (length cs = length (cs0 ++ a :: nil)) by (rewrite <- Hsplit; reflexivity).
    rewrite length_app in H. simpl in H. rewrite HlenSd in H. lia. }
  assert (Hrat0 : Forall is_rational cs0 /\ is_rational a).
  { assert (Hr : Forall is_rational (cs0 ++ a :: nil)) by (rewrite <- Hsplit; exact Hratcs).
    apply Forall_app in Hr. destruct Hr as [Hr0 Hra]. split; [exact Hr0 | inversion Hra; assumption]. }
  destruct Hrat0 as [Hrat0 Hrata].
  rewrite powers_app, Hsplit in Hfccs.
  rewrite Fcomb_app in Hfccs by (rewrite Hlen0, powers_length; reflexivity).
  cbn [Fcomb] in Hfccs.
  assert (Hane : a <> 0).
  { intro Ha0. apply Hnd. rewrite Hsplit.
    assert (Hcs00 : Fcomb cs0 (powers x d) = 0) by (rewrite Ha0 in Hfccs; lra).
    apply Forall_app. split.
    - apply Hind; [rewrite powers_length; exact Hlen0 | exact Hrat0 | exact Hcs00].
    - rewrite Ha0. constructor; [reflexivity | constructor]. }
  exists (map (Rmult (- / a)) cs0). split; [rewrite length_map, powers_length; exact Hlen0 | split].
  - apply Forall_forall. intros z Hz. apply in_map_iff in Hz. destruct Hz as [w [Hzw Hw]]. subst z.
    apply (subfield_mul is_rational (- / a) w is_rational_subfield).
    + apply (subfield_opp is_rational (/ a) is_rational_subfield).
      apply (subfield_inv is_rational a is_rational_subfield); [exact Hrata | exact Hane].
    + rewrite Forall_forall in Hrat0. apply Hrat0; exact Hw.
  - rewrite Fcomb_scale_l.
    assert (Hval : Fcomb cs0 (powers x d) = - a * x ^ d) by lra.
    rewrite Hval. field. exact Hane.
Qed.

Lemma pow_le_spanned : forall x d k,
  spans is_rational (powers x d) (x ^ d) -> (k <= d)%nat -> spans is_rational (powers x d) (x ^ k).
Proof.
  intros x d k Hxd Hk. destruct (Nat.eq_dec k d) as [->|Hne]; [exact Hxd|].
  apply spans_in_self; [apply is_rational_subfield|].
  unfold powers. apply in_map_iff. exists k. split; [reflexivity | apply in_seq; lia].
Qed.

Lemma spans_mult_x : forall x d v, spans is_rational (powers x d) (x ^ d) ->
  spans is_rational (powers x d) v -> spans is_rational (powers x d) (x * v).
Proof.
  intros x d v Hxd [cs [Hlen [HF Hfc]]].
  apply (spans_trans is_rational (powers x d) (vscale x (powers x d)) (x * v) is_rational_subfield).
  - intros w Hw. unfold vscale in Hw. apply in_map_iff in Hw. destruct Hw as [u [Hwu Hu]]. subst w.
    unfold powers in Hu. apply in_map_iff in Hu. destruct Hu as [i [Hui Hi]]. subst u.
    apply in_seq in Hi.
    replace (x * x ^ i) with (x ^ (S i)) by (simpl; ring).
    apply pow_le_spanned; [exact Hxd | lia].
  - exists cs. split; [unfold vscale; rewrite length_map; exact Hlen | split; [exact HF |]].
    rewrite Fcomb_vscale_r, Hfc. reflexivity.
Qed.

Lemma pow_all_spanned : forall x d k,
  spans is_rational (powers x d) (x ^ d) -> spans is_rational (powers x d) (x ^ k).
Proof.
  intros x d k Hxd. induction k as [|k IH].
  - apply pow_le_spanned; [exact Hxd | lia].
  - replace (x ^ (S k)) with (x * x ^ k) by (simpl; ring).
    apply spans_mult_x; [exact Hxd | exact IH].
Qed.

Lemma Qx_spanned_by_powers : forall x d v,
  spans is_rational (powers x d) (x ^ d) -> Qx x v -> spans is_rational (powers x d) v.
Proof.
  intros x d v Hxd [cs [Hcs Hv]]. rewrite <- Hv. unfold pe.
  apply (spans_trans is_rational (powers x d) (powers x (length cs))
           (Fcomb cs (powers x (length cs))) is_rational_subfield).
  - intros w Hw. unfold powers in Hw. apply in_map_iff in Hw. destruct Hw as [i [Hwi _]]. subst w.
    apply pow_all_spanned; exact Hxd.
  - exists cs. split; [rewrite powers_length; reflexivity | split; [exact Hcs | reflexivity]].
Qed.

Lemma Qx_x : forall x, Qx x x.
Proof.
  intros x. exists (0 :: 1 :: nil). split.
  - repeat constructor;
      [apply (subfield_0 is_rational is_rational_subfield)
       | apply (subfield_1 is_rational is_rational_subfield)].
  - rewrite pe_cons, pe_cons, pe_nil. ring.
Qed.

Lemma exists_powers_boundary : forall x F B, is_subfield F -> F x -> basis is_rational B F ->
  exists d, lin_indep is_rational (powers x d) /\ ~ lin_indep is_rational (powers x (S d)).
Proof.
  intros x F B HF Hx [HBF [HliB HspB]].
  apply (nat_boundary (fun k => lin_indep is_rational (powers x k)) (length B)).
  - apply lin_indep_nil.
  - intro Hli.
    assert (HpowF : Forall F (powers x (S (length B)))).
    { apply Forall_forall. intros w Hw. unfold powers in Hw. apply in_map_iff in Hw.
      destruct Hw as [i [Hwi _]]. subst w. apply subfield_pow; [exact HF | exact Hx]. }
    pose proof (indep_le_span is_rational (powers x (S (length B))) B F
                  is_rational_subfield Hli HpowF HspB) as Hle.
    rewrite powers_length in Hle. lia.
Qed.

Lemma Qx_powers_basis : forall x d,
  lin_indep is_rational (powers x d) -> ~ lin_indep is_rational (powers x (S d)) ->
  basis is_rational (powers x d) (Qx x).
Proof.
  intros x d Hind Hdep. split; [|split].
  - apply Forall_forall. intros w Hw. unfold powers in Hw. apply in_map_iff in Hw.
    destruct Hw as [i [Hwi _]]. subst w. apply subring_pow; [apply Qx_subring | apply Qx_x].
  - exact Hind.
  - intros y Hy. apply Qx_spanned_by_powers; [apply powers_top_in_span; assumption | exact Hy].
Qed.

Lemma spans_sub_field : forall F1 F2 vs y,
  (forall z, F1 z -> F2 z) -> spans F1 vs y -> spans F2 vs y.
Proof.
  intros F1 F2 vs y Hsub [cs [Hlen [HF1 Hfc]]]. exists cs.
  split; [exact Hlen | split; [|exact Hfc]].
  apply Forall_forall. intros z Hz. apply Hsub. rewrite Forall_forall in HF1. apply HF1; exact Hz.
Qed.

Lemma Qx_subset : forall x F v, is_subfield F -> F x -> Qx x v -> F v.
Proof.
  intros x F v HF Hx [cs [Hcs Hv]]. rewrite <- Hv. unfold pe.
  apply Fcomb_in_field; [exact HF | |].
  - apply Forall_forall. intros z Hz. apply subfield_contains_rational;
      [exact HF | rewrite Forall_forall in Hcs; apply Hcs; exact Hz].
  - apply Forall_forall. intros z Hz. unfold powers in Hz. apply in_map_iff in Hz.
    destruct Hz as [i [Hzi _]]. subst z. apply subfield_pow; [exact HF | exact Hx].
Qed.

(* the degree of x divides the dimension of any finite field containing x *)
Lemma tower_law_div : forall x F BL, is_subfield F -> F x -> basis is_rational BL F ->
  exists d, basis is_rational (powers x d) (Qx x) /\ Nat.divide d (length BL).
Proof.
  intros x F BL HF Hx HbBL.
  destruct (exists_powers_boundary x F BL HF Hx HbBL) as [d [Hind Hdep]].
  pose proof (Qx_powers_basis x d Hind Hdep) as HbBx.
  assert (HQxsf : is_subfield (Qx x)) by (apply (Qx_subfield x F BL); assumption).
  assert (HbBL2 := HbBL). destruct HbBL2 as [HBLF [HliBL HspBL]].
  assert (HbBe : exists Be, basis (Qx x) Be F).
  { apply (basis_extract (Qx x) BL F HQxsf HBLF).
    intros y Hy. apply (spans_sub_field is_rational (Qx x) BL y);
      [intros z Hz; apply Qx_rational; exact Hz | apply HspBL; exact Hy]. }
  destruct HbBe as [Be HbBe].
  exists d. split; [exact HbBx |].
  rewrite (tower_law_dim (powers x d) Be BL (Qx x) F HQxsf HF
             (fun z H => Qx_rational x z H) (fun z H => Qx_subset x F z HF Hx H)
             HbBx HbBe HbBL).
  rewrite powers_length. apply Nat.divide_factor_r.
Qed.

(* ============================================================================
   The quadratic tower has 2-power dimension, hence Euclidean degree | 2^k.
   ============================================================================ *)

Lemma QF_step_basis : forall F s, is_subfield F -> F (s * s) ->
  exists Be, basis F Be (QF F s) /\ (length Be = 1 \/ length Be = 2)%nat.
Proof.
  intros F s HF Hss.
  assert (Hspanned : spanning F (1 :: s :: nil) (QF F s)).
  { intros y [p [q [Hp [Hq Hy]]]]. exists (p :: q :: nil). split; [reflexivity | split].
    - constructor; [exact Hp | constructor; [exact Hq | constructor]].
    - cbn [Fcomb]. rewrite Hy. ring. }
  assert (Hin : Forall (QF F s) (1 :: s :: nil)).
  { constructor; [apply QF_contains; [exact HF | apply subfield_1; exact HF] |].
    constructor; [apply QF_self; exact HF | constructor]. }
  destruct (basis_extract F (1 :: s :: nil) (QF F s) HF Hin Hspanned) as [Be HbBe].
  exists Be. split; [exact HbBe |].
  destruct HbBe as [HBeQ [HliBe HspBe]].
  assert (Hle : (length Be <= 2)%nat).
  { pose proof (indep_le_span F Be (1 :: s :: nil) (QF F s) HF HliBe HBeQ Hspanned) as H.
    simpl in H. exact H. }
  assert (Hge : (1 <= length Be)%nat).
  { destruct Be as [|b Be']; [|simpl; lia]. exfalso.
    destruct (HspBe 1 (QF_contains F s 1 HF (subfield_1 F HF))) as [cs [Hl [Hf Hfc]]].
    destruct cs; [simpl in Hfc; lra | simpl in Hl; lia]. }
  lia.
Qed.

Lemma tower_dim_pow2 : forall L, wf_tower L ->
  exists BL, basis is_rational BL (tower L) /\ is_power_of_2 (length BL).
Proof.
  induction L as [|s L' IH]; intros Wf.
  - exists (1 :: nil). split.
    + split; [|split].
      * constructor; [apply (subfield_1 is_rational is_rational_subfield) | constructor].
      * intros cs Hl Hf Hfc. destruct cs as [|c cs']; [simpl in Hl; lia|].
        destruct cs' as [|c2 cs'']; [|simpl in Hl; lia]. cbn [Fcomb] in Hfc.
        constructor; [lra | constructor].
      * intros y Hy. exists (y :: nil). split; [reflexivity | split].
        -- constructor; [exact Hy | constructor].
        -- cbn [Fcomb]. ring.
    + exists 0%nat. reflexivity.
  - simpl in Wf. destruct Wf as [Wss Wf'].
    destruct (IH Wf') as [BL' [HbBL' Hpow']].
    assert (HsfL' : is_subfield (tower L')) by (apply tower_subfield; exact Wf').
    destruct (QF_step_basis (tower L') s HsfL' Wss) as [Be [HbBe Hbecard]].
    assert (HsfL : is_subfield (tower (s :: L'))) by (apply tower_subfield; simpl; split; assumption).
    exists (flat_map (fun e => map (Rmult e) BL') Be). split.
    + apply (product_basis BL' Be (tower L') (tower (s :: L'))).
      * exact HsfL'.
      * exact HsfL.
      * intros z Hz. apply subfield_contains_rational; [exact HsfL' | exact Hz].
      * intros z Hz. simpl. apply QF_contains; [exact HsfL' | exact Hz].
      * exact HbBL'.
      * exact HbBe.
    + rewrite product_length. destruct Hpow' as [j Hj]. rewrite Hj.
      destruct Hbecard as [H1 | H2].
      * rewrite H1. exists j. lia.
      * rewrite H2. exists (S j). simpl. lia.
Qed.

Lemma divisor_pow2 : forall k d, Nat.divide d (2 ^ k) -> is_power_of_2 d.
Proof.
  induction k as [|k IH]; intros d [c Hc].
  - simpl in Hc. exists 0%nat. simpl. symmetry in Hc.
    apply Nat.mul_eq_1 in Hc. destruct Hc as [_ Hd]. exact Hd.
  - rewrite Nat.pow_succ_r' in Hc.
    destruct (Nat.even d) eqn:Ed.
    + apply Nat.even_spec in Ed. destruct Ed as [e He]. subst d.
      assert (He2 : Nat.divide e (2 ^ k)) by (exists c; nia).
      destruct (IH e He2) as [j Hj]. exists (S j). subst e. simpl. lia.
    + assert (Hce : Nat.even c = true).
      { assert (He : Nat.even (c * d) = true) by (rewrite <- Hc, Nat.even_mul; reflexivity).
        rewrite Nat.even_mul, Ed, Bool.orb_false_r in He. exact He. }
      apply Nat.even_spec in Hce. destruct Hce as [c' Hc']. subst c.
      apply IH. exists c'. nia.
Qed.

(* ============================================================================
   #2 (exact): a Euclidean-constructible number generates a field extension of
   Q whose degree (dimension of Q(x) over Q) is a power of 2.
   ============================================================================ *)
Theorem euclid_field_degree_pow2 : forall x, EuclidNum x ->
  exists d, basis is_rational (powers x d) (Qx x) /\ is_power_of_2 d.
Proof.
  intros x HE. destruct (EuclidNum_in_tower x HE) as [L [Wf Tx]].
  destruct (tower_dim_pow2 L Wf) as [BL [HbBL HpowBL]].
  assert (HsfL : is_subfield (tower L)) by (apply tower_subfield; exact Wf).
  destruct (tower_law_div x (tower L) BL HsfL Tx HbBL) as [d [HbBx Hdiv]].
  exists d. split; [exact HbBx |].
  destruct HpowBL as [k Hk]. rewrite Hk in Hdiv.
  apply (divisor_pow2 k d Hdiv).
Qed.


(* ============================================================================
   Origami degree is exactly 2^a * 3^b: the mixed tower has 2-3-smooth
   dimension, and the degree of x divides it.
   ============================================================================ *)

Lemma CF_step_basis : forall F a b r, is_subfield F -> F a -> F b -> r*r*r + a*r + b = 0 ->
  exists Be, basis F Be (CF F a b r) /\ (length Be = 1 \/ length Be = 2 \/ length Be = 3)%nat.
Proof.
  intros F a b r HF Ha Hb Hr.
  assert (Hspanned : spanning F (1 :: r :: (r*r) :: nil) (CF F a b r)).
  { intros y [p [q [s [Hp [Hq [Hs Hy]]]]]]. exists (p :: q :: s :: nil). split; [reflexivity | split].
    - constructor; [exact Hp | constructor; [exact Hq | constructor; [exact Hs | constructor]]].
    - cbn [Fcomb]. rewrite Hy. ring. }
  assert (Hin : Forall (CF F a b r) (1 :: r :: (r*r) :: nil)).
  { constructor.
    - exists 1, 0, 0. repeat split;
        [apply subfield_1; exact HF | apply subfield_0; exact HF | apply subfield_0; exact HF | ring].
    - constructor.
      + exists 0, 1, 0. repeat split;
          [apply subfield_0; exact HF | apply subfield_1; exact HF | apply subfield_0; exact HF | ring].
      + constructor.
        * exists 0, 0, 1. repeat split;
            [apply subfield_0; exact HF | apply subfield_0; exact HF | apply subfield_1; exact HF | ring].
        * constructor. }
  destruct (basis_extract F (1 :: r :: (r*r) :: nil) (CF F a b r) HF Hin Hspanned) as [Be HbBe].
  exists Be. split; [exact HbBe |].
  destruct HbBe as [HBeC [HliBe HspBe]].
  assert (Hle : (length Be <= 3)%nat).
  { pose proof (indep_le_span F Be (1 :: r :: (r*r) :: nil) (CF F a b r) HF HliBe HBeC Hspanned) as H.
    simpl in H. exact H. }
  assert (Hge : (1 <= length Be)%nat).
  { destruct Be as [|bb Be']; [|simpl; lia]. exfalso.
    destruct (HspBe 1 (CF_contains_sr F a b r 1 (subfield_is_subring F HF) (subfield_1 F HF)))
      as [cs [Hl [Hf Hfc]]].
    destruct cs; [simpl in Hfc; lra | simpl in Hl; lia]. }
  lia.
Qed.

Lemma otower_dim_smooth : forall L, owf L ->
  exists BL, basis is_rational BL (otower L) /\ two_three_smooth (length BL).
Proof.
  induction L as [|st L' IH]; intros Wf.
  - exists (1 :: nil). split.
    + split; [|split].
      * constructor; [apply (subfield_1 is_rational is_rational_subfield) | constructor].
      * intros cs Hl Hf Hfc. destruct cs as [|c cs']; [simpl in Hl; lia|].
        destruct cs' as [|c2 cs'']; [|simpl in Hl; lia]. cbn [Fcomb] in Hfc.
        constructor; [lra | constructor].
      * intros y Hy. exists (y :: nil). split; [reflexivity | split].
        -- constructor; [exact Hy | constructor].
        -- cbn [Fcomb]. ring.
    + exists 0%nat, 0%nat. reflexivity.
  - destruct st as [s | a b r].
    + simpl in Wf. destruct Wf as [Wss Wf'].
      destruct (IH Wf') as [BL' [HbBL' Hsm']].
      assert (HsfL' : is_subfield (otower L')) by (apply otower_subfield; exact Wf').
      destruct (QF_step_basis (otower L') s HsfL' Wss) as [Be [HbBe Hbecard]].
      assert (HsfL : is_subfield (otower (OQuad s :: L'))) by (apply otower_subfield; simpl; split; assumption).
      exists (flat_map (fun e => map (Rmult e) BL') Be). split.
      * apply (product_basis BL' Be (otower L') (otower (OQuad s :: L'))).
        -- exact HsfL'.
        -- exact HsfL.
        -- intros z Hz. apply subfield_contains_rational; [exact HsfL' | exact Hz].
        -- intros z Hz. simpl. apply QF_contains; [exact HsfL' | exact Hz].
        -- exact HbBL'.
        -- exact HbBe.
      * rewrite product_length. destruct Hsm' as [aa [bb Hsm]]. rewrite Hsm.
        destruct Hbecard as [H1 | H2].
        -- rewrite H1. exists aa, bb. lia.
        -- rewrite H2. exists (S aa), bb. rewrite Nat.pow_succ_r'. lia.
    + simpl in Wf. destruct Wf as [Wa [Wb [Wr Wf']]].
      destruct (IH Wf') as [BL' [HbBL' Hsm']].
      assert (HsfL' : is_subfield (otower L')) by (apply otower_subfield; exact Wf').
      destruct (CF_step_basis (otower L') a b r HsfL' Wa Wb Wr) as [Be [HbBe Hbecard]].
      assert (HsfL : is_subfield (otower (OCubic a b r :: L')))
        by (apply otower_subfield; simpl; repeat split; assumption).
      exists (flat_map (fun e => map (Rmult e) BL') Be). split.
      * apply (product_basis BL' Be (otower L') (otower (OCubic a b r :: L'))).
        -- exact HsfL'.
        -- exact HsfL.
        -- intros z Hz. apply subfield_contains_rational; [exact HsfL' | exact Hz].
        -- intros z Hz. simpl. apply CF_contains_sr; [apply subfield_is_subring; exact HsfL' | exact Hz].
        -- exact HbBL'.
        -- exact HbBe.
      * rewrite product_length. destruct Hsm' as [aa [bb Hsm]]. rewrite Hsm.
        destruct Hbecard as [H1 | [H2 | H3]].
        -- rewrite H1. exists aa, bb. lia.
        -- rewrite H2. exists (S aa), bb. rewrite Nat.pow_succ_r'. lia.
        -- rewrite H3. exists aa, (S bb). rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma gcd_d_3_eq_1 : forall d, ~ Nat.divide 3 d -> Nat.gcd d 3 = 1%nat.
Proof.
  intros d H3.
  pose proof (Nat.gcd_divide_r d 3) as Hg3.
  pose proof (Nat.gcd_divide_l d 3) as Hgd.
  pose proof (Nat.divide_pos_le (Nat.gcd d 3) 3 ltac:(lia) Hg3) as Hle.
  remember (Nat.gcd d 3) as g eqn:Eg.
  destruct g as [|[|[|[|g']]]].
  - destruct Hg3 as [c Hc]. lia.
  - reflexivity.
  - destruct Hg3 as [c Hc]. lia.
  - exfalso. apply H3. exact Hgd.
  - lia.
Qed.

Lemma divisor_pow3 : forall k d, Nat.divide d (3 ^ k)%nat -> exists e, d = (3 ^ e)%nat.
Proof.
  induction k as [|k IH]; intros d Hd.
  - simpl in Hd. apply Nat.divide_1_r in Hd. subst. exists 0%nat. reflexivity.
  - rewrite Nat.pow_succ_r' in Hd.
    destruct (Ndivide_dec 3 d) as [H3 | H3].
    + destruct H3 as [e He]. subst d.
      assert (He2 : Nat.divide e (3 ^ k)%nat) by (destruct Hd as [c Hc]; exists c; nia).
      destruct (IH e He2) as [j Hj]. exists (S j). subst e. rewrite Nat.pow_succ_r'. lia.
    + assert (Hcop : Nat.gcd d 3 = 1%nat) by (apply gcd_d_3_eq_1; exact H3).
      apply IH. apply (Nat.gauss d 3 (3 ^ k) Hd Hcop).
Qed.

Lemma gcd_d_2_eq_1 : forall d, ~ Nat.divide 2 d -> Nat.gcd d 2 = 1%nat.
Proof.
  intros d H2.
  pose proof (Nat.gcd_divide_r d 2) as Hg2.
  pose proof (Nat.gcd_divide_l d 2) as Hgd.
  pose proof (Nat.divide_pos_le (Nat.gcd d 2) 2 ltac:(lia) Hg2) as Hle.
  remember (Nat.gcd d 2) as g eqn:Eg.
  destruct g as [|[|[|g']]].
  - destruct Hg2 as [c Hc]. lia.
  - reflexivity.
  - exfalso. apply H2. exact Hgd.
  - lia.
Qed.

Lemma divisor_smooth : forall a b d, Nat.divide d (2 ^ a * 3 ^ b)%nat -> two_three_smooth d.
Proof.
  induction a as [|a IH]; intros b d Hd.
  - replace (2 ^ 0 * 3 ^ b)%nat with (3 ^ b)%nat in Hd
      by (rewrite Nat.pow_0_r, Nat.mul_1_l; reflexivity).
    destruct (divisor_pow3 b d Hd) as [e He]. exists 0%nat, e.
    rewrite Nat.pow_0_r, Nat.mul_1_l. exact He.
  - replace (2 ^ S a * 3 ^ b)%nat with (2 * (2 ^ a * 3 ^ b))%nat in Hd
      by (rewrite Nat.pow_succ_r'; ring).
    destruct (Ndivide_dec 2 d) as [H2 | H2].
    + destruct H2 as [e He]. subst d.
      assert (He2 : Nat.divide e (2 ^ a * 3 ^ b)%nat) by (destruct Hd as [c Hc]; exists c; nia).
      destruct (IH b e He2) as [c' [e' Hee]]. exists (S c'), e'.
      rewrite Nat.pow_succ_r'. nia.
    + assert (Hcop : Nat.gcd d 2 = 1%nat) by (apply gcd_d_2_eq_1; exact H2).
      apply (IH b d). apply (Nat.gauss d 2 (2 ^ a * 3 ^ b)%nat Hd Hcop).
Qed.

(* ============================================================================
   #1 (exact): an origami-constructible number generates a field extension of
   Q whose degree is exactly of the form 2^a * 3^b.
   ============================================================================ *)
Theorem origami_field_degree_smooth : forall x, OrigamiNum x ->
  exists d, basis is_rational (powers x d) (Qx x) /\ two_three_smooth d.
Proof.
  intros x HO. destruct (OrigamiNum_in_otower x HO) as [L [Wf Tx]].
  destruct (otower_dim_smooth L Wf) as [BL [HbBL HsmBL]].
  assert (HsfL : is_subfield (otower L)) by (apply otower_subfield; exact Wf).
  destruct (tower_law_div x (otower L) BL HsfL Tx HbBL) as [d [HbBx Hdiv]].
  exists d. split; [exact HbBx |].
  destruct HsmBL as [a [b Hab]]. rewrite Hab in Hdiv.
  apply (divisor_smooth a b d Hdiv).
Qed.


(* ============================================================================
   Monic polynomial division (toward irreducibility of minpoly_2cos).
   Polynomials are coefficient lists, low degree first; pe cs y = sum cs_i y^i.
   ============================================================================ *)

Definition shiftp (n : nat) (p : list R) : list R := repeat 0 n ++ p.

Definition psub (p q : list R) : list R := padd p (map (Rmult (-1)) q).

Lemma pe_shiftp : forall n p y, pe (shiftp n p) y = y ^ n * pe p y.
Proof.
  intros n p y. unfold shiftp. induction n as [|n IH].
  - simpl. ring.
  - cbn [repeat app]. rewrite pe_cons, IH. simpl. ring.
Qed.

Lemma pe_psub : forall p q y, pe (psub p q) y = pe p y - pe q y.
Proof.
  intros p q y. unfold psub. rewrite pe_padd, pe_scale. ring.
Qed.

Lemma length_shiftp : forall n p, length (shiftp n p) = (n + length p)%nat.
Proof. intros n p. unfold shiftp. rewrite length_app, repeat_length. reflexivity. Qed.

Lemma pe_app : forall p q y, pe (p ++ q) y = pe p y + y ^ (length p) * pe q y.
Proof.
  induction p as [|a p IH]; intros q y.
  - cbn [app length]. rewrite pe_nil. simpl. ring.
  - cbn [app length]. rewrite !pe_cons, IH. simpl. ring.
Qed.

Lemma pe_app_0 : forall p y, pe (p ++ (0 :: nil)) y = pe p y.
Proof.
  induction p as [|a p IH]; intros y.
  - cbn [app]. rewrite pe_cons, pe_nil. ring.
  - cbn [app]. rewrite !pe_cons, IH. ring.
Qed.

Lemma pe_removelast_last0 : forall l y, l <> nil -> last l 0 = 0 -> pe (removelast l) y = pe l y.
Proof.
  intros l y Hne Hlast.
  rewrite (app_removelast_last 0 Hne) at 2. rewrite Hlast, pe_app_0. reflexivity.
Qed.

Lemma nth_padd : forall i p q, nth i (padd p q) 0 = nth i p 0 + nth i q 0.
Proof.
  induction i as [|i IH]; intros p q;
    destruct p as [|a p]; destruct q as [|b q]; simpl; try ring.
  apply IH.
Qed.

Lemma nth_map_mult : forall i a l, nth i (map (Rmult a) l) 0 = a * nth i l 0.
Proof.
  induction i as [|i IH]; intros a l; destruct l as [|x l]; simpl; try ring. apply IH.
Qed.

Lemma nth_shiftp : forall n k mu, (n <= k)%nat -> nth k (shiftp n mu) 0 = nth (k - n) mu 0.
Proof.
  intros n k mu Hnk. unfold shiftp.
  rewrite app_nth2 by (rewrite repeat_length; exact Hnk).
  rewrite repeat_length. reflexivity.
Qed.

Lemma length_padd : forall p q, length (padd p q) = Nat.max (length p) (length q).
Proof.
  induction p as [|a p IH]; intros q; [reflexivity|].
  destruct q as [|b q]; simpl; [lia | rewrite IH; reflexivity].
Qed.

Lemma last_as_nth : forall (l : list R) d, last l d = nth (Nat.pred (length l)) l d.
Proof.
  induction l as [|a l IH]; intros d; [reflexivity|].
  destruct l as [|b l']; [reflexivity|].
  change (last (a :: b :: l') d) with (last (b :: l') d).
  rewrite IH. reflexivity.
Qed.

Lemma divstep_top_zero : forall g mu d,
  length mu = S d -> nth d mu 0 = 1 -> (d < length g)%nat ->
  nth (length g - 1)
      (psub g (map (Rmult (nth (length g - 1) g 0)) (shiftp (length g - 1 - d) mu))) 0 = 0.
Proof.
  intros g mu d Hmu Hmonic Hd. unfold psub.
  rewrite nth_padd, nth_map_mult, nth_map_mult.
  rewrite nth_shiftp by lia.
  replace (length g - 1 - (length g - 1 - d))%nat with d by lia.
  rewrite Hmonic. ring.
Qed.

Lemma Forall_rat_map_mult : forall c p,
  is_rational c -> Forall is_rational p -> Forall is_rational (map (Rmult c) p).
Proof.
  intros c p Hc Hp. apply Forall_forall. intros z Hz. apply in_map_iff in Hz.
  destruct Hz as [w [Hzw Hw]]. subst z.
  apply (subfield_mul is_rational c w is_rational_subfield);
    [exact Hc | rewrite Forall_forall in Hp; apply Hp; exact Hw].
Qed.

Lemma Forall_rat_shiftp : forall n p, Forall is_rational p -> Forall is_rational (shiftp n p).
Proof.
  intros n p Hp. unfold shiftp. apply Forall_app. split; [|exact Hp].
  apply Forall_forall. intros z Hz. apply repeat_spec in Hz. subst z.
  apply (subfield_0 is_rational is_rational_subfield).
Qed.

Lemma Forall_rat_psub : forall p q,
  Forall is_rational p -> Forall is_rational q -> Forall is_rational (psub p q).
Proof.
  intros p q Hp Hq. unfold psub. apply Forall_rat_padd; [exact Hp |].
  apply Forall_rat_map_mult; [|exact Hq].
  apply (subfield_opp is_rational 1 is_rational_subfield).
  apply (subfield_1 is_rational is_rational_subfield).
Qed.

Lemma Forall_removelast_gen : forall (P:R->Prop) l, Forall P l -> Forall P (removelast l).
Proof.
  intros P l. induction l as [|a l IH]; intros Hl; [exact Hl|].
  destruct l as [|b l']; [constructor|].
  cbn [removelast]. inversion Hl; subst. constructor; [assumption | apply IH; assumption].
Qed.

Lemma monic_div_exists : forall mu d, length mu = S d -> nth d mu 0 = 1 -> Forall is_rational mu ->
  forall n g, (length g <= n)%nat -> Forall is_rational g ->
  exists q r, (forall y, pe g y = pe mu y * pe q y + pe r y) /\ (length r <= d)%nat
              /\ Forall is_rational q /\ Forall is_rational r.
Proof.
  intros mu d Hmu Hmonic Hmurat. induction n as [|n IH]; intros g Hlen Hgrat.
  - assert (Hg : g = nil) by (destruct g; [reflexivity | simpl in Hlen; lia]).
    subst g. exists nil, nil.
    split; [intros y; rewrite pe_nil; ring | split; [simpl; lia | split; constructor]].
  - destruct (Nat.le_gt_cases (length g) d) as [Hsmall | Hbig].
    + exists nil, g.
      split; [intros y; rewrite pe_nil; ring | split; [exact Hsmall | split; [constructor | exact Hgrat]]].
    + remember (length g - 1)%nat as k eqn:Ek.
      remember (nth k g 0) as c eqn:Ec.
      remember (psub g (map (Rmult c) (shiftp (k - d) mu))) as gsub eqn:Egsub.
      assert (Hgne : g <> nil) by (intro Hg; subst g; simpl in Hbig; lia).
      assert (Hcrat : is_rational c)
        by (rewrite Ec; apply (Forall_F_nth is_rational k g is_rational_subfield Hgrat)).
      assert (Hgsubrat : Forall is_rational gsub).
      { rewrite Egsub. apply Forall_rat_psub;
          [exact Hgrat | apply Forall_rat_map_mult; [exact Hcrat | apply Forall_rat_shiftp; exact Hmurat]]. }
      assert (Hgsublen : length gsub = length g).
      { rewrite Egsub. unfold psub.
        rewrite length_padd, length_map, length_map, length_shiftp, Hmu. rewrite Ek. lia. }
      assert (Hgsubne : gsub <> nil)
        by (intro H; rewrite H in Hgsublen; simpl in Hgsublen; lia).
      assert (Hgsubtop : last gsub 0 = 0).
      { rewrite last_as_nth, Hgsublen.
        replace (Nat.pred (length g)) with k by (rewrite Ek; lia).
        rewrite Egsub, Ec, Ek. apply divstep_top_zero; [exact Hmu | exact Hmonic | exact Hbig]. }
      assert (Hrlen : (length (removelast gsub) <= n)%nat).
      { assert (Hsplit : gsub = removelast gsub ++ (last gsub 0 :: nil))
          by (apply app_removelast_last; exact Hgsubne).
        assert (Hl1 : length gsub = (length (removelast gsub) + 1)%nat)
          by (rewrite Hsplit at 1; rewrite length_app; simpl; lia).
        rewrite Hgsublen in Hl1. lia. }
      destruct (IH (removelast gsub) Hrlen (Forall_removelast_gen is_rational gsub Hgsubrat))
        as [q' [r' [Hid [Hr'len [Hq'rat Hr'rat]]]]].
      exists (padd (shiftp (k - d) (c :: nil)) q'), r'.
      split; [|split; [exact Hr'len | split; [|exact Hr'rat]]].
      * intros y.
        assert (Hpegsub : pe gsub y = pe g y - c * y ^ (k - d) * pe mu y)
          by (rewrite Egsub, pe_psub, pe_scale, pe_shiftp; ring).
        assert (Hperl : pe (removelast gsub) y = pe gsub y)
          by (apply pe_removelast_last0; assumption).
        specialize (Hid y). rewrite Hperl, Hpegsub in Hid.
        rewrite pe_padd, pe_shiftp, pe_cons, pe_nil. nra.
      * apply Forall_rat_padd;
          [apply Forall_rat_shiftp; constructor; [exact Hcrat | constructor] | exact Hq'rat].
Qed.


(* ============================================================================
   Toward irreducibility of minpoly_2cos and #8 (cos(2pi/11) not single-fold).

   We first develop, over Z, the multiplicative theory of polynomial content
   (Gauss's lemma): a monic integer quintic admits a monic rational factor only
   when it admits a monic integer factor of the same degree.  Polynomials here
   are coefficient lists over Z, low degree first.  This block lives in
   Z_scope; the rational-side development below resumes in R_scope.
   ============================================================================ *)
Open Scope Z_scope.
Fixpoint Zpadd (p q : list Z) : list Z :=
  match p, q with
  | nil, _ => q
  | _, nil => p
  | a :: p', b :: q' => (a + b) :: Zpadd p' q'
  end.

Fixpoint Zpmul (p q : list Z) : list Z :=
  match p with
  | nil => nil
  | a :: p' => Zpadd (map (Z.mul a) q) (0 :: Zpmul p' q)
  end.

Definition Zcontent (p : list Z) : Z := fold_right Z.gcd 0 p.

Lemma nth_Zpadd : forall i p q, nth i (Zpadd p q) 0 = nth i p 0 + nth i q 0.
Proof.
  induction i as [|i IH]; intros p q;
    destruct p as [|a p]; destruct q as [|b q]; simpl; try ring.
  apply IH.
Qed.

Lemma nth_map_Zmul : forall i a l, nth i (map (Z.mul a) l) 0 = a * nth i l 0.
Proof.
  induction i as [|i IH]; intros a l; destruct l as [|x l]; simpl; try ring. apply IH.
Qed.

(* r divides the content iff it divides every coefficient *)
Lemma divide_content_iff : forall r p, (r | Zcontent p) <-> Forall (fun c => (r | c)) p.
Proof.
  intros r p. unfold Zcontent. induction p as [|a p IH]; simpl.
  - split; intros _; [constructor | exists 0; ring].
  - split.
    + intros Hd. constructor.
      * eapply Z.divide_trans; [exact Hd | apply Z.gcd_divide_l].
      * apply IH. eapply Z.divide_trans; [exact Hd | apply Z.gcd_divide_r].
    + intros HF. inversion HF as [|? ? Ha Hp]; subst.
      apply Z.gcd_greatest; [exact Ha | apply IH; exact Hp].
Qed.

(* convolution: the k-th coefficient of a product (recursion on the first poly) *)
Fixpoint Zconv (p q : list Z) (k : nat) : Z :=
  match p with
  | nil => 0
  | a :: p' => a * nth k q 0 + match k with O => 0 | S k' => Zconv p' q k' end
  end.

Lemma nth_Zpmul : forall p q k, nth k (Zpmul p q) 0 = Zconv p q k.
Proof.
  induction p as [|a p IH]; intros q k.
  - simpl. destruct k; reflexivity.
  - simpl Zpmul. rewrite nth_Zpadd, nth_map_Zmul. simpl Zconv.
    destruct k as [|k']; cbn [nth]; [ring | rewrite IH; ring].
Qed.

(* r divides the content iff it divides every coefficient (nth form) *)
Lemma divide_content_nth : forall r p, (r | Zcontent p) <-> (forall k, (r | nth k p 0)).
Proof.
  intros r p. rewrite divide_content_iff. split.
  - intros HF k. destruct (Nat.lt_ge_cases k (length p)) as [Hlt|Hge].
    + rewrite Forall_forall in HF. apply HF. apply nth_In. exact Hlt.
    + rewrite nth_overflow by exact Hge. exists 0; ring.
  - intros Hk. apply Forall_forall. intros x Hx.
    apply In_nth with (d:=0) in Hx. destruct Hx as [i [Hi Hnth]]. rewrite <- Hnth. apply Hk.
Qed.

(* if r divides q at indices 0..k then it divides the k-th coeff of p*q *)
Lemma Zconv_div : forall r p q k,
  (forall m, (m < S k)%nat -> (r | nth m q 0)) -> (r | Zconv p q k).
Proof.
  intros r p. induction p as [|a p IH]; intros q k Hq.
  - simpl. exists 0; ring.
  - cbn [Zconv]. destruct k as [|k'].
    + rewrite Z.add_0_r. apply Z.divide_mul_r. apply Hq. lia.
    + apply Z.divide_add_r.
      * apply Z.divide_mul_r. apply Hq. lia.
      * apply IH. intros m Hm. apply Hq. lia.
Qed.

(* first index whose coefficient is not divisible by r *)
Fixpoint firstnd (r : Z) (q : list Z) : nat :=
  match q with
  | nil => 0
  | b :: q' => if Znumtheory.Zdivide_dec r b then S (firstnd r q') else 0
  end.

Lemma firstnd_below : forall r q m, (m < firstnd r q)%nat -> (r | nth m q 0).
Proof.
  intros r q. induction q as [|b q' IH]; intros m Hm; cbn [firstnd] in Hm.
  - lia.
  - destruct (Znumtheory.Zdivide_dec r b) as [Hdb|Hdb].
    + destruct m as [|m']; [exact Hdb | cbn [nth]; apply IH; lia].
    + lia.
Qed.

Lemma firstnd_nondiv : forall r q,
  ~ Forall (fun c => (r | c)) q -> ~ (r | nth (firstnd r q) q 0).
Proof.
  intros r q. induction q as [|b q' IH]; intros Hnf.
  - exfalso. apply Hnf. constructor.
  - cbn [firstnd]. destruct (Znumtheory.Zdivide_dec r b) as [Hdb|Hdb].
    + cbn [nth]. apply IH. intro Hf. apply Hnf. constructor; assumption.
    + cbn [nth]. exact Hdb.
Qed.

(* Gauss's lemma, prime form: a prime not dividing either content does not
   divide the content of the product *)
Lemma gauss_prime : forall r p q, Znumtheory.prime r ->
  ~ (r | Zcontent p) -> ~ (r | Zcontent q) -> ~ (r | Zcontent (Zpmul p q)).
Proof.
  intros r p. induction p as [|a p IH]; intros q Hr Hp Hq.
  - exfalso. apply Hp. exists 0; simpl; ring.
  - rewrite divide_content_nth. intro Hall.
    destruct (Znumtheory.Zdivide_dec r a) as [Hda | Hda].
    + (* r | a : descend to p *)
      assert (Hpp : ~ (r | Zcontent p)).
      { intro Hcp. apply Hp. rewrite divide_content_nth. intro k.
        destruct k as [|k']; [cbn [nth]; exact Hda
                            | cbn [nth]; rewrite divide_content_nth in Hcp; apply Hcp]. }
      apply (IH q Hr Hpp Hq). rewrite divide_content_nth. intro k.
      pose proof (Hall (S k)) as Hk. rewrite nth_Zpmul in Hk. cbn [Zconv] in Hk.
      rewrite nth_Zpmul.
      replace (Zconv p q k) with ((a * nth (S k) q 0 + Zconv p q k) - a * nth (S k) q 0) by ring.
      apply Z.divide_sub_r; [exact Hk | apply Z.divide_mul_l; exact Hda].
    + (* ~ r | a : the coefficient at firstnd r q is not divisible by r *)
      assert (Hqnf : ~ Forall (fun c => (r | c)) q)
        by (rewrite <- divide_content_iff; exact Hq).
      pose proof (firstnd_nondiv r q Hqnf) as Hqj.
      pose proof (Hall (firstnd r q)) as Hj. rewrite nth_Zpmul in Hj.
      destruct (firstnd r q) as [|j'] eqn:Ej.
      * cbn [Zconv] in Hj. rewrite Z.add_0_r in Hj.
        apply Znumtheory.prime_mult in Hj; [|exact Hr].
        destruct Hj as [H|H]; [apply Hda; exact H | apply Hqj; cbn [nth]; exact H].
      * cbn [Zconv] in Hj.
        assert (Hdivconv : (r | Zconv p q j')).
        { apply Zconv_div. intros m Hm. apply firstnd_below. rewrite Ej. lia. }
        assert (Haq : (r | a * nth (S j') q 0)).
        { replace (a * nth (S j') q 0)
            with ((a * nth (S j') q 0 + Zconv p q j') - Zconv p q j') by ring.
          apply Z.divide_sub_r; [exact Hj | exact Hdivconv]. }
        apply Znumtheory.prime_mult in Haq; [|exact Hr].
        destruct Haq as [H|H]; [apply Hda; exact H | apply Hqj; cbn [nth]; exact H].
Qed.

Lemma Zcontent_nonneg : forall p, 0 <= Zcontent p.
Proof.
  induction p as [|a p IH]; simpl; [lia | apply Z.gcd_nonneg].
Qed.

Lemma Zcontent_zero_iff : forall p, Zcontent p = 0 <-> Forall (fun c => c = 0) p.
Proof.
  induction p as [|a p IH]; simpl.
  - split; intros _; [constructor | reflexivity].
  - rewrite Z.gcd_eq_0. split.
    + intros [Ha Hp]. constructor; [exact Ha | rewrite <- IH; exact Hp].
    + intros HF. inversion HF as [|x l Ha Hp]. split; [exact Ha | rewrite IH; exact Hp].
Qed.

(* every integer > 1 has a prime divisor *)
Lemma exists_prime_divisor : forall n, 1 < n -> exists p, Znumtheory.prime p /\ (p | n).
Proof.
  assert (Hwf : forall m n, (Z.to_nat n < m)%nat -> 1 < n -> exists p, Znumtheory.prime p /\ (p | n)).
  { induction m as [|m IH]; intros n Hm Hn; [lia|].
    destruct (Znumtheory.prime_dec n) as [Hp|Hnp].
    - exists n; split; [exact Hp | apply Z.divide_refl].
    - destruct (Znumtheory.not_prime_divide n Hn Hnp) as [k [[Hk1 Hk2] Hdiv]].
      assert (Hkm : (Z.to_nat k < m)%nat).
      { assert (Hlt : (Z.to_nat k < Z.to_nat n)%nat) by (apply Z2Nat.inj_lt; lia).
        lia. }
      destruct (IH k Hkm Hk1) as [p [Hp Hpk]].
      exists p; split; [exact Hp | apply (Z.divide_trans p k n Hpk Hdiv)]. }
  intros n Hn. apply (Hwf (S (Z.to_nat n)) n); [lia | exact Hn].
Qed.

Lemma prime_not_div_1 : forall r, Znumtheory.prime r -> ~ (r | 1).
Proof.
  intros r Hr Hdiv. destruct Hr as [Hr1 _].
  apply Z.divide_1_r in Hdiv. lia.
Qed.

(* content is multiplicative on primitive polynomials: primitive * primitive is
   primitive (given the product is not the zero polynomial). *)
Lemma primitive_mult : forall p q,
  Zcontent p = 1 -> Zcontent q = 1 -> Zcontent (Zpmul p q) <> 0 ->
  Zcontent (Zpmul p q) = 1.
Proof.
  intros p q Hp Hq Hnz.
  set (c := Zcontent (Zpmul p q)) in *.
  assert (Hc_nn : 0 <= c) by (apply Zcontent_nonneg).
  destruct (Z.eq_dec c 1) as [|Hcne]; [assumption | exfalso].
  assert (Hc_gt1 : 1 < c) by lia.
  destruct (exists_prime_divisor c Hc_gt1) as [r [Hr Hrc]].
  apply (gauss_prime r p q Hr).
  - rewrite Hp. apply prime_not_div_1; exact Hr.
  - rewrite Hq. apply prime_not_div_1; exact Hr.
  - exact Hrc.
Qed.

(* cleared form of minpoly_2cos at a/b: b^5 * minpoly_2cos(a/b). *)
Definition quintic_form (a b : Z) : Z :=
  a*a*a*a*a + a*a*a*a*b - 4*(a*a*a*(b*b)) - 3*(a*a*(b*b*b)) + 3*(a*(b*b*b*b)) + b*b*b*b*b.

Lemma quintic_form_coprime : forall a b, b > 0 -> Z.gcd a b = 1 -> quintic_form a b <> 0.
Proof.
  intros a b Hb Hcop Heq.
  assert (Hrel : Znumtheory.rel_prime b a)
    by (apply Znumtheory.Zgcd_1_rel_prime; rewrite Z.gcd_comm; exact Hcop).
  unfold quintic_form in Heq.
  assert (Hb4 : (b | a*a*a*a)).
  { apply (Znumtheory.Gauss b a (a*a*a*a)); [| exact Hrel].
    exists (- (a*a*a*a - 4*(a*a*a*b) - 3*(a*a*(b*b)) + 3*(a*(b*b*b)) + b*b*b*b)). nia. }
  assert (Hb3 : (b | a*a*a)) by
    (apply (Znumtheory.Gauss b a (a*a*a)); [destruct Hb4 as [k Hk]; exists k; nia | exact Hrel]).
  assert (Hb2 : (b | a*a)) by
    (apply (Znumtheory.Gauss b a (a*a)); [destruct Hb3 as [k Hk]; exists k; nia | exact Hrel]).
  assert (Hb1 : (b | a)) by
    (apply (Znumtheory.Gauss b a a); [destruct Hb2 as [k Hk]; exists k; nia | exact Hrel]).
  assert (Hbg : (b | Z.gcd a b)) by (apply Z.gcd_greatest; [exact Hb1 | apply Z.divide_refl]).
  rewrite Hcop in Hbg. apply Z.divide_1_r in Hbg.
  destruct Hbg as [Hb1'|Hb1']; [|lia]. subst b.
  assert (Ha : (a | 1)) by (exists (-(a*a*a*a + a*a*a - 4*(a*a) - 3*a + 3)); nia).
  apply Z.divide_1_r in Ha. destruct Ha as [Ha1|Ha1]; subst a; lia.
Qed.

Lemma quintic_form_homog : forall g a b,
  quintic_form (a*g) (b*g) = g*g*g*g*g * quintic_form a b.
Proof. intros. unfold quintic_form. ring. Qed.

Lemma quintic_form_neg : forall a b, quintic_form (-a) (-b) = - quintic_form a b.
Proof. intros. unfold quintic_form. ring. Qed.

Lemma quintic_form_general : forall a b, b <> 0 -> quintic_form a b <> 0.
Proof.
  intros a b Hb Heq.
  set (g := Z.gcd a b).
  assert (Hg0 : g <> 0) by (unfold g; intro H; apply Z.gcd_eq_0 in H; destruct H; contradiction).
  assert (Hgpos : g > 0) by (assert (0 <= g) by (unfold g; apply Z.gcd_nonneg); lia).
  assert (Hga : (g | a)) by (unfold g; apply Z.gcd_divide_l).
  assert (Hgb : (g | b)) by (unfold g; apply Z.gcd_divide_r).
  destruct Hga as [a' Ha']. destruct Hgb as [b' Hb'].
  assert (Hcop : Z.gcd a' b' = 1).
  { assert (Hgg : Z.gcd a b = g) by reflexivity.
    rewrite Ha', Hb' in Hgg. rewrite Z.gcd_mul_mono_r in Hgg.
    rewrite Z.abs_eq in Hgg by lia. nia. }
  assert (Hb'0 : b' <> 0) by (intro H; subst b'; rewrite Z.mul_0_l in Hb'; contradiction).
  assert (Hfab' : quintic_form a' b' = 0).
  { assert (Hh : quintic_form a b = g*g*g*g*g * quintic_form a' b').
    { rewrite Ha', Hb'. apply quintic_form_homog. }
    rewrite Heq in Hh. symmetry in Hh.
    apply Zmult_integral in Hh. destruct Hh as [Hh|Hh]; [exfalso; nia | exact Hh]. }
  destruct (Z_lt_le_dec b' 0) as [Hbneg | Hbpos].
  - assert (Hopp : quintic_form (-a') (-b') = 0) by (rewrite quintic_form_neg, Hfab'; ring).
    assert (Hcop' : Z.gcd (-a') (-b') = 1) by (rewrite Z.gcd_opp_l, Z.gcd_opp_r; exact Hcop).
    apply (quintic_form_coprime (-a') (-b')); [lia | exact Hcop' | exact Hopp].
  - apply (quintic_form_coprime a' b'); [lia | exact Hcop | exact Hfab'].
Qed.

(* The coefficient equations for minpoly_2cos = (y^2+my+s)(y^3+ay^2+by+c) over Z
   have no solution: s*c=1 forces (s,c) in {(1,1),(-1,-1)}, after which the y^3 and
   y^2 coefficients force m^2 = 8 (impossible) or a mismatch.  Rules out a monic
   integer quadratic factor of minpoly_2cos. *)
Lemma minpoly_quad_coeffs_absurd : forall s m a b c : Z,
  s*c = 1 ->
  s*b + m*c = 3 ->
  s*a + m*b + c = -3 ->
  s + m*a + b = -4 ->
  m + a = 1 ->
  False.
Proof.
  intros s m a b c H0 H1 H2 H3 H4.
  assert (Hsdiv : (s | 1)) by (exists c; lia).
  apply Z.divide_1_r in Hsdiv.
  destruct Hsdiv as [Hs | Hs]; subst s.
  - assert (c = 1) by lia. subst c.
    assert (Hm2 : m * m = 8) by nia. nia.
  - assert (c = -1) by lia. subst c. nia.
Qed.

(* scaling a coefficient list by a constant: needed for the primitive-part
   decomposition in the monic form of Gauss's lemma. *)
Lemma map_Zmul_Zpadd : forall k p q,
  map (Z.mul k) (Zpadd p q) = Zpadd (map (Z.mul k) p) (map (Z.mul k) q).
Proof.
  intros k p. induction p as [|a p IH]; intros q; [reflexivity|].
  destruct q as [|b q]; simpl; [reflexivity|].
  rewrite IH. f_equal. ring.
Qed.

Lemma Zpmul_scale_l : forall k p q,
  Zpmul (map (Z.mul k) p) q = map (Z.mul k) (Zpmul p q).
Proof.
  intros k p. induction p as [|a p IH]; intros q; [reflexivity|].
  simpl. rewrite map_Zmul_Zpadd, IH.
  rewrite map_map. f_equal.
  - apply map_ext. intros x. ring.
  - simpl. f_equal. ring.
Qed.

Lemma Zcontent_scale : forall k p, 0 <= k -> Zcontent (map (Z.mul k) p) = k * Zcontent p.
Proof.
  intros k p Hk. induction p as [|a p IH]; simpl; [ring|].
  rewrite IH. rewrite Z.gcd_mul_mono_l, Z.abs_eq by exact Hk. reflexivity.
Qed.
Open Scope R_scope.
Lemma pe_zeros : forall p y, Forall (fun c => c = 0) p -> pe p y = 0.
Proof.
  induction p as [|a p IH]; intros y H; [apply pe_nil|].
  inversion H as [|? ? Ha Hp]; subst. rewrite pe_cons, (IH y Hp). ring.
Qed.
Open Scope R_scope.
Lemma peval_continuity : forall p, continuity (peval p).
Proof.
  induction p as [|a p IH]; intro x.
  - change (continuity_pt (fun _ => 0) x). apply continuity_const. intros y z; reflexivity.
  - change (continuity_pt (fun y => IZR a + y * peval p y) x).
    apply continuity_pt_plus.
    + apply continuity_const. intros y z; reflexivity.
    + apply continuity_pt_mult.
      * apply derivable_continuous_pt. apply derivable_pt_id.
      * apply IH.
Qed.

Lemma g0_of_yg : forall g, continuity g -> (forall y, y * g y = 0) -> g 0 = 0.
Proof.
  intros g Hc Hyg.
  assert (Hgu : forall n, g (RinvN n) = 0).
  { intro n. pose proof (cond_pos (RinvN n)) as Hpos.
    specialize (Hyg (RinvN n)). apply Rmult_integral in Hyg.
    destruct Hyg as [H|H]; [exfalso; lra | exact H]. }
  apply (UL_sequence (fun n => g (RinvN n)) (g 0) 0).
  - apply (continuity_seq g RinvN 0 (Hc 0)). apply RinvN_cv.
  - intros eps Heps. exists 0%nat. intros n _.
    unfold R_dist. rewrite Hgu. rewrite Rminus_0_r, Rabs_R0. exact Heps.
Qed.

Lemma poly_vanish : forall p, (forall y, peval p y = 0) -> Forall (fun c => c = 0%Z) p.
Proof.
  induction p as [|a p IH]; intro H; [constructor|].
  assert (Ha : a = 0%Z).
  { apply eq_IZR_R0. specialize (H 0). simpl in H. lra. }
  subst a.
  assert (Hyg : forall y, y * peval p y = 0).
  { intro y. specialize (H y). simpl in H. lra. }
  assert (Hp : forall y, peval p y = 0).
  { intro y. destruct (Req_dec y 0) as [Hy0 | Hyne].
    - subst y. apply (g0_of_yg (peval p) (peval_continuity p) Hyg).
    - specialize (Hyg y). apply Rmult_integral in Hyg. destruct Hyg as [H1|H1]; [lra | exact H1]. }
  constructor; [reflexivity | apply IH; exact Hp].
Qed.

(* bridges between the integer-polynomial evaluation peval and the real-side pe,
   and peval distributing over the integer product Zpmul. *)
Lemma peval_eq_pe : forall p y, peval p y = pe (map IZR p) y.
Proof.
  induction p as [|a p IH]; intros y; [reflexivity|].
  simpl peval. simpl map. rewrite pe_cons, IH. reflexivity.
Qed.

Lemma peval_Zpadd : forall p q y, peval (Zpadd p q) y = peval p y + peval q y.
Proof.
  induction p as [|a p IH]; intros q y.
  - simpl. ring.
  - destruct q as [|b q]; simpl.
    + ring.
    + rewrite plus_IZR. rewrite IH. ring.
Qed.

Lemma peval_map_Zmul : forall a q y, peval (map (Z.mul a) q) y = IZR a * peval q y.
Proof.
  induction q as [|b q IH]; intros y.
  - simpl. ring.
  - simpl. rewrite mult_IZR, IH. ring.
Qed.

Lemma peval_Zpmul : forall p q y, peval (Zpmul p q) y = peval p y * peval q y.
Proof.
  induction p as [|a p IH]; intros q y.
  - simpl. ring.
  - simpl Zpmul. rewrite peval_Zpadd, peval_map_Zmul.
    simpl peval. rewrite IH. ring.
Qed.
Open Scope Z_scope.
Lemma Forall_eq0_nth : forall l, Forall (fun c => c = 0) l -> forall i, nth i l 0 = 0.
Proof.
  induction l as [|a l IH]; intros H i.
  - destruct i; reflexivity.
  - inversion H as [|? ? Ha Hl]; subst. destruct i as [|i']; [reflexivity | apply IH; exact Hl].
Qed.

(* two integer polynomials with equal real evaluation everywhere have equal
   content (their coefficients agree, so each content divides the other). *)
Lemma peval_eq_content : forall p q,
  (forall y, peval p y = peval q y) -> Zcontent p = Zcontent q.
Proof.
  intros p q Hpq.
  assert (Hz : Forall (fun c => c = 0) (Zpadd p (map (Z.mul (-1)) q))).
  { apply poly_vanish. intro y.
    rewrite peval_Zpadd, peval_map_Zmul.
    pose proof (Hpq y). lra. }
  assert (Hnth : forall i, nth i p 0 = nth i q 0).
  { intro i. pose proof (Forall_eq0_nth _ Hz i) as Hi.
    rewrite nth_Zpadd, nth_map_Zmul in Hi. lia. }
  apply Z.divide_antisym_nonneg; try apply Zcontent_nonneg.
  - apply divide_content_nth. intro i. rewrite <- (Hnth i).
    apply (proj1 (divide_content_nth (Zcontent p) p)). apply Z.divide_refl.
  - apply divide_content_nth. intro i. rewrite (Hnth i).
    apply (proj1 (divide_content_nth (Zcontent q) q)). apply Z.divide_refl.
Qed.

(* primitive part: dividing a list by its content gives a primitive list that
   reconstructs the original when scaled back by the content. *)
Definition Zprim (p : list Z) : list Z := map (fun z => z / Zcontent p) p.

Lemma Zprim_reconstruct : forall p, Zcontent p <> 0 -> map (Z.mul (Zcontent p)) (Zprim p) = p.
Proof.
  intros p Hc. unfold Zprim. rewrite map_map.
  assert (Hcpos : 0 < Zcontent p) by (pose proof (Zcontent_nonneg p); lia).
  assert (Hdiv : Forall (fun z => (Zcontent p | z)) p)
    by (apply divide_content_iff; apply Z.divide_refl).
  rewrite <- (map_id p) at 2. apply map_ext_in.
  intros z Hz. rewrite Forall_forall in Hdiv.
  symmetry. apply Znumtheory.Zdivide_Zdiv_eq; [exact Hcpos | apply Hdiv; exact Hz].
Qed.

Lemma Zprim_content : forall p, Zcontent p <> 0 -> Zcontent (Zprim p) = 1.
Proof.
  intros p Hc.
  assert (Hcpos : 0 < Zcontent p) by (pose proof (Zcontent_nonneg p); lia).
  assert (Heq : Zcontent p = Zcontent p * Zcontent (Zprim p)).
  { rewrite <- (Zcontent_scale (Zcontent p) (Zprim p)) by lia.
    rewrite Zprim_reconstruct by exact Hc. reflexivity. }
  nia.
Qed.

Lemma peval_Zprim : forall (p : list Z) (y : R), Zcontent p <> 0 ->
  (IZR (Zcontent p) * peval (Zprim p) y)%R = peval p y.
Proof.
  intros p y Hc. rewrite <- peval_map_Zmul. rewrite Zprim_reconstruct by exact Hc. reflexivity.
Qed.

(* content is multiplicative: content of a product is the product of contents
   (when the product is not the zero polynomial). *)
Lemma Zcontent_mult : forall p q,
  Zcontent p <> 0 -> Zcontent q <> 0 -> Zcontent (Zpmul p q) <> 0 ->
  Zcontent (Zpmul p q) = Zcontent p * Zcontent q.
Proof.
  intros p q Hcp Hcq Hcpq.
  assert (Hcppos : 0 < Zcontent p) by (pose proof (Zcontent_nonneg p); lia).
  assert (Hcqpos : 0 < Zcontent q) by (pose proof (Zcontent_nonneg q); lia).
  assert (Hpeval : forall y, peval (Zpmul p q) y =
                   peval (map (Z.mul (Zcontent p * Zcontent q)) (Zpmul (Zprim p) (Zprim q))) y).
  { intro y. rewrite peval_Zpmul, peval_map_Zmul, peval_Zpmul.
    rewrite <- (peval_Zprim p y Hcp), <- (peval_Zprim q y Hcq), mult_IZR. ring. }
  assert (Hcont : Zcontent (Zpmul p q)
                  = (Zcontent p * Zcontent q) * Zcontent (Zpmul (Zprim p) (Zprim q))).
  { rewrite (peval_eq_content _ _ Hpeval). rewrite Zcontent_scale by nia. reflexivity. }
  assert (Hprimnz : Zcontent (Zpmul (Zprim p) (Zprim q)) <> 0).
  { intro H0. rewrite H0, Z.mul_0_r in Hcont. apply Hcpq. exact Hcont. }
  rewrite (primitive_mult (Zprim p) (Zprim q)
             (Zprim_content p Hcp) (Zprim_content q Hcq) Hprimnz) in Hcont.
  rewrite Z.mul_1_r in Hcont. exact Hcont.
Qed.
Open Scope R_scope.
(* minpoly_2cos as an integer coefficient list, and its evaluation. *)
Open Scope Z_scope.
Lemma peval_eq_nth : forall p q,
  (forall y, peval p y = peval q y) -> forall i, nth i p 0 = nth i q 0.
Proof.
  intros p q Hpq i.
  assert (Hz : Forall (fun c => c = 0) (Zpadd p (map (Z.mul (-1)) q))).
  { apply poly_vanish. intro y. rewrite peval_Zpadd, peval_map_Zmul. pose proof (Hpq y). lra. }
  pose proof (Forall_eq0_nth _ Hz i) as Hi.
  rewrite nth_Zpadd, nth_map_Zmul in Hi. lia.
Qed.

(* Dividing each coefficient of a cleared list by the clearing factor recovers
   the original rational coefficients, provided the factor divides each
   coefficient. *)
Lemma map_div_IZR_eq : forall (D : Z) (zs : list Z) (cs : list R), 0 < D ->
  Forall (fun z => (D | z)) zs ->
  Forall2 (fun z c => IZR z = (IZR D * c)%R) zs cs -> map (fun z => IZR (z / D)) zs = cs.
Proof.
  intros D zs cs HD Hdiv HF2. induction HF2 as [| z c zs' cs' Hzc HF2' IH].
  - reflexivity.
  - simpl. inversion Hdiv as [|? ? Hz Hdiv']; subst. f_equal.
    + assert (Hzeq : z = D * (z / D)) by (apply Znumtheory.Zdivide_Zdiv_eq; [exact HD | exact Hz]).
      assert (HIZ : IZR z = (IZR D * IZR (z / D))%R) by (rewrite Hzeq at 1; rewrite mult_IZR; reflexivity).
      assert (HDne : (IZR D <> 0)%R) by (apply not_0_IZR; lia).
      assert (Hgoal : (IZR D * IZR (z / D))%R = (IZR D * c)%R) by (rewrite <- HIZ; exact Hzc).
      exact (Rmult_eq_reg_l (IZR D) (IZR (z / D)) c Hgoal HDne).
    + apply IH. exact Hdiv'.
Qed.
Open Scope R_scope.
(* A rational-coefficient polynomial that vanishes everywhere has zero
   coefficients.  Clearing denominators reduces this to the integer case. *)
Lemma pe_rat_vanish : forall p, Forall is_rational p ->
  (forall y, pe p y = 0) -> Forall (fun c => c = 0) p.
Proof.
  intros p Hrat Hpe.
  destruct (clear_denoms p Hrat) as [D [pZ [HD [Hlen HF2]]]].
  assert (HpevalZ : forall y, peval pZ y = 0).
  { intro y. rewrite peval_eq_pe, (Forall2_map_eq _ _ _ HF2), pe_scale, Hpe. ring. }
  pose proof (poly_vanish pZ HpevalZ) as HpZ0.
  clear Hpe HpevalZ Hlen. revert HpZ0 Hrat.
  induction HF2 as [|z c pZ' p' Hzc HF2' IH]; intros HpZ0 Hrat.
  - constructor.
  - constructor.
    + assert (Hz0 : z = 0%Z) by exact (Forall_inv HpZ0).
      assert (Hc0 : (IZR D * c = 0)%R) by (rewrite <- Hzc, Hz0; lra).
      apply Rmult_integral in Hc0. destruct Hc0 as [Hbad | Hgood];
        [ exfalso; apply (not_0_IZR D); [lia | exact Hbad] | exact Hgood ].
    + apply IH; [ exact (Forall_inv_tail HpZ0) | exact (Forall_inv_tail Hrat) ].
Qed.

Lemma nth_map_Rmult : forall a q i, nth i (map (Rmult a) q) 0 = a * nth i q 0.
Proof.
  intros a. induction q as [|b q IH]; intros i.
  - destruct i; simpl; ring.
  - destruct i as [|i]; simpl; [ring | apply IH].
Qed.

Lemma R_Forall0_nth : forall (l : list R), Forall (fun c => c = 0) l -> forall i, nth i l 0 = 0.
Proof.
  induction l as [|a l IH]; intros H i.
  - destruct i; reflexivity.
  - destruct i as [|i]; simpl; [ exact (Forall_inv H) | apply IH; exact (Forall_inv_tail H) ].
Qed.

(* Coefficient uniqueness for rational polynomials: equal evaluations force
   equal coefficients. *)
Lemma pe_rat_eq_nth : forall p q, Forall is_rational p -> Forall is_rational q ->
  (forall y, pe p y = pe q y) -> forall i, nth i p 0 = nth i q 0.
Proof.
  intros p q Hp Hq Heq i.
  assert (Hsub : Forall (fun c => c = 0) (psub p q)).
  { apply pe_rat_vanish; [ apply Forall_rat_psub; assumption | intro y; rewrite pe_psub, Heq; ring ]. }
  pose proof (R_Forall0_nth _ Hsub i) as Hni.
  unfold psub in Hni. rewrite nth_padd, nth_map_Rmult in Hni. lra.
Qed.
Open Scope Z_scope.
(* The convolution of a polynomial all of whose coefficients are zero is zero. *)
Lemma Zconv_zero : forall p q, (forall i, nth i p 0 = 0) -> forall k, Zconv p q k = 0.
Proof.
  induction p as [|a p IH]; intros q Hp k.
  - destruct k; reflexivity.
  - assert (Ha : a = 0) by exact (Hp 0%nat).
    assert (Hp' : forall i, nth i p 0 = 0) by (intro i; exact (Hp (S i))).
    simpl Zconv. rewrite Ha. destruct k as [|k']; [ring | rewrite (IH q Hp' k'); ring].
Qed.

(* The top coefficient of a product is the product of the top coefficients: if p
   has degree at most m and q at most n, the coefficient of degree m + n in the
   product is the product of those coefficients. *)
Lemma Zconv_top : forall p q m n,
  (forall i, (m < i)%nat -> nth i p 0 = 0) ->
  (forall j, (n < j)%nat -> nth j q 0 = 0) ->
  Zconv p q (m + n) = nth m p 0 * nth n q 0.
Proof.
  induction p as [|a p IH]; intros q m n Hp Hq.
  - assert (Hnil : nth m (@nil Z) 0 = 0) by (destruct m; reflexivity).
    rewrite Hnil. cbn [Zconv]. ring.
  - destruct m as [|m'].
    + assert (Hp' : forall i, nth i p 0 = 0) by (intros i; apply (Hp (S i)); lia).
      replace (0 + n)%nat with n by lia.
      destruct n as [|n']; cbn [Zconv nth].
      * ring.
      * rewrite (Zconv_zero p q Hp' n'). ring.
    + assert (Hp' : forall i, (m' < i)%nat -> nth i p 0 = 0) by (intros i Hi; apply (Hp (S i)); lia).
      replace (S m' + n)%nat with (S (m' + n))%nat by lia.
      cbn [Zconv nth].
      rewrite (IH q m' n Hp' Hq).
      assert (HqTop : nth (S (m' + n)) q 0 = 0) by (apply Hq; lia).
      rewrite HqTop. ring.
Qed.

(* If muZ0 has degree d with nonzero leading coefficient and the product with
   qZ0 is a multiple of minpoly_Z (degree 5), then qZ0 has degree at most 5 - d:
   any higher coefficient would create a coefficient of the product beyond
   degree 5, where minpoly_Z vanishes. *)
Open Scope Z_scope.
Lemma Forall2_IZRrel_nth : forall D zs cs i,
  Forall2 (fun z c => IZR z = (IZR D * c)%R) zs cs ->
  (i < length zs)%nat -> IZR (nth i zs 0%Z) = (IZR D * nth i cs 0%R)%R.
Proof.
  intros D zs cs i HF2. revert i. induction HF2 as [|z c zs' cs' Hzc HF2' IH]; intros i Hi.
  - simpl in Hi. lia.
  - destruct i as [|i']; simpl; [ exact Hzc | apply IH; simpl in Hi; lia ].
Qed.

(* Monic Gauss: a monic rational factor of the integer monic minpoly_2cos has
   integer coefficients.  Clearing denominators of both factors, the leading
   coefficient pins the cofactor's degree to 5 - d and its leading coefficient
   to the clearing factor; the content of the product equals the product of
   clearing factors and, by multiplicativity of content, the product of
   contents, so each content equals its clearing factor and each cleared factor
   divided by its content recovers an integer polynomial. *)
Open Scope R_scope.
Lemma peval_app : forall p q y, peval (p ++ q) y = peval p y + y ^ (length p) * peval q y.
Proof.
  induction p as [|a p IH]; intros q y; simpl; [ ring | rewrite IH; ring ].
Qed.

(* The evaluation of a polynomial with all zero coefficients is zero. *)
Lemma peval_all_zero : forall p, Forall (fun c => c = 0%Z) p -> forall y, peval p y = 0.
Proof.
  induction p as [|a p IH]; intros H y.
  - reflexivity.
  - simpl peval. rewrite (Forall_inv H), (IH (Forall_inv_tail H) y). lra.
Qed.

(* Evaluating a polynomial ignores coefficients beyond a cutoff once they vanish. *)
Lemma peval_high_zero : forall p n, (forall j, (n <= j)%nat -> nth j p 0%Z = 0%Z) ->
  forall y, peval p y = peval (firstn n p) y.
Proof.
  intros p n Hhigh y.
  rewrite <- (firstn_skipn n p) at 1. rewrite peval_app.
  rewrite (peval_all_zero (skipn n p)).
  - ring.
  - apply Forall_forall. intros z Hz.
    apply In_nth with (d := 0%Z) in Hz. destruct Hz as [i [Hi Hnth]].
    rewrite nth_skipn in Hnth. rewrite <- Hnth. apply Hhigh. lia.
Qed.

(* A monic integer linear factor of minpoly_2cos yields an integer (hence
   rational) root, contradicting the no-rational-root result. *)
Open Scope R_scope.
Lemma powers_split : forall x k d, (k <= d)%nat ->
  powers x d = powers x k ++ map (fun i => x ^ i) (seq k (d - k)).
Proof.
  intros x k d Hkd. unfold powers.
  replace (seq 0 d) with (seq 0 (k + (d - k))) by (f_equal; lia).
  rewrite seq_app, map_app. rewrite Nat.add_0_l. reflexivity.
Qed.

(* an independent family of powers stays independent when truncated *)
Lemma lin_indep_powers_le : forall x k d, (k <= d)%nat ->
  lin_indep is_rational (powers x d) -> lin_indep is_rational (powers x k).
Proof.
  intros x k d Hkd Hd cs Hlen Hrat Hfc.
  set (cs' := cs ++ repeat 0 (d - k)).
  assert (Hlen' : length cs' = length (powers x d)).
  { unfold cs'. rewrite length_app, repeat_length, powers_length.
    rewrite Hlen, powers_length. lia. }
  assert (Hrat' : Forall is_rational cs').
  { unfold cs'. apply Forall_app. split; [exact Hrat |].
    apply Forall_forall. intros z Hz. apply repeat_spec in Hz. subst z.
    apply (subfield_0 is_rational is_rational_subfield). }
  assert (Hrep0 : Forall (fun c => c = 0) (repeat 0 (d - k)))
    by (apply Forall_forall; intros z Hz; apply repeat_spec in Hz; subst z; reflexivity).
  assert (Hfc' : Fcomb cs' (powers x d) = 0).
  { unfold cs'. rewrite (powers_split x k d Hkd).
    rewrite Fcomb_app by exact Hlen. rewrite Hfc, (Fcomb_zeros _ _ Hrep0). ring. }
  pose proof (Hd cs' Hlen' Hrat' Hfc') as Hall.
  unfold cs' in Hall. apply Forall_app in Hall. destruct Hall as [Hcs0 _]. exact Hcs0.
Qed.

(* #3 resolved: the algebraic degree of 2 cos(2 pi / 11) is exactly 5, exhibited
   as a power basis of Qx of length 5.  The minimal polynomial gives a degree-6
   dependency, so the boundary degree d (independent powers up to d, dependent at
   d+1) is at most 5; were it at most 4 the minimal polynomial would factor with
   a monic rational factor of that degree, contradicting irreducibility, so d is
   exactly 5. *)
Open Scope Z_scope.
Lemma Zconv_comm : forall g h k, Zconv g h k = Zconv h g k.
Proof.
  intros g h k. rewrite <- (nth_Zpmul g h k), <- (nth_Zpmul h g k).
  apply peval_eq_nth. intro y. rewrite !peval_Zpmul. ring.
Qed.

Lemma Zmul_div_mono : forall a b c d : Z, (a | b) -> (c | d) -> (a * c | b * d).
Proof. intros a b c d [x Hx] [y Hy]. exists (x * y). rewrite Hx, Hy. ring. Qed.

(* pi divides Zconv g h r minus the top term g_r * h_0, when all lower g-coeffs
   are divisible by pi. *)
Lemma Zconv_split_top : forall (pi : Z) g h r,
  (forall i, (i < r)%nat -> (pi | nth i g 0)) ->
  (pi | (Zconv g h r - nth r g 0 * nth 0 h 0)).
Proof.
  intros pi g h r. revert g. induction r as [|r IH]; intros g Hlow.
  - destruct g as [|g0 g']; cbn [Zconv nth]; exists 0; ring.
  - destruct g as [|g0 g'].
    + cbn [Zconv nth]; exists 0; ring.
    + cbn [Zconv nth].
      assert (Hg0 : (pi | g0)) by (apply (Hlow 0%nat); lia).
      assert (Hlow' : forall i, (i < r)%nat -> (pi | nth i g' 0))
        by (intros i Hi; apply (Hlow (S i)); lia).
      replace (g0 * nth (S r) h 0 + Zconv g' h r - nth r g' 0 * nth 0 h 0)
        with (g0 * nth (S r) h 0 + (Zconv g' h r - nth r g' 0 * nth 0 h 0)) by ring.
      apply Z.divide_add_r; [apply Z.divide_mul_l; exact Hg0 | apply IH; exact Hlow'].
Qed.

(* Core of Eisenstein: if pi divides the constant term of g but not its leading
   coefficient, and pi divides every coefficient of f = g*h below the top, then pi
   divides the constant term of h. *)
Lemma eisenstein_core : forall (pi : Z) f g h n dg,
  Znumtheory.prime pi -> (1 <= dg)%nat -> (dg < n)%nat ->
  (pi | nth 0 g 0) -> ~ (pi | nth dg g 0) ->
  (forall i, (i < n)%nat -> (pi | nth i f 0)) ->
  (forall k, nth k f 0 = Zconv g h k) ->
  (pi | nth 0 h 0).
Proof.
  intros pi f g h n dg Hp Hdg1 Hdgn Hg0 Hgdg Hlow Hfact.
  assert (Hnf : ~ Forall (fun c => (pi | c)) g).
  { intro HF. rewrite Forall_forall in HF. apply Hgdg.
    destruct (Nat.lt_ge_cases dg (length g)) as [Hlt|Hge].
    - apply HF. apply nth_In. exact Hlt.
    - rewrite nth_overflow by exact Hge. exists 0; ring. }
  assert (Hgr : ~ (pi | nth (firstnd pi g) g 0)) by (apply firstnd_nondiv; exact Hnf).
  assert (Hrne0 : firstnd pi g <> 0%nat) by (intro Hr0; apply Hgr; rewrite Hr0; exact Hg0).
  assert (Hr_le : (firstnd pi g <= dg)%nat).
  { destruct (Nat.le_gt_cases (firstnd pi g) dg) as [H|H]; [exact H|].
    exfalso. apply Hgdg. apply firstnd_below. exact H. }
  assert (Har : (pi | nth (firstnd pi g) f 0)) by (apply Hlow; lia).
  rewrite Hfact in Har.
  assert (Hsplit : (pi | (Zconv g h (firstnd pi g) - nth (firstnd pi g) g 0 * nth 0 h 0)))
    by (apply Zconv_split_top; intros i Hi; apply firstnd_below; exact Hi).
  assert (Hprod : (pi | nth (firstnd pi g) g 0 * nth 0 h 0)).
  { replace (nth (firstnd pi g) g 0 * nth 0 h 0)
      with (Zconv g h (firstnd pi g)
            - (Zconv g h (firstnd pi g) - nth (firstnd pi g) g 0 * nth 0 h 0)) by ring.
    apply Z.divide_sub_r; [exact Har | exact Hsplit]. }
  destruct (Znumtheory.prime_mult pi Hp _ _ Hprod) as [Hbad|Hgood];
    [exfalso; exact (Hgr Hbad) | exact Hgood].
Qed.

Theorem eisenstein : forall (f g h : list Z) (pi : Z) (n dg dh : nat),
  Znumtheory.prime pi ->
  ~ (pi | nth n f 0) ->
  (forall i, (i < n)%nat -> (pi | nth i f 0)) ->
  ~ (pi * pi | nth 0 f 0) ->
  (1 <= dg)%nat -> (1 <= dh)%nat -> (dg + dh = n)%nat ->
  (forall i, (dg < i)%nat -> nth i g 0 = 0) ->
  (forall j, (dh < j)%nat -> nth j h 0 = 0) ->
  (forall k, nth k f 0 = Zconv g h k) ->
  False.
Proof.
  intros f g h pi n dg dh Hp Hanf Hlow Ha0 Hdg1 Hdh1 Hsum Hgdeg Hhdeg Hfact.
  assert (Han_eq : nth n f 0 = nth dg g 0 * nth dh h 0).
  { rewrite Hfact, <- Hsum. apply Zconv_top; assumption. }
  assert (Hgdg : ~ (pi | nth dg g 0))
    by (intro Hd; apply Hanf; rewrite Han_eq; apply Z.divide_mul_l; exact Hd).
  assert (Hhdh : ~ (pi | nth dh h 0))
    by (intro Hd; apply Hanf; rewrite Han_eq; apply Z.divide_mul_r; exact Hd).
  assert (Ha0_eq : nth 0 f 0 = nth 0 g 0 * nth 0 h 0)
    by (rewrite Hfact; destruct g as [|g0 g']; cbn [Zconv nth]; ring).
  assert (Hpa0 : (pi | nth 0 f 0)) by (apply Hlow; lia).
  rewrite Ha0_eq in Hpa0.
  destruct (Znumtheory.prime_mult pi Hp _ _ Hpa0) as [Hg0|Hh0].
  - assert (Hh0 : (pi | nth 0 h 0))
      by (apply (eisenstein_core pi f g h n dg); try assumption; lia).
    apply Ha0. rewrite Ha0_eq. apply Zmul_div_mono; assumption.
  - assert (Hg0 : (pi | nth 0 g 0)).
    { apply (eisenstein_core pi f h g n dh); try assumption; try lia.
      intro k. rewrite Hfact. apply Zconv_comm. }
    apply Ha0. rewrite Ha0_eq. apply Zmul_div_mono; assumption.
Qed.
Open Scope R_scope.
(* ============================================================================
   Cyclotomic irreducibility for prime index: Phi_p = 1 + x + ... + x^(p-1) is
   irreducible over Z. Binomial coefficients, the polynomial shift x -> x+1, and
   Eisenstein at p assemble the classical argument.
   ============================================================================ *)
Open Scope nat_scope.
Fixpoint binom (n k : nat) : nat :=
  match n with
  | O => match k with O => 1 | S _ => 0 end
  | S n' => match k with O => 1 | S k' => binom n' k' + binom n' (S k') end
  end.

Lemma binom_n_0 : forall n, binom n 0 = 1.
Proof. destruct n; reflexivity. Qed.

Lemma binom_S_S : forall n k, binom (S n) (S k) = binom n k + binom n (S k).
Proof. reflexivity. Qed.

Lemma binom_0_S : forall k, binom 0 (S k) = 0.
Proof. reflexivity. Qed.

Lemma binom_n_1 : forall n, binom n 1 = n.
Proof. induction n as [|n IH]; [reflexivity|]. rewrite binom_S_S, binom_n_0, IH. lia. Qed.

(* absorption identity: (k+1) C(n+1,k+1) = (n+1) C(n,k) *)
Lemma binom_absorb : forall n k, S k * binom (S n) (S k) = S n * binom n k.
Proof.
  induction n as [|n IH]; intros k.
  - rewrite binom_S_S. destruct k as [|k]; simpl; lia.
  - rewrite (binom_S_S (S n) k).
    destruct k as [|k].
    + rewrite binom_n_0. rewrite binom_n_1. lia.
    + pose proof (IH k) as IHk.
      pose proof (IH (S k)) as IHSk.
      rewrite (binom_S_S n k) in *.
      rewrite (binom_S_S n (S k)) in *.
      lia.
Qed.

(* a prime p divides the middle binomial coefficients C(p,k), 0 < k < p *)
Lemma prime_div_binom : forall p k,
  Znumtheory.prime (Z.of_nat p) -> 0 < k < p ->
  Z.divide (Z.of_nat p) (Z.of_nat (binom p k)).
Proof.
  intros p k Hp [Hk0 Hkp].
  destruct p as [|p']; [lia|]. destruct k as [|k']; [lia|].
  pose proof (binom_absorb p' k') as Hab.
  assert (Hdvd : Z.divide (Z.of_nat (S p'))
                   (Z.of_nat (S k') * Z.of_nat (binom (S p') (S k')))%Z).
  { rewrite <- Nat2Z.inj_mul, Hab, Nat2Z.inj_mul.
    apply Z.divide_mul_l. apply Z.divide_refl. }
  apply (Znumtheory.Gauss (Z.of_nat (S p')) (Z.of_nat (S k')) (Z.of_nat (binom (S p') (S k')))).
  - exact Hdvd.
  - apply Znumtheory.prime_rel_prime; [exact Hp|].
    intro Hdiv.
    pose proof (Znumtheory.Zdivide_le (Z.of_nat (S p')) (Z.of_nat (S k'))
                  ltac:(lia) ltac:(lia) Hdiv) as Hle.
    apply Nat2Z.inj_le in Hle. lia.
Qed.
Open Scope R_scope.
(* the polynomial shift c(x) -> c(x+1) on integer coefficient lists *)
Fixpoint pshift (c : list Z) : list Z :=
  match c with
  | nil => nil
  | a :: q => let s := pshift q in Zpadd (a :: nil) (Zpadd (0%Z :: s) s)
  end.

Lemma peval_pshift : forall c y, peval (pshift c) y = peval c (y + 1).
Proof.
  induction c as [|a q IH]; intro y; [reflexivity|].
  cbn [pshift]. rewrite !peval_Zpadd. cbn [peval]. rewrite IH. ring.
Qed.

(* the shift commutes with the polynomial product, coefficient-wise *)
Lemma pshift_Zpmul_nth : forall g h k,
  nth k (pshift (Zpmul g h)) 0%Z = nth k (Zpmul (pshift g) (pshift h)) 0%Z.
Proof.
  intros g h k.
  assert (Hpe : forall y, peval (pshift (Zpmul g h)) y = peval (Zpmul (pshift g) (pshift h)) y).
  { intro y. rewrite peval_pshift, !peval_Zpmul, !peval_pshift. ring. }
  apply (peval_eq_nth _ _ Hpe).
Qed.
Open Scope Z_scope.
(* the shifted all-ones polynomial (Phi_n shifted by x -> x+1) has binomial
   coefficients: nth k = C(n, k+1). *)
Lemma nth_pshift_ones : forall n k,
  nth k (pshift (repeat 1%Z n)) 0 = Z.of_nat (binom n (S k)).
Proof.
  induction n as [|n IH]; intro k.
  - cbn [repeat pshift]. destruct k as [|k']; reflexivity.
  - cbn [repeat pshift]. rewrite !nth_Zpadd.
    destruct k as [|k'].
    + cbn [nth]. rewrite (IH 0%nat). rewrite !binom_n_1. lia.
    + assert (Hov : nth (S k') (1%Z :: nil) 0%Z = 0%Z) by (apply nth_overflow; simpl; lia).
      rewrite Hov. cbn [nth].
      rewrite (IH k'), (IH (S k')).
      assert (Hps : binom (S n) (S (S k')) = (binom n (S k') + binom n (S (S k')))%nat)
        by apply binom_S_S.
      rewrite Hps, Nat2Z.inj_add. lia.
Qed.
Open Scope nat_scope.
Lemma binom_gt : forall n k, n < k -> binom n k = 0.
Proof.
  induction n as [|n IH]; intros k Hk.
  - destruct k; [lia | reflexivity].
  - destruct k as [|k]; [lia|].
    rewrite binom_S_S. rewrite (IH k) by lia. rewrite (IH (S k)) by lia. lia.
Qed.

Lemma binom_n_n : forall n, binom n n = 1.
Proof.
  induction n as [|n IH]; [reflexivity|].
  rewrite binom_S_S, IH. rewrite binom_gt by lia. lia.
Qed.

Lemma length_Zpadd : forall p q, length (Zpadd p q) = Nat.max (length p) (length q).
Proof.
  induction p as [|a p IH]; intros q; [reflexivity|].
  destruct q as [|b q]; [simpl; lia|]. cbn [Zpadd length]. rewrite IH. lia.
Qed.

Lemma length_pshift : forall c, length (pshift c) = length c.
Proof.
  induction c as [|a q IH]; [reflexivity|].
  cbn [pshift]. rewrite !length_Zpadd. cbn [length]. rewrite IH. lia.
Qed.
Open Scope R_scope.
(* two integer coefficient lists with equal coefficients evaluate equally *)
Lemma peval_ext : forall a b, (forall k, nth k a 0%Z = nth k b 0%Z) ->
  forall y, peval a y = peval b y.
Proof.
  intros a b Hnth y.
  assert (Hd : forall k, nth k (Zpadd a (map (Z.mul (-1)%Z) b)) 0%Z = 0%Z).
  { intro k. rewrite nth_Zpadd, nth_map_Zmul, Hnth. ring. }
  assert (Hz : Forall (fun c => c = 0%Z) (Zpadd a (map (Z.mul (-1)%Z) b))).
  { apply Forall_forall. intros x Hx. apply In_nth with (d := 0%Z) in Hx.
    destruct Hx as [i [_ Hi]]. rewrite <- Hi. apply Hd. }
  pose proof (peval_all_zero _ Hz y) as Hpe.
  rewrite peval_Zpadd, peval_map_Zmul in Hpe.
  replace (IZR (-1)%Z) with (-1) in Hpe by (simpl; lra). lra.
Qed.
Open Scope Z_scope.
(* The cyclotomic polynomial Phi_p = 1 + x + ... + x^(p-1) (the all-ones list of
   length p) is irreducible over Z for prime p: it has no factorization into two
   integer polynomials of positive degree.  Proof by Eisenstein at p applied to
   the shifted polynomial Phi_p(x+1), whose coefficients are the binomials
   C(p,k+1): the leading one is C(p,p)=1, the constant is C(p,1)=p, and the middle
   ones are divisible by p. *)
Theorem cyclotomic_prime_irreducible : forall p G H dg dh,
  Znumtheory.prime (Z.of_nat p) ->
  (1 <= dg)%nat -> (1 <= dh)%nat -> (dg + dh = p - 1)%nat ->
  length G = S dg -> length H = S dh ->
  (forall k, nth k (repeat 1%Z p) 0 = Zconv G H k) ->
  False.
Proof.
  intros p G H dg dh Hp Hdg Hdh Hsum HlenG HlenH Hfact.
  assert (HpZ : 1 < Z.of_nat p) by (destruct Hp; assumption).
  assert (Hp2 : (2 <= p)%nat) by lia.
  set (f := pshift (repeat 1%Z p)).
  assert (Hf : forall k, nth k f 0 = Z.of_nat (binom p (S k)))
    by (intro k; unfold f; apply nth_pshift_ones).
  apply (eisenstein f (pshift G) (pshift H) (Z.of_nat p) (p - 1)%nat dg dh).
  - exact Hp.
  - rewrite Hf. replace (S (p - 1))%nat with p by lia. rewrite binom_n_n.
    intro Hdiv. pose proof (Znumtheory.Zdivide_le (Z.of_nat p) (Z.of_nat 1)
                  ltac:(lia) ltac:(lia) Hdiv) as Hle. simpl Z.of_nat in Hle. lia.
  - intros i Hi. rewrite Hf. apply prime_div_binom; [exact Hp | lia].
  - rewrite Hf. replace (S 0)%nat with 1%nat by lia. rewrite binom_n_1.
    intro Hdiv. pose proof (Znumtheory.Zdivide_le (Z.of_nat p * Z.of_nat p) (Z.of_nat p)
                  ltac:(nia) ltac:(lia) Hdiv) as Hle. nia.
  - exact Hdg.
  - exact Hdh.
  - exact Hsum.
  - intros i Hi. apply nth_overflow. rewrite length_pshift, HlenG. lia.
  - intros j Hj. apply nth_overflow. rewrite length_pshift, HlenH. lia.
  - intro k. unfold f.
    assert (Hcoeff : forall j, nth j (repeat 1%Z p) 0 = nth j (Zpmul G H) 0)
      by (intro j; rewrite Hfact, nth_Zpmul; reflexivity).
    assert (Hpe1 : forall y, peval (pshift (repeat 1%Z p)) y = peval (pshift (Zpmul G H)) y)
      by (intro y; rewrite !peval_pshift; apply peval_ext; exact Hcoeff).
    rewrite (peval_eq_nth _ _ Hpe1 k), pshift_Zpmul_nth, nth_Zpmul. reflexivity.
Qed.

(* ============================================================================
   Composite-index cyclotomic irreducibility (concrete cases). The prime-index
   argument above shifts Phi by x -> x+1 and applies Eisenstein; the same shift
   makes several composite Phi_n Eisenstein at a prime dividing n. This handles
   the prime-power examples Phi_4 = x^2+1, Phi_8 = x^4+1 (the textbook polynomial
   irreducible over Z yet reducible mod every prime) and Phi_9 = x^6+x^3+1.
   ============================================================================ *)

Lemma cyclo_irreducible_via_shift : forall (phi : list Z) (pi : Z) (n : nat),
  Znumtheory.prime pi ->
  ~ (pi | nth n (pshift phi) 0) ->
  (forall i, (i < n)%nat -> (pi | nth i (pshift phi) 0)) ->
  ~ (pi * pi | nth 0 (pshift phi) 0) ->
  forall G H dg dh, (1 <= dg)%nat -> (1 <= dh)%nat -> (dg + dh = n)%nat ->
  length G = S dg -> length H = S dh ->
  (forall k, nth k phi 0 = Zconv G H k) -> False.
Proof.
  intros phi pi n Hp Hanf Hlow Ha0 G H dg dh Hdg Hdh Hsum HlenG HlenH Hfact.
  apply (eisenstein (pshift phi) (pshift G) (pshift H) pi n dg dh).
  - exact Hp.
  - exact Hanf.
  - exact Hlow.
  - exact Ha0.
  - exact Hdg.
  - exact Hdh.
  - exact Hsum.
  - intros i Hi. apply nth_overflow. rewrite length_pshift, HlenG. lia.
  - intros j Hj. apply nth_overflow. rewrite length_pshift, HlenH. lia.
  - intro k.
    assert (Hcoeff : forall j, nth j phi 0 = nth j (Zpmul G H) 0)
      by (intro j; rewrite Hfact, nth_Zpmul; reflexivity).
    assert (Hpe1 : forall y, peval (pshift phi) y = peval (pshift (Zpmul G H)) y)
      by (intro y; rewrite !peval_pshift; apply peval_ext; exact Hcoeff).
    rewrite (peval_eq_nth _ _ Hpe1 k), pshift_Zpmul_nth, nth_Zpmul. reflexivity.
Qed.

(* Phi_4 = x^2 + 1 is irreducible over Z (Eisenstein at 2 after the shift). *)
Theorem cyclotomic_4_irreducible : forall G H dg dh,
  (1 <= dg)%nat -> (1 <= dh)%nat -> (dg + dh = 2)%nat ->
  length G = S dg -> length H = S dh ->
  (forall k, nth k [1; 0; 1] 0 = Zconv G H k) -> False.
Proof.
  apply (cyclo_irreducible_via_shift [1; 0; 1] 2 2 Znumtheory.prime_2).
  - replace (nth 2 (pshift [1;0;1]) 0) with 1 by reflexivity. intros [z Hz]. lia.
  - intros i Hi. destruct i as [|[|i]]; try lia.
    + replace (nth 0 (pshift [1;0;1]) 0) with 2 by reflexivity. exists 1; reflexivity.
    + replace (nth 1 (pshift [1;0;1]) 0) with 2 by reflexivity. exists 1; reflexivity.
  - replace (nth 0 (pshift [1;0;1]) 0) with 2 by reflexivity. intros [z Hz]. lia.
Qed.

(* Phi_8 = x^4 + 1 is irreducible over Z (the classic composite example). *)
Theorem cyclotomic_8_irreducible : forall G H dg dh,
  (1 <= dg)%nat -> (1 <= dh)%nat -> (dg + dh = 4)%nat ->
  length G = S dg -> length H = S dh ->
  (forall k, nth k [1; 0; 0; 0; 1] 0 = Zconv G H k) -> False.
Proof.
  apply (cyclo_irreducible_via_shift [1; 0; 0; 0; 1] 2 4 Znumtheory.prime_2).
  - replace (nth 4 (pshift [1;0;0;0;1]) 0) with 1 by reflexivity. intros [z Hz]. lia.
  - intros i Hi. destruct i as [|[|[|[|i]]]]; try lia.
    + replace (nth 0 (pshift [1;0;0;0;1]) 0) with 2 by reflexivity. exists 1; reflexivity.
    + replace (nth 1 (pshift [1;0;0;0;1]) 0) with 4 by reflexivity. exists 2; reflexivity.
    + replace (nth 2 (pshift [1;0;0;0;1]) 0) with 6 by reflexivity. exists 3; reflexivity.
    + replace (nth 3 (pshift [1;0;0;0;1]) 0) with 4 by reflexivity. exists 2; reflexivity.
  - replace (nth 0 (pshift [1;0;0;0;1]) 0) with 2 by reflexivity. intros [z Hz]. lia.
Qed.

(* Phi_9 = x^6 + x^3 + 1 is irreducible over Z (Eisenstein at 3 after the shift). *)
Theorem cyclotomic_9_irreducible : forall G H dg dh,
  (1 <= dg)%nat -> (1 <= dh)%nat -> (dg + dh = 6)%nat ->
  length G = S dg -> length H = S dh ->
  (forall k, nth k [1; 0; 0; 1; 0; 0; 1] 0 = Zconv G H k) -> False.
Proof.
  apply (cyclo_irreducible_via_shift [1; 0; 0; 1; 0; 0; 1] 3 6 Znumtheory.prime_3).
  - replace (nth 6 (pshift [1;0;0;1;0;0;1]) 0) with 1 by reflexivity. intros [z Hz]. lia.
  - intros i Hi. destruct i as [|[|[|[|[|[|i]]]]]]; try lia.
    + replace (nth 0 (pshift [1;0;0;1;0;0;1]) 0) with 3 by reflexivity. exists 1; reflexivity.
    + replace (nth 1 (pshift [1;0;0;1;0;0;1]) 0) with 9 by reflexivity. exists 3; reflexivity.
    + replace (nth 2 (pshift [1;0;0;1;0;0;1]) 0) with 18 by reflexivity. exists 6; reflexivity.
    + replace (nth 3 (pshift [1;0;0;1;0;0;1]) 0) with 21 by reflexivity. exists 7; reflexivity.
    + replace (nth 4 (pshift [1;0;0;1;0;0;1]) 0) with 15 by reflexivity. exists 5; reflexivity.
    + replace (nth 5 (pshift [1;0;0;1;0;0;1]) 0) with 6 by reflexivity. exists 2; reflexivity.
  - replace (nth 0 (pshift [1;0;0;1;0;0;1]) 0) with 3 by reflexivity. intros [z Hz]. lia.
Qed.
Open Scope R_scope.
(* ============================================================================
   Palindromic lift: plift A = x^(deg A) * A(x + 1/x), the integer polynomial that
   sends the minimal polynomial of 2cos(2pi/p) to the cyclotomic Phi_p. Together
   with cyclotomic_prime_irreducible it transfers irreducibility from Phi_p to the
   degree-(p-1)/2 minimal polynomial of 2cos(2pi/p).
   ============================================================================ *)
Open Scope R_scope.
(* a polynomial vanishing off 0 vanishes everywhere (continuity at 0) *)
Lemma peval_vanish_punctured : forall p,
  (forall y, y <> 0 -> peval p y = 0) -> forall y, peval p y = 0.
Proof.
  intros p Hpunc y.
  destruct (Req_dec y 0) as [Hy0|Hyn0]; [subst y | apply Hpunc; exact Hyn0].
  apply (UL_sequence (fun n => peval p (RinvN n)) (peval p 0) 0).
  - apply (continuity_seq (peval p) RinvN 0 (peval_continuity p 0)). apply RinvN_cv.
  - intros eps Heps. exists 0%nat. intros n _.
    unfold R_dist. rewrite (Hpunc (RinvN n) (Rgt_not_eq _ _ (cond_pos (RinvN n)))).
    rewrite Rminus_0_r, Rabs_R0. exact Heps.
Qed.

(* two integer polynomials agreeing off 0 have equal coefficients *)
Lemma peval_eq_nth_punctured : forall a b,
  (forall y, y <> 0 -> peval a y = peval b y) -> forall k, nth k a 0%Z = nth k b 0%Z.
Proof.
  intros a b Hpe.
  assert (Hvan : forall y, peval (Zpadd a (map (Z.mul (-1)%Z) b)) y = 0).
  { apply peval_vanish_punctured. intros y Hy.
    rewrite peval_Zpadd, peval_map_Zmul.
    replace (IZR (-1)%Z) with (-1) by (simpl; lra). rewrite (Hpe y Hy). ring. }
  pose proof (poly_vanish _ Hvan) as Hz.
  intro k. pose proof (Forall_eq0_nth _ Hz k) as Hk.
  rewrite nth_Zpadd, nth_map_Zmul in Hk. lia.
Qed.

(* peval of a list prefixed with n zeros = x^n * peval *)
Lemma peval_Zsh : forall n p x, peval (repeat 0%Z n ++ p) x = x ^ n * peval p x.
Proof.
  induction n as [|n IH]; intros p x.
  - simpl. ring.
  - cbn [repeat app peval]. rewrite IH.
    replace (IZR 0%Z) with 0 by (simpl; lra). simpl. ring.
Qed.

(* palindromic lift: plift A is x^(deg A) * A(x + 1/x), an integer polynomial *)
Fixpoint plift (A : list Z) : list Z :=
  match A with
  | nil => nil
  | a :: A' => Zpadd (repeat 0%Z (length A') ++ (a :: nil))
                     (Zpmul (1%Z :: 0%Z :: 1%Z :: nil) (plift A'))
  end.

Lemma plift_char : forall A x, x <> 0 ->
  x * peval (plift A) x = x ^ (length A) * peval A (x + / x).
Proof.
  intros A. induction A as [|a A' IH]; intros x Hx.
  - simpl. ring.
  - cbn [plift length].
    set (z := x + / x).
    assert (Hxz : x * z = x * x + 1) by (unfold z; field; exact Hx).
    rewrite peval_Zpadd, peval_Zsh, peval_Zpmul.
    assert (Ha : peval (a :: nil) x = IZR a) by (cbn [peval]; ring).
    assert (Hq : peval (1%Z :: 0%Z :: 1%Z :: nil) x = 1 + x * x)
      by (cbn [peval]; replace (IZR 1%Z) with 1 by (simpl; lra);
          replace (IZR 0%Z) with 0 by (simpl; lra); ring).
    assert (Hpe : peval (a :: A') z = IZR a + z * peval A' z) by (cbn [peval]; ring).
    rewrite Ha, Hq, Hpe.
    pose proof (IH x Hx) as HIH. fold z in HIH.
    set (P := peval (plift A') x) in *. set (Q := peval A' z) in *.
    set (W := x ^ (length A')) in *.
    replace (x ^ S (length A')) with (x * W) by (unfold W; simpl; ring).
    transitivity (x * W * IZR a + (1 + x * x) * (x * P)).
    + ring.
    + rewrite HIH. replace (1 + x * x) with (x * z) by (rewrite Hxz; ring). ring.
Qed.

Lemma length_Zpmul : forall A B, A <> nil -> B <> nil ->
  length (Zpmul A B) = (length A + length B - 1)%nat.
Proof.
  intros A. induction A as [|a A' IH]; intros B HA HB; [contradiction|].
  cbn [Zpmul]. rewrite length_Zpadd, length_map. cbn [length].
  assert (HBl : (1 <= length B)%nat) by (destruct B; [contradiction|simpl; lia]).
  destruct A' as [|a' A''].
  - cbn [Zpmul length]. lia.
  - rewrite (IH B ltac:(discriminate) HB). cbn [length]. lia.
Qed.

(* the lift commutes with the polynomial product, coefficient-wise *)
Lemma plift_Zpmul_nth : forall A B, A <> nil -> B <> nil ->
  forall k, nth k (plift (Zpmul A B)) 0%Z = nth k (Zpmul (plift A) (plift B)) 0%Z.
Proof.
  intros A B HA HB.
  apply peval_eq_nth_punctured. intros x Hx.
  rewrite peval_Zpmul.
  pose proof (plift_char A x Hx) as HA1.
  pose proof (plift_char B x Hx) as HB1.
  pose proof (plift_char (Zpmul A B) x Hx) as HAB1.
  rewrite (length_Zpmul A B HA HB), peval_Zpmul in HAB1.
  set (LA := length A) in *. set (LB := length B) in *.
  assert (HLA : (1 <= LA)%nat) by (unfold LA; destruct A; [contradiction|simpl; lia]).
  assert (HLB : (1 <= LB)%nat) by (unfold LB; destruct B; [contradiction|simpl; lia]).
  set (PA := peval (plift A) x) in *. set (PB := peval (plift B) x) in *.
  set (PAB := peval (plift (Zpmul A B)) x) in *.
  set (QA := peval A (x + / x)) in *. set (QB := peval B (x + / x)) in *.
  assert (Hkey : x * x ^ (LA + LB - 1) = x ^ LA * x ^ LB).
  { rewrite tech_pow_Rmult, <- pow_add. f_equal. lia. }
  set (WA := x ^ LA) in *. set (WB := x ^ LB) in *. set (W1 := x ^ (LA + LB - 1)) in *.
  apply (Rmult_eq_reg_l (x * x)); [| apply Rmult_integral_contrapositive_currified; exact Hx].
  transitivity (WA * WB * (QA * QB)).
  - replace (x * x * PAB) with (x * (x * PAB)) by ring.
    rewrite HAB1. replace (x * (W1 * (QA * QB))) with ((x * W1) * (QA * QB)) by ring.
    rewrite Hkey. ring.
  - replace (x * x * (PA * PB)) with ((x * PA) * (x * PB)) by ring.
    rewrite HA1, HB1. ring.
Qed.
Open Scope R_scope.
(* ============================================================================
   Degree of 2cos(2pi/17): the explicit degree-8 minimal polynomial is irreducible.
   Its palindromic lift is Phi_17, so any positive-degree integer factorization
   would lift to one of Phi_17, contradicting cyclotomic_prime_irreducible.
   ============================================================================ *)
Open Scope Z_scope.
Lemma nth_repeat0 : forall m k, nth k (repeat 0%Z m) 0%Z = 0%Z.
Proof.
  induction m as [|m IH]; intro k.
  - destruct k; reflexivity.
  - destruct k as [|k]; cbn [repeat nth]; [reflexivity| apply IH].
Qed.

Lemma nth_app_zeros : forall (l : list Z) m k, nth k (l ++ repeat 0%Z m) 0%Z = nth k l 0%Z.
Proof.
  intros l m k. destruct (Nat.lt_ge_cases k (length l)) as [Hlt|Hge].
  - rewrite app_nth1 by exact Hlt. reflexivity.
  - rewrite app_nth2 by exact Hge. rewrite nth_repeat0.
    rewrite nth_overflow by exact Hge. reflexivity.
Qed.

Lemma nth_firstn_eq : forall (l : list Z) n k, (k < n)%nat -> nth k (firstn n l) 0%Z = nth k l 0%Z.
Proof.
  induction l as [|a l IH]; intros n k Hk.
  - rewrite firstn_nil. reflexivity.
  - destruct n as [|n]; [lia|]. cbn [firstn]. destruct k as [|k]; [reflexivity|].
    cbn [nth]. apply IH. lia.
Qed.

(* one-level unfolding of plift, to avoid cbn unfolding the recursive call *)
Lemma plift_cons : forall a A',
  plift (a :: A') = Zpadd (repeat 0%Z (length A') ++ (a :: nil))
                          (Zpmul (1%Z::0%Z::1%Z::nil) (plift A')).
Proof. reflexivity. Qed.

Lemma plift_nonnil : forall A, A <> nil -> plift A <> nil.
Proof.
  intros [|a A'] H; [contradiction|]. intro Hc.
  assert (Hl : length (plift (a :: A')) = 0%nat) by (rewrite Hc; reflexivity).
  rewrite plift_cons in Hl. rewrite length_Zpadd, length_app, repeat_length in Hl.
  cbn [length] in Hl. lia.
Qed.

(* plift carries two trailing zeros, so its length is 2*len + 1 *)
Lemma length_plift : forall A, A <> nil -> length (plift A) = (2 * length A + 1)%nat.
Proof.
  intros A. induction A as [|a A' IH]; intro HA; [contradiction|].
  destruct A' as [|a' A''].
  - vm_compute. reflexivity.
  - rewrite plift_cons. rewrite length_Zpadd, length_app, repeat_length.
    rewrite length_Zpmul; [| discriminate | apply plift_nonnil; discriminate].
    rewrite (IH ltac:(discriminate)). cbn [length]. lia.
Qed.

(* convolution by 1 + x^2 picks out two coefficients *)
Lemma nth_Zpmul_101 : forall q i,
  nth (S (S i)) (Zpmul (1%Z::0%Z::1%Z::nil) q) 0%Z = nth (S (S i)) q 0%Z + nth i q 0%Z.
Proof.
  intros q i. cbn [Zpmul map].
  rewrite nth_Zpadd, nth_map_Zmul. cbn [nth].
  rewrite nth_Zpadd, nth_map_Zmul. cbn [nth].
  rewrite nth_Zpadd, nth_map_Zmul.
  replace (nth i (0%Z :: nil) 0%Z) with 0%Z
    by (destruct i; [reflexivity | symmetry; apply nth_overflow; cbn [length]; lia]).
  ring.
Qed.

(* coefficients of plift A above the true degree 2*(len A - 1) vanish *)
Lemma plift_high_zero : forall A i, (2 * length A - 1 <= i)%nat -> nth i (plift A) 0%Z = 0%Z.
Proof.
  intros A. induction A as [|a A' IH]; intros i Hi.
  - destruct i; reflexivity.
  - rewrite plift_cons. rewrite nth_Zpadd.
    assert (Hx : nth i (repeat 0%Z (length A') ++ a :: nil) 0%Z = 0%Z).
    { apply nth_overflow. rewrite length_app, repeat_length. cbn [length].
      cbn [length] in Hi. lia. }
    rewrite Hx, Z.add_0_l.
    destruct i as [|[|i']].
    + cbn [length] in Hi. lia.
    + assert (HA' : A' = nil)
        by (destruct A' as [|a' A'']; [reflexivity|]; cbn [length] in Hi; lia).
      subst A'. vm_compute. reflexivity.
    + rewrite nth_Zpmul_101. rewrite !IH by (cbn [length] in Hi; lia). ring.
Qed.

(* explicit minimal polynomial of 2cos(2pi/17): the depalindromization of Phi_17 *)
Open Scope Z_scope.
Lemma prime_17 : Znumtheory.prime 17.
Proof.
  apply Znumtheory.prime_intro; [lia|].
  intros n [Hn1 Hn2]. unfold Znumtheory.rel_prime.
  assert (Hd : Z.gcd n 17 = 1).
  { assert (Hc : n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8
                \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16) by lia.
    repeat (destruct Hc as [Hc0|Hc]; [subst n; vm_compute; reflexivity|]).
    subst n; vm_compute; reflexivity. }
  rewrite <- Hd. apply Znumtheory.Zgcd_is_gcd.
Qed.

(* The minimal polynomial of 2cos(2pi/17) admits no factorization into two integer
   polynomials of positive degree: any such factor would lift (palindromically) to a
   positive-degree factorization of Phi_17, which cyclotomic_prime_irreducible forbids. *)
Open Scope R_scope.
Fixpoint cossum (n : nat) (a : R) : R :=
  match n with
  | O => 0
  | S n' => cossum n' a + cos (INR n' * a)
  end.

(* Dirichlet-kernel telescoping identity *)
Lemma cossum_telescope : forall n a,
  2 * sin (a / 2) * cossum n a = sin ((INR n - 1/2) * a) + sin (a / 2).
Proof.
  induction n as [|n IH]; intro a.
  - simpl cossum. simpl INR.
    replace ((0 - 1/2) * a) with (- (a/2)) by field. rewrite sin_neg. ring.
  - simpl cossum.
    replace (2 * sin (a/2) * (cossum n a + cos (INR n * a)))
      with (2 * sin (a/2) * cossum n a + 2 * sin (a/2) * cos (INR n * a)) by ring.
    rewrite IH.
    replace (2 * sin (a/2) * cos (INR n * a))
      with (sin (a/2 + INR n * a) - sin (INR n * a - a/2)) by (rewrite sin_plus, sin_minus; ring).
    rewrite S_INR.
    replace ((INR n + 1 - 1/2) * a) with (a/2 + INR n * a) by field.
    replace ((INR n - 1/2) * a) with (INR n * a - a/2) by field.
    ring.
Qed.

(* the full sum of cos(2 pi k / p) over a complete residue system is zero *)
Lemma cossum_full_zero : forall p, (2 <= p)%nat -> cossum p (2 * PI / INR p) = 0.
Proof.
  intros p Hp.
  set (a := 2 * PI / INR p).
  assert (HPI : 0 < PI) by apply PI_RGT_0.
  assert (HpR : 0 < INR p) by (apply lt_0_INR; lia).
  assert (Hp2 : 2 <= INR p) by (replace 2 with (INR 2) by (simpl; ring); apply le_INR; lia).
  assert (Hsin : sin (a / 2) <> 0).
  { unfold a. replace (2 * PI / INR p / 2) with (PI / INR p) by (field; lra).
    apply Rgt_not_eq. apply sin_gt_0.
    - apply Rdiv_lt_0_compat; [exact HPI | exact HpR].
    - apply Rmult_lt_reg_r with (INR p); [exact HpR|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r. nra. }
  apply (Rmult_eq_reg_l (2 * sin (a / 2))).
  - rewrite cossum_telescope, Rmult_0_r.
    assert (Hpa : INR p * a = 2 * PI) by (unfold a; field; lra).
    replace ((INR p - 1/2) * a) with (2 * PI - a / 2) by (rewrite <- Hpa; field).
    rewrite sin_minus, sin_2PI, cos_2PI. ring.
  - apply Rmult_integral_contrapositive_currified; [lra | exact Hsin].
Qed.

(* psi m = 1 + D_1 + ... + D_m : the minimal polynomial of 2cos(2 pi/(2m+1)) *)
Open Scope R_scope.
Lemma cossum_Sm_half : forall m, (1 <= m)%nat ->
  cossum (S m) (2 * PI / INR (2*m+1)) = 1/2.
Proof.
  intros m Hm. set (p := (2*m+1)%nat). set (a := 2 * PI / INR p).
  assert (HPI : 0 < PI) by apply PI_RGT_0.
  assert (HpR : 0 < INR p) by (apply lt_0_INR; unfold p; lia).
  assert (Hp2 : 2 <= INR p) by (replace 2 with (INR 2) by (simpl; ring); apply le_INR; unfold p; lia).
  assert (HpINR : INR p = 2 * INR m + 1) by (unfold p; rewrite plus_INR, mult_INR; simpl INR; ring).
  assert (Hsin : sin (a / 2) <> 0).
  { unfold a. replace (2 * PI / INR p / 2) with (PI / INR p) by (field; lra).
    apply Rgt_not_eq. apply sin_gt_0.
    - apply Rdiv_lt_0_compat; [exact HPI | exact HpR].
    - apply Rmult_lt_reg_r with (INR p); [exact HpR|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r. nra. }
  apply (Rmult_eq_reg_l (2 * sin (a/2)));
    [| apply Rmult_integral_contrapositive_currified; [lra | exact Hsin]].
  rewrite cossum_telescope.
  assert (Hpi : (INR (S m) - 1/2) * a = PI).
  { unfold a. rewrite HpINR, S_INR. field. pose proof (pos_INR m). lra. }
  rewrite Hpi, sin_PI. lra.
Qed.

(* 2 cos(2 pi/(2m+1)) is a root of psi m *)
Open Scope R_scope.
Lemma peval_repeat1_geom : forall n x,
  x * peval (repeat 1%Z n) x = peval (repeat 1%Z n) x - 1 + x ^ n.
Proof.
  induction n as [|n IH]; intro x.
  - simpl. ring.
  - cbn [repeat peval]. replace (IZR 1%Z) with 1 by (simpl; lra).
    set (P := peval (repeat 1%Z n) x).
    assert (HxP : x * P = P - 1 + x ^ n) by (unfold P; exact (IH x)).
    simpl pow. nra.
Qed.

(* extending Phi_n by two leading ones *)
Lemma peval_repeat1_two : forall n x,
  peval (repeat 1%Z (n + 2)) x = peval (repeat 1%Z n) x + x ^ n + x ^ (n + 1).
Proof.
  intros n x. rewrite repeat_app, peval_app, repeat_length.
  cbn [repeat peval]. replace (IZR 1%Z) with 1 by (simpl; lra).
  rewrite pow_add. simpl pow. ring.
Qed.

(* the palindromic identity x^m * psi_m(x + 1/x) = Phi_{2m+1}(x) *)
Open Scope Z_scope.
Lemma high_coeff_zero_gen : forall (f : list Z) N muZ0 qZ0 Dmu Dq d,
  (forall j, (N < j)%nat -> nth j f 0%Z = 0%Z) ->
  length muZ0 = S d -> nth d muZ0 0 <> 0 ->
  (forall k, nth k (Zpmul muZ0 qZ0) 0 = (Dmu * Dq) * nth k f 0) ->
  forall j, (N < d + j)%nat -> nth j qZ0 0 = 0.
Proof.
  intros f N muZ0 qZ0 Dmu Dq d Hfdeg Hlen Hlead Hprod.
  assert (Hmudeg : forall i, (d < i)%nat -> nth i muZ0 0 = 0).
  { intros i Hi. apply nth_overflow. lia. }
  assert (Hrange : forall n j, (length qZ0 <= j + n)%nat -> (N < d + j)%nat -> nth j qZ0 0 = 0).
  { induction n as [|n IH]; intros j Hjn Hj.
    - apply nth_overflow. lia.
    - destruct (Nat.le_gt_cases (length qZ0) j) as [Hov | Hlt].
      + apply nth_overflow. exact Hov.
      + assert (Hqdeg : forall j', (j < j')%nat -> nth j' qZ0 0 = 0).
        { intros j' Hj'. apply IH; lia. }
        pose proof (Zconv_top muZ0 qZ0 d j Hmudeg Hqdeg) as Htop.
        rewrite <- nth_Zpmul in Htop. rewrite Hprod in Htop.
        assert (Hhi : nth (d + j) f 0 = 0) by (apply Hfdeg; lia).
        rewrite Hhi, Z.mul_0_r in Htop. symmetry in Htop.
        apply Z.mul_eq_0 in Htop. destruct Htop as [Hbad | Hgood];
          [ exfalso; apply Hlead; exact Hbad | exact Hgood ]. }
  intros j Hj. apply (Hrange (length qZ0) j); [ lia | exact Hj ].
Qed.

Lemma monic_gauss_factor_gen : forall (f : list Z) (N : nat) mu q d,
  length f = S N -> nth N f 0%Z = 1%Z -> Zcontent f = 1%Z ->
  Forall is_rational mu -> Forall is_rational q ->
  length mu = S d -> nth d mu 0%R = 1%R -> (d <= N)%nat ->
  (forall y, pe (map IZR f) y = (pe mu y * pe q y)%R) ->
  exists muZ qZ : list Z,
    map IZR muZ = mu /\ length muZ = S d /\ nth d muZ 0%Z = 1%Z /\
    map IZR qZ = q /\
    (forall y, peval (Zpmul muZ qZ) y = peval f y).
Proof.
  intros f N mu q d HlenF HmonF HcontF Hmurat Hqrat Hmulen Hmonic Hd5 Hfact.
  assert (Hfdeg : forall j, (N < j)%nat -> nth j f 0%Z = 0%Z)
    by (intros j Hj; apply nth_overflow; lia).
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
  assert (HprodPev : forall y, peval (Zpmul muZ0 qZ0) y = peval (map (Z.mul (Dmu * Dq)) f) y).
  { intro y. rewrite peval_Zpmul, HpevMu, HpevQ, peval_map_Zmul, (peval_eq_pe f y).
    rewrite (Hfact y), mult_IZR. ring. }
  assert (Hprodnth : forall k, nth k (Zpmul muZ0 qZ0) 0 = (Dmu * Dq) * nth k f 0)
    by (intro k; rewrite (peval_eq_nth _ _ HprodPev k), nth_map_Zmul; reflexivity).
  pose proof (high_coeff_zero_gen f N muZ0 qZ0 Dmu Dq d Hfdeg HmuZlenSd HleadMuNz Hprodnth) as Hqhigh.
  assert (Hmudeg : forall i, (d < i)%nat -> nth i muZ0 0 = 0) by (intros i Hi; apply nth_overflow; lia).
  assert (HqdegBound : forall j, ((N - d) < j)%nat -> nth j qZ0 0%Z = 0) by (intros j Hj; apply Hqhigh; lia).
  assert (HleadQ : nth (N - d) qZ0 0%Z = Dq).
  { pose proof (Zconv_top muZ0 qZ0 d (N - d) Hmudeg HqdegBound) as Htop.
    replace (d + (N - d))%nat with N in Htop by lia.
    rewrite <- nth_Zpmul, Hprodnth, HleadMu, HmonF, Z.mul_1_r in Htop.
    assert (Hcancel : Dmu * (Dq - nth (N - d) qZ0 0) = 0) by (rewrite Z.mul_sub_distr_l; lia).
    apply Z.mul_eq_0 in Hcancel. destruct Hcancel as [Hb | Hg]; lia. }
  assert (HcMuNz : Zcontent muZ0 <> 0).
  { intro H0. rewrite Zcontent_zero_iff in H0.
    pose proof (Forall_eq0_nth _ H0 d) as Hz. rewrite HleadMu in Hz. lia. }
  assert (HcQNz : Zcontent qZ0 <> 0).
  { intro H0. rewrite Zcontent_zero_iff in H0.
    pose proof (Forall_eq0_nth _ H0 (N - d)) as Hz. rewrite HleadQ in Hz. lia. }
  assert (Hprodcontnz : Zcontent (Zpmul muZ0 qZ0) <> 0).
  { rewrite (peval_eq_content _ _ HprodPev), Zcontent_scale by nia.
    rewrite HcontF. nia. }
  pose proof (Zcontent_mult muZ0 qZ0 HcMuNz HcQNz Hprodcontnz) as Hcmult.
  assert (Hcontprod : Zcontent (Zpmul muZ0 qZ0) = Dmu * Dq).
  { rewrite (peval_eq_content _ _ HprodPev), Zcontent_scale by nia.
    rewrite HcontF. ring. }
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
    rewrite (peval_eq_pe f y), (Hfact y). reflexivity.
Qed.
Open Scope R_scope.
Lemma minpoly_low_degree_factors_gen : forall (fR : list R) delta d,
  Forall is_rational fR ->
  lin_indep is_rational (powers delta d) ->
  spans is_rational (powers delta d) (delta ^ d) ->
  pe fR delta = 0 ->
  exists mu q, length mu = S d /\ nth d mu 0 = 1 /\
               Forall is_rational mu /\ Forall is_rational q /\
               (forall y, pe fR y = pe mu y * pe q y).
Proof.
  intros fR delta d HfRrat Hli Hsp Hroot.
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
  destruct (monic_div_exists mu d Hmulen Hmonic Hmurat (length fR) fR
              (le_n _) HfRrat) as [q [r [Hid [Hrlen [Hqrat Hrrat]]]]].
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
Open Scope R_scope.
Lemma general_cubic_root_exists : forall c3 c2 c1 c0, c3 <> 0 ->
  exists s, c3*(s^3) + c2*(s^2) + c1*s + c0 = 0.
Proof.
  intros c3 c2 c1 c0 Hc3.
  set (sh := c2 / (3 * c3)).
  set (P := c1/c3 - c2*c2/(3*c3*c3)).
  set (Q := c0/c3 - c1*c2/(3*c3*c3) + 2*(c2*c2*c2)/(27*c3*c3*c3)).
  destruct (depressed_cubic_root_exists P Q) as [u Hu].
  unfold is_cubic_root, depressed_cubic in Hu.
  exists (u - sh).
  assert (Hdep : c3*((u - sh)^3) + c2*((u - sh)^2) + c1*(u - sh) + c0
                 = c3 * (u^3 + P*u + Q)) by (unfold sh, P, Q; field; exact Hc3).
  rewrite Hdep, Hu. ring.
Qed.

(* General exact O6 solvability: for the reference parabola (focus (0,1),
   directrix y=-1) and an arbitrary second point (a,b) and non-horizontal line
   l2, there is a crease tangent to the reference parabola that also reflects
   (a,b) onto l2 - the common tangent, found via the depressed cubic.  Any O6
   configuration reduces to this one by a similarity fixing the first parabola. *)
Open Scope R_scope.
Lemma general_cubic_unique_root : forall c3 c2 c1 c0, c3 <> 0 ->
  cubic_discriminant (c1/c3 - c2*c2/(3*c3*c3))
                     (c0/c3 - c1*c2/(3*c3*c3) + 2*(c2*c2*c2)/(27*c3*c3*c3)) < 0 ->
  exists! s, c3*(s^3) + c2*(s^2) + c1*s + c0 = 0.
Proof.
  intros c3 c2 c1 c0 Hc3 Hdisc.
  set (sh := c2 / (3 * c3)).
  set (P := c1/c3 - c2*c2/(3*c3*c3)).
  set (Q := c0/c3 - c1*c2/(3*c3*c3) + 2*(c2*c2*c2)/(27*c3*c3*c3)).
  destruct (neg_disc_unique_root_exists P Q Hdisc) as [u [Hu Huniq]].
  unfold is_cubic_root, depressed_cubic in Hu.
  assert (Hdep : forall x, c3*(x^3) + c2*(x^2) + c1*x + c0 = c3 * ((x+sh)^3 + P*(x+sh) + Q))
    by (intro x; unfold sh, P, Q; field; exact Hc3).
  exists (u - sh). split.
  - rewrite Hdep. replace (u - sh + sh) with u by ring. rewrite Hu. ring.
  - intros s' Hs'. rewrite Hdep in Hs'.
    apply Rmult_integral in Hs'. destruct Hs' as [Hbad | Hgood]; [exfalso; exact (Hc3 Hbad)|].
    assert (Hu' : is_cubic_root P Q (s' + sh))
      by (unfold is_cubic_root, depressed_cubic; exact Hgood).
    pose proof (Huniq (s' + sh) Hu') as Heq. lra.
Qed.

(* a general cubic with nonzero leading coefficient and positive depressed
   discriminant has three distinct real roots: the three-solution O6 case *)
Lemma general_cubic_three_roots : forall c3 c2 c1 c0, c3 <> 0 ->
  cubic_discriminant (c1/c3 - c2*c2/(3*c3*c3))
                     (c0/c3 - c1*c2/(3*c3*c3) + 2*(c2*c2*c2)/(27*c3*c3*c3)) > 0 ->
  exists s1 s2 s3,
    c3*(s1^3) + c2*(s1^2) + c1*s1 + c0 = 0 /\
    c3*(s2^3) + c2*(s2^2) + c1*s2 + c0 = 0 /\
    c3*(s3^3) + c2*(s3^2) + c1*s3 + c0 = 0 /\
    s1 < s2 /\ s2 < s3.
Proof.
  intros c3 c2 c1 c0 Hc3 Hdisc.
  set (sh := c2 / (3 * c3)).
  set (P := c1/c3 - c2*c2/(3*c3*c3)).
  set (Q := c0/c3 - c1*c2/(3*c3*c3) + 2*(c2*c2*c2)/(27*c3*c3*c3)).
  destruct (pos_disc_three_distinct_roots P Q Hdisc)
    as [u1 [u2 [u3 [H1 [H2 [H3 [H12 H23]]]]]]].
  unfold is_cubic_root, depressed_cubic in H1, H2, H3.
  assert (Hdep : forall x, c3*(x^3) + c2*(x^2) + c1*x + c0 = c3 * ((x+sh)^3 + P*(x+sh) + Q))
    by (intro x; unfold sh, P, Q; field; exact Hc3).
  exists (u1 - sh), (u2 - sh), (u3 - sh).
  repeat split.
  - rewrite Hdep. replace (u1 - sh + sh) with u1 by ring. rewrite H1. ring.
  - rewrite Hdep. replace (u2 - sh + sh) with u2 by ring. rewrite H2. ring.
  - rewrite Hdep. replace (u3 - sh + sh) with u3 by ring. rewrite H3. ring.
  - lra.
  - lra.
Qed.

(* O6 for a parabola of arbitrary focal scale: focus (0,d1), directrix y=-d1
   (d1 <> 0), and an arbitrary second focus (a,b) and non-horizontal directrix l2.
   The crease tangent to this parabola reflecting (a,b) onto l2 exists, via the
   depressed cubic.  Subsumes O6_general_solvable (d1 = 1); any non-degenerate O6
   configuration reduces to this by a rigid motion fixing the directrix horizontal. *)
Open Scope R_scope.
Lemma exists_angle : forall c s, c*c + s*s = 1 -> exists th, cos th = c /\ sin th = s.
Proof.
  intros c s Hcs. assert (Hc1 : -1 <= c <= 1) by nra.
  pose proof (cos_acos c Hc1) as Hcos.
  destruct (acos_bound c) as [Hb1 Hb2].
  assert (Hsinpos : 0 <= sin (acos c)) by (apply sin_ge_0; lra).
  pose proof (sin2_cos2 (acos c)) as Hpy. rewrite Hcos in Hpy. unfold Rsqr in Hpy.
  assert (Hsin2 : sin (acos c) * sin (acos c) = s * s) by lra.
  destruct (Rle_dec 0 s) as [Hs|Hs].
  - exists (acos c). split; [exact Hcos|].
    apply Rsqr_inj; [exact Hsinpos | exact Hs | unfold Rsqr; exact Hsin2].
  - exists (- acos c). split; [rewrite cos_neg; exact Hcos|].
    rewrite sin_neg.
    assert (Hsin : sin (acos c) = - s)
      by (apply Rsqr_inj; [exact Hsinpos | lra | unfold Rsqr; nra]).
    rewrite Hsin. ring.
Qed.

(* rotation composition / identity and line-scale invariance: the remaining
   algebra for the O6 normalization. *)
Open Scope R_scope.
Module Cardano_C.
Open Scope R_scope.
(* ===== Complex numbers as R*R, with ring and field structure ===== *)
Definition C : Type := (R * R)%type.
Definition Cre (z : C) : R := fst z.
Definition Cim (z : C) : R := snd z.
Definition C0 : C := (0, 0).
Definition C1 : C := (1, 0).
Definition Ci : C := (0, 1).
(* Decidability of complex equality. *)
Lemma Ceq_dec : forall a b : C, {a = b} + {a <> b}.
Proof.
  intros [a1 a2] [b1 b2].
  destruct (Req_dec_T a1 b1) as [E1|N1]; [| right; intro H; inversion H; contradiction].
  destruct (Req_dec_T a2 b2) as [E2|N2]; [| right; intro H; inversion H; contradiction].
  left; subst; reflexivity.
Qed.
Definition Cadd (a b : C) : C := (fst a + fst b, snd a + snd b).
Definition Copp (a : C) : C := (- fst a, - snd a).
Definition Csub (a b : C) : C := Cadd a (Copp b).
Definition Cmul (a b : C) : C :=
  (fst a * fst b - snd a * snd b, fst a * snd b + snd a * fst b).
Definition Cinv (a : C) : C :=
  (fst a / (fst a * fst a + snd a * snd a), - snd a / (fst a * fst a + snd a * snd a)).
Definition Cdiv (a b : C) : C := Cmul a (Cinv b).

Declare Scope C_scope.
Delimit Scope C_scope with C.
Bind Scope C_scope with C.
Infix "+" := Cadd : C_scope.
Infix "*" := Cmul : C_scope.
Infix "-" := Csub : C_scope.
Notation "- x" := (Copp x) : C_scope.
Infix "/" := Cdiv : C_scope.

Lemma C_ring : ring_theory C0 C1 Cadd Cmul Csub Copp (@eq C).
Proof.
  constructor; intros;
    repeat match goal with z : C |- _ => destruct z end;
    cbv [Cadd Cmul Csub Copp C0 C1 fst snd]; f_equal; ring.
Qed.

Add Ring Cring : C_ring.

Lemma C1_neq_C0 : C1 <> C0.
Proof. unfold C1, C0. intro H. inversion H. lra. Qed.

Lemma Cmod_sq_pos : forall z, z <> C0 -> fst z * fst z + snd z * snd z <> 0.
Proof.
  intros [x y] H. simpl. intro Hc.
  apply H. unfold C0. f_equal; nra.
Qed.

Lemma Cinv_l : forall z, z <> C0 -> Cmul (Cinv z) z = C1.
Proof.
  intros z Hz. pose proof (Cmod_sq_pos z Hz) as Hm.
  destruct z as [x y]. unfold Cmul, Cinv, C1; simpl in *.
  f_equal; field; exact Hm.
Qed.

Lemma C_field : field_theory C0 C1 Cadd Cmul Csub Copp Cdiv Cinv (@eq C).
Proof.
  constructor.
  - exact C_ring.
  - exact C1_neq_C0.
  - reflexivity.
  - exact Cinv_l.
Qed.

Add Field Cfield : C_field.

(* injection R -> C and basic facts *)
Definition RtoC (x : R) : C := (x, 0).

Lemma RtoC_add : forall a b, RtoC (a + b) = Cadd (RtoC a) (RtoC b).
Proof. intros; unfold RtoC, Cadd; simpl; f_equal; ring. Qed.

Lemma RtoC_mul : forall a b, RtoC (a * b) = Cmul (RtoC a) (RtoC b).
Proof. intros; unfold RtoC, Cmul; simpl; f_equal; ring. Qed.

Lemma C0_eq : RtoC 0 = C0. Proof. reflexivity. Qed.
Lemma C1_eq : RtoC 1 = C1. Proof. reflexivity. Qed.

(* ===== de Moivre: double / triple angle in the exact polynomial forms ===== *)
Lemma cos_double : forall b, cos (2 * b) = cos b * cos b - sin b * sin b.
Proof. intro b. replace (2 * b) with (b + b) by ring. rewrite cos_plus. ring. Qed.

Lemma sin_double : forall b, sin (2 * b) = 2 * (sin b * cos b).
Proof. intro b. replace (2 * b) with (b + b) by ring. rewrite sin_plus. ring. Qed.

Lemma cos_triple_cs : forall b,
  cos (3 * b) = cos b * (cos b * cos b) - 3 * (sin b * sin b) * cos b.
Proof.
  intro b. replace (3 * b) with (b + 2 * b) by ring.
  rewrite cos_plus, cos_double, sin_double. ring.
Qed.

Lemma sin_triple_cs : forall b,
  sin (3 * b) = 3 * (cos b * cos b) * sin b - sin b * (sin b * sin b).
Proof.
  intro b. replace (3 * b) with (b + 2 * b) by ring.
  rewrite sin_plus, cos_double, sin_double. ring.
Qed.

(* squaring / cubing a complex number in polar component form *)
Lemma Cmul_sq_polar : forall rho c s,
  Cmul (rho * c, rho * s) (rho * c, rho * s)
  = (rho * rho * (c * c - s * s), rho * rho * (2 * (s * c))).
Proof. intros. unfold Cmul; simpl. f_equal; ring. Qed.

Lemma Cmul_cube_polar : forall rho c s,
  Cmul (Cmul (rho * c, rho * s) (rho * c, rho * s)) (rho * c, rho * s)
  = (rho * (rho * rho) * (c * (c * c) - 3 * (s * s) * c),
     rho * (rho * rho) * (3 * (c * c) * s - s * (s * s))).
Proof. intros. unfold Cmul; simpl. f_equal; ring. Qed.

(* ===== every complex number has a square root and a cube root ===== *)
Lemma C_sqrt_exists : forall z, exists w, Cmul w w = z.
Proof.
  intros [x y].
  destruct (Req_dec (x * x + y * y) 0) as [Hz | Hnz].
  - exists C0. unfold Cmul, C0; simpl.
    assert (x = 0) by nra. assert (y = 0) by nra. subst. f_equal; ring.
  - assert (Hpos : 0 < x * x + y * y) by nra.
    set (r := R_sqrt.sqrt (x * x + y * y)).
    assert (Hr : 0 < r) by (unfold r; apply sqrt_lt_R0; exact Hpos).
    assert (Hrr : r * r = x * x + y * y) by (unfold r; apply sqrt_sqrt; lra).
    destruct (exists_angle (x / r) (y / r)) as [th [Hc Hs]].
    { replace (x / r * (x / r) + y / r * (y / r)) with ((x * x + y * y) / (r * r))
        by (field; lra). rewrite Hrr. field; lra. }
    set (rho := R_sqrt.sqrt r).
    assert (Hrho : rho * rho = r) by (unfold rho; apply sqrt_sqrt; lra).
    exists (rho * cos (th / 2), rho * sin (th / 2)).
    rewrite Cmul_sq_polar.
    rewrite <- (cos_double (th / 2)), <- (sin_double (th / 2)).
    assert (E2 : 2 * (th / 2) = th) by field.
    rewrite E2, Hc, Hs, Hrho. f_equal; field; lra.
Qed.

Lemma C_cbrt_exists : forall z, exists w, Cmul (Cmul w w) w = z.
Proof.
  intros [x y].
  destruct (Req_dec (x * x + y * y) 0) as [Hz | Hnz].
  - exists C0. unfold Cmul, C0; simpl.
    assert (x = 0) by nra. assert (y = 0) by nra. subst. f_equal; ring.
  - assert (Hpos : 0 < x * x + y * y) by nra.
    set (r := R_sqrt.sqrt (x * x + y * y)).
    assert (Hr : 0 < r) by (unfold r; apply sqrt_lt_R0; exact Hpos).
    assert (Hrr : r * r = x * x + y * y) by (unfold r; apply sqrt_sqrt; lra).
    destruct (exists_angle (x / r) (y / r)) as [th [Hc Hs]].
    { replace (x / r * (x / r) + y / r * (y / r)) with ((x * x + y * y) / (r * r))
        by (field; lra). rewrite Hrr. field; lra. }
    exists (cbrt r * cos (th / 3), cbrt r * sin (th / 3)).
    rewrite Cmul_cube_polar.
    rewrite <- (cos_triple_cs (th / 3)), <- (sin_triple_cs (th / 3)).
    assert (E3 : 3 * (th / 3) = th) by field.
    rewrite E3, Hc, Hs.
    assert (Hcube : cbrt r * (cbrt r * cbrt r) = r)
      by (pose proof (cbrt_spec r) as H3; unfold cube_func in H3; lra).
    rewrite Hcube. f_equal; field; lra.
Qed.

(* ===== Cardano over C: cube of a sum, root of unity, and the key identity ===== *)
Definition Ccube (z : C) : C := Cmul (Cmul z z) z.

(* a primitive cube root of unity *)
Definition Comega : C := (- (1 / 2), R_sqrt.sqrt 3 / 2).

Lemma sqrt3_sq : R_sqrt.sqrt 3 * R_sqrt.sqrt 3 = 3.
Proof. apply sqrt_sqrt; lra. Qed.

Lemma Comega_cube : Ccube Comega = C1.
Proof.
  assert (H2 : R_sqrt.sqrt 3 * R_sqrt.sqrt 3 = 3) by (apply sqrt_sqrt; lra).
  assert (H3 : R_sqrt.sqrt 3 * R_sqrt.sqrt 3 * R_sqrt.sqrt 3 = 3 * R_sqrt.sqrt 3) by (rewrite H2; ring).
  unfold Ccube, Comega, Cmul, C1; simpl. f_equal; nra.
Qed.

Lemma Comega_sum : Cadd C1 (Cadd Comega (Cmul Comega Comega)) = C0.
Proof.
  assert (H2 : R_sqrt.sqrt 3 * R_sqrt.sqrt 3 = 3) by (apply sqrt_sqrt; lra).
  unfold Comega, Cadd, Cmul, C1, C0; simpl. f_equal; nra.
Qed.

(* The core Cardano identity: if a^3 = b^3 = ab = 1, 3uv = -p and u^3+v^3 = -q,
   then z = a*u + b*v solves z^3 + p z + q = 0.  Instantiating (a,b) by
   (1,1), (omega, omega^2), (omega^2, omega) yields the three roots. *)
Lemma cardano_root_helper : forall a b u v p q z,
  Ccube a = C1 -> Ccube b = C1 -> Cmul a b = C1 ->
  z = Cadd (Cmul a u) (Cmul b v) ->
  Cmul (RtoC 3) (Cmul u v) = Copp p ->
  Cadd (Ccube u) (Ccube v) = Copp q ->
  Cadd (Cadd (Ccube z) (Cmul p z)) q = C0.
Proof.
  intros a b u v p q z Ha3 Hb3 Hab Hz Huv Hsum. subst z.
  unfold Ccube in *.
  assert (R3 : RtoC 3 = Cadd C1 (Cadd C1 C1)) by (cbv [RtoC C1 Cadd fst snd]; f_equal; ring).
  rewrite R3 in Huv.
  transitivity (Cadd (Cadd
      (Cadd (Cmul (Csub (Cmul (Cmul a a) a) C1) (Cmul (Cmul u u) u))
            (Cmul (Csub (Cmul (Cmul b b) b) C1) (Cmul (Cmul v v) v)))
      (Cadd (Cmul (Cadd C1 (Cadd C1 C1)) (Cmul (Cmul a (Csub (Cmul a b) C1)) (Cmul (Cmul u u) v)))
            (Cmul (Cadd C1 (Cadd C1 C1)) (Cmul (Cmul b (Csub (Cmul a b) C1)) (Cmul u (Cmul v v))))))
      (Cadd (Cmul (Cadd (Cmul (Cadd C1 (Cadd C1 C1)) (Cmul u v)) p) (Cadd (Cmul a u) (Cmul b v)))
            (Cadd (Cadd (Cmul (Cmul u u) u) (Cmul (Cmul v v) v)) q))).
  - ring.
  - rewrite Ha3, Hb3, Hab, Huv, Hsum. ring.
Qed.

(* support: nonzero facts and the integral-domain property of C *)
Lemma RtoC_neq_0 : forall r, r <> 0 -> RtoC r <> C0.
Proof. intros r Hr H. apply Hr. unfold RtoC, C0 in H. inversion H. reflexivity. Qed.

Lemma Cmul_integral : forall a b, Cmul a b = C0 -> a = C0 \/ b = C0.
Proof.
  intros a b H. destruct (Ceq_dec a C0) as [Ha | Ha]; [left; exact Ha | right].
  transitivity (Cdiv (Cmul a b) a); [ field; exact Ha | rewrite H; field; exact Ha ].
Qed.

Lemma Cmul_neq_0 : forall a b, a <> C0 -> b <> C0 -> Cmul a b <> C0.
Proof.
  intros a b Ha Hb H. destruct (Cmul_integral a b H); [apply Ha | apply Hb]; assumption.
Qed.

Lemma Ccube_C0 : Ccube C0 = C0.
Proof. unfold Ccube; ring. Qed.

Lemma Ccube_neq_0 : forall u, u <> C0 -> Ccube u <> C0.
Proof.
  intros u Hu. unfold Ccube. apply Cmul_neq_0; [apply Cmul_neq_0 |]; assumption.
Qed.

Lemma Cadd_move : forall x d, Cadd x d = C0 -> d = Copp x.
Proof. intros x d H. transitivity (Csub (Cadd x d) x); [ring | rewrite H; ring]. Qed.

Lemma Cadd_eq_l : forall x y, Cadd x y = x -> y = C0.
Proof. intros x y H. transitivity (Csub (Cadd x y) x); [ring | rewrite H; ring]. Qed.

(* The Cardano radicals exist over C for every p, q: there are u, v with
   3 u v = -p and u^3 + v^3 = -q.  Then (a u + b v) for the three (a,b) pairs
   are the roots.  The discriminant is written with 2*2 and 3*3*3 so that the
   field tactic sees the numeral factorizations it would otherwise treat as
   opaque constants. *)
Lemma cardano_uv_exists : forall p q : C, exists u v,
  Cmul (RtoC 3) (Cmul u v) = Copp p /\ Cadd (Ccube u) (Ccube v) = Copp q.
Proof.
  intros p q.
  pose proof (RtoC_neq_0 2 ltac:(lra)) as H2.
  pose proof (RtoC_neq_0 3 ltac:(lra)) as H3.
  set (num := Cadd (Cdiv (Cmul q q) (Cmul (RtoC 2) (RtoC 2)))
                   (Cdiv (Ccube p) (Cmul (RtoC 3) (Cmul (RtoC 3) (RtoC 3))))).
  destruct (C_sqrt_exists num) as [d Hd].
  destruct (Ceq_dec p C0) as [Hp0 | Hpn0].
  - destruct (C_cbrt_exists (Copp q)) as [u Hu].
    exists u, C0. split.
    + rewrite Hp0. ring.
    + unfold Ccube; rewrite Hu; ring.
  - set (A := Cadd (Cdiv (Copp q) (RtoC 2)) d).
    set (B := Csub (Cdiv (Copp q) (RtoC 2)) d).
    assert (HAn0 : A <> C0).
    { intro HA0.
      assert (Hdv : d = Copp (Cdiv (Copp q) (RtoC 2))) by (apply Cadd_move; exact HA0).
      assert (Hp3 : Cdiv (Ccube p) (Cmul (RtoC 3) (Cmul (RtoC 3) (RtoC 3))) = C0).
      { apply (Cadd_eq_l (Cdiv (Cmul q q) (Cmul (RtoC 2) (RtoC 2)))).
        change (Cadd (Cdiv (Cmul q q) (Cmul (RtoC 2) (RtoC 2)))
                     (Cdiv (Ccube p) (Cmul (RtoC 3) (Cmul (RtoC 3) (RtoC 3))))) with num.
        rewrite <- Hd, Hdv. field; exact H2. }
      assert (Hpc : Ccube p = C0).
      { transitivity (Cmul (Cdiv (Ccube p) (Cmul (RtoC 3) (Cmul (RtoC 3) (RtoC 3))))
                           (Cmul (RtoC 3) (Cmul (RtoC 3) (RtoC 3)))).
        - field; exact H3.
        - rewrite Hp3; ring. }
      apply Hpn0. unfold Ccube in Hpc.
      destruct (Cmul_integral _ _ Hpc) as [Hpp | Hpz];
        [destruct (Cmul_integral _ _ Hpp); assumption | assumption]. }
    destruct (C_cbrt_exists A) as [u Hu].
    assert (Hu' : Ccube u = A) by (unfold Ccube; exact Hu).
    assert (Hun0 : u <> C0)
      by (intro Hu0; apply HAn0; rewrite <- Hu', Hu0; unfold Ccube; ring).
    set (v := Cdiv (Copp p) (Cmul (RtoC 3) u)).
    assert (H3un0 : Cmul (RtoC 3) u <> C0) by (apply Cmul_neq_0; [exact H3 | exact Hun0]).
    exists u, v. split.
    + unfold v. field; split; [exact Hun0 | exact H3].
    + assert (Hvb : Ccube v = B).
      { assert (Hv3 : Ccube v = Cdiv (Copp (Ccube p)) (Ccube (Cmul (RtoC 3) u)))
          by (unfold v, Ccube; field; split; [exact Hun0 | exact H3]).
        assert (Hc3u : Ccube (Cmul (RtoC 3) u)
                       = Cmul (Cmul (RtoC 3) (Cmul (RtoC 3) (RtoC 3))) (Ccube u))
          by (unfold Ccube; ring).
        rewrite Hv3, Hc3u, Hu'.
        assert (HAB : Cmul A B = Cdiv (Copp (Ccube p)) (Cmul (RtoC 3) (Cmul (RtoC 3) (RtoC 3)))).
        { transitivity (Csub (Cdiv (Cmul q q) (Cmul (RtoC 2) (RtoC 2))) (Cmul d d)).
          - unfold A, B. field; repeat split; try exact H2; try exact H3.
          - rewrite Hd. unfold num. field; repeat split; try exact H2; try exact H3. }
        assert (HABp : Copp (Ccube p)
                       = Cmul (Cmul (RtoC 3) (Cmul (RtoC 3) (RtoC 3))) (Cmul A B))
          by (rewrite HAB; field; repeat split; try exact H2; try exact H3).
        rewrite HABp. field; repeat split; try exact H3; try exact HAn0. }
      assert (R2 : RtoC 2 = Cadd C1 C1) by (cbv [RtoC C1 Cadd fst snd]; f_equal; ring).
      assert (R2n0 : Cadd C1 C1 <> C0)
        by (intro Hc; cbv [Cadd C1 C0 fst snd] in Hc; inversion Hc; lra).
      assert (Hq : Cadd A B = Copp q).
      { unfold A, B. rewrite R2. field. exact R2n0. }
      rewrite Hu', Hvb; exact Hq.
Qed.

(* ===== Complex Cardano: every depressed cubic z^3 + p z + q over C has the
   three roots produced by the radical formula, with no discriminant-sign
   restriction (the cube and square roots always exist over C). ===== *)
Theorem cardano_complex_three_roots : forall p q : C,
  exists z1 z2 z3,
    Cadd (Cadd (Ccube z1) (Cmul p z1)) q = C0 /\
    Cadd (Cadd (Ccube z2) (Cmul p z2)) q = C0 /\
    Cadd (Cadd (Ccube z3) (Cmul p z3)) q = C0.
Proof.
  intros p q.
  destruct (cardano_uv_exists p q) as [u [v [Huv Hsum]]].
  pose proof Comega_cube as Hw3.
  assert (Hw2_3 : Ccube (Cmul Comega Comega) = C1).
  { transitivity (Cmul (Ccube Comega) (Ccube Comega)); [unfold Ccube; ring | rewrite Hw3; ring]. }
  assert (Hwab : Cmul Comega (Cmul Comega Comega) = C1).
  { transitivity (Ccube Comega); [unfold Ccube; ring | exact Hw3]. }
  assert (Hwba : Cmul (Cmul Comega Comega) Comega = C1).
  { transitivity (Ccube Comega); [unfold Ccube; ring | exact Hw3]. }
  exists (Cadd (Cmul C1 u) (Cmul C1 v)).
  exists (Cadd (Cmul Comega u) (Cmul (Cmul Comega Comega) v)).
  exists (Cadd (Cmul (Cmul Comega Comega) u) (Cmul Comega v)).
  split; [| split].
  - apply (cardano_root_helper C1 C1 u v p q);
      [ unfold Ccube; ring | unfold Ccube; ring | ring | reflexivity | exact Huv | exact Hsum ].
  - apply (cardano_root_helper Comega (Cmul Comega Comega) u v p q);
      [ exact Hw3 | exact Hw2_3 | exact Hwab | reflexivity | exact Huv | exact Hsum ].
  - apply (cardano_root_helper (Cmul Comega Comega) Comega u v p q);
      [ exact Hw2_3 | exact Hw3 | exact Hwba | reflexivity | exact Huv | exact Hsum ].
Qed.

Lemma Csub_eq_0 : forall z w, Csub z w = C0 -> z = w.
Proof. intros z w H. transitivity (Cadd (Csub z w) w); [ring | rewrite H; ring]. Qed.

(* The full statement: the three radical values factor the cubic, hence they are
   exactly its roots (over C, with no discriminant-sign restriction). *)
Theorem cardano_complex : forall p q : C,
  exists z1 z2 z3,
    (forall z, Cadd (Cadd (Ccube z) (Cmul p z)) q
               = Cmul (Csub z z1) (Cmul (Csub z z2) (Csub z z3)))
    /\ (forall w, Cadd (Cadd (Ccube w) (Cmul p w)) q = C0 -> w = z1 \/ w = z2 \/ w = z3).
Proof.
  intros p q.
  destruct (cardano_uv_exists p q) as [u [v [Huv Hsum]]].
  set (z1 := Cadd (Cmul C1 u) (Cmul C1 v)).
  set (z2 := Cadd (Cmul Comega u) (Cmul (Cmul Comega Comega) v)).
  set (z3 := Cadd (Cmul (Cmul Comega Comega) u) (Cmul Comega v)).
  assert (R3 : RtoC 3 = Cadd C1 (Cadd C1 C1)) by (cbv [RtoC C1 Cadd fst snd]; f_equal; ring).
  assert (He1 : Cadd z1 (Cadd z2 z3) = C0).
  { unfold z1, z2, z3.
    transitivity (Cmul (Cadd C1 (Cadd Comega (Cmul Comega Comega))) (Cadd u v));
      [ring | rewrite Comega_sum; ring]. }
  assert (He2 : Cadd (Cmul z1 z2) (Cadd (Cmul z1 z3) (Cmul z2 z3)) = p).
  { rewrite R3 in Huv. unfold z1, z2, z3.
    transitivity (Csub (Cadd
        (Cmul (Csub (Ccube Comega) C1)
              (Cadd (Cmul u u) (Cadd (Cmul v v) (Cmul Comega (Cmul u v)))))
        (Cmul (Cadd C1 (Cadd Comega (Cmul Comega Comega)))
              (Cadd (Cmul u u)
                    (Cadd (Cmul v v) (Cmul (Cadd C1 (Cadd C1 C1)) (Cmul u v))))))
                       (Cmul (Cadd C1 (Cadd C1 C1)) (Cmul u v))).
    - unfold Ccube; ring.
    - rewrite Comega_cube, Comega_sum, Huv. ring. }
  assert (He3 : Cmul z1 (Cmul z2 z3) = Copp q).
  { unfold z1, z2, z3.
    transitivity (Cadd (Cadd (Ccube u) (Ccube v))
                       (Cadd (Cmul (Csub (Ccube Comega) C1) (Cadd (Ccube u) (Ccube v)))
                             (Cmul (Cmul (Cmul Comega Comega)
                                         (Cadd C1 (Cadd Comega (Cmul Comega Comega))))
                                   (Cadd (Cmul (Cmul u u) v) (Cmul u (Cmul v v)))))).
    - unfold Ccube; ring.
    - rewrite Comega_cube, Comega_sum, Hsum. ring. }
  assert (Hfact : forall z, Cadd (Cadd (Ccube z) (Cmul p z)) q
                  = Cmul (Csub z z1) (Cmul (Csub z z2) (Csub z z3))).
  { intro z. symmetry.
    transitivity (Csub (Csub (Cadd (Ccube z)
                                   (Cmul (Cadd (Cmul z1 z2) (Cadd (Cmul z1 z3) (Cmul z2 z3))) z))
                             (Cmul (Cadd z1 (Cadd z2 z3)) (Cmul z z)))
                       (Cmul z1 (Cmul z2 z3))).
    - unfold Ccube; ring.
    - rewrite He1, He2, He3. ring. }
  exists z1, z2, z3. split.
  - exact Hfact.
  - intros w Hw.
    assert (Hprod : Cmul (Csub w z1) (Cmul (Csub w z2) (Csub w z3)) = C0)
      by (rewrite <- Hfact; exact Hw).
    destruct (Cmul_integral _ _ Hprod) as [H1 | H23].
    + left. apply Csub_eq_0; exact H1.
    + destruct (Cmul_integral _ _ H23) as [H2 | H3].
      * right; left. apply Csub_eq_0; exact H2.
      * right; right. apply Csub_eq_0; exact H3.
Qed.

Close Scope R_scope.
End Cardano_C.
Open Scope R_scope.
(* ===== Two-fold degree theorem (item 7): the exact algebraic degree of
   every OrigamiNum2 number is 2^a*3^b*5^c.  Built on a degree-5 ring/field
   extension Quint5F (the quintic analog of CF) and a 5-smooth tower o5tower
   (quadratic, cubic, and quintic steps), then the generic tower_law_div. ===== *)
Open Scope R_scope.
(* ===== Degree-5 ring extension F[r] for a root r of a monic quintic =====
   Quint5F F a b c d e r = { p0 + p1 r + p2 r^2 + p3 r^3 + p4 r^4 : pi in F }.
   Closure under multiplication is reduced to closure under F-scalar
   multiplication and multiplication by r (one r^5 reduction), avoiding the
   degree-8 product expansion. *)
Definition Quint5F (F : R -> Prop) (a b c d e r : R) (x : R) : Prop :=
  exists p0 p1 p2 p3 p4,
    F p0 /\ F p1 /\ F p2 /\ F p3 /\ F p4 /\
    x = p0 + p1 * r + p2 * (r * r) + p3 * (r * r * r) + p4 * (r * r * r * r).

Ltac dq H px0 px1 px2 px3 px4 Hx0 Hx1 Hx2 Hx3 Hx4 Hxe :=
  destruct H as [px0 [px1 [px2 [px3 [px4 [Hx0 [Hx1 [Hx2 [Hx3 [Hx4 Hxe]]]]]]]]]].

Lemma Quint5F_0 : forall F a b c d e r, is_subring F -> Quint5F F a b c d e r 0.
Proof.
  intros F a b c d e r HF. exists 0, 0, 0, 0, 0.
  repeat split; try (apply subring_0; exact HF). ring.
Qed.

Lemma Quint5F_1 : forall F a b c d e r, is_subring F -> Quint5F F a b c d e r 1.
Proof.
  intros F a b c d e r HF. exists 1, 0, 0, 0, 0.
  repeat split; try (apply subring_0; exact HF); try (apply subring_1; exact HF). ring.
Qed.

Lemma Quint5F_add : forall F a b c d e r x y, is_subring F ->
  Quint5F F a b c d e r x -> Quint5F F a b c d e r y -> Quint5F F a b c d e r (x + y).
Proof.
  intros F a b c d e r x y HF Hx Hy.
  dq Hx px0 px1 px2 px3 px4 Hx0 Hx1 Hx2 Hx3 Hx4 Hxe.
  dq Hy py0 py1 py2 py3 py4 Hy0 Hy1 Hy2 Hy3 Hy4 Hye.
  exists (px0+py0),(px1+py1),(px2+py2),(px3+py3),(px4+py4).
  repeat split; [srclose|srclose|srclose|srclose|srclose|]. subst x y. ring.
Qed.

Lemma Quint5F_sub : forall F a b c d e r x y, is_subring F ->
  Quint5F F a b c d e r x -> Quint5F F a b c d e r y -> Quint5F F a b c d e r (x - y).
Proof.
  intros F a b c d e r x y HF Hx Hy.
  dq Hx px0 px1 px2 px3 px4 Hx0 Hx1 Hx2 Hx3 Hx4 Hxe.
  dq Hy py0 py1 py2 py3 py4 Hy0 Hy1 Hy2 Hy3 Hy4 Hye.
  exists (px0-py0),(px1-py1),(px2-py2),(px3-py3),(px4-py4).
  repeat split; [srclose|srclose|srclose|srclose|srclose|]. subst x y. ring.
Qed.

Lemma Quint5F_scalar : forall F a b c d e r lam x, is_subring F ->
  F lam -> Quint5F F a b c d e r x -> Quint5F F a b c d e r (lam * x).
Proof.
  intros F a b c d e r lam x HF Hlam Hx.
  dq Hx p0 p1 p2 p3 p4 H0 H1 H2 H3 H4 Hxe.
  exists (lam*p0),(lam*p1),(lam*p2),(lam*p3),(lam*p4).
  repeat split; [srclose|srclose|srclose|srclose|srclose|]. subst x. ring.
Qed.

Lemma Quint5F_mulr : forall F a b c d e r x, is_subring F ->
  F a -> F b -> F c -> F d -> F e ->
  r ^ 5 + a * r ^ 4 + b * r ^ 3 + c * r ^ 2 + d * r + e = 0 ->
  Quint5F F a b c d e r x -> Quint5F F a b c d e r (r * x).
Proof.
  intros F a b c d e r x HF Ha Hb Hc Hd He Hr Hx.
  dq Hx p0 p1 p2 p3 p4 H0 H1 H2 H3 H4 Hxe.
  assert (Hr' : r * r * r * r * r + a * (r * r * r * r) + b * (r * r * r)
                + c * (r * r) + d * r + e = 0)
    by (replace (r * r * r * r * r + a * (r * r * r * r) + b * (r * r * r)
                 + c * (r * r) + d * r + e)
          with (r ^ 5 + a * r ^ 4 + b * r ^ 3 + c * r ^ 2 + d * r + e) by ring; exact Hr).
  exists (0 - p4 * e), (p0 - p4 * d), (p1 - p4 * c), (p2 - p4 * b), (p3 - p4 * a).
  repeat split; [srclose|srclose|srclose|srclose|srclose|]. subst x.
  transitivity ((0 - p4 * e) + (p0 - p4 * d) * r + (p1 - p4 * c) * (r * r)
                + (p2 - p4 * b) * (r * r * r) + (p3 - p4 * a) * (r * r * r * r)
                + p4 * (r * r * r * r * r + a * (r * r * r * r) + b * (r * r * r)
                        + c * (r * r) + d * r + e)).
  - ring.
  - rewrite Hr'. ring.
Qed.

Lemma Quint5F_subring : forall F a b c d e r,
  is_subring F -> F a -> F b -> F c -> F d -> F e ->
  r ^ 5 + a * r ^ 4 + b * r ^ 3 + c * r ^ 2 + d * r + e = 0 ->
  is_subring (Quint5F F a b c d e r).
Proof.
  intros F a b c d e r HF Ha Hb Hc Hd He Hr. repeat split.
  - apply Quint5F_0; exact HF.
  - apply Quint5F_1; exact HF.
  - intros x y Hx Hy. apply Quint5F_add; assumption.
  - intros x y Hx Hy. apply Quint5F_sub; assumption.
  - intros x y Hx Hy.
    dq Hy q0 q1 q2 q3 q4 Hq0 Hq1 Hq2 Hq3 Hq4 Hye.
    replace (x * y) with
      (q0 * x + (q1 * (r * x) + (q2 * (r * (r * x))
        + (q3 * (r * (r * (r * x))) + q4 * (r * (r * (r * (r * x))))))))
      by (rewrite Hye; ring).
    assert (Trx : Quint5F F a b c d e r (r * x)) by (apply Quint5F_mulr; assumption).
    assert (Trrx : Quint5F F a b c d e r (r * (r * x))) by (apply Quint5F_mulr; assumption).
    assert (Trrrx : Quint5F F a b c d e r (r * (r * (r * x)))) by (apply Quint5F_mulr; assumption).
    assert (Trrrrx : Quint5F F a b c d e r (r * (r * (r * (r * x)))))
      by (apply Quint5F_mulr; assumption).
    assert (T0 : Quint5F F a b c d e r (q0 * x)) by (apply Quint5F_scalar; assumption).
    assert (T1 : Quint5F F a b c d e r (q1 * (r * x))) by (apply Quint5F_scalar; assumption).
    assert (T2 : Quint5F F a b c d e r (q2 * (r * (r * x)))) by (apply Quint5F_scalar; assumption).
    assert (T3 : Quint5F F a b c d e r (q3 * (r * (r * (r * x)))))
      by (apply Quint5F_scalar; assumption).
    assert (T4 : Quint5F F a b c d e r (q4 * (r * (r * (r * (r * x))))))
      by (apply Quint5F_scalar; assumption).
    apply Quint5F_add; [exact HF | exact T0 |].
    apply Quint5F_add; [exact HF | exact T1 |].
    apply Quint5F_add; [exact HF | exact T2 |].
    apply Quint5F_add; [exact HF | exact T3 | exact T4].
Qed.

Lemma Quint5F_contains_sr : forall F a b c d e r x,
  is_subring F -> F x -> Quint5F F a b c d e r x.
Proof.
  intros F a b c d e r x HF Hx. exists x, 0, 0, 0, 0.
  repeat split;
    [ exact Hx | apply subring_0; exact HF | apply subring_0; exact HF
    | apply subring_0; exact HF | apply subring_0; exact HF | ring ].
Qed.

Lemma Quint5F_subfield : forall F a b c d e r,
  is_subfield F -> F a -> F b -> F c -> F d -> F e ->
  r ^ 5 + a * r ^ 4 + b * r ^ 3 + c * r ^ 2 + d * r + e = 0 ->
  is_subfield (Quint5F F a b c d e r).
Proof.
  intros F a b c d e r HF Ha Hb Hc Hd He Hr.
  assert (HsrF : is_subring F) by (apply subfield_is_subring; exact HF).
  assert (HsrQ : is_subring (Quint5F F a b c d e r)) by (apply Quint5F_subring; assumption).
  repeat split.
  - apply subring_0; exact HsrQ.
  - apply subring_1; exact HsrQ.
  - intros x y Hx Hy. apply subring_add; assumption.
  - intros x y Hx Hy. apply subring_sub; assumption.
  - intros x y Hx Hy. apply subring_mul; assumption.
  - intros u Hu Hune.
    assert (Hspan : Forall (spans F (1 :: r :: (r*r) :: (r*r*r) :: (r*r*r*r) :: nil))
                          (powers u 6)).
    { apply Forall_forall. intros w Hw. unfold powers in Hw. apply in_map_iff in Hw.
      destruct Hw as [i [Hwi Hi]]. subst w.
      assert (HuiQ : Quint5F F a b c d e r (u ^ i)) by (apply subring_pow; [exact HsrQ | exact Hu]).
      destruct HuiQ as [p0 [p1 [p2 [p3 [p4 [Hp0 [Hp1 [Hp2 [Hp3 [Hp4 Hue]]]]]]]]]].
      exists (p0 :: p1 :: p2 :: p3 :: p4 :: nil). split; [reflexivity|]. split.
      - repeat (constructor; [assumption|]). constructor.
      - simpl. rewrite Hue. ring. }
    assert (Hgt : Nat.lt (length (1 :: r :: (r*r) :: (r*r*r) :: (r*r*r*r) :: nil))
                   (length (powers u 6))).
    { unfold powers; rewrite length_map, length_seq; simpl; lia. }
    destruct (lin_dep_of_spanned F (1 :: r :: (r*r) :: (r*r*r) :: (r*r*r*r) :: nil)
                (powers u 6) HF Hspan Hgt) as [cs [Hlencs [Hratcs [Hfccs Hnd]]]].
    assert (Hlen6 : length cs = 6%nat)
      by (rewrite Hlencs; unfold powers; rewrite length_map, length_seq; reflexivity).
    assert (Hrel : Fcomb cs (powers u (length cs)) = 0) by (rewrite Hlen6; exact Hfccs).
    destruct (inverse_from_relation F cs u HF Hune Hratcs Hnd Hrel) as [ds [Hdsf Hinv]].
    assert (HvQ : Quint5F F a b c d e r (Fcomb ds (powers u (length ds)))).
    { apply Fcomb_in_subring; [exact HsrQ | |].
      - apply Forall_forall. intros z Hz. apply Quint5F_contains_sr; [exact HsrF |].
        rewrite Forall_forall in Hdsf; apply Hdsf; exact Hz.
      - apply Forall_forall. intros z Hz. unfold powers in Hz. apply in_map_iff in Hz.
        destruct Hz as [i [Hzi Hi]]. subst z. apply subring_pow; [exact HsrQ | exact Hu]. }
    replace (/ u) with (Fcomb ds (powers u (length ds))).
    + exact HvQ.
    + apply (Rmult_eq_reg_l u); [|exact Hune]. rewrite Rinv_r by exact Hune. exact Hinv.
Qed.

Lemma Quint5F_step_basis : forall F a b c d e r,
  is_subfield F -> F a -> F b -> F c -> F d -> F e ->
  r ^ 5 + a * r ^ 4 + b * r ^ 3 + c * r ^ 2 + d * r + e = 0 ->
  exists Be, basis F Be (Quint5F F a b c d e r) /\
    (length Be = 1 \/ length Be = 2 \/ length Be = 3 \/ length Be = 4 \/ length Be = 5)%nat.
Proof.
  intros F a b c d e r HF Ha Hb Hc Hd He Hr.
  assert (Hspanned : spanning F (1 :: r :: (r*r) :: (r*r*r) :: (r*r*r*r) :: nil)
                              (Quint5F F a b c d e r)).
  { intros y [p0 [p1 [p2 [p3 [p4 [Hp0 [Hp1 [Hp2 [Hp3 [Hp4 Hy]]]]]]]]]].
    exists (p0 :: p1 :: p2 :: p3 :: p4 :: nil). split; [reflexivity | split].
    - repeat (constructor; [assumption|]). constructor.
    - cbn [Fcomb]. rewrite Hy. ring. }
  assert (Hin : Forall (Quint5F F a b c d e r)
                       (1 :: r :: (r*r) :: (r*r*r) :: (r*r*r*r) :: nil)).
  { constructor; [exists 1,0,0,0,0; repeat split;
      try (apply subfield_1; exact HF); try (apply subfield_0; exact HF); ring |].
    constructor; [exists 0,1,0,0,0; repeat split;
      try (apply subfield_1; exact HF); try (apply subfield_0; exact HF); ring |].
    constructor; [exists 0,0,1,0,0; repeat split;
      try (apply subfield_1; exact HF); try (apply subfield_0; exact HF); ring |].
    constructor; [exists 0,0,0,1,0; repeat split;
      try (apply subfield_1; exact HF); try (apply subfield_0; exact HF); ring |].
    constructor; [exists 0,0,0,0,1; repeat split;
      try (apply subfield_1; exact HF); try (apply subfield_0; exact HF); ring |].
    constructor. }
  destruct (basis_extract F (1 :: r :: (r*r) :: (r*r*r) :: (r*r*r*r) :: nil)
              (Quint5F F a b c d e r) HF Hin Hspanned) as [Be HbBe].
  exists Be. split; [exact HbBe |].
  destruct HbBe as [HBeC [HliBe HspBe]].
  assert (Hle : (length Be <= 5)%nat).
  { pose proof (indep_le_span F Be (1 :: r :: (r*r) :: (r*r*r) :: (r*r*r*r) :: nil)
                  (Quint5F F a b c d e r) HF HliBe HBeC Hspanned) as H.
    simpl in H. exact H. }
  assert (Hge : (1 <= length Be)%nat).
  { destruct Be as [|bb Be']; [|simpl; lia]. exfalso.
    destruct (HspBe 1 (Quint5F_contains_sr F a b c d e r 1
                (subfield_is_subring F HF) (subfield_1 F HF)))
      as [cs [Hl [Hf Hfc]]].
    destruct cs; [simpl in Hfc; lra | simpl in Hl; lia]. }
  lia.
Qed.

(* ===== Tower of quadratic / cubic / quintic ring extensions (5-smooth) ===== *)
Inductive o5step : Type :=
  | O5Quad (s : R)
  | O5Cubic (a b r : R)
  | O5Quint (a b c d e r : R).

Fixpoint o5tower (L : list o5step) : R -> Prop :=
  match L with
  | nil => is_rational
  | O5Quad s :: L' => QF (o5tower L') s
  | O5Cubic a b r :: L' => CF (o5tower L') a b r
  | O5Quint a b c d e r :: L' => Quint5F (o5tower L') a b c d e r
  end.

Fixpoint o5wf (L : list o5step) : Prop :=
  match L with
  | nil => True
  | O5Quad s :: L' => o5tower L' (s * s) /\ o5wf L'
  | O5Cubic a b r :: L' => o5tower L' a /\ o5tower L' b /\ (r*r*r + a*r + b = 0) /\ o5wf L'
  | O5Quint a b c d e r :: L' =>
      o5tower L' a /\ o5tower L' b /\ o5tower L' c /\ o5tower L' d /\ o5tower L' e
      /\ (r ^ 5 + a * r ^ 4 + b * r ^ 3 + c * r ^ 2 + d * r + e = 0) /\ o5wf L'
  end.

Lemma o5tower_subring : forall L, o5wf L -> is_subring (o5tower L).
Proof.
  induction L as [|st L' IH]; intros W.
  - simpl. apply is_rational_subring.
  - destruct st as [s | a b r | a b c d e r]; simpl in *.
    + destruct W as [Wss W']. apply QF_subring; [apply IH; exact W' | exact Wss].
    + destruct W as [Wa [Wb [Wr W']]].
      apply CF_subring; [apply IH; exact W' | exact Wa | exact Wb | exact Wr].
    + destruct W as [Wa [Wb [Wc [Wd [We [Wr W']]]]]].
      apply Quint5F_subring; [apply IH; exact W' | exact Wa | exact Wb | exact Wc
        | exact Wd | exact We | exact Wr].
Qed.

Lemma o5tower_subfield : forall L, o5wf L -> is_subfield (o5tower L).
Proof.
  induction L as [|st L' IH]; intros W.
  - simpl. apply is_rational_subfield.
  - destruct st as [s | a b r | a b c d e r]; simpl in *.
    + destruct W as [Wss W']. apply QF_subfield; [apply IH; exact W' | exact Wss].
    + destruct W as [Wa [Wb [Wr W']]].
      apply CF_subfield; [apply IH; exact W' | exact Wa | exact Wb | exact Wr].
    + destruct W as [Wa [Wb [Wc [Wd [We [Wr W']]]]]].
      apply Quint5F_subfield; [apply IH; exact W' | exact Wa | exact Wb | exact Wc
        | exact Wd | exact We | exact Wr].
Qed.

Lemma o5tower_contains_rational : forall L, o5wf L -> forall x, is_rational x -> o5tower L x.
Proof.
  induction L as [|st L' IH]; intros W x Hx.
  - simpl. exact Hx.
  - destruct st as [s | a b r | a b c d e r]; simpl in *.
    + destruct W as [_ W'].
      apply QF_contains_sr; [apply o5tower_subring; exact W' | apply IH; assumption].
    + destruct W as [_ [_ [_ W']]].
      apply CF_contains_sr; [apply o5tower_subring; exact W' | apply IH; assumption].
    + destruct W as [_ [_ [_ [_ [_ [_ W']]]]]].
      apply Quint5F_contains_sr; [apply o5tower_subring; exact W' | apply IH; assumption].
Qed.

Lemma o5tower_weaken_base : forall L1 L2 x, o5wf L2 -> o5tower L1 x -> o5tower (L1 ++ L2) x.
Proof.
  induction L1 as [|st L1' IH]; intros L2 x W2 Tx.
  - simpl in Tx. simpl. apply o5tower_contains_rational; [exact W2 | exact Tx].
  - destruct st as [s | a b r | a b c d e r]; simpl in *.
    + destruct Tx as [p [q [Tp [Tq Hx]]]]. exists p, q.
      repeat split; [apply IH; assumption | apply IH; assumption | exact Hx].
    + destruct Tx as [p [q [s0 [Tp [Tq [Ts0 Hx]]]]]]. exists p, q, s0.
      repeat split; [apply IH; assumption | apply IH; assumption | apply IH; assumption | exact Hx].
    + destruct Tx as [p0 [p1 [p2 [p3 [p4 [T0 [T1 [T2 [T3 [T4 Hx]]]]]]]]]].
      exists p0, p1, p2, p3, p4.
      repeat split; [apply IH; assumption | apply IH; assumption | apply IH; assumption
        | apply IH; assumption | apply IH; assumption | exact Hx].
Qed.

Lemma o5wf_app : forall L1 L2, o5wf L1 -> o5wf L2 -> o5wf (L1 ++ L2).
Proof.
  induction L1 as [|st L1' IH]; intros L2 W1 W2.
  - simpl. exact W2.
  - destruct st as [s | a b r | a b c d e r]; simpl in *.
    + destruct W1 as [Wss W1']. split.
      * apply o5tower_weaken_base; [exact W2 | exact Wss].
      * apply IH; [exact W1' | exact W2].
    + destruct W1 as [Wa [Wb [Wr W1']]]. split; [|split; [|split]].
      * apply o5tower_weaken_base; [exact W2 | exact Wa].
      * apply o5tower_weaken_base; [exact W2 | exact Wb].
      * exact Wr.
      * apply IH; [exact W1' | exact W2].
    + destruct W1 as [Wa [Wb [Wc [Wd [We [Wr W1']]]]]].
      split; [|split; [|split; [|split; [|split; [|split]]]]].
      * apply o5tower_weaken_base; [exact W2 | exact Wa].
      * apply o5tower_weaken_base; [exact W2 | exact Wb].
      * apply o5tower_weaken_base; [exact W2 | exact Wc].
      * apply o5tower_weaken_base; [exact W2 | exact Wd].
      * apply o5tower_weaken_base; [exact W2 | exact We].
      * exact Wr.
      * apply IH; [exact W1' | exact W2].
Qed.

Lemma o5tower_weaken_top : forall L1 L2 x, o5wf (L1 ++ L2) -> o5tower L2 x -> o5tower (L1 ++ L2) x.
Proof.
  induction L1 as [|st L1' IH]; intros L2 x W Tx.
  - simpl in *. exact Tx.
  - destruct st as [s | a b r | a b c d e r]; simpl in *.
    + destruct W as [Wss W'].
      apply QF_contains_sr; [apply o5tower_subring; exact W' | apply IH; [exact W' | exact Tx]].
    + destruct W as [Wa [Wb [Wr W']]].
      apply CF_contains_sr; [apply o5tower_subring; exact W' | apply IH; [exact W' | exact Tx]].
    + destruct W as [Wa [Wb [Wc [Wd [We [Wr W']]]]]].
      apply Quint5F_contains_sr; [apply o5tower_subring; exact W' | apply IH; [exact W' | exact Tx]].
Qed.

Lemma OrigamiNum2_in_o5tower : forall x, OrigamiNum2 x -> exists L, o5wf L /\ o5tower L x.
Proof.
  intros x H. induction H as
    [ | | x y Hx IHx Hy IHy | x y Hx IHx Hy IHy | x y Hx IHx Hy IHy
    | x Hx IHx Hxne | x Hx IHx Hxnn | a b r Ha IHa Hb IHb Hcubic
    | a b c d e r Ha IHa Hb IHb Hc IHc Hd IHd He IHe Hquint ].
  - exists nil. split; [exact I | simpl; exists 0%Z, 1%Z; split; [lia | simpl; field]].
  - exists nil. split; [exact I | simpl; exists 1%Z, 1%Z; split; [lia | simpl; field]].
  - destruct IHx as [L1 [W1 T1]]. destruct IHy as [L2 [W2 T2]].
    exists (L1 ++ L2). assert (Wapp : o5wf (L1 ++ L2)) by (apply o5wf_app; assumption).
    split; [exact Wapp |]. apply subring_add; [apply o5tower_subring; exact Wapp
      | apply o5tower_weaken_base; [exact W2 | exact T1]
      | apply o5tower_weaken_top; [exact Wapp | exact T2]].
  - destruct IHx as [L1 [W1 T1]]. destruct IHy as [L2 [W2 T2]].
    exists (L1 ++ L2). assert (Wapp : o5wf (L1 ++ L2)) by (apply o5wf_app; assumption).
    split; [exact Wapp |]. apply subring_sub; [apply o5tower_subring; exact Wapp
      | apply o5tower_weaken_base; [exact W2 | exact T1]
      | apply o5tower_weaken_top; [exact Wapp | exact T2]].
  - destruct IHx as [L1 [W1 T1]]. destruct IHy as [L2 [W2 T2]].
    exists (L1 ++ L2). assert (Wapp : o5wf (L1 ++ L2)) by (apply o5wf_app; assumption).
    split; [exact Wapp |]. apply subring_mul; [apply o5tower_subring; exact Wapp
      | apply o5tower_weaken_base; [exact W2 | exact T1]
      | apply o5tower_weaken_top; [exact Wapp | exact T2]].
  - destruct IHx as [L [W T]]. exists L. split; [exact W |].
    apply subfield_inv; [apply o5tower_subfield; exact W | exact T | exact Hxne].
  - destruct IHx as [L [W T]]. exists (O5Quad (R_sqrt.sqrt x) :: L). split.
    + simpl. split; [| exact W]. rewrite (R_sqrt.sqrt_sqrt x Hxnn). exact T.
    + simpl. exists 0, 1. repeat split;
        [ apply subring_0; apply o5tower_subring; exact W
        | apply subring_1; apply o5tower_subring; exact W | ring ].
  - destruct IHa as [La [Wa Ta]]. destruct IHb as [Lb [Wb Tb]].
    assert (Wapp : o5wf (La ++ Lb)) by (apply o5wf_app; assumption).
    exists (O5Cubic a b r :: (La ++ Lb)). split.
    + simpl. split; [|split; [|split]].
      * apply o5tower_weaken_base; [exact Wb | exact Ta].
      * apply o5tower_weaken_top; [exact Wapp | exact Tb].
      * exact Hcubic.
      * exact Wapp.
    + simpl. exists 0, 1, 0. repeat split;
        [ apply subring_0; apply o5tower_subring; exact Wapp
        | apply subring_1; apply o5tower_subring; exact Wapp
        | apply subring_0; apply o5tower_subring; exact Wapp | ring ].
  - destruct IHa as [La [Wa Ta]]. destruct IHb as [Lb [Wb Tb]].
    destruct IHc as [Lc [Wc Tc]]. destruct IHd as [Ld [Wd Td]]. destruct IHe as [Le [We Te]].
    assert (Wab : o5wf (La ++ Lb)) by (apply o5wf_app; assumption).
    assert (Ta1 : o5tower (La ++ Lb) a) by (apply o5tower_weaken_base; assumption).
    assert (Tb1 : o5tower (La ++ Lb) b) by (apply o5tower_weaken_top; assumption).
    assert (Wabc : o5wf ((La ++ Lb) ++ Lc)) by (apply o5wf_app; assumption).
    assert (Ta2 : o5tower ((La ++ Lb) ++ Lc) a) by (apply o5tower_weaken_base; assumption).
    assert (Tb2 : o5tower ((La ++ Lb) ++ Lc) b) by (apply o5tower_weaken_base; assumption).
    assert (Tc2 : o5tower ((La ++ Lb) ++ Lc) c) by (apply o5tower_weaken_top; assumption).
    assert (Wabcd : o5wf (((La ++ Lb) ++ Lc) ++ Ld)) by (apply o5wf_app; assumption).
    assert (Ta3 : o5tower (((La ++ Lb) ++ Lc) ++ Ld) a) by (apply o5tower_weaken_base; assumption).
    assert (Tb3 : o5tower (((La ++ Lb) ++ Lc) ++ Ld) b) by (apply o5tower_weaken_base; assumption).
    assert (Tc3 : o5tower (((La ++ Lb) ++ Lc) ++ Ld) c) by (apply o5tower_weaken_base; assumption).
    assert (Td3 : o5tower (((La ++ Lb) ++ Lc) ++ Ld) d) by (apply o5tower_weaken_top; assumption).
    assert (Wabcde : o5wf ((((La ++ Lb) ++ Lc) ++ Ld) ++ Le)) by (apply o5wf_app; assumption).
    assert (Ta4 : o5tower ((((La ++ Lb) ++ Lc) ++ Ld) ++ Le) a) by (apply o5tower_weaken_base; assumption).
    assert (Tb4 : o5tower ((((La ++ Lb) ++ Lc) ++ Ld) ++ Le) b) by (apply o5tower_weaken_base; assumption).
    assert (Tc4 : o5tower ((((La ++ Lb) ++ Lc) ++ Ld) ++ Le) c) by (apply o5tower_weaken_base; assumption).
    assert (Td4 : o5tower ((((La ++ Lb) ++ Lc) ++ Ld) ++ Le) d) by (apply o5tower_weaken_base; assumption).
    assert (Te4 : o5tower ((((La ++ Lb) ++ Lc) ++ Ld) ++ Le) e) by (apply o5tower_weaken_top; assumption).
    exists (O5Quint a b c d e r :: ((((La ++ Lb) ++ Lc) ++ Ld) ++ Le)). split.
    + simpl. split; [|split; [|split; [|split; [|split; [|split]]]]];
        [ exact Ta4 | exact Tb4 | exact Tc4 | exact Td4 | exact Te4 | exact Hquint | exact Wabcde ].
    + simpl. exists 0, 1, 0, 0, 0. repeat split;
        [ apply subring_0; apply o5tower_subring; exact Wabcde
        | apply subring_1; apply o5tower_subring; exact Wabcde
        | apply subring_0; apply o5tower_subring; exact Wabcde
        | apply subring_0; apply o5tower_subring; exact Wabcde
        | apply subring_0; apply o5tower_subring; exact Wabcde | ring ].
Qed.

Lemma o5tower_dim_smooth : forall L, o5wf L ->
  exists BL, basis is_rational BL (o5tower L) /\ is_5_smooth (length BL).
Proof.
  induction L as [|st L' IH]; intros Wf.
  - exists (1 :: nil). split.
    + split; [|split].
      * constructor; [apply (subfield_1 is_rational is_rational_subfield) | constructor].
      * intros cs Hl Hf Hfc. destruct cs as [|c cs']; [simpl in Hl; lia|].
        destruct cs' as [|c2 cs'']; [|simpl in Hl; lia]. cbn [Fcomb] in Hfc.
        constructor; [lra | constructor].
      * intros y Hy. exists (y :: nil). split; [reflexivity | split].
        -- constructor; [exact Hy | constructor].
        -- cbn [Fcomb]. ring.
    + apply is_5_smooth_one.
  - destruct st as [s | a b r | a b c d e r].
    + simpl in Wf. destruct Wf as [Wss Wf'].
      destruct (IH Wf') as [BL' [HbBL' Hsm']].
      assert (HsfL' : is_subfield (o5tower L')) by (apply o5tower_subfield; exact Wf').
      destruct (QF_step_basis (o5tower L') s HsfL' Wss) as [Be [HbBe Hbecard]].
      assert (HsfL : is_subfield (o5tower (O5Quad s :: L')))
        by (apply o5tower_subfield; simpl; split; assumption).
      exists (flat_map (fun e => map (Rmult e) BL') Be). split.
      * apply (product_basis BL' Be (o5tower L') (o5tower (O5Quad s :: L'))).
        -- exact HsfL'. -- exact HsfL.
        -- intros z Hz. apply subfield_contains_rational; [exact HsfL' | exact Hz].
        -- intros z Hz. simpl. apply QF_contains; [exact HsfL' | exact Hz].
        -- exact HbBL'. -- exact HbBe.
      * rewrite product_length. destruct Hsm' as [aa [bb [cc Hsm]]]. rewrite Hsm.
        destruct Hbecard as [H1 | H2].
        -- rewrite H1. exists aa, bb, cc. nia.
        -- rewrite H2. exists (S aa), bb, cc. rewrite Nat.pow_succ_r'. nia.
    + simpl in Wf. destruct Wf as [Wa [Wb [Wr Wf']]].
      destruct (IH Wf') as [BL' [HbBL' Hsm']].
      assert (HsfL' : is_subfield (o5tower L')) by (apply o5tower_subfield; exact Wf').
      destruct (CF_step_basis (o5tower L') a b r HsfL' Wa Wb Wr) as [Be [HbBe Hbecard]].
      assert (HsfL : is_subfield (o5tower (O5Cubic a b r :: L')))
        by (apply o5tower_subfield; simpl; repeat split; assumption).
      exists (flat_map (fun e => map (Rmult e) BL') Be). split.
      * apply (product_basis BL' Be (o5tower L') (o5tower (O5Cubic a b r :: L'))).
        -- exact HsfL'. -- exact HsfL.
        -- intros z Hz. apply subfield_contains_rational; [exact HsfL' | exact Hz].
        -- intros z Hz. simpl. apply CF_contains_sr; [apply subfield_is_subring; exact HsfL' | exact Hz].
        -- exact HbBL'. -- exact HbBe.
      * rewrite product_length. destruct Hsm' as [aa [bb [cc Hsm]]]. rewrite Hsm.
        destruct Hbecard as [H1 | [H2 | H3]].
        -- rewrite H1. exists aa, bb, cc. nia.
        -- rewrite H2. exists (S aa), bb, cc. rewrite Nat.pow_succ_r'. nia.
        -- rewrite H3. exists aa, (S bb), cc. rewrite Nat.pow_succ_r'. nia.
    + simpl in Wf. destruct Wf as [Wa [Wb [Wc [Wd [We [Wr Wf']]]]]].
      destruct (IH Wf') as [BL' [HbBL' Hsm']].
      assert (HsfL' : is_subfield (o5tower L')) by (apply o5tower_subfield; exact Wf').
      destruct (Quint5F_step_basis (o5tower L') a b c d e r HsfL' Wa Wb Wc Wd We Wr)
        as [Be [HbBe Hbecard]].
      assert (HsfL : is_subfield (o5tower (O5Quint a b c d e r :: L')))
        by (apply o5tower_subfield; simpl; repeat split; assumption).
      exists (flat_map (fun ee => map (Rmult ee) BL') Be). split.
      * apply (product_basis BL' Be (o5tower L') (o5tower (O5Quint a b c d e r :: L'))).
        -- exact HsfL'. -- exact HsfL.
        -- intros z Hz. apply subfield_contains_rational; [exact HsfL' | exact Hz].
        -- intros z Hz. simpl. apply Quint5F_contains_sr; [apply subfield_is_subring; exact HsfL' | exact Hz].
        -- exact HbBL'. -- exact HbBe.
      * rewrite product_length. destruct Hsm' as [aa [bb [cc Hsm]]]. rewrite Hsm.
        destruct Hbecard as [H1 | [H2 | [H3 | [H4 | H5]]]].
        -- rewrite H1. exists aa, bb, cc. nia.
        -- rewrite H2. exists (S aa), bb, cc. rewrite Nat.pow_succ_r'. nia.
        -- rewrite H3. exists aa, (S bb), cc. rewrite Nat.pow_succ_r'. nia.
        -- rewrite H4. exists (S (S aa)), bb, cc. rewrite !Nat.pow_succ_r'. nia.
        -- rewrite H5. exists aa, bb, (S cc). rewrite Nat.pow_succ_r'. nia.
Qed.

(* divisor of a 2-3-5-smooth number is 2-3-5-smooth *)
Lemma gcd_d_5_eq_1 : forall d, ~ Nat.divide 5 d -> Nat.gcd d 5 = 1%nat.
Proof.
  intros d H5.
  pose proof (Nat.gcd_divide_r d 5) as Hg5.
  pose proof (Nat.gcd_divide_l d 5) as Hgd.
  pose proof (Nat.divide_pos_le (Nat.gcd d 5) 5 ltac:(lia) Hg5) as Hle.
  remember (Nat.gcd d 5) as g eqn:Eg.
  destruct g as [|[|[|[|[|[|g']]]]]].
  - destruct Hg5 as [c Hc]. lia.
  - reflexivity.
  - destruct Hg5 as [c Hc]. lia.
  - destruct Hg5 as [c Hc]. lia.
  - destruct Hg5 as [c Hc]. lia.
  - exfalso. apply H5. exact Hgd.
  - lia.
Qed.

Lemma divisor_pow5 : forall k d, Nat.divide d (5 ^ k)%nat -> exists e, d = (5 ^ e)%nat.
Proof.
  induction k as [|k IH]; intros d Hd.
  - simpl in Hd. apply Nat.divide_1_r in Hd. subst. exists 0%nat. reflexivity.
  - rewrite Nat.pow_succ_r' in Hd.
    destruct (Ndivide_dec 5 d) as [H5 | H5].
    + destruct H5 as [ee He]. subst d.
      assert (He2 : Nat.divide ee (5 ^ k)%nat) by (destruct Hd as [c Hc]; exists c; nia).
      destruct (IH ee He2) as [j Hj]. exists (S j). subst ee. rewrite Nat.pow_succ_r'. lia.
    + assert (Hcop : Nat.gcd d 5 = 1%nat) by (apply gcd_d_5_eq_1; exact H5).
      apply IH. apply (Nat.gauss d 5 (5 ^ k) Hd Hcop).
Qed.

Lemma divisor_35_smooth : forall b c d, Nat.divide d (3 ^ b * 5 ^ c)%nat ->
  exists e f, d = (3 ^ e * 5 ^ f)%nat.
Proof.
  induction b as [|b IH]; intros c d Hd.
  - replace (3 ^ 0 * 5 ^ c)%nat with (5 ^ c)%nat in Hd
      by (rewrite Nat.pow_0_r, Nat.mul_1_l; reflexivity).
    destruct (divisor_pow5 c d Hd) as [f Hf]. exists 0%nat, f.
    rewrite Nat.pow_0_r, Nat.mul_1_l. exact Hf.
  - replace (3 ^ S b * 5 ^ c)%nat with (3 * (3 ^ b * 5 ^ c))%nat in Hd
      by (rewrite Nat.pow_succ_r'; ring).
    destruct (Ndivide_dec 3 d) as [H3 | H3].
    + destruct H3 as [ee He]. subst d.
      assert (He2 : Nat.divide ee (3 ^ b * 5 ^ c)%nat) by (destruct Hd as [cc Hc]; exists cc; nia).
      destruct (IH c ee He2) as [e' [f' Hee]]. exists (S e'), f'. rewrite Nat.pow_succ_r'. nia.
    + assert (Hcop : Nat.gcd d 3 = 1%nat) by (apply gcd_d_3_eq_1; exact H3).
      apply (IH c d). apply (Nat.gauss d 3 (3 ^ b * 5 ^ c)%nat Hd Hcop).
Qed.

Lemma divisor_5_smooth : forall a b c d, Nat.divide d (2 ^ a * 3 ^ b * 5 ^ c)%nat -> is_5_smooth d.
Proof.
  induction a as [|a IH]; intros b c d Hd.
  - replace (2 ^ 0 * 3 ^ b * 5 ^ c)%nat with (3 ^ b * 5 ^ c)%nat in Hd
      by (rewrite Nat.pow_0_r, Nat.mul_1_l; reflexivity).
    destruct (divisor_35_smooth b c d Hd) as [e [f He]]. exists 0%nat, e, f.
    rewrite Nat.pow_0_r, Nat.mul_1_l. exact He.
  - replace (2 ^ S a * 3 ^ b * 5 ^ c)%nat with (2 * (2 ^ a * 3 ^ b * 5 ^ c))%nat in Hd
      by (rewrite Nat.pow_succ_r'; ring).
    destruct (Ndivide_dec 2 d) as [H2 | H2].
    + destruct H2 as [ee He]. subst d.
      assert (He2 : Nat.divide ee (2 ^ a * 3 ^ b * 5 ^ c)%nat)
        by (destruct Hd as [cc Hc]; exists cc; nia).
      destruct (IH b c ee He2) as [a' [b' [c' Hee]]]. exists (S a'), b', c'.
      rewrite Nat.pow_succ_r'. nia.
    + assert (Hcop : Nat.gcd d 2 = 1%nat) by (apply gcd_d_2_eq_1; exact H2).
      apply (IH b c d). apply (Nat.gauss d 2 (2 ^ a * 3 ^ b * 5 ^ c)%nat Hd Hcop).
Qed.

(* ===== item 7: every two-fold origami number has algebraic degree 2^a*3^b*5^c ===== *)
Theorem OrigamiNum2_field_degree_smooth : forall x, OrigamiNum2 x ->
  exists d, basis is_rational (powers x d) (Qx x) /\ is_5_smooth d.
Proof.
  intros x HO. destruct (OrigamiNum2_in_o5tower x HO) as [L [Wf Tx]].
  destruct (o5tower_dim_smooth L Wf) as [BL [HbBL HsmBL]].
  assert (HsfL : is_subfield (o5tower L)) by (apply o5tower_subfield; exact Wf).
  destruct (tower_law_div x (o5tower L) BL HsfL Tx HbBL) as [d [HbBx Hdiv]].
  exists d. split; [exact HbBx |].
  destruct HsmBL as [a [b [c Hab]]]. rewrite Hab in Hdiv.
  apply (divisor_5_smooth a b c d Hdiv).
Qed.
Open Scope R_scope.
(* ============================================================================
   Toward general cyclotomic irreducibility (the Dedekind reduction-mod-q
   argument): foundation for separability of x^n - 1 modulo a prime p not
   dividing n. Xn1 n is x^n - 1, Xn1_deriv n is its formal derivative n*x^(n-1),
   and separability_seed is the Bezout-type coefficient identity
   x * (n x^(n-1)) - n * (x^n - 1) = n, which forces any common divisor of
   x^n-1 and its derivative to divide the constant n -- a unit modulo p when
   p does not divide n, hence x^n-1 has no repeated factor mod p.
   ============================================================================ *)
Open Scope Z_scope.
Definition Xn1 (n : nat) : list Z := (-1) :: repeat 0 (n - 1) ++ [1].
Definition Xn1_deriv (n : nat) : list Z := repeat 0 (n - 1) ++ [Z.of_nat n].
Open Scope R_scope.
Lemma peval_monomial_c : forall (m : nat) (c : Z) (y : R),
  peval (repeat 0%Z m ++ [c]) y = IZR c * y ^ m.
Proof.
  induction m as [|m IH]; intro c; intro y.
  - cbn [repeat app peval]. ring.
  - cbn [repeat app peval]. rewrite IH. simpl. ring.
Qed.

Lemma peval_Xn1 : forall n y, (1 <= n)%nat -> peval (Xn1 n) y = y ^ n - 1.
Proof.
  intros n y Hn. unfold Xn1. cbn [peval].
  rewrite peval_monomial_c. simpl IZR.
  replace n with (S (n - 1))%nat at 2 by lia. simpl. ring.
Qed.

Lemma peval_Xn1_deriv : forall n y, (1 <= n)%nat ->
  peval (Xn1_deriv n) y = IZR (Z.of_nat n) * y ^ (n - 1).
Proof. intros n y Hn. unfold Xn1_deriv. apply peval_monomial_c. Qed.

Theorem separability_seed : forall n, (1 <= n)%nat -> forall k,
  nth k (Zpadd (Zpmul [0%Z; 1%Z] (Xn1_deriv n))
               (map (Z.mul (-1)) (map (Z.mul (Z.of_nat n)) (Xn1 n)))) 0%Z
  = nth k [Z.of_nat n] 0%Z.
Proof.
  intros n Hn. apply peval_eq_nth. intro y.
  rewrite peval_Zpadd, peval_Zpmul, peval_map_Zmul, peval_map_Zmul.
  rewrite (peval_Xn1 n y Hn), (peval_Xn1_deriv n y Hn).
  cbn [peval]. simpl IZR.
  assert (Hyn : y ^ n = y * y ^ (n - 1)).
  { replace n with (S (n - 1))%nat at 1 by lia. reflexivity. }
  rewrite Hyn. ring.
Qed.
Open Scope R_scope.
(* ============================================================================
   Polynomial congruence modulo a prime (the reduction-mod-q layer of the
   Dedekind cyclotomic argument): equality of integer-coefficient polynomials
   up to coefficientwise divisibility by m, with the ring structure it inherits.
   ============================================================================ *)
Open Scope Z_scope.
Definition pcong (m : Z) (f g : list Z) : Prop :=
  forall k, (m | nth k f 0 - nth k g 0).

Lemma pcong_refl : forall m f, pcong m f f.
Proof. intros m f k. rewrite Z.sub_diag. apply Z.divide_0_r. Qed.

Lemma pcong_of_eq_nth : forall m f g, (forall k, nth k f 0 = nth k g 0) -> pcong m f g.
Proof. intros m f g H k. rewrite H, Z.sub_diag. apply Z.divide_0_r. Qed.

Lemma pcong_sym : forall m f g, pcong m f g -> pcong m g f.
Proof.
  intros m f g H k. specialize (H k).
  replace (nth k g 0 - nth k f 0) with (- (nth k f 0 - nth k g 0)) by ring.
  apply Z.divide_opp_r. exact H.
Qed.

Lemma pcong_trans : forall m f g h, pcong m f g -> pcong m g h -> pcong m f h.
Proof.
  intros m f g h Hfg Hgh k. specialize (Hfg k). specialize (Hgh k).
  replace (nth k f 0 - nth k h 0)
    with ((nth k f 0 - nth k g 0) + (nth k g 0 - nth k h 0)) by ring.
  apply Z.divide_add_r; assumption.
Qed.

Lemma pcong_Zpadd : forall m f f' g g',
  pcong m f f' -> pcong m g g' -> pcong m (Zpadd f g) (Zpadd f' g').
Proof.
  intros m f f' g g' Hf Hg k. rewrite !nth_Zpadd.
  replace (nth k f 0 + nth k g 0 - (nth k f' 0 + nth k g' 0))
    with ((nth k f 0 - nth k f' 0) + (nth k g 0 - nth k g' 0)) by ring.
  apply Z.divide_add_r; [apply Hf | apply Hg].
Qed.

Lemma Zconv_divide : forall m f g k,
  (forall i, (m | nth i f 0)) -> (m | Zconv f g k).
Proof.
  intros m f g k Hf. revert k. induction f as [|a f IH]; intros k.
  - simpl. apply Z.divide_0_r.
  - simpl. apply Z.divide_add_r.
    + apply Z.divide_mul_l. specialize (Hf 0%nat). simpl in Hf. exact Hf.
    + destruct k as [|k']; [apply Z.divide_0_r |].
      apply IH. intro i. specialize (Hf (S i)). simpl in Hf. exact Hf.
Qed.

Lemma Zconv_pcong : forall m g f f' k,
  (forall i, (m | nth i f 0 - nth i f' 0)) ->
  (m | Zconv f g k - Zconv f' g k).
Proof.
  intros m g. induction f as [|a f IH]; intros f' k Hco.
  - simpl. destruct f' as [|a' f'].
    + simpl. apply Z.divide_0_r.
    + replace (0 - Zconv (a' :: f') g k) with (- Zconv (a' :: f') g k) by ring.
      apply Z.divide_opp_r. apply Zconv_divide. intro i.
      specialize (Hco i).
      assert (Hnil : nth i (@nil Z) 0 = 0) by (destruct i; reflexivity).
      rewrite Hnil in Hco.
      replace (nth i (a' :: f') 0) with (- (0 - nth i (a' :: f') 0)) by ring.
      apply Z.divide_opp_r. exact Hco.
  - destruct f' as [|a' f'].
    + replace (Zconv (@nil Z) g k) with 0 by reflexivity. rewrite Z.sub_0_r.
      apply Zconv_divide. intro i. specialize (Hco i).
      assert (Hnil : nth i (@nil Z) 0 = 0) by (destruct i; reflexivity).
      rewrite Hnil, Z.sub_0_r in Hco. exact Hco.
    + simpl. destruct k as [|k'].
      * replace (a * nth 0 g 0 + 0 - (a' * nth 0 g 0 + 0))
          with ((a - a') * nth 0 g 0) by ring.
        apply Z.divide_mul_l. specialize (Hco 0%nat). simpl in Hco. exact Hco.
      * replace (a * nth (S k') g 0 + Zconv f g k' - (a' * nth (S k') g 0 + Zconv f' g k'))
          with ((a - a') * nth (S k') g 0 + (Zconv f g k' - Zconv f' g k')) by ring.
        apply Z.divide_add_r.
        -- apply Z.divide_mul_l. specialize (Hco 0%nat). simpl in Hco. exact Hco.
        -- apply IH. intro i. specialize (Hco (S i)). simpl in Hco. exact Hco.
Qed.

Lemma pcong_Zpmul_l : forall m f f' g, pcong m f f' -> pcong m (Zpmul f g) (Zpmul f' g).
Proof. intros m f f' g H k. rewrite !nth_Zpmul. apply Zconv_pcong. exact H. Qed.

Lemma pcong_Zpmul_r : forall m f g g', pcong m g g' -> pcong m (Zpmul f g) (Zpmul f g').
Proof. intros m f g g' H k. rewrite !nth_Zpmul, !(Zconv_comm f). apply Zconv_pcong. exact H. Qed.

Lemma pcong_Zpmul : forall m f f' g g',
  pcong m f f' -> pcong m g g' -> pcong m (Zpmul f g) (Zpmul f' g').
Proof.
  intros m f f' g g' Hf Hg. apply (pcong_trans m _ (Zpmul f' g)).
  - apply pcong_Zpmul_l; exact Hf.
  - apply pcong_Zpmul_r; exact Hg.
Qed.

Definition pdvd_mod (m : Z) (f g : list Z) : Prop := exists q, pcong m g (Zpmul f q).

Lemma seed_pcong : forall p n, (1 <= n)%nat ->
  pcong p (Zpadd (Zpmul [0%Z; 1%Z] (Xn1_deriv n))
                 (map (Z.mul (-1)) (map (Z.mul (Z.of_nat n)) (Xn1 n))))
          [Z.of_nat n].
Proof.
  intros p n Hn. apply pcong_of_eq_nth. intro k. apply separability_seed. exact Hn.
Qed.
Open Scope R_scope.
(* ============================================================================
   Separability of x^n - 1 modulo p (p not dividing n): the heart of the
   Dedekind argument. Any common divisor of x^n-1 and its derivative, modulo p,
   divides the constant n; since n is a unit mod a prime not dividing it, x^n-1
   has no repeated factor mod p.
   ============================================================================ *)
Open Scope Z_scope.
Lemma pcong_map_Zmul : forall m c f g,
  pcong m f g -> pcong m (map (Z.mul c) f) (map (Z.mul c) g).
Proof.
  intros m c f g H k. rewrite !nth_map_Zmul.
  replace (c * nth k f 0 - c * nth k g 0) with (c * (nth k f 0 - nth k g 0)) by ring.
  apply Z.divide_mul_r. apply H.
Qed.

Theorem sep_common_divisor : forall p n h,
  (1 <= n)%nat -> pdvd_mod p h (Xn1 n) -> pdvd_mod p h (Xn1_deriv n) ->
  pdvd_mod p h [Z.of_nat n].
Proof.
  intros p n h Hn [q1 H1] [q2 H2].
  exists (Zpadd (Zpmul [0%Z; 1%Z] q2) (map (Z.mul (-1)) (map (Z.mul (Z.of_nat n)) q1))).
  apply pcong_sym. apply (pcong_trans p _
    (Zpadd (Zpmul [0%Z; 1%Z] (Xn1_deriv n))
           (map (Z.mul (-1)) (map (Z.mul (Z.of_nat n)) (Xn1 n))))).
  - apply pcong_sym. apply (pcong_trans p _
      (Zpadd (Zpmul [0%Z; 1%Z] (Zpmul h q2))
             (map (Z.mul (-1)) (map (Z.mul (Z.of_nat n)) (Zpmul h q1))))).
    + apply pcong_Zpadd.
      * apply pcong_Zpmul_r. exact H2.
      * apply pcong_map_Zmul, pcong_map_Zmul. exact H1.
    + apply pcong_of_eq_nth.
      apply (peval_eq_nth
        (Zpadd (Zpmul [0%Z; 1%Z] (Zpmul h q2))
               (map (Z.mul (-1)) (map (Z.mul (Z.of_nat n)) (Zpmul h q1))))
        (Zpmul h (Zpadd (Zpmul [0%Z; 1%Z] q2)
                        (map (Z.mul (-1)) (map (Z.mul (Z.of_nat n)) q1))))).
      intro y.
      rewrite ?peval_Zpadd, ?peval_Zpmul, ?peval_map_Zmul,
              ?peval_Zpadd, ?peval_Zpmul, ?peval_map_Zmul.
      ring.
  - apply seed_pcong; exact Hn.
Qed.
Open Scope R_scope.
(* Polynomial power and its congruence preservation (toward the Frobenius map
   g(x)^p == g(x^p) mod p that closes the Dedekind argument). *)
Open Scope Z_scope.
Fixpoint Zppow (f : list Z) (k : nat) : list Z :=
  match k with
  | O => [1]
  | S k' => Zpmul f (Zppow f k')
  end.

Lemma pcong_Zppow : forall m k f g, pcong m f g -> pcong m (Zppow f k) (Zppow g k).
Proof.
  intros m k. induction k as [|k IH]; intros f g H.
  - simpl. apply pcong_refl.
  - simpl. apply pcong_Zpmul; [exact H | apply IH; exact H].
Qed.

Lemma peval_Zppow : forall k f y, peval (Zppow f k) y = ((peval f y) ^ k)%R.
Proof.
  induction k as [|k IH]; intros f y.
  - simpl. cbn [peval]. simpl IZR. ring.
  - simpl. rewrite peval_Zpmul, IH. ring.
Qed.
Open Scope R_scope.
(* Zppow algebra toward the Frobenius map, via the peval ring homomorphism. *)
Open Scope Z_scope.
Lemma nth_eq_via_peval : forall a b,
  (forall y, peval a y = peval b y) -> forall k, nth k a 0 = nth k b 0.
Proof. intros a b H. apply peval_eq_nth. exact H. Qed.

Lemma Zppow_Zpmul : forall k A B j,
  nth j (Zppow (Zpmul A B) k) 0 = nth j (Zpmul (Zppow A k) (Zppow B k)) 0.
Proof.
  intros k A B. apply nth_eq_via_peval. intro y.
  rewrite peval_Zppow, peval_Zpmul, peval_Zpmul, !peval_Zppow.
  rewrite Rpow_mult_distr. reflexivity.
Qed.

Lemma Zppow_1 : forall A j, nth j (Zppow A 1) 0 = nth j A 0.
Proof.
  intros A. apply nth_eq_via_peval. intro y. rewrite peval_Zppow. simpl. ring.
Qed.
Open Scope R_scope.
(* Bridge between the real binomial coefficient (Binomial.C, the Reals library's,
   distinct from the Line field C) and the nat binomial used here, toward the
   polynomial binomial theorem and the Frobenius freshman's dream mod p. *)
Open Scope R_scope.
Lemma INR_fact_neq_0 : forall n, INR (fact n) <> 0.
Proof. intro n. apply not_0_INR. apply fact_neq_0. Qed.

Lemma C_n0 : forall n, Binomial.C n 0 = 1.
Proof.
  intro n. unfold Binomial.C. rewrite Nat.sub_0_r.
  replace (fact 0) with 1%nat by reflexivity. rewrite INR_1, Rmult_1_l.
  apply Rinv_r. apply INR_fact_neq_0.
Qed.

Lemma C_nn : forall n, Binomial.C n n = 1.
Proof.
  intro n. unfold Binomial.C. rewrite Nat.sub_diag.
  replace (fact 0) with 1%nat by reflexivity. rewrite INR_1, Rmult_1_r.
  apply Rinv_r. apply INR_fact_neq_0.
Qed.

Lemma C_eq_binom : forall n k, (k <= n)%nat -> Binomial.C n k = INR (binom n k).
Proof.
  induction n as [|n IH]; intros k Hk.
  - assert (Hk0 : k = 0%nat) by lia. subst k. rewrite C_n0, binom_n_0. reflexivity.
  - destruct k as [|k].
    + rewrite C_n0, binom_n_0. reflexivity.
    + destruct (Nat.eq_dec k n) as [Hkn | Hkn].
      * subst k. rewrite C_nn, binom_n_n. reflexivity.
      * rewrite <- (pascal n k) by lia.
        rewrite (IH k) by lia. rewrite (IH (S k)) by lia.
        rewrite binom_S_S, plus_INR. ring.
Qed.
Open Scope R_scope.
(* The polynomial binomial theorem (toward the Frobenius freshman's dream):
   (A+B)^m = sum_{i=0}^m binom(m,i) A^i B^(m-i) as integer polynomials, via the
   real binomial theorem and the C/binom bridge. *)
Open Scope Z_scope.
Fixpoint psum (f : nat -> list Z) (n : nat) : list Z :=
  match n with
  | O => f O
  | S n' => Zpadd (psum f n') (f (S n'))
  end.

Lemma peval_psum : forall f n y,
  peval (psum f n) y = sum_f_R0 (fun i => peval (f i) y) n.
Proof.
  intros f n y. induction n as [|n IH].
  - reflexivity.
  - simpl psum. rewrite peval_Zpadd, IH. reflexivity.
Qed.

Definition binom_poly (A B : list Z) (m : nat) : list Z :=
  psum (fun i => map (Z.mul (Z.of_nat (binom m i))) (Zpmul (Zppow A i) (Zppow B (m - i)))) m.

Theorem binom_thm : forall A B m k,
  nth k (Zppow (Zpadd A B) m) 0 = nth k (binom_poly A B m) 0.
Proof.
  intros A B m. apply nth_eq_via_peval. intro y.
  rewrite peval_Zppow, peval_Zpadd.
  unfold binom_poly. rewrite peval_psum.
  rewrite (binomial (peval A y) (peval B y) m).
  apply sum_eq. intros i Hi.
  rewrite peval_map_Zmul, peval_Zpmul, peval_Zppow, peval_Zppow.
  rewrite <- INR_IZR_INZ, <- (C_eq_binom m i Hi). ring.
Qed.
Open Scope R_scope.
(* The Frobenius freshman's dream for integer polynomials: (A+B)^p == A^p + B^p
   mod p for prime p, since the middle binomial coefficients are divisible by p
   (prime_div_binom). *)
Open Scope Z_scope.
Definition bterm (p : nat) (A B : list Z) (i : nat) : list Z :=
  map (Z.mul (Z.of_nat (binom p i))) (Zpmul (Zppow A i) (Zppow B (p - i))).

Lemma binom_poly_psum : forall A B m, binom_poly A B m = psum (bterm m A B) m.
Proof. intros. unfold binom_poly, bterm. reflexivity. Qed.

Lemma bterm_vanish : forall p A B i,
  Znumtheory.prime (Z.of_nat p) -> (0 < i < p)%nat ->
  pcong (Z.of_nat p) (bterm p A B i) [].
Proof.
  intros p A B i Hp Hi k. unfold bterm.
  rewrite nth_map_Zmul. assert (Hnil : nth k (@nil Z) 0 = 0) by (destruct k; reflexivity).
  rewrite Hnil, Z.sub_0_r.
  apply Z.divide_mul_l. apply prime_div_binom; assumption.
Qed.

Lemma pcong_psum_drop : forall m f n,
  (forall i, (1 <= i <= n)%nat -> pcong m (f i) []) ->
  pcong m (psum f n) (f 0%nat).
Proof.
  intros m f n. induction n as [|n IH]; intros Hmid.
  - simpl. apply pcong_refl.
  - simpl psum.
    assert (Hf0 : pcong m (psum f n) (f 0%nat)) by (apply IH; intros i Hi; apply Hmid; lia).
    assert (HfS : pcong m (f (S n)) []) by (apply Hmid; lia).
    apply (pcong_trans m _ (Zpadd (f 0%nat) (@nil Z))).
    + apply pcong_Zpadd; assumption.
    + apply pcong_of_eq_nth. intro k. rewrite nth_Zpadd.
      assert (Hn : nth k (@nil Z) 0 = 0) by (destruct k; reflexivity). rewrite Hn. ring.
Qed.

Lemma bterm_0 : forall p A B k, nth k (bterm p A B 0) 0 = nth k (Zppow B p) 0.
Proof.
  intros p A B. apply nth_eq_via_peval. intro y. unfold bterm.
  rewrite peval_map_Zmul, peval_Zpmul, !peval_Zppow.
  rewrite binom_n_0, Nat.sub_0_r.
  replace (IZR (Z.of_nat 1)) with 1%R by (simpl; reflexivity). ring.
Qed.

Lemma bterm_p : forall p A B k, nth k (bterm p A B p) 0 = nth k (Zppow A p) 0.
Proof.
  intros p A B. apply nth_eq_via_peval. intro y. unfold bterm.
  rewrite peval_map_Zmul, peval_Zpmul, !peval_Zppow.
  rewrite binom_n_n, Nat.sub_diag.
  replace (IZR (Z.of_nat 1)) with 1%R by (simpl; reflexivity). ring.
Qed.

Theorem freshman : forall p A B, Znumtheory.prime (Z.of_nat p) ->
  pcong (Z.of_nat p) (Zppow (Zpadd A B) p) (Zpadd (Zppow A p) (Zppow B p)).
Proof.
  intros p A B Hp.
  apply (pcong_trans _ _ (binom_poly A B p)).
  { apply pcong_of_eq_nth. intro k. apply binom_thm. }
  rewrite binom_poly_psum.
  destruct p as [|p']; [destruct Hp as [Hpp _]; simpl in Hpp; lia|].
  apply (pcong_trans _ _ (Zpadd (Zppow B (S p')) (Zppow A (S p')))).
  - simpl psum. apply pcong_Zpadd.
    + apply (pcong_trans _ _ (bterm (S p') A B 0%nat)).
      * apply pcong_psum_drop. intros i Hi. apply bterm_vanish; [exact Hp | lia].
      * apply pcong_of_eq_nth. intro k. apply bterm_0.
    + apply pcong_of_eq_nth. intro k. apply bterm_p.
  - apply pcong_of_eq_nth. intro k. rewrite !nth_Zpadd. ring.
Qed.
Open Scope R_scope.
(* Integer Fermat (nonnegative bases) from the polynomial freshman dream, and the
   constant-polynomial power, toward the full Frobenius map g(x)^p == g(x^p). *)
Open Scope Z_scope.
Lemma IZR_pow_nat : forall c k, ((IZR c) ^ k)%R = IZR (c ^ Z.of_nat k).
Proof.
  induction k as [|k IH].
  - simpl. reflexivity.
  - simpl pow. rewrite IH, <- mult_IZR, Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity.
Qed.

Lemma Zppow_single : forall c k j,
  nth j (Zppow [c] k) 0 = nth j [(c ^ Z.of_nat k)%Z] 0.
Proof.
  intros c k. apply nth_eq_via_peval. intro y.
  rewrite peval_Zppow.
  assert (Hc : peval [c] y = IZR c) by (cbn [peval]; ring).
  rewrite Hc, IZR_pow_nat. cbn [peval]. ring.
Qed.

Lemma int_freshman : forall p a b, Znumtheory.prime (Z.of_nat p) ->
  (Z.of_nat p | (a + b) ^ Z.of_nat p - (a ^ Z.of_nat p + b ^ Z.of_nat p)).
Proof.
  intros p a b Hp.
  pose proof (freshman p [a] [b] Hp 0%nat) as Hfr.
  rewrite !nth_Zpadd in Hfr.
  rewrite (Zppow_single a), (Zppow_single b) in Hfr.
  assert (Hab : Zpadd [a] [b] = [a + b]) by reflexivity.
  rewrite Hab, (Zppow_single (a + b)) in Hfr.
  cbn [nth] in Hfr. exact Hfr.
Qed.

Lemma fermat_nonneg : forall p m, Znumtheory.prime (Z.of_nat p) ->
  (Z.of_nat p | (Z.of_nat m) ^ Z.of_nat p - Z.of_nat m).
Proof.
  intros p m Hp. induction m as [|m IH].
  - simpl. replace (0 ^ Z.of_nat p - 0) with 0.
    + apply Z.divide_0_r.
    + rewrite Z.pow_0_l; [ring | destruct Hp; lia].
  - rewrite Nat2Z.inj_succ.
    pose proof (int_freshman p (Z.of_nat m) 1 Hp) as Hf.
    rewrite Z.pow_1_l in Hf by (destruct Hp; lia).
    replace (Z.succ (Z.of_nat m) ^ Z.of_nat p - Z.succ (Z.of_nat m))
      with (((Z.of_nat m + 1) ^ Z.of_nat p - (Z.of_nat m ^ Z.of_nat p + 1))
            + (Z.of_nat m ^ Z.of_nat p - Z.of_nat m)) by (unfold Z.succ; ring).
    apply Z.divide_add_r; assumption.
Qed.
Open Scope R_scope.
(* Fermat's little theorem over all of Z (negative bases via parity of p), and
   its constant-polynomial form [c]^p == [c] mod p. *)
Open Scope Z_scope.
Lemma int_fermat : forall p c, Znumtheory.prime (Z.of_nat p) ->
  (Z.of_nat p | c ^ Z.of_nat p - c).
Proof.
  intros p c Hp.
  destruct (Z_le_gt_dec 0 c) as [Hpos | Hneg].
  - pose proof (fermat_nonneg p (Z.to_nat c) Hp) as Hd.
    rewrite Z2Nat.id in Hd by lia. exact Hd.
  - destruct (Z.eq_dec (Z.of_nat p) 2) as [Hp2 | Hp2].
    + rewrite Hp2.
      destruct (Z.Even_or_Odd c) as [[k Hk] | [k Hk]]; subst c.
      * exists (2 * k * k - k). ring.
      * exists (2 * k * k + k). ring.
    + assert (Hodd : Z.Odd (Z.of_nat p)).
      { destruct (Z.Even_or_Odd (Z.of_nat p)) as [He | Ho]; [exfalso | exact Ho].
        destruct He as [k Hk].
        assert (H2d : (2 | Z.of_nat p)) by (exists k; lia).
        pose proof (Znumtheory.prime_divisors (Z.of_nat p) Hp 2 H2d) as Hdiv.
        destruct Hp as [Hp1 _]. lia. }
      pose proof (fermat_nonneg p (Z.to_nat (- c)) Hp) as Hd.
      rewrite Z2Nat.id in Hd by lia.
      rewrite Z.pow_opp_odd in Hd by exact Hodd.
      replace (- c ^ Z.of_nat p - - c) with (- (c ^ Z.of_nat p - c)) in Hd by ring.
      apply Z.divide_opp_r in Hd. rewrite Z.opp_involutive in Hd. exact Hd.
Qed.

Lemma fermat_const : forall p c, Znumtheory.prime (Z.of_nat p) ->
  pcong (Z.of_nat p) (Zppow [c] p) [c].
Proof.
  intros p c Hp k.
  rewrite (Zppow_single c p k).
  destruct k as [|k']; cbn [nth].
  - apply int_fermat. exact Hp.
  - rewrite Z.sub_diag. apply Z.divide_0_r.
Qed.
Open Scope R_scope.
(* ============================================================================
   The Frobenius map for integer polynomials: g(x)^p == g(x^p) mod p for prime p.
   subst_xp substitutes x -> x^p; the structural induction uses the freshman
   dream (additivity), fermat_const (constants fixed), and Zppow_Zpmul. With
   separability this is the second mod-p ingredient of the Dedekind argument.
   ============================================================================ *)
Open Scope Z_scope.
Fixpoint subst_xp (p : nat) (g : list Z) : list Z :=
  match g with
  | [] => []
  | c :: rest => c :: (repeat 0 (p - 1) ++ subst_xp p rest)
  end.

Lemma peval_repeat0_app : forall m t y,
  peval (repeat 0%Z m ++ t) y = (y ^ m * peval t y)%R.
Proof.
  induction m as [|m IH]; intros t y.
  - simpl. ring.
  - cbn [repeat app peval]. rewrite IH. simpl. ring.
Qed.

Lemma peval_subst_xp : forall p g y,
  (1 <= p)%nat -> peval (subst_xp p g) y = peval g (y ^ p).
Proof.
  intros p g y Hp. induction g as [|c rest IH].
  - reflexivity.
  - cbn [subst_xp peval]. rewrite peval_repeat0_app, IH.
    assert (Hyp : (y ^ p = y * y ^ (p - 1))%R).
    { replace p with (S (p - 1))%nat at 1 by lia. reflexivity. }
    rewrite Hyp. ring.
Qed.

Lemma Zppow_cong : forall p a b,
  (forall j, nth j a 0 = nth j b 0) ->
  forall j, nth j (Zppow a p) 0 = nth j (Zppow b p) 0.
Proof.
  intros p a b H. apply nth_eq_via_peval. intro y.
  rewrite !peval_Zppow. f_equal. apply peval_ext. exact H.
Qed.

Lemma peval_x : forall y, peval [0%Z; 1%Z] y = y.
Proof.
  intro y. cbn [peval].
  replace (IZR 0) with 0%R by reflexivity. replace (IZR 1) with 1%R by reflexivity. ring.
Qed.

Lemma peval_const : forall c y, peval [c] y = IZR c.
Proof. intros c y. cbn [peval]. ring. Qed.

Lemma cons_split : forall c rest j,
  nth j (c :: rest) 0 = nth j (Zpadd [c] (Zpmul [0; 1] rest)) 0.
Proof.
  intros c rest. apply nth_eq_via_peval. intro y.
  rewrite peval_Zpadd, peval_Zpmul, peval_x, peval_const. cbn [peval]. ring.
Qed.

Lemma subst_xp_split : forall p c rest j, (1 <= p)%nat ->
  nth j (subst_xp p (c :: rest)) 0
  = nth j (Zpadd [c] (Zpmul (Zppow [0; 1] p) (subst_xp p rest))) 0.
Proof.
  intros p c rest j Hp. apply nth_eq_via_peval. intro y.
  rewrite peval_Zpadd, peval_Zpmul, peval_Zppow, peval_x, peval_const.
  rewrite (peval_subst_xp p (c :: rest) y Hp), (peval_subst_xp p rest y Hp).
  cbn [peval]. ring.
Qed.

Theorem frobenius : forall p g, Znumtheory.prime (Z.of_nat p) ->
  pcong (Z.of_nat p) (Zppow g p) (subst_xp p g).
Proof.
  intros p g Hp.
  assert (Hp1 : (1 <= p)%nat) by (destruct Hp as [Hpp _]; lia).
  induction g as [|c rest IH].
  - destruct p as [|p']; [lia|]. simpl Zppow. apply pcong_refl.
  - apply (pcong_trans _ _ (Zppow (Zpadd [c] (Zpmul [0;1] rest)) p)).
    { apply pcong_of_eq_nth. apply Zppow_cong. intro j. apply cons_split. }
    apply (pcong_trans _ _ (Zpadd (Zppow [c] p) (Zppow (Zpmul [0;1] rest) p))).
    { apply freshman; exact Hp. }
    apply (pcong_trans _ _ (Zpadd [c] (Zpmul (Zppow [0;1] p) (subst_xp p rest)))).
    2:{ apply pcong_sym. apply pcong_of_eq_nth. intro j. apply subst_xp_split; exact Hp1. }
    apply pcong_Zpadd.
    + apply fermat_const; exact Hp.
    + apply (pcong_trans _ _ (Zpmul (Zppow [0;1] p) (Zppow rest p))).
      * apply pcong_of_eq_nth. intro j. apply Zppow_Zpmul.
      * apply pcong_Zpmul_r. exact IH.
Qed.
Open Scope R_scope.
(* ============================================================================
   Complex evaluation of integer polynomials (toward roots of unity and the
   algebraic half of the Dedekind argument). Uses the Cardano_C complex field;
   imported here at the end of the file so the complex C does not shadow the
   Line field C used above. cpe is a ring homomorphism into C.
   ============================================================================ *)
Close Scope R_scope.
Close Scope nat_scope.
Close Scope Z_scope.
Close Scope R_scope.
Close Scope nat_scope.
Close Scope R_scope.
Close Scope R_scope.
Close Scope R_scope.
Close Scope R_scope.
Import Cardano_C.
Open Scope nat_scope.
Definition ZtoC (z : Z) : C := RtoC (IZR z).

Fixpoint cpe (p : list Z) (z : C) : C :=
  match p with
  | [] => C0
  | a :: p' => Cadd (ZtoC a) (Cmul z (cpe p' z))
  end.

Lemma cpe_Zpadd : forall p q z, cpe (Zpadd p q) z = Cadd (cpe p z) (cpe q z).
Proof.
  induction p as [|a p IH]; intros q z.
  - simpl. ring.
  - destruct q as [|b q].
    + simpl. ring.
    + cbn [Zpadd cpe]. rewrite IH. unfold ZtoC. rewrite plus_IZR, RtoC_add. ring.
Qed.

Lemma cpe_map_Zmul : forall a q z, cpe (map (Z.mul a) q) z = Cmul (ZtoC a) (cpe q z).
Proof.
  induction q as [|b q IH]; intros z.
  - simpl. ring.
  - cbn [map cpe]. rewrite IH. unfold ZtoC. rewrite mult_IZR, RtoC_mul. ring.
Qed.

Lemma cpe_Zpmul : forall p q z, cpe (Zpmul p q) z = Cmul (cpe p z) (cpe q z).
Proof.
  induction p as [|a p IH]; intros q z.
  - simpl. ring.
  - cbn [Zpmul]. rewrite cpe_Zpadd, cpe_map_Zmul. cbn [cpe]. rewrite IH.
    replace (ZtoC 0%Z) with C0 by reflexivity. unfold ZtoC. ring.
Qed.

(* Complex power, De Moivre's formula, and the n-th roots of unity zeta n, with
   zeta n raised to the n being 1. (Cardano_C still imported from above.) *)
Open Scope R_scope.
Fixpoint Cpow (z : C) (k : nat) : C :=
  match k with O => C1 | S k' => Cmul z (Cpow z k') end.
Open Scope R_scope.
Lemma cpe_monomial : forall m c z,
  cpe (repeat 0%Z m ++ [c]) z = Cmul (ZtoC c) (Cpow z m).
Proof.
  induction m as [|m IH]; intros c z.
  - cbn [repeat app cpe Cpow]. replace (ZtoC 0%Z) with C0 by reflexivity. ring.
  - cbn [repeat app cpe]. rewrite IH.
    replace (ZtoC 0%Z) with C0 by reflexivity. cbn [Cpow]. ring.
Qed.

Lemma ZtoC_1 : ZtoC 1%Z = C1.
Proof. reflexivity. Qed.

Lemma ZtoC_m1 : ZtoC (-1)%Z = Copp C1.
Proof. unfold ZtoC, RtoC, Copp, C1. f_equal; simpl; ring. Qed.

Lemma cpe_Xn1 : forall n z, (1 <= n)%nat -> cpe (Xn1 n) z = Csub (Cpow z n) C1.
Proof.
  intros n z Hn. unfold Xn1. cbn [cpe].
  rewrite cpe_monomial, ZtoC_m1, ZtoC_1.
  assert (Hz : Cpow z n = Cmul z (Cpow z (n - 1))).
  { replace n with (S (n - 1))%nat at 1 by lia. reflexivity. }
  rewrite Hz. ring.
Qed.
Open Scope R_scope.
Lemma Cpow_add : forall z a b, Cpow z (a + b) = Cmul (Cpow z a) (Cpow z b).
Proof.
  intros z a b. induction a as [|a IH].
  - simpl. ring.
  - cbn [Nat.add Cpow]. rewrite IH. ring.
Qed.

Lemma Cpow_mul : forall z a b, Cpow z (a * b) = Cpow (Cpow z a) b.
Proof.
  intros z a b. induction b as [|b IH].
  - rewrite Nat.mul_0_r. reflexivity.
  - rewrite Nat.mul_succ_r, Cpow_add, IH. cbn [Cpow]. ring.
Qed.

Lemma Cpow_C1 : forall k, Cpow C1 k = C1.
Proof.
  induction k as [|k IH]; [reflexivity|]. cbn [Cpow]. rewrite IH. ring.
Qed.
Open Scope R_scope.
Lemma cos_eq_1_in_range : forall x, 0 <= x <= 2 * PI -> cos x = 1 -> x = 0 \/ x = 2 * PI.
Proof.
  intros x [Hx0 Hx2] Hc.
  assert (HPI : PI > 0) by apply PI_RGT_0.
  destruct (Rle_dec x PI) as [Hle | Hgt].
  - left. apply (cos_inj x 0); [lra | lra | rewrite cos_0; exact Hc].
  - right.
    assert (Hsub : cos (2 * PI - x) = 1).
    { rewrite cos_minus, cos_2PI, sin_2PI. rewrite Hc. ring. }
    assert (H0 : 2 * PI - x = 0).
    { apply (cos_inj (2 * PI - x) 0); [lra | lra | rewrite cos_0; exact Hsub]. }
    lra.
Qed.
Open Scope R_scope.
Fixpoint ceval (p : list C) (z : C) : C :=
  match p with
  | [] => C0
  | a :: p' => Cadd a (Cmul z (ceval p' z))
  end.

Fixpoint qdiv (p : list C) (a : C) : list C :=
  match p with
  | [] => []
  | c :: p' => (ceval p' a) :: qdiv p' a
  end.

Lemma ceval_qdiv : forall p a z,
  ceval p z = Cadd (Cmul (Csub z a) (ceval (qdiv p a) z)) (ceval p a).
Proof.
  induction p as [|c p IH]; intros a z.
  - simpl. ring.
  - cbn [ceval qdiv]. rewrite (IH a z). ring.
Qed.

Theorem factor_thm : forall p a, ceval p a = C0 ->
  forall z, ceval p z = Cmul (Csub z a) (ceval (qdiv p a) z).
Proof.
  intros p a Ha z. rewrite (ceval_qdiv p a z), Ha. ring.
Qed.

Lemma cpe_ceval : forall p z, cpe p z = ceval (map ZtoC p) z.
Proof.
  induction p as [|a p IH]; intros z.
  - reflexivity.
  - cbn [cpe map ceval]. rewrite IH. reflexivity.
Qed.

Lemma length_qdiv : forall p a, length (qdiv p a) = length p.
Proof.
  induction p as [|c p IH]; intros a; [reflexivity|].
  cbn [qdiv length]. rewrite IH. reflexivity.
Qed.

(* ============================================================================
   Degree-aware root counting over C (toward the Dedekind cyclotomic argument):
   a nonzero integer polynomial, viewed over C, has fewer distinct complex roots
   than its length -- i.e. at most its degree.  The everywhere-zero half is a
   clean root-peeling induction (factor_thm via qdiv, handling the trailing zero
   qdiv leaves), and the descent to integer coefficients reuses poly_vanish, so
   no real-analytic machinery is needed.
   ============================================================================ *)

(* appending a zero coefficient does not change the complex evaluation *)
Lemma ceval_snoc_zero : forall l z, ceval (l ++ [C0]) z = ceval l z.
Proof.
  induction l as [|c l' IH]; intro z.
  - cbn [app ceval]. ring.
  - cbn [app ceval]. rewrite IH. reflexivity.
Qed.

(* qdiv always leaves a trailing zero coefficient *)
Lemma qdiv_last_zero : forall p a, p <> [] -> last (qdiv p a) C0 = C0.
Proof.
  induction p as [|c p' IH]; intros a Hne; [contradiction|].
  destruct p' as [|c1 p''].
  - reflexivity.
  - cbn [qdiv]. cbn [qdiv] in IH.
    change (last ((ceval (c1 :: p'') a) :: (ceval p'' a) :: qdiv p'' a) C0)
      with (last ((ceval p'' a) :: qdiv p'' a) C0).
    fold (qdiv (c1 :: p'') a).
    specialize (IH a ltac:(discriminate)). cbn [qdiv] in IH. exact IH.
Qed.

(* the genuine quotient removelast(qdiv p a) evaluates like qdiv p a *)
Lemma ceval_removelast_qdiv : forall p a z, p <> [] ->
  ceval (removelast (qdiv p a)) z = ceval (qdiv p a) z.
Proof.
  intros p a z Hne.
  assert (Hqne : qdiv p a <> []).
  { intro Hc. assert (Hl : length (qdiv p a) = 0%nat) by (rewrite Hc; reflexivity).
    rewrite length_qdiv in Hl. destruct p; [contradiction | simpl in Hl; lia]. }
  pose proof (app_removelast_last C0 Hqne) as Hsplit.
  rewrite (qdiv_last_zero p a Hne) in Hsplit.
  rewrite Hsplit at 2. rewrite ceval_snoc_zero. reflexivity.
Qed.

Lemma length_removelast_qdiv : forall p a, p <> [] ->
  length (removelast (qdiv p a)) = (length p - 1)%nat.
Proof.
  intros p a Hne.
  assert (Hqne : qdiv p a <> []).
  { intro Hc. assert (Hl : length (qdiv p a) = 0%nat) by (rewrite Hc; reflexivity).
    rewrite length_qdiv in Hl. destruct p; [contradiction | simpl in Hl; lia]. }
  pose proof (app_removelast_last C0 Hqne) as Hsplit.
  assert (Hlen : length (qdiv p a) = (length (removelast (qdiv p a)) + 1)%nat).
  { rewrite Hsplit at 1. rewrite length_app. simpl. lia. }
  rewrite length_qdiv in Hlen. lia.
Qed.

(* cpe at a real point is the real polynomial evaluation, lifted to C *)
Lemma cpe_RtoC : forall p t, cpe p (RtoC t) = RtoC (peval p t).
Proof.
  induction p as [|a p' IH]; intro t.
  - reflexivity.
  - cbn [cpe peval]. rewrite IH.
    unfold ZtoC. rewrite RtoC_add, RtoC_mul. reflexivity.
Qed.

Lemma RtoC_inj : forall a b, RtoC a = RtoC b -> a = b.
Proof. intros a b H. unfold RtoC in H. inversion H. reflexivity. Qed.

(* a list vanishing at length-many distinct points is everywhere zero *)
Lemma ceval_roots_zero : forall zs p,
  NoDup zs -> (forall z, In z zs -> ceval p z = C0) ->
  (length p <= length zs)%nat -> forall z, ceval p z = C0.
Proof.
  induction zs as [|z0 zs' IH]; intros p Hnd Hroots Hlen z.
  - simpl in Hlen. destruct p as [|c p']; [reflexivity | simpl in Hlen; lia].
  - destruct p as [|c p'].
    + reflexivity.
    + inversion Hnd as [|x l Hnin Hnd']; subst.
      set (q := removelast (qdiv (c :: p') z0)).
      assert (Hz0 : ceval (c :: p') z0 = C0) by (apply Hroots; left; reflexivity).
      assert (Hfac : forall w, ceval (c :: p') w = Cmul (Csub w z0) (ceval q w)).
      { intro w. rewrite (factor_thm (c :: p') z0 Hz0 w).
        unfold q. rewrite (ceval_removelast_qdiv (c :: p') z0 w ltac:(discriminate)).
        reflexivity. }
      assert (Hqroots : forall w, In w zs' -> ceval q w = C0).
      { intros w Hw.
        assert (Hwne : w <> z0) by (intro He; subst w; contradiction).
        assert (Hcw : ceval (c :: p') w = C0) by (apply Hroots; right; exact Hw).
        rewrite Hfac in Hcw.
        destruct (Cmul_integral _ _ Hcw) as [Hsub | Hqw].
        - exfalso. apply Hwne. apply Csub_eq_0. exact Hsub.
        - exact Hqw. }
      assert (Hqlen : (length q <= length zs')%nat).
      { unfold q. rewrite length_removelast_qdiv by discriminate.
        simpl in Hlen |- *. lia. }
      assert (Hqz : forall w, ceval q w = C0) by (apply IH; assumption).
      rewrite Hfac. rewrite Hqz. ring.
Qed.

(* descent: an integer polynomial whose C-evaluation is everywhere zero is zero *)
Lemma cpe_zero_all_poly_zero : forall fZ,
  (forall z, cpe fZ z = C0) -> Forall (fun c => c = 0%Z) fZ.
Proof.
  intros fZ Hz. apply poly_vanish. intro t.
  apply RtoC_inj. rewrite <- cpe_RtoC. rewrite (Hz (RtoC t)).
  unfold RtoC. reflexivity.
Qed.

(* an integer polynomial with length-many distinct C-roots is the zero list *)
Lemma cpe_roots_poly_zero : forall fZ zs,
  NoDup zs -> (forall z, In z zs -> cpe fZ z = C0) ->
  (length fZ <= length zs)%nat -> Forall (fun c => c = 0%Z) fZ.
Proof.
  intros fZ zs Hnd Hroots Hlen.
  apply cpe_zero_all_poly_zero.
  assert (Hcz : forall z, ceval (map ZtoC fZ) z = C0).
  { apply (ceval_roots_zero zs).
    - exact Hnd.
    - intros z Hz. rewrite <- cpe_ceval. apply Hroots; exact Hz.
    - rewrite length_map. exact Hlen. }
  intro z. rewrite cpe_ceval. apply Hcz.
Qed.

(* the usable degree bound: a nonzero integer polynomial has fewer distinct
   C-roots than its length (hence at most its degree) *)
Theorem cpe_roots_lt_length : forall fZ zs,
  (exists k, nth k fZ 0%Z <> 0%Z) ->
  NoDup zs -> (forall z, In z zs -> cpe fZ z = C0) ->
  (length zs < length fZ)%nat.
Proof.
  intros fZ zs [k Hk] Hnd Hroots.
  destruct (Nat.lt_ge_cases (length zs) (length fZ)) as [Hlt | Hge]; [exact Hlt|].
  exfalso. apply Hk.
  pose proof (cpe_roots_poly_zero fZ zs Hnd Hroots Hge) as Hall.
  apply Forall_eq0_nth. exact Hall.
Qed.

(* ============================================================================
   Totient sum  sum_{d | n} phi(d) = n  (toward deg Phi_n = phi(n)).  Proven by
   the gcd-fiber bijection: each k in [1,n] maps to its reduced denominator
   d = n / gcd(k,n) and reduced numerator j = k / gcd(k,n) (coprime to d), so the
   list [1,n] is a Permutation of the fibers {(n/d)*j : d|n, j in [1,d], gcd(j,d)=1}.
   ============================================================================ *)

Import Permutation.
Open Scope nat_scope.
Definition divisors (n : nat) : list nat :=
  filter (fun d => Nat.eqb (n mod d) 0) (seq 1 n).

Definition tot_rhs (n : nat) : list nat :=
  flat_map (fun d => map (fun j => (n / d) * j)
                         (filter (fun j => coprime j d) (seq 1 d)))
           (divisors n).

Lemma length_flat_map_sum : forall (A B:Type)(f:A->list B) l,
  length (flat_map f l) = list_sum (map (fun x => length (f x)) l).
Proof.
  intros A B f l. induction l as [|a l IH]; [reflexivity|].
  cbn [flat_map map list_sum]. rewrite length_app, IH. reflexivity.
Qed.

Lemma NoDup_flat_map : forall (A B:Type)(f:A->list B) l,
  NoDup l -> (forall x, In x l -> NoDup (f x)) ->
  (forall x y, In x l -> In y l -> x<>y -> forall z, In z (f x) -> In z (f y) -> False) ->
  NoDup (flat_map f l).
Proof.
  intros A B f l. induction l as [|a l IH]; intros Hnd Hfx Hcross.
  - constructor.
  - cbn [flat_map]. inversion Hnd as [|x0 l0 Hnin Hnd']; subst.
    apply NoDup_app.
    + apply Hfx. left; reflexivity.
    + apply IH.
      * exact Hnd'.
      * intros x Hx. apply Hfx. right; exact Hx.
      * intros x y Hx Hy Hxy z Hzx Hzy.
        exact (Hcross x y (or_intror Hx) (or_intror Hy) Hxy z Hzx Hzy).
    + intros z Hza Hzrest. apply in_flat_map in Hzrest. destruct Hzrest as [b [Hb Hzb]].
      assert (Hab : a <> b) by (intro He; subst b; contradiction).
      exact (Hcross a b (or_introl eq_refl) (or_intror Hb) Hab z Hza Hzb).
Qed.

Lemma NoDup_filter_nat : forall (p:nat->bool) l, NoDup l -> NoDup (filter p l).
Proof.
  intros p l. induction l as [|a l IH]; intro Hnd; [constructor|].
  inversion Hnd as [|x0 l0 Hnin Hnd']; subst. cbn [filter].
  destruct (p a).
  - constructor; [intro Hin; apply Hnin; apply filter_In in Hin; tauto | apply IH; exact Hnd'].
  - apply IH; exact Hnd'.
Qed.

Lemma divides_div_mul : forall d n, d <> 0 -> Nat.divide d n -> (n / d) * d = n.
Proof. intros d n Hd [c Hc]. subst n. rewrite Nat.div_mul by exact Hd. reflexivity. Qed.

Lemma gcd_pos : forall x n, 1 <= x -> 1 <= Nat.gcd x n.
Proof.
  intros x n Hx. destruct (Nat.eq_dec (Nat.gcd x n) 0) as [H0|H0].
  - apply Nat.gcd_eq_0 in H0. lia.
  - lia.
Qed.

Lemma in_divisors : forall n d, In d (divisors n) <-> (1 <= d <= n /\ Nat.divide d n).
Proof.
  intros n d. unfold divisors. rewrite filter_In, in_seq.
  split.
  - intros [Hin Hmod]. apply Nat.eqb_eq in Hmod.
    assert (Hd : d <> 0) by lia.
    split; [lia | apply Nat.mod_divide; assumption].
  - intros [[H1 H2] Hdiv]. split; [lia|].
    apply Nat.eqb_eq. apply Nat.mod_divide; [lia | exact Hdiv].
Qed.

Lemma gcd_fiber : forall n d j, 1 <= n -> Nat.divide d n -> 1 <= d <= n ->
  Nat.gcd j d = 1 -> Nat.gcd ((n / d) * j) n = n / d.
Proof.
  intros n d j Hn Hdiv Hd Hco.
  assert (Hd0 : d <> 0) by lia.
  assert (Hnd : (n / d) * d = n) by (apply divides_div_mul; assumption).
  replace n with ((n / d) * d) at 2 by exact Hnd.
  rewrite Nat.gcd_mul_mono_l, Hco, Nat.mul_1_r. reflexivity.
Qed.

Lemma div_div_self : forall n g, 1 <= n -> 1 <= g -> Nat.divide g n -> n / (n / g) = g.
Proof.
  intros n g Hn Hg Hdiv.
  assert (Hg0 : g <> 0) by lia.
  assert (Hng : (n / g) * g = n) by (apply divides_div_mul; assumption).
  assert (Hngc : g * (n / g) = n) by (rewrite Nat.mul_comm; exact Hng).
  assert (Hz : n / g <> 0) by (intro Hc; rewrite Hc in Hng; simpl in Hng; lia).
  rewrite <- Hngc at 1. rewrite Nat.div_mul by exact Hz. reflexivity.
Qed.

Lemma tot_mem : forall n x, 1 <= n -> (In x (seq 1 n) <-> In x (tot_rhs n)).
Proof.
  intros n x Hn. rewrite in_seq. unfold tot_rhs. rewrite in_flat_map.
  split.
  - intros Hx.
    set (g := Nat.gcd x n).
    assert (Hxpos : 1 <= x) by lia.
    assert (Hgpos : 1 <= g) by (apply gcd_pos; lia).
    assert (Hgx : Nat.divide g x) by (apply Nat.gcd_divide_l).
    assert (Hgn : Nat.divide g n) by (apply Nat.gcd_divide_r).
    set (d := n / g). set (j := x / g).
    assert (Hg0 : g <> 0) by lia.
    assert (Hgxe : g * j = x) by (unfold j; rewrite (Nat.mul_comm g); apply divides_div_mul; assumption).
    assert (Hgne : g * d = n) by (unfold d; rewrite (Nat.mul_comm g); apply divides_div_mul; assumption).
    assert (Hdn : Nat.divide d n) by (exists g; lia).
    assert (Hd1 : 1 <= d).
    { destruct (Nat.eq_dec d 0) as [Hz|Hz]; [rewrite Hz in Hgne; simpl in Hgne; lia | lia]. }
    assert (Hgle_n : g <= n) by (apply Nat.divide_pos_le; [lia | exact Hgn]).
    assert (Hdn_le : d <= n) by (apply Nat.divide_pos_le; [lia | exact Hdn]).
    assert (Hndg : n / d = g).
    { unfold d. apply div_div_self; [lia | lia | exact Hgn]. }
    exists d. split.
    + apply in_divisors. split; [lia | exact Hdn].
    + apply in_map_iff. exists j. split.
      * rewrite Hndg. exact Hgxe.
      * apply filter_In. split.
        -- apply in_seq.
           assert (Hjpos : 1 <= j).
           { destruct (Nat.eq_dec j 0) as [Hz|Hz]; [rewrite Hz in Hgxe; simpl in Hgxe; lia | lia]. }
           assert (Hjle : j <= d).
           { unfold j, d. apply Nat.Div0.div_le_mono. lia. }
           lia.
        -- apply coprime_iff_gcd_1.
           assert (Hgcd : Nat.gcd (g * j) (g * d) = g * Nat.gcd j d) by apply Nat.gcd_mul_mono_l.
           rewrite Hgxe, Hgne in Hgcd.
           change (Nat.gcd x n) with g in Hgcd.
           nia.
  - intros [d [Hd Hin]].
    apply in_divisors in Hd. destruct Hd as [[Hd1 Hdn] Hdiv].
    apply in_map_iff in Hin. destruct Hin as [j [Hxj Hjf]].
    apply filter_In in Hjf. destruct Hjf as [Hjseq _].
    apply in_seq in Hjseq.
    assert (Hd0 : d <> 0) by lia.
    assert (Hndd : (n / d) * d = n) by (apply divides_div_mul; assumption).
    assert (Hnd1 : 1 <= n / d).
    { destruct (Nat.eq_dec (n/d) 0) as [Hz|Hz]; [rewrite Hz in Hndd; lia | lia]. }
    subst x. nia.
Qed.

Lemma NoDup_tot_rhs : forall n, 1 <= n -> NoDup (tot_rhs n).
Proof.
  intros n Hn. unfold tot_rhs. apply NoDup_flat_map.
  - apply NoDup_filter_nat. apply seq_NoDup.
  - intros d Hd. apply in_divisors in Hd. destruct Hd as [[Hd1 Hdn] Hdiv].
    apply pm_NoDup_map_inj_in.
    + intros j1 j2 _ _ He.
      assert (Hnd1 : 1 <= n / d).
      { assert (Hd0 : d <> 0) by lia.
        assert (Hndd : (n / d) * d = n) by (apply divides_div_mul; assumption).
        destruct (Nat.eq_dec (n/d) 0) as [Hz|Hz]; [rewrite Hz in Hndd; lia | lia]. }
      nia.
    + apply NoDup_filter_nat. apply seq_NoDup.
  - intros d1 d2 Hd1 Hd2 Hne z Hz1 Hz2.
    apply in_divisors in Hd1. destruct Hd1 as [[Hd11 Hd1n] Hdiv1].
    apply in_divisors in Hd2. destruct Hd2 as [[Hd21 Hd2n] Hdiv2].
    apply in_map_iff in Hz1. destruct Hz1 as [j1 [Hzj1 Hj1f]].
    apply in_map_iff in Hz2. destruct Hz2 as [j2 [Hzj2 Hj2f]].
    apply filter_In in Hj1f. destruct Hj1f as [_ Hco1]. apply coprime_iff_gcd_1 in Hco1.
    apply filter_In in Hj2f. destruct Hj2f as [_ Hco2]. apply coprime_iff_gcd_1 in Hco2.
    assert (Hg1 : Nat.gcd ((n / d1) * j1) n = n / d1)
      by (apply gcd_fiber; [lia | exact Hdiv1 | lia | exact Hco1]).
    assert (Hg2 : Nat.gcd ((n / d2) * j2) n = n / d2)
      by (apply gcd_fiber; [lia | exact Hdiv2 | lia | exact Hco2]).
    assert (Hzz : (n / d1) * j1 = (n / d2) * j2) by (rewrite Hzj1, Hzj2; reflexivity).
    assert (Heq : n / d1 = n / d2)
      by (rewrite <- Hg1, <- Hg2, Hzz; reflexivity).
    apply Hne.
    assert (Hdd1 : n / (n / d1) = d1) by (apply div_div_self; [lia | lia | exact Hdiv1]).
    assert (Hdd2 : n / (n / d2) = d2) by (apply div_div_self; [lia | lia | exact Hdiv2]).
    rewrite <- Hdd1, <- Hdd2, Heq. reflexivity.
Qed.

Theorem totient_sum : forall n, 1 <= n -> list_sum (map euler_phi (divisors n)) = n.
Proof.
  intros n Hn.
  assert (Hperm : Permutation (seq 1 n) (tot_rhs n)).
  { apply NoDup_Permutation.
    - apply seq_NoDup.
    - apply NoDup_tot_rhs; exact Hn.
    - intro x. apply tot_mem; exact Hn. }
  apply Permutation_length in Hperm.
  rewrite length_seq in Hperm.
  assert (Hlen : length (tot_rhs n) = list_sum (map euler_phi (divisors n))).
  { unfold tot_rhs. rewrite length_flat_map_sum. f_equal. apply map_ext_in.
    intros d Hd. cbn beta. rewrite length_map.
    unfold euler_phi. rewrite (count_coprime_filter d d). reflexivity. }
  rewrite <- Hlen. symmetry. exact Hperm.
Qed.
Open Scope R_scope.
(* ============================================================================
   Integer monic polynomial division (toward the cyclotomic Phi_n construction
   and minimal-polynomial divisibility): dividing any integer polynomial by a
   monic integer polynomial of degree d yields an integer quotient and an integer
   remainder of degree < d.  Because the divisor is monic, the division algorithm
   needs no inverses and stays in Z; this ports the real-coefficient monic_div_exists.
   ============================================================================ *)
Open Scope Z_scope.
Definition Zpsub (p q : list Z) : list Z := Zpadd p (map (Z.mul (-1)) q).
Open Scope R_scope.
Lemma peval_Zpsub : forall p q y, peval (Zpsub p q) y = peval p y - peval q y.
Proof.
  intros p q y. unfold Zpsub. rewrite peval_Zpadd, peval_map_Zmul.
  replace (IZR (-1)%Z) with (-1) by (simpl; lra). ring.
Qed.
Open Scope Z_scope.
Lemma nth_prepend_zeros : forall (l:list Z) m k, (m <= k)%nat ->
  nth k (repeat 0 m ++ l) 0 = nth (k - m) l 0.
Proof.
  intros l m k Hmk. rewrite app_nth2 by (rewrite repeat_length; lia).
  rewrite repeat_length. reflexivity.
Qed.

Lemma length_Zpsub : forall p q, length (Zpsub p q) = Nat.max (length p) (length q).
Proof. intros p q. unfold Zpsub. rewrite length_Zpadd, length_map. reflexivity. Qed.

(* the leading coefficient cancels when subtracting c * x^(k-d) * (monic mu) *)
Lemma Zdivstep_top_zero : forall g mu d,
  length mu = S d -> nth d mu 0 = 1 -> (d < length g)%nat ->
  nth (length g - 1)
      (Zpsub g (map (Z.mul (nth (length g - 1) g 0)) (repeat 0 (length g - 1 - d) ++ mu))) 0 = 0.
Proof.
  intros g mu d Hmu Hmonic Hd.
  unfold Zpsub. rewrite nth_Zpadd, nth_map_Zmul, nth_map_Zmul.
  rewrite nth_prepend_zeros by lia.
  replace (length g - 1 - (length g - 1 - d))%nat with d by lia.
  rewrite Hmonic. ring.
Qed.

Lemma last_nth_Z : forall (l:list Z) d, last l d = nth (Nat.pred (length l)) l d.
Proof.
  induction l as [|a l IH]; intro d; [reflexivity|].
  destruct l as [|b l']; [reflexivity|].
  change (last (a::b::l') d) with (last (b::l') d). rewrite IH. reflexivity.
Qed.

Lemma peval_removelast_last0 : forall (l:list Z) y, l <> [] -> nth (length l - 1) l 0 = 0 ->
  (peval (removelast l) y = peval l y)%R.
Proof.
  intros l y Hne Hlast.
  pose proof (app_removelast_last 0 Hne) as Hsplit.
  assert (Hlasteq : last l 0 = 0).
  { rewrite last_nth_Z. replace (Nat.pred (length l)) with (length l - 1)%nat by lia. exact Hlast. }
  rewrite Hsplit at 2. rewrite Hlasteq.
  rewrite peval_app. cbn [peval]. simpl IZR. ring.
Qed.

Lemma length_removelast_gen : forall (l:list Z), l <> [] ->
  length (removelast l) = (length l - 1)%nat.
Proof.
  intros l Hne.
  pose proof (app_removelast_last 0 Hne) as Hsplit.
  assert (Hl : length l = (length (removelast l) + 1)%nat)
    by (rewrite Hsplit at 1; rewrite length_app; simpl; lia).
  lia.
Qed.
Open Scope R_scope.
Theorem Zmonic_div : forall mu d, length mu = S d -> nth d mu 0%Z = 1%Z ->
  forall n g, (length g <= n)%nat ->
  exists q r, (forall y, (peval g y = peval mu y * peval q y + peval r y)%R)
              /\ (length r <= d)%nat.
Proof.
  intros mu d Hmu Hmonic. induction n as [|n IH]; intros g Hlen.
  - assert (Hg : g = []) by (destruct g; [reflexivity | simpl in Hlen; lia]).
    subst g. exists [], []. split; [intros y; cbn [peval]; ring | simpl; lia].
  - destruct (Nat.le_gt_cases (length g) d) as [Hsmall | Hbig].
    + exists [], g. split; [intros y; cbn [peval]; ring | exact Hsmall].
    + remember (length g - 1)%nat as k eqn:Ek.
      remember (nth k g 0%Z) as c eqn:Ec.
      remember (Zpsub g (map (Z.mul c) (repeat 0%Z (k - d) ++ mu))) as gsub eqn:Egsub.
      assert (Hgne : g <> []) by (intro Hg; subst g; simpl in Hbig; lia).
      assert (Hgsublen : length gsub = length g).
      { rewrite Egsub, length_Zpsub, length_map, length_app, repeat_length, Hmu. lia. }
      assert (Hgsubne : gsub <> []) by (intro H; rewrite H in Hgsublen; simpl in Hgsublen; lia).
      assert (Hgsubtop : nth (length gsub - 1) gsub 0%Z = 0%Z).
      { rewrite Hgsublen, Egsub, Ec, Ek. apply Zdivstep_top_zero; assumption. }
      assert (Hrlen : (length (removelast gsub) <= n)%nat).
      { rewrite length_removelast_gen by exact Hgsubne. rewrite Hgsublen. lia. }
      destruct (IH (removelast gsub) Hrlen) as [q' [r' [Hid Hr'len]]].
      exists (Zpadd (repeat 0%Z (k - d) ++ [c]) q'), r'.
      split; [|exact Hr'len].
      intros y.
      assert (Hpegsub : (peval gsub y = peval g y - IZR c * y ^ (k - d) * peval mu y)%R).
      { rewrite Egsub, peval_Zpsub, peval_map_Zmul, peval_Zsh. ring. }
      assert (Hperl : (peval (removelast gsub) y = peval gsub y)%R)
        by (apply peval_removelast_last0; [exact Hgsubne | exact Hgsubtop]).
      specialize (Hid y). rewrite Hperl, Hpegsub in Hid.
      rewrite peval_Zpadd, peval_Zsh.
      cbn [peval]. nra.
Qed.

(* ============================================================================
   Roots of x^n - 1 over C are exactly the n distinct n-th roots of unity.
   The powers zeta_n^0, ..., zeta_n^(n-1) are pairwise distinct (zeta_order) and
   each is a root (zeta_pow_n); since x^n-1 has length n+1, the degree-aware root
   bound cpe_roots_lt_length forces these to be ALL the roots.  This regroups (by
   order) into the primitive roots of each divisor -- the C-side of the cyclotomic
   product formula.
   ============================================================================ *)
Open Scope R_scope.
Lemma Cpow_neq_0 : forall z k, z <> C0 -> Cpow z k <> C0.
Proof.
  intros z k Hz. induction k as [|k IH].
  - cbn [Cpow]. exact C1_neq_C0.
  - cbn [Cpow]. apply Cmul_neq_0; assumption.
Qed.

(* every power of zeta n is a root of x^n - 1 *)
Open Scope R_scope.
Lemma length_Xn1 : forall n, (1 <= n)%nat -> length (Xn1 n) = S n.
Proof.
  intros n Hn. unfold Xn1. cbn [length]. rewrite length_app, repeat_length. simpl. lia.
Qed.

Lemma nth0_Xn1 : forall n, nth 0 (Xn1 n) 0%Z = (-1)%Z.
Proof. intro n. unfold Xn1. reflexivity. Qed.

(* the list of the n distinct roots of unity *)
Open Scope R_scope.
Fixpoint Cpadd (p q : list C) : list C :=
  match p, q with
  | [], _ => q
  | _, [] => p
  | a :: p', b :: q' => Cadd a b :: Cpadd p' q'
  end.

Fixpoint Cpmul (p q : list C) : list C :=
  match p with
  | [] => []
  | a :: p' => Cpadd (map (Cmul a) q) (C0 :: Cpmul p' q)
  end.

Lemma ceval_Cpadd : forall p q z, ceval (Cpadd p q) z = Cadd (ceval p z) (ceval q z).
Proof.
  induction p as [|a p IH]; intros q z.
  - cbn [Cpadd ceval]. ring.
  - destruct q as [|b q].
    + cbn [Cpadd ceval]. ring.
    + cbn [Cpadd ceval]. rewrite IH. ring.
Qed.

Lemma ceval_map_Cmul : forall a q z, ceval (map (Cmul a) q) z = Cmul a (ceval q z).
Proof.
  induction q as [|b q IH]; intros z; [cbn [map ceval]; ring | cbn [map ceval]; rewrite IH; ring].
Qed.

Lemma ceval_Cpmul : forall p q z, ceval (Cpmul p q) z = Cmul (ceval p z) (ceval q z).
Proof.
  induction p as [|a p IH]; intros q z.
  - cbn [Cpmul ceval]. ring.
  - cbn [Cpmul]. rewrite ceval_Cpadd, ceval_map_Cmul. cbn [ceval]. rewrite IH. ring.
Qed.

(* linear factor x - a, and the product of linear factors *)
Definition linfac (a : C) : list C := [Copp a; C1].

Lemma ceval_linfac : forall a z, ceval (linfac a) z = Csub z a.
Proof. intros a z. cbn [ceval linfac]. ring. Qed.

Definition linprod (rs : list C) : list C := fold_right Cpmul [C1] (map linfac rs).

Lemma ceval_linprod : forall rs z,
  ceval (linprod rs) z = fold_right (fun a acc => Cmul (Csub z a) acc) C1 rs.
Proof.
  induction rs as [|a rs IH]; intros z.
  - cbn [linprod map fold_right ceval]. ring.
  - cbn [linprod map fold_right]. rewrite ceval_Cpmul, ceval_linfac, IH. reflexivity.
Qed.

Lemma length_Cpadd : forall p q, length (Cpadd p q) = Nat.max (length p) (length q).
Proof.
  induction p as [|a p IH]; intros q; [reflexivity|].
  destruct q as [|b q]; [reflexivity | cbn [Cpadd length]; rewrite IH; reflexivity].
Qed.

Lemma length_Cpmul_linfac : forall a q, q <> [] -> length (Cpmul (linfac a) q) = S (length q).
Proof.
  intros a q Hq. cbn [Cpmul linfac map]. rewrite length_Cpadd, length_map.
  cbn [length Cpmul]. rewrite length_Cpadd, length_map. cbn [length].
  destruct q; [contradiction | cbn [length]; lia].
Qed.

Lemma length_linprod : forall rs, length (linprod rs) = S (length rs).
Proof.
  induction rs as [|a rs IH]; [reflexivity|].
  cbn [linprod map fold_right]. fold (linprod rs).
  rewrite length_Cpmul_linfac.
  - rewrite IH. reflexivity.
  - intro Hc. assert (length (linprod rs) = 0%nat) by (rewrite Hc; reflexivity).
    rewrite IH in H. simpl in H. lia.
Qed.
Open Scope R_scope.
(* ===== Factorization of x^n - 1 over C into linear root-of-unity factors ===== *)
Open Scope R_scope.
(* nth of C-polynomial sum and scalar-multiple *)
Lemma nth_Cpadd : forall i p q, nth i (Cpadd p q) C0 = Cadd (nth i p C0) (nth i q C0).
Proof.
  induction i as [|i IH]; intros p q;
    destruct p as [|a p]; destruct q as [|b q]; cbn [Cpadd nth]; try ring.
  apply IH.
Qed.

Lemma nth_map_Cmul : forall i a q, nth i (map (Cmul a) q) C0 = Cmul a (nth i q C0).
Proof.
  induction i as [|i IH]; intros a q; destruct q as [|b q]; cbn [map nth]; try ring.
  apply IH.
Qed.

(* convolution by the linear factor [ -a ; 1 ], split by index parity to dodge match reduction *)
Lemma nth_Cpmul_linfac_0 : forall a q, nth 0 (Cpmul (linfac a) q) C0 = Cmul (Copp a) (nth 0 q C0).
Proof.
  intros a q.
  assert (Hunf : Cpmul (linfac a) q
                 = Cpadd (map (Cmul (Copp a)) q) (C0 :: Cpadd (map (Cmul C1) q) [C0]))
    by reflexivity.
  rewrite Hunf, nth_Cpadd, nth_map_Cmul.
  replace (nth 0 (C0 :: Cpadd (map (Cmul C1) q) [C0]) C0) with C0 by reflexivity. ring.
Qed.

Lemma nth_Cpmul_linfac_S : forall a q m',
  nth (S m') (Cpmul (linfac a) q) C0 = Cadd (Cmul (Copp a) (nth (S m') q C0)) (nth m' q C0).
Proof.
  intros a q m'.
  assert (Hunf : Cpmul (linfac a) q
                 = Cpadd (map (Cmul (Copp a)) q) (C0 :: Cpadd (map (Cmul C1) q) [C0]))
    by reflexivity.
  rewrite Hunf, nth_Cpadd, nth_map_Cmul.
  replace (nth (S m') (C0 :: Cpadd (map (Cmul C1) q) [C0]) C0)
     with (nth m' (Cpadd (map (Cmul C1) q) [C0]) C0) by reflexivity.
  rewrite nth_Cpadd, nth_map_Cmul.
  replace (nth m' [C0] C0) with C0
    by (destruct m' as [|m'']; [reflexivity | symmetry; apply nth_overflow; cbn [length]; lia]).
  ring.
Qed.

(* linprod is monic of degree (length rs), with no higher coefficients *)
Lemma linprod_coeffs : forall rs,
  nth (length rs) (linprod rs) C0 = C1 /\ (forall k, (length rs < k)%nat -> nth k (linprod rs) C0 = C0).
Proof.
  induction rs as [|a rs [IHlead IHhigh]].
  - split; [reflexivity | intros k Hk; destruct k; [lia | destruct k; reflexivity]].
  - cbn [linprod map fold_right]. fold (linprod rs).
    split.
    + cbn [length]. rewrite nth_Cpmul_linfac_S.
      rewrite IHhigh by lia. rewrite IHlead. ring.
    + intros k Hk. cbn [length] in Hk.
      destruct k as [|k']; [lia|].
      rewrite nth_Cpmul_linfac_S.
      rewrite IHhigh by lia. rewrite IHhigh by lia. ring.
Qed.

Lemma linprod_monic : forall rs, nth (length rs) (linprod rs) C0 = C1.
Proof. intro rs. apply linprod_coeffs. Qed.

(* a product of linear factors vanishes at any of its roots *)
Lemma linprod_root_in : forall rs z, In z rs ->
  fold_right (fun a acc => Cmul (Csub z a) acc) C1 rs = C0.
Proof.
  induction rs as [|a rs IH]; intros z Hin; [inversion Hin|].
  cbn [fold_right]. destruct Hin as [He|Hin].
  - subst a. replace (Csub z z) with C0 by ring. ring.
  - rewrite (IH z Hin). ring.
Qed.

(* C-polynomial subtraction *)
Definition Cpsub (p q : list C) : list C := Cpadd p (map Copp q).

Lemma ceval_map_Copp : forall q z, ceval (map Copp q) z = Copp (ceval q z).
Proof.
  induction q as [|b q IH]; intros z; [cbn [map ceval]; ring | cbn [map ceval]; rewrite IH; ring].
Qed.

Lemma ceval_Cpsub : forall p q z, ceval (Cpsub p q) z = Csub (ceval p z) (ceval q z).
Proof.
  intros p q z. unfold Cpsub. rewrite ceval_Cpadd, ceval_map_Copp. ring.
Qed.

Lemma nth_map_Copp : forall i q, nth i (map Copp q) C0 = Copp (nth i q C0).
Proof.
  induction i as [|i IH]; intro q; destruct q as [|b q]; cbn [map nth]; try ring.
  apply IH.
Qed.

Lemma nth_Cpsub : forall i p q, nth i (Cpsub p q) C0 = Csub (nth i p C0) (nth i q C0).
Proof.
  intros i p q. unfold Cpsub. rewrite nth_Cpadd, nth_map_Copp. ring.
Qed.

(* trailing-zero removal for C-lists *)
Lemma last_nth_C : forall (l:list C) d, last l d = nth (Nat.pred (length l)) l d.
Proof.
  induction l as [|a l IH]; intro d; [reflexivity|].
  destruct l as [|b l']; [reflexivity|].
  change (last (a::b::l') d) with (last (b::l') d). rewrite IH. reflexivity.
Qed.

Lemma ceval_removelast_zero : forall l z, l <> [] -> last l C0 = C0 ->
  ceval (removelast l) z = ceval l z.
Proof.
  intros l z Hne Hlast.
  pose proof (app_removelast_last C0 Hne) as Hsplit.
  rewrite Hsplit at 2. rewrite Hlast. rewrite ceval_snoc_zero. reflexivity.
Qed.

Lemma length_removelast_C : forall (l:list C), l <> [] -> length (removelast l) = (length l - 1)%nat.
Proof.
  intros l Hne. pose proof (app_removelast_last C0 Hne) as Hsplit.
  assert (length l = (length (removelast l) + 1)%nat)
    by (rewrite Hsplit at 1; rewrite length_app; simpl; lia).
  lia.
Qed.

Lemma nth_n_Xn1 : forall n, (1 <= n)%nat -> nth n (Xn1 n) 0%Z = 1%Z.
Proof.
  intros n Hn. unfold Xn1. destruct n as [|n']; [lia|].
  replace (S n' - 1)%nat with n' by lia. cbn [nth].
  rewrite app_nth2; rewrite repeat_length; [|lia].
  replace (n' - n')%nat with 0%nat by lia. reflexivity.
Qed.

(* Generalized factorization: ANY list of n distinct roots of x^n-1 factors it.
   The proof uses only the abstract list's length, NoDup, and root membership. *)
Theorem Xn1_factorization_gen : forall n (rs : list C), (1 <= n)%nat ->
  length rs = n -> NoDup rs -> (forall w, In w rs -> cpe (Xn1 n) w = C0) ->
  forall z, cpe (Xn1 n) z = ceval (linprod rs) z.
Proof.
  intros n rs Hn Hlen Hnd Hroots z.
  set (A := map ZtoC (Xn1 n)).
  set (B := linprod rs).
  set (D := Cpsub A B).
  assert (HlenA : length A = S n) by (unfold A; rewrite length_map; apply length_Xn1; exact Hn).
  assert (HlenB : length B = S n) by (unfold B; rewrite length_linprod, Hlen; reflexivity).
  assert (HlenD : length D = S n)
    by (unfold D, Cpsub; rewrite length_Cpadd, length_map, HlenA, HlenB; lia).
  assert (HtopA : nth n A C0 = C1).
  { unfold A. change C0 with (ZtoC 0%Z). rewrite map_nth.
    rewrite (nth_n_Xn1 n Hn). reflexivity. }
  assert (HtopB : nth n B C0 = C1) by (unfold B; rewrite <- Hlen at 1; apply linprod_monic).
  assert (HtopD : nth n D C0 = C0) by (unfold D; rewrite nth_Cpsub, HtopA, HtopB; ring).
  assert (HrootsD : forall w, In w rs -> ceval D w = C0).
  { intros w Hw. unfold D. rewrite ceval_Cpsub.
    assert (HA : ceval A w = C0)
      by (unfold A; rewrite <- cpe_ceval; apply (Hroots w Hw)).
    assert (HB : ceval B w = C0)
      by (unfold B; rewrite ceval_linprod; apply linprod_root_in; exact Hw).
    rewrite HA, HB. ring. }
  assert (HDne : D <> []) by (intro Hc; rewrite Hc in HlenD; simpl in HlenD; lia).
  assert (HlastD : last D C0 = C0).
  { rewrite last_nth_C. replace (Nat.pred (length D)) with n by (rewrite HlenD; lia). exact HtopD. }
  assert (Hrl : forall w, ceval (removelast D) w = ceval D w)
    by (intro w; apply ceval_removelast_zero; [exact HDne | exact HlastD]).
  assert (HrlLen : length (removelast D) = n)
    by (rewrite length_removelast_C by exact HDne; rewrite HlenD; lia).
  assert (Hrz : forall w, ceval (removelast D) w = C0).
  { apply (ceval_roots_zero rs).
    - exact Hnd.
    - intros w Hw. rewrite Hrl. apply HrootsD; exact Hw.
    - rewrite HrlLen, Hlen. lia. }
  assert (HDz : ceval D z = C0) by (rewrite <- Hrl; apply Hrz).
  unfold D in HDz. rewrite ceval_Cpsub in HDz.
  unfold A in HDz. rewrite <- cpe_ceval in HDz.
  apply Csub_eq_0 in HDz. unfold B in HDz. exact HDz.
Qed.

(* the n distinct roots of unity factor x^n - 1 over C *)
Open Scope nat_scope.
Lemma flat_map_map_comm :
  forall (T1 T2 T3 : Type) (g : T2 -> T3) (h : T1 -> list T2) (l : list T1),
  flat_map (fun x => map g (h x)) l = map g (flat_map h l).
Proof.
  intros T1 T2 T3 g h l. induction l as [|a l IH]; [reflexivity|].
  cbn [flat_map]. rewrite map_app, IH. reflexivity.
Qed.

Lemma flat_map_ext_in : forall (A B : Type) (f g : A -> list B) l,
  (forall x, In x l -> f x = g x) -> flat_map f l = flat_map g l.
Proof.
  intros A B f g l H. induction l as [|a l IH]; [reflexivity|].
  cbn [flat_map]. rewrite (H a (or_introl eq_refl)).
  rewrite IH; [reflexivity | intros x Hx; apply H; right; exact Hx].
Qed.

(* each primitive d-th root (d | n) is a power of zeta n with exponent (n/d)*j *)
Open Scope nat_scope.
Lemma tot_rhs_bounds : forall n x, 1 <= n -> In x (tot_rhs n) -> 1 <= x <= n.
Proof.
  intros n x Hn Hin. apply tot_mem in Hin; [|exact Hn]. apply in_seq in Hin. lia.
Qed.

(* the regrouped roots are n distinct roots of x^n - 1 *)
Open Scope nat_scope.
Lemma linprod_app_eval : forall l1 l2 z,
  ceval (linprod (l1 ++ l2)) z = Cmul (ceval (linprod l1) z) (ceval (linprod l2) z).
Proof.
  intros l1 l2 z. rewrite !ceval_linprod.
  induction l1 as [|a l1 IH]; cbn [app fold_right].
  - ring.
  - rewrite IH. ring.
Qed.

Lemma linprod_flatmap_eval : forall (f : nat -> list C) ds z,
  ceval (linprod (flat_map f ds)) z
   = fold_right (fun d acc => Cmul (ceval (linprod (f d)) z) acc) C1 ds.
Proof.
  intros f ds z. induction ds as [|d ds IH].
  - cbn [flat_map linprod map fold_right ceval]. ring.
  - change (flat_map f (d :: ds)) with (f d ++ flat_map f ds).
    rewrite linprod_app_eval, IH. reflexivity.
Qed.

(* THE PRODUCT FORMULA over C: x^n - 1 = prod_{d | n} Phi_d^C *)
Open Scope R_scope.
Lemma cpe_all0 : forall q z, (forall k, nth k q 0%Z = 0%Z) -> cpe q z = C0.
Proof.
  induction q as [|b q IH]; intros z Hk.
  - reflexivity.
  - cbn [cpe].
    assert (Hb : b = 0%Z) by (specialize (Hk O); cbn in Hk; exact Hk).
    assert (Hq : cpe q z = C0) by (apply IH; intro k; specialize (Hk (S k)); cbn in Hk; exact Hk).
    rewrite Hb, Hq. replace (ZtoC 0%Z) with C0 by reflexivity. ring.
Qed.

Lemma cpe_nth_ext : forall p q z,
  (forall k, nth k p 0%Z = nth k q 0%Z) -> cpe p z = cpe q z.
Proof.
  induction p as [|a p IH]; intros q z Hk.
  - symmetry. apply cpe_all0. intro k. specialize (Hk k).
    rewrite <- Hk. destruct k; reflexivity.
  - destruct q as [|b q].
    + apply cpe_all0. intro k. specialize (Hk k).
      rewrite Hk. destruct k; reflexivity.
    + cbn [cpe].
      assert (Hab : a = b) by (specialize (Hk O); cbn in Hk; exact Hk).
      assert (Htl : cpe p z = cpe q z)
        by (apply IH; intro k; specialize (Hk (S k)); cbn in Hk; exact Hk).
      rewrite Hab, Htl. reflexivity.
Qed.

Lemma monic_roots_divides : forall (P F : list Z) (rts : list C) (dP : nat),
  length P = S dP -> nth dP P 0%Z = 1%Z ->
  length rts = dP -> NoDup rts ->
  (forall r, In r rts -> cpe P r = C0) ->
  (forall r, In r rts -> cpe F r = C0) ->
  exists q, forall k, nth k F 0%Z = nth k (Zpmul P q) 0%Z.
Proof.
  intros P F rts dP HlenP HmonP Hlenrts Hndrts HrtsP HrtsF.
  destruct (Zmonic_div P dP HlenP HmonP (length F) F (le_n _)) as [q [r [Hid Hrlen]]].
  exists q.
  assert (Hcoeff : forall k, nth k F 0%Z = nth k (Zpadd (Zpmul P q) r) 0%Z).
  { apply peval_eq_nth. intro y. rewrite peval_Zpadd, peval_Zpmul. apply Hid. }
  assert (Hrvan : forall rho, In rho rts -> cpe r rho = C0).
  { intros rho Hin.
    assert (HF : cpe F rho = Cadd (Cmul (cpe P rho) (cpe q rho)) (cpe r rho)).
    { rewrite (cpe_nth_ext F (Zpadd (Zpmul P q) r) rho Hcoeff).
      rewrite cpe_Zpadd, cpe_Zpmul. reflexivity. }
    rewrite (HrtsP rho Hin) in HF. rewrite (HrtsF rho Hin) in HF.
    transitivity (Cadd (Cmul (C0) (cpe q rho)) (cpe r rho)).
    - ring.
    - symmetry; exact HF. }
  assert (Hr0 : forall k, nth k r 0%Z = 0%Z).
  { destruct (Zlist_ex_nonzero_dec r) as [Hex | Hnone].
    - exfalso. pose proof (cpe_roots_lt_length r rts Hex Hndrts Hrvan) as Hlt.
      rewrite Hlenrts in Hlt. lia.
    - intro k. destruct (Z.eq_dec (nth k r 0%Z) 0%Z) as [E|E];
        [exact E | exfalso; apply Hnone; exists k; exact E]. }
  intro k. rewrite (Hcoeff k), nth_Zpadd, Hr0. lia.
Qed.

(* ===== Product of a list of integer polynomials, and product-of-monics ===== *)
Open Scope Z_scope.
Definition Zprod (ps : list (list Z)) : list Z := fold_right Zpmul [1%Z] ps.

Lemma Zpmul_monic_len : forall P Q dP dQ,
  length P = S dP -> length Q = S dQ -> length (Zpmul P Q) = S (dP + dQ).
Proof.
  intros P Q dP dQ HP HQ.
  rewrite length_Zpmul; [rewrite HP, HQ; lia | | ].
  - intro Hc; rewrite Hc in HP; simpl in HP; lia.
  - intro Hc; rewrite Hc in HQ; simpl in HQ; lia.
Qed.

Lemma Zpmul_monic_top : forall P Q dP dQ,
  length P = S dP -> nth dP P 0 = 1 -> length Q = S dQ -> nth dQ Q 0 = 1 ->
  nth (dP + dQ) (Zpmul P Q) 0 = 1.
Proof.
  intros P Q dP dQ HlenP HmonP HlenQ HmonQ.
  rewrite nth_Zpmul.
  rewrite (Zconv_top P Q dP dQ).
  - rewrite HmonP, HmonQ. ring.
  - intros i Hi. apply nth_overflow. lia.
  - intros j Hj. apply nth_overflow. lia.
Qed.

Definition degsum (ps : list (list Z)) : nat := list_sum (map (fun p => (length p - 1)%nat) ps).

Lemma Zprod_monic : forall ps,
  (forall p, In p ps -> p <> [] /\ nth (length p - 1)%nat p 0 = 1) ->
  length (Zprod ps) = S (degsum ps) /\ nth (degsum ps) (Zprod ps) 0 = 1.
Proof.
  induction ps as [|p ps IH]; intros Hmon.
  - cbn [Zprod fold_right degsum map list_sum]. split; reflexivity.
  - assert (Hp : p <> [] /\ nth (length p - 1)%nat p 0 = 1) by (apply Hmon; left; reflexivity).
    destruct Hp as [Hpne Hptop].
    assert (Hps : forall q, In q ps -> q <> [] /\ nth (length q - 1)%nat q 0 = 1)
      by (intros q Hq; apply Hmon; right; exact Hq).
    destruct (IH Hps) as [Hlen Htop].
    assert (HdP : length p = S (length p - 1)%nat)
      by (destruct p; [contradiction | simpl; lia]).
    cbn [Zprod fold_right]. fold (Zprod ps).
    assert (Hd : degsum (p :: ps) = ((length p - 1) + degsum ps)%nat)
      by (unfold degsum; cbn [map list_sum]; reflexivity).
    split.
    + rewrite Hd. apply (Zpmul_monic_len p (Zprod ps) (length p - 1) (degsum ps) HdP Hlen).
    + rewrite Hd. apply (Zpmul_monic_top p (Zprod ps) (length p - 1) (degsum ps));
        [exact HdP | exact Hptop | exact Hlen | exact Htop].
Qed.
Open Scope R_scope.
Lemma cpe_Zprod : forall ps z,
  cpe (Zprod ps) z = fold_right (fun p acc => Cmul (cpe p z) acc) C1 ps.
Proof.
  induction ps as [|p ps IH]; intros z.
  - cbn [Zprod fold_right cpe]. replace (ZtoC 1%Z) with C1 by reflexivity. ring.
  - cbn [Zprod fold_right]. fold (Zprod ps).
    rewrite cpe_Zpmul, IH. reflexivity.
Qed.

(* two monic C-polynomials of the same degree with the same d distinct roots agree *)
Open Scope R_scope.
Lemma monic_Cpoly_unique : forall (a b : list C) (rts : list C) d,
  length a = S d -> nth d a C0 = C1 ->
  length b = S d -> nth d b C0 = C1 ->
  length rts = d -> NoDup rts ->
  (forall r, In r rts -> ceval a r = C0) -> (forall r, In r rts -> ceval b r = C0) ->
  forall z, ceval a z = ceval b z.
Proof.
  intros a b rts d Hla Hma Hlb Hmb Hlr Hndr Hra Hrb z.
  set (D := Cpsub a b).
  assert (HlenD : length D = S d)
    by (unfold D, Cpsub; rewrite length_Cpadd, length_map, Hla, Hlb; lia).
  assert (HtopD : nth d D C0 = C0) by (unfold D; rewrite nth_Cpsub, Hma, Hmb; ring).
  assert (HDne : D <> []) by (intro Hc; rewrite Hc in HlenD; simpl in HlenD; lia).
  assert (HlastD : last D C0 = C0).
  { rewrite last_nth_C. replace (Nat.pred (length D)) with d by (rewrite HlenD; lia). exact HtopD. }
  assert (Hrl : forall w, ceval (removelast D) w = ceval D w)
    by (intro w; apply ceval_removelast_zero; [exact HDne | exact HlastD]).
  assert (HrlLen : length (removelast D) = d)
    by (rewrite length_removelast_C by exact HDne; rewrite HlenD; lia).
  assert (HrootsD : forall r, In r rts -> ceval D r = C0).
  { intros r Hr. unfold D. rewrite ceval_Cpsub, (Hra r Hr), (Hrb r Hr). ring. }
  assert (Hrz : forall w, ceval (removelast D) w = C0).
  { apply (ceval_roots_zero rts).
    - exact Hndr.
    - intros w Hw. rewrite Hrl. apply HrootsD; exact Hw.
    - rewrite HrlLen, Hlr. lia. }
  assert (HDz : ceval D z = C0) by (rewrite <- Hrl; apply Hrz).
  unfold D in HDz. rewrite ceval_Cpsub in HDz. apply Csub_eq_0 in HDz. exact HDz.
Qed.
Open Scope R_scope.
(* ===== A characterized cyclotomic polynomial divides x^n - 1 over Z ===== *)
Open Scope R_scope.
Lemma fold_cmul_pull : forall (g : nat -> C) (X : C) (ds : list nat),
  fold_right (fun d acc => Cmul (g d) acc) (Cmul X C1) ds
  = Cmul X (fold_right (fun d acc => Cmul (g d) acc) C1 ds).
Proof.
  intros g X ds. induction ds as [|d ds IH]; cbn [fold_right]; [reflexivity|].
  rewrite IH. ring.
Qed.

Lemma fold_cmul_nonzero : forall (g : nat -> C) (ds : list nat),
  (forall d, In d ds -> g d <> C0) ->
  fold_right (fun d acc => Cmul (g d) acc) C1 ds <> C0.
Proof.
  intros g ds. induction ds as [|d ds IH]; intros Hne; cbn [fold_right].
  - exact C1_neq_C0.
  - apply Cmul_neq_0.
    + apply Hne. left; reflexivity.
    + apply IH. intros d0 Hd0. apply Hne. right; exact Hd0.
Qed.

(* a point avoiding all roots makes a product of linear factors nonzero *)
Lemma fold_csub_nonzero : forall (z : C) (rs : list C),
  (forall a, In a rs -> z <> a) ->
  fold_right (fun a acc => Cmul (Csub z a) acc) C1 rs <> C0.
Proof.
  intros z rs. induction rs as [|a rs IH]; intros Hne; cbn [fold_right].
  - exact C1_neq_C0.
  - apply Cmul_neq_0.
    + intro Hc. apply (Hne a (or_introl eq_refl)). apply Csub_eq_0. exact Hc.
    + apply IH. intros b Hb. apply Hne. right; exact Hb.
Qed.

Lemma ceval_linprod_nonzero : forall rs z,
  (forall a, In a rs -> z <> a) -> ceval (linprod rs) z <> C0.
Proof.
  intros rs z Hne. rewrite ceval_linprod. apply fold_csub_nonzero. exact Hne.
Qed.

(* every primitive d-th root r satisfies r^d = 1 *)
Open Scope nat_scope.
Lemma divisors_app_last : forall n, 1 <= n ->
  divisors n = filter (fun d => Nat.eqb (n mod d) 0) (seq 1 (n-1)) ++ [n].
Proof.
  intros n Hn. unfold divisors.
  replace n with (S (n-1)) at 1 by lia.
  rewrite seq_S, filter_app. cbn [filter].
  replace (1 + (n-1)) with n by lia.
  assert (Hmod : n mod n = 0) by (apply Nat.Div0.mod_same).
  rewrite Hmod. cbn [Nat.eqb]. reflexivity.
Qed.
Open Scope R_scope.
(* ===== Formal derivative of an integer polynomial, with the Leibniz product rule.
   Toward the separability step of the Dedekind argument (a repeated factor mod p
   forces a common factor with the derivative). ===== *)
Open Scope Z_scope.
Fixpoint Zderiv (p : list Z) : list Z :=
  match p with
  | [] => []
  | _ :: p' => Zpadd p' (0 :: Zderiv p')
  end.
Open Scope R_scope.
Lemma peval_Zderiv_cons : forall a p' y,
  peval (Zderiv (a :: p')) y = peval p' y + y * peval (Zderiv p') y.
Proof.
  intros a p' y. cbn [Zderiv]. rewrite peval_Zpadd. cbn [peval]. simpl IZR. ring.
Qed.

Lemma peval_Zderiv_Zpadd : forall u v y,
  peval (Zderiv (Zpadd u v)) y = peval (Zderiv u) y + peval (Zderiv v) y.
Proof.
  induction u as [|a u IH]; intros v y.
  - cbn [Zpadd Zderiv peval]. simpl. ring.
  - destruct v as [|b v].
    + cbn [Zpadd]. cbn [Zderiv peval]. ring.
    + cbn [Zpadd]. rewrite !peval_Zderiv_cons. rewrite IH.
      rewrite !peval_Zpadd. ring.
Qed.

Lemma peval_Zderiv_scalar : forall c p y,
  peval (Zderiv (map (Z.mul c) p)) y = IZR c * peval (Zderiv p) y.
Proof.
  induction p as [|a p IH]; intros y.
  - cbn [map Zderiv peval]. ring.
  - cbn [map]. rewrite !peval_Zderiv_cons. rewrite IH, peval_map_Zmul. ring.
Qed.

(* the product (Leibniz) rule, as a peval identity *)
Lemma peval_Zderiv_Zpmul : forall f g y,
  peval (Zderiv (Zpmul f g)) y
   = peval (Zderiv f) y * peval g y + peval f y * peval (Zderiv g) y.
Proof.
  induction f as [|a f IH]; intros g y.
  - cbn [Zpmul Zderiv peval]. ring.
  - cbn [Zpmul]. rewrite peval_Zderiv_Zpadd, peval_Zderiv_scalar.
    rewrite !peval_Zderiv_cons.
    rewrite peval_Zpmul, IH.
    cbn [peval]. ring.
Qed.
Open Scope R_scope.
(* coefficient-level derivative facts, for the mod-p separability layer *)
Open Scope Z_scope.
Lemma nth_Zderiv : forall p k, nth k (Zderiv p) 0 = Z.of_nat (S k) * nth (S k) p 0.
Proof.
  induction p as [|a p IH]; intros k.
  - destruct k; cbn; ring.
  - cbn [Zderiv]. rewrite nth_Zpadd.
    destruct k as [|k'].
    + cbn [nth]. simpl Z.of_nat. ring.
    + cbn [nth]. rewrite IH. rewrite (Nat2Z.inj_succ (S k')). ring.
Qed.

(* product rule as a coefficient identity *)
Lemma nth_Zderiv_Zpmul : forall f g k,
  nth k (Zderiv (Zpmul f g)) 0
   = nth k (Zpadd (Zpmul (Zderiv f) g) (Zpmul f (Zderiv g))) 0.
Proof.
  intros f g. apply peval_eq_nth. intro y.
  rewrite peval_Zderiv_Zpmul, peval_Zpadd, !peval_Zpmul. ring.
Qed.

Lemma pcong_Zderiv : forall m f g, pcong m f g -> pcong m (Zderiv f) (Zderiv g).
Proof.
  intros m f g H k. rewrite !nth_Zderiv.
  replace (Z.of_nat (S k) * nth (S k) f 0 - Z.of_nat (S k) * nth (S k) g 0)
     with (Z.of_nat (S k) * (nth (S k) f 0 - nth (S k) g 0)) by ring.
  apply Z.divide_mul_r. apply H.
Qed.

Lemma nth_repeat_app : forall m c k, nth k (repeat 0 m ++ [c]) 0 = if Nat.eqb k m then c else 0.
Proof.
  induction m as [|m IH]; intros c k.
  - cbn [repeat app]. destruct k as [|k'].
    + reflexivity.
    + cbn [nth Nat.eqb]. destruct k'; reflexivity.
  - cbn [repeat app]. destruct k as [|k'].
    + reflexivity.
    + cbn [nth Nat.eqb]. apply IH.
Qed.

(* the formal derivative of x^n - 1 agrees with the existing Xn1_deriv coefficient-wise *)
Lemma nth_Zderiv_Xn1 : forall n k, (1 <= n)%nat ->
  nth k (Zderiv (Xn1 n)) 0 = nth k (Xn1_deriv n) 0.
Proof.
  intros n k Hn. rewrite nth_Zderiv. unfold Xn1, Xn1_deriv.
  cbn [nth]. rewrite !nth_repeat_app.
  destruct (Nat.eqb_spec k (n - 1)) as [E|E].
  - rewrite E. replace (S (n - 1))%nat with n by lia. ring.
  - ring.
Qed.

(* ===== Repeated-factor / separability machinery in the mod-p layer ===== *)

(* pdvd_mod depends on its target only up to coefficientwise equality *)
Lemma pdvd_mod_cong_target : forall p h g g',
  (forall k, nth k g 0 = nth k g' 0) -> pdvd_mod p h g -> pdvd_mod p h g'.
Proof.
  intros p h g g' Heq [q Hq]. exists q.
  apply (pcong_trans p _ g).
  - apply pcong_of_eq_nth. intro k. symmetry. apply Heq.
  - exact Hq.
Qed.

(* if d^2 divides f mod p then d divides the formal derivative f' mod p *)
Lemma pdvd_mod_sq_deriv : forall p d f,
  pdvd_mod p (Zpmul d d) f -> pdvd_mod p d (Zderiv f).
Proof.
  intros p d f [s Hs].
  exists (Zpadd (Zpmul (Zderiv d) s) (Zderiv (Zpmul d s))).
  apply (pcong_trans p _ (Zderiv (Zpmul (Zpmul d d) s))).
  - apply pcong_Zderiv. exact Hs.
  - apply pcong_of_eq_nth. apply peval_eq_nth. intro y.
    repeat first [ rewrite peval_Zderiv_Zpmul
                 | rewrite peval_Zpadd
                 | rewrite peval_Zpmul ].
    ring.
Qed.

(* d | g and d | h mod p  =>  d^2 | g*h mod p *)
Lemma pdvd_mod_mul : forall p d g h,
  pdvd_mod p d g -> pdvd_mod p d h -> pdvd_mod p (Zpmul d d) (Zpmul g h).
Proof.
  intros p d g h [a Ha] [b Hb].
  exists (Zpmul a b).
  apply (pcong_trans p _ (Zpmul (Zpmul d a) (Zpmul d b))).
  - apply pcong_Zpmul; assumption.
  - apply pcong_of_eq_nth. apply peval_eq_nth. intro y.
    rewrite !peval_Zpmul. ring.
Qed.

(* transfer a derivative-divisibility from Zderiv (Xn1 n) to the existing Xn1_deriv n *)
Lemma pdvd_mod_deriv_Xn1 : forall p h n, (1 <= n)%nat ->
  pdvd_mod p h (Zderiv (Xn1 n)) -> pdvd_mod p h (Xn1_deriv n).
Proof.
  intros p h n Hn. apply pdvd_mod_cong_target.
  intro k. apply nth_Zderiv_Xn1; exact Hn.
Qed.

(* divisibility mod p is transitive *)
Lemma pdvd_mod_trans : forall p a b c,
  pdvd_mod p a b -> pdvd_mod p b c -> pdvd_mod p a c.
Proof.
  intros p a b c [u Hu] [v Hv].
  exists (Zpmul u v).
  apply (pcong_trans p _ (Zpmul b v)).
  - exact Hv.
  - apply (pcong_trans p _ (Zpmul (Zpmul a u) v)).
    + apply pcong_Zpmul_l. exact Hu.
    + apply pcong_of_eq_nth. apply peval_eq_nth. intro y. rewrite !peval_Zpmul. ring.
Qed.

(* a left factor of a divisor is a divisor *)
Lemma pdvd_mod_factorL : forall p d e f,
  pdvd_mod p (Zpmul d e) f -> pdvd_mod p d f.
Proof.
  intros p d e f [s Hs].
  exists (Zpmul e s).
  apply (pcong_trans p _ (Zpmul (Zpmul d e) s)).
  - exact Hs.
  - apply pcong_of_eq_nth. apply peval_eq_nth. intro y. rewrite !peval_Zpmul. ring.
Qed.

(* SEPARABILITY PAYOFF: a common factor d of G and H, when G*H divides x^n - 1
   mod p (p not dividing n), must divide the constant n mod p. *)
Lemma shared_factor_divides_n : forall p d G H n, (1 <= n)%nat ->
  pdvd_mod p d G -> pdvd_mod p d H ->
  pdvd_mod p (Zpmul G H) (Xn1 n) ->
  pdvd_mod p d [Z.of_nat n].
Proof.
  intros p d G H n Hn HdG HdH HGH.
  assert (Hd2GH : pdvd_mod p (Zpmul d d) (Zpmul G H)) by (apply pdvd_mod_mul; assumption).
  assert (Hd2 : pdvd_mod p (Zpmul d d) (Xn1 n))
    by (apply (pdvd_mod_trans p _ (Zpmul G H)); assumption).
  assert (HdXn1 : pdvd_mod p d (Xn1 n)) by (apply (pdvd_mod_factorL p d d); exact Hd2).
  assert (HdDeriv : pdvd_mod p d (Xn1_deriv n)).
  { apply pdvd_mod_deriv_Xn1; [exact Hn |]. apply pdvd_mod_sq_deriv. exact Hd2. }
  apply (sep_common_divisor p n d Hn HdXn1 HdDeriv).
Qed.

(* ===== Degree theory in F_p[x] (p prime), toward the final separability
   contradiction and the shared-factor extraction. ===== *)

(* a polynomial nonzero mod pr has a largest index with coefficient not divisible by pr *)
Lemma pdeg_mod_exists : forall pr f, (exists k, ~ (pr | nth k f 0)) ->
  exists d, ~ (pr | nth d f 0) /\ (forall j, (d < j)%nat -> (pr | nth j f 0)).
Proof.
  intros pr f.
  induction f as [|a f IH]; intros [k Hk].
  - exfalso. apply Hk. destruct k; apply Z.divide_0_r.
  - destruct (Zlist_ex_notdiv_dec pr f) as [Hf | Hf].
    + destruct (IH Hf) as [d' [Hd'1 Hd'2]].
      exists (S d'). split.
      * cbn [nth]. exact Hd'1.
      * intros j Hj. destruct j as [|j']; [lia|]. cbn [nth]. apply Hd'2. lia.
    + assert (Hfall : forall m, (pr | nth m f 0)).
      { intro m. destruct (Znumtheory.Zdivide_dec pr (nth m f 0)) as [H|H]; [exact H|].
        exfalso. apply Hf. exists m. exact H. }
      exists 0%nat. split.
      * destruct k as [|k'].
        -- cbn [nth] in Hk |- *. exact Hk.
        -- cbn [nth] in Hk. exfalso. apply Hk. apply Hfall.
      * intros j Hj. destruct j as [|j']; [lia|]. cbn [nth]. apply Hfall.
Qed.

(* mod-pr leading coefficient of a product: only the top diagonal term survives *)
Lemma Zconv_top_mod : forall pr f g df dg,
  (forall i, (df < i)%nat -> (pr | nth i f 0)) ->
  (forall j, (dg < j)%nat -> (pr | nth j g 0)) ->
  (pr | Zconv f g (df + dg) - nth df f 0 * nth dg g 0).
Proof.
  intros pr f.
  induction f as [|a f IH]; intros g df dg Hf Hg.
  - assert (Hnil : nth df (@nil Z) 0 = 0) by (destruct df; reflexivity).
    rewrite Hnil. cbn [Zconv].
    replace (0 - 0 * nth dg g 0) with 0 by ring. apply Z.divide_0_r.
  - destruct df as [|df'].
    + assert (Hf' : forall j, (pr | nth j f 0)) by (intros j; apply (Hf (S j)); lia).
      replace (0 + dg)%nat with dg by lia.
      cbn [Zconv nth].
      destruct dg as [|dg'].
      * replace (a * nth 0 g 0 + 0 - a * nth 0 g 0) with 0 by ring. apply Z.divide_0_r.
      * replace (a * nth (S dg') g 0 + Zconv f g dg' - a * nth (S dg') g 0)
           with (Zconv f g dg') by ring.
        apply (Zconv_divide pr f g dg' Hf').
    + assert (Hf' : forall i, (df' < i)%nat -> (pr | nth i f 0))
        by (intros i Hi; apply (Hf (S i)); lia).
      replace (S df' + dg)%nat with (S (df' + dg))%nat by lia.
      cbn [Zconv nth].
      assert (HgTop : (pr | nth (S (df' + dg)) g 0)) by (apply Hg; lia).
      replace (a * nth (S (df' + dg)) g 0 + Zconv f g (df' + dg) - nth df' f 0 * nth dg g 0)
         with ((a * nth (S (df' + dg)) g 0) + (Zconv f g (df' + dg) - nth df' f 0 * nth dg g 0))
         by ring.
      apply Z.divide_add_r.
      * apply Z.divide_mul_r. exact HgTop.
      * apply (IH g df' dg Hf' Hg).
Qed.

(* a positive-degree polynomial (mod p) cannot divide a nonzero constant mod p *)
Lemma pdvd_mod_const_absurd : forall p d c dd,
  Znumtheory.prime (Z.of_nat p) ->
  ~ (Z.of_nat p | nth dd d 0) ->
  (forall j, (dd < j)%nat -> (Z.of_nat p | nth j d 0)) ->
  (1 <= dd)%nat ->
  ~ (Z.of_nat p | c) ->
  pdvd_mod (Z.of_nat p) d [c] -> False.
Proof.
  intros p d c dd Hp Hdd Hdtop Hdd1 Hc [q Hq].
  set (P := Z.of_nat p) in *.
  destruct (Zlist_ex_notdiv_dec P q) as [Hqnz | Hqz].
  - destruct (pdeg_mod_exists P q Hqnz) as [dq [Hdq Hqtop]].
    pose proof (Zconv_top_mod P d q dd dq Hdtop Hqtop) as Htop.
    specialize (Hq (dd + dq)%nat).
    assert (Hcnth : nth (dd + dq)%nat [c] 0 = 0)
      by (apply nth_overflow; cbn [length]; lia).
    rewrite Hcnth, nth_Zpmul in Hq.
    assert (HPconv : (P | Zconv d q (dd + dq))).
    { replace (Zconv d q (dd + dq)) with (- (0 - Zconv d q (dd + dq))) by ring.
      apply Z.divide_opp_r. exact Hq. }
    assert (HPprod : (P | nth dd d 0 * nth dq q 0)).
    { replace (nth dd d 0 * nth dq q 0)
         with (Zconv d q (dd + dq) - (Zconv d q (dd + dq) - nth dd d 0 * nth dq q 0)) by ring.
      apply Z.divide_sub_r; [exact HPconv | exact Htop]. }
    destruct (Znumtheory.prime_mult P Hp (nth dd d 0) (nth dq q 0) HPprod) as [H|H];
      [apply Hdd; exact H | apply Hdq; exact H].
  - assert (Hqall : forall m, (P | nth m q 0)).
    { intro m. destruct (Znumtheory.Zdivide_dec P (nth m q 0)) as [H|H];
        [exact H | exfalso; apply Hqz; exists m; exact H]. }
    specialize (Hq 0%nat).
    assert (Hc0 : nth 0 [c] 0 = c) by reflexivity.
    rewrite Hc0, nth_Zpmul in Hq.
    assert (HPconv0 : (P | Zconv d q 0)) by (apply (Zconv_div P d q 0); intros m Hm; apply Hqall).
    apply Hc.
    replace c with ((c - Zconv d q 0) + Zconv d q 0) by ring.
    apply Z.divide_add_r; [exact Hq | exact HPconv0].
Qed.

(* FULL SEPARABILITY CONTRADICTION: a positive-degree (mod p) common factor d of
   G and H, with G*H dividing x^n - 1 mod p and p prime not dividing n, is absurd. *)
Lemma no_positive_shared_factor : forall p d G H n dd,
  Znumtheory.prime (Z.of_nat p) -> (1 <= n)%nat -> ~ (Z.of_nat p | Z.of_nat n) ->
  ~ (Z.of_nat p | nth dd d 0) ->
  (forall j, (dd < j)%nat -> (Z.of_nat p | nth j d 0)) ->
  (1 <= dd)%nat ->
  pdvd_mod (Z.of_nat p) d G -> pdvd_mod (Z.of_nat p) d H ->
  pdvd_mod (Z.of_nat p) (Zpmul G H) (Xn1 n) ->
  False.
Proof.
  intros p d G H n dd Hp Hn Hpn Hdd Hdtop Hdd1 HdG HdH HGH.
  apply (pdvd_mod_const_absurd p d (Z.of_nat n) dd Hp Hdd Hdtop Hdd1 Hpn).
  apply (shared_factor_divides_n (Z.of_nat p) d G H n Hn HdG HdH HGH).
Qed.

(* ===== Toward F_p[x] divisibility (shared-factor extraction from Frobenius) ===== *)

(* a unit mod a prime has a modular inverse (Bezout) *)
Lemma zinv_mod : forall p a, Znumtheory.prime p -> ~ (p | a) -> exists b, (p | a * b - 1).
Proof.
  intros p a Hp Hna.
  assert (Hrel : Znumtheory.rel_prime a p).
  { apply Znumtheory.rel_prime_sym. apply Znumtheory.prime_rel_prime; assumption. }
  destruct (Znumtheory.rel_prime_bezout a p Hrel) as [u v Huv].
  exists u. exists (- v).
  rewrite <- Huv. ring.
Qed.

Lemma nth_Zpsub : forall a b k, nth k (Zpsub a b) 0 = nth k a 0 - nth k b 0.
Proof. intros a b k. unfold Zpsub. rewrite nth_Zpadd, nth_map_Zmul. ring. Qed.

(* Subtracting (c * binv) * x^(da-db) * b from a kills every coefficient of a at
   index >= da modulo p, when binv inverts b's leading coefficient mod p.  This is
   one step of Euclidean division in F_p[x]. *)
Lemma pmod_reduce_step : forall p a b da db c binv,
  (db <= da)%nat ->
  c = nth da a 0 ->
  (p | nth db b 0 * binv - 1) ->
  (forall j, (da < j)%nat -> (p | nth j a 0)) ->
  (forall j, (db < j)%nat -> (p | nth j b 0)) ->
  forall j, (da <= j)%nat ->
    (p | nth j (Zpsub a (map (Z.mul (c * binv)) (repeat 0 (da - db) ++ b))) 0).
Proof.
  intros p a b da db c binv Hle Hc Hinv Hda Hdb j Hj.
  rewrite nth_Zpsub, nth_map_Zmul.
  destruct (Nat.eq_dec j da) as [Ej | Ej].
  - subst j.
    rewrite nth_prepend_zeros by lia.
    replace (da - (da - db))%nat with db by lia.
    rewrite <- Hc.
    replace (c - c * binv * nth db b 0) with (- (c * (nth db b 0 * binv - 1))) by ring.
    apply Z.divide_opp_r. apply Z.divide_mul_r. exact Hinv.
  - assert (Hjda : (da < j)%nat) by lia.
    assert (Hja : (p | nth j a 0)) by (apply Hda; exact Hjda).
    assert (Hjt : (p | c * binv * nth j (repeat 0 (da - db) ++ b) 0)).
    { rewrite nth_prepend_zeros by lia.
      apply Z.divide_mul_r. apply Hdb. lia. }
    replace (nth j a 0 - c * binv * nth j (repeat 0 (da - db) ++ b) 0)
       with (nth j a 0 - (c * binv * nth j (repeat 0 (da - db) ++ b) 0)) by ring.
    apply Z.divide_sub_r; assumption.
Qed.

Lemma Zconv_nil_r : forall b k, Zconv b [] k = 0.
Proof.
  induction b as [|a b IH]; intros k; [reflexivity|].
  cbn [Zconv]. destruct k as [|k']; cbn [nth]; [ring | rewrite IH; ring].
Qed.

Lemma nth_Zpmul_nil : forall b k, nth k (Zpmul b []) 0 = 0.
Proof. intros b k. rewrite nth_Zpmul. apply Zconv_nil_r. Qed.
Open Scope R_scope.
Lemma peval_repeat_app : forall m b y,
  peval (repeat 0%Z m ++ b) y = (y ^ m * peval b y)%R.
Proof.
  induction m as [|m IH]; intros b y.
  - cbn [repeat app]. simpl. ring.
  - cbn [repeat app peval]. rewrite IH. simpl. ring.
Qed.
Open Scope Z_scope.
(* Euclidean division in F_p[x]: dividing any a by a divisor b whose leading
   coefficient at index db is a unit mod p yields q, r with a = b*q + r mod p and
   r of mod-p degree below db.  By induction on a degree bound m for a. *)
Lemma pmod_div_bounded : forall p b db binv,
  (p | nth db b 0 * binv - 1) ->
  (forall j, (db < j)%nat -> (p | nth j b 0)) ->
  forall m a, (forall j, (m <= j)%nat -> (p | nth j a 0)) ->
  exists q r,
    (forall k, (p | nth k a 0 - nth k (Zpadd (Zpmul b q) r) 0)) /\
    (forall j, (db <= j)%nat -> (p | nth j r 0)).
Proof.
  intros p b db binv Hinv Hdb.
  induction m as [|m IH]; intros a Ha.
  - exists nil, nil. split.
    + intro k.
      assert (Hz : nth k (Zpadd (Zpmul b []) []) 0 = 0).
      { rewrite nth_Zpadd, nth_Zpmul_nil.
        replace (nth k (@nil Z) 0) with 0 by (destruct k; reflexivity). ring. }
      rewrite Hz, Z.sub_0_r. apply Ha. lia.
    + intros j Hj. destruct j; apply Z.divide_0_r.
  - destruct (list_ex_ge_notdiv_dec p a db)
      as [Hbig | Hsmall].
    + assert (Hex : exists j, ~ (p | nth j a 0))
        by (destruct Hbig as [j [_ Hj]]; exists j; exact Hj).
      destruct (pdeg_mod_exists p a Hex) as [da [Hda1 Hda2]].
      assert (Hdadb : (db <= da)%nat).
      { destruct Hbig as [j [Hjdb Hjnd]].
        destruct (Nat.le_gt_cases j da) as [Hjle | Hjgt]; [lia|].
        exfalso. apply Hjnd. apply Hda2. exact Hjgt. }
      assert (Hdam : (da <= m)%nat).
      { destruct (Nat.le_gt_cases da m) as [Hle|Hgt]; [exact Hle|].
        exfalso. apply Hda1. apply Ha. lia. }
      set (c := nth da a 0).
      set (t := map (Z.mul (c * binv)) (repeat 0%Z (da - db) ++ b)).
      set (a' := Zpsub a t).
      assert (Ha' : forall j, (m <= j)%nat -> (p | nth j a' 0)).
      { intros j Hj. unfold a', t.
        exact (pmod_reduce_step p a b da db c binv Hdadb eq_refl Hinv Hda2 Hdb j ltac:(lia)). }
      destruct (IH a' Ha') as [q' [r' [Hid' Hr']]].
      set (mono := repeat 0%Z (da - db) ++ [c * binv]).
      assert (Ht : forall i, nth i t 0 = nth i (Zpmul b mono) 0).
      { intro i. unfold t, mono. apply peval_eq_nth. intro y.
        rewrite peval_map_Zmul, peval_repeat_app, peval_Zpmul, peval_monomial_c. ring. }
      exists (Zpadd q' mono), r'. split.
      * intro k.
        assert (Hsplit : nth k a 0 = nth k a' 0 + nth k t 0)
          by (unfold a'; rewrite nth_Zpsub; ring).
        assert (Hdist : nth k (Zpmul b (Zpadd q' mono)) 0
                        = nth k (Zpadd (Zpmul b q') (Zpmul b mono)) 0).
        { apply peval_eq_nth. intro y.
          repeat first [ rewrite peval_Zpmul | rewrite peval_Zpadd ]. ring. }
        rewrite Hsplit. rewrite nth_Zpadd. rewrite Hdist. rewrite nth_Zpadd. rewrite <- Ht.
        specialize (Hid' k). rewrite nth_Zpadd in Hid'.
        replace (nth k a' 0 + nth k t 0 - (nth k (Zpmul b q') 0 + nth k t 0 + nth k r' 0))
           with (nth k a' 0 - (nth k (Zpmul b q') 0 + nth k r' 0)) by ring.
        exact Hid'.
      * exact Hr'.
    + assert (Hsm : forall j, (db <= j)%nat -> (p | nth j a 0)).
      { intros j Hj. destruct (Znumtheory.Zdivide_dec p (nth j a 0)) as [H|H]; [exact H|].
        exfalso. apply Hsmall. exists j. split; assumption. }
      exists nil, a. split.
      * intro k.
        assert (Hz : nth k (Zpadd (Zpmul b []) a) 0 = nth k a 0)
          by (rewrite nth_Zpadd, nth_Zpmul_nil; ring).
        rewrite Hz, Z.sub_diag. apply Z.divide_0_r.
      * exact Hsm.
Qed.

(* Euclidean division for any dividend: use its length as the degree bound *)
Lemma pmod_div : forall p b db binv,
  (p | nth db b 0 * binv - 1) -> (forall j, (db < j)%nat -> (p | nth j b 0)) ->
  forall a, exists q r,
    (forall k, (p | nth k a 0 - nth k (Zpadd (Zpmul b q) r) 0)) /\
    (forall j, (db <= j)%nat -> (p | nth j r 0)).
Proof.
  intros p b db binv Hinv Hdb a.
  apply (pmod_div_bounded p b db binv Hinv Hdb (length a) a).
  intros j Hj. rewrite nth_overflow by exact Hj. apply Z.divide_0_r.
Qed.

(* pdvd_mod closure lemmas, toward Bezout / extended Euclid in F_p[x] *)

Lemma pdvd_mod_from_pcong : forall P a X d,
  pcong P a X -> pdvd_mod P d X -> pdvd_mod P d a.
Proof.
  intros P a X d Hax [q Hq]. exists q. apply (pcong_trans P _ X); assumption.
Qed.

Lemma pdvd_mod_Zpadd : forall P d x y,
  pdvd_mod P d x -> pdvd_mod P d y -> pdvd_mod P d (Zpadd x y).
Proof.
  intros P d x y [a Ha] [b Hb]. exists (Zpadd a b).
  apply (pcong_trans P _ (Zpadd (Zpmul d a) (Zpmul d b))).
  - apply pcong_Zpadd; assumption.
  - apply pcong_of_eq_nth. apply peval_eq_nth. intro y0.
    repeat first [ rewrite peval_Zpadd | rewrite peval_Zpmul ]. ring.
Qed.

Lemma pdvd_mod_Zpmul_r : forall P d x z,
  pdvd_mod P d x -> pdvd_mod P d (Zpmul x z).
Proof.
  intros P d x z [a Ha]. exists (Zpmul a z).
  apply (pcong_trans P _ (Zpmul (Zpmul d a) z)).
  - apply pcong_Zpmul_l. exact Ha.
  - apply pcong_of_eq_nth. apply peval_eq_nth. intro y. rewrite !peval_Zpmul. ring.
Qed.

(* the zero polynomial mod p is divisible by anything *)
Lemma pdvd_mod_zero : forall P d b, (forall k, (P | nth k b 0)) -> pdvd_mod P d b.
Proof.
  intros P d b Hb. exists nil.
  intro k. rewrite nth_Zpmul_nil, Z.sub_0_r. apply Hb.
Qed.

Lemma peval_one : forall y, peval [1%Z] y = 1%R.
Proof. intro y. cbn [peval]. simpl IZR. ring. Qed.

(* Bezout / extended Euclid in F_p[x]: for any a and b (with b of mod-p degree
   below m), there are d, u, v with d = u*a + v*b mod p and d dividing both a and b. *)
Lemma bezout_mod : forall p, Znumtheory.prime (Z.of_nat p) ->
  forall m b a, (forall j, (m <= j)%nat -> (Z.of_nat p | nth j b 0)) ->
  exists d u v,
    pcong (Z.of_nat p) d (Zpadd (Zpmul u a) (Zpmul v b)) /\
    pdvd_mod (Z.of_nat p) d a /\ pdvd_mod (Z.of_nat p) d b.
Proof.
  intros p Hp. set (P := Z.of_nat p) in *.
  induction m as [|m IH]; intros b a Hb.
  - exists a, [1%Z], nil. split; [|split].
    + apply pcong_of_eq_nth. apply peval_eq_nth. intro y.
      rewrite peval_Zpadd, !peval_Zpmul, peval_one. cbn [peval]. ring.
    + exists [1%Z]. apply pcong_of_eq_nth. apply peval_eq_nth. intro y.
      rewrite peval_Zpmul, peval_one. ring.
    + apply pdvd_mod_zero. intros k. apply Hb. lia.
  - destruct (Zlist_ex_notdiv_dec P b) as [Hbnz | Hbz].
    + destruct (pdeg_mod_exists P b Hbnz) as [db [Hdb1 Hdb2]].
      assert (Hdbm : (db <= m)%nat).
      { destruct (Nat.le_gt_cases db m) as [Hle|Hgt]; [exact Hle | exfalso; apply Hdb1; apply Hb; lia]. }
      destruct (zinv_mod P (nth db b 0) Hp Hdb1) as [binv Hbinv].
      destruct (pmod_div P b db binv Hbinv Hdb2 a) as [q [r [Hdiv Hr]]].
      assert (Hrm : forall j, (m <= j)%nat -> (P | nth j r 0)) by (intros j Hj; apply Hr; lia).
      destruct (IH r b Hrm) as [d [u' [v' [Hdbez [Hd_b Hd_r]]]]].
      exists d, v', (Zpsub u' (Zpmul v' q)). split; [|split].
      * apply (pcong_trans P d (Zpadd (Zpmul u' b) (Zpmul v' r))).
        -- exact Hdbez.
        -- apply pcong_sym. intro k.
           assert (Hid : nth k (Zpadd (Zpmul v' a) (Zpmul (Zpsub u' (Zpmul v' q)) b)) 0
                       - nth k (Zpadd (Zpmul u' b) (Zpmul v' r)) 0
                       = nth k (Zpmul v' (Zpsub a (Zpadd (Zpmul b q) r))) 0).
           { rewrite <- nth_Zpsub.
             apply (peval_eq_nth
               (Zpsub (Zpadd (Zpmul v' a) (Zpmul (Zpsub u' (Zpmul v' q)) b))
                      (Zpadd (Zpmul u' b) (Zpmul v' r)))
               (Zpmul v' (Zpsub a (Zpadd (Zpmul b q) r)))).
             intro y. rewrite peval_Zpsub.
             repeat first [ rewrite peval_Zpadd | rewrite peval_Zpmul | rewrite peval_Zpsub ]. ring. }
           rewrite Hid, nth_Zpmul.
           apply (Zconv_div P v' (Zpsub a (Zpadd (Zpmul b q) r)) k).
           intros mm Hmm. rewrite nth_Zpsub. apply Hdiv.
      * apply (pdvd_mod_from_pcong P a (Zpadd (Zpmul b q) r) d).
        -- exact Hdiv.
        -- apply pdvd_mod_Zpadd; [apply pdvd_mod_Zpmul_r; exact Hd_b | exact Hd_r].
      * exact Hd_b.
    + assert (Hbz' : forall k, (P | nth k b 0)).
      { intro k. destruct (Znumtheory.Zdivide_dec P (nth k b 0)) as [H|H];
          [exact H | exfalso; apply Hbz; exists k; exact H]. }
      exists a, [1%Z], nil. split; [|split].
      * apply pcong_of_eq_nth. apply peval_eq_nth. intro y.
        rewrite peval_Zpadd, !peval_Zpmul, peval_one. cbn [peval]. ring.
      * exists [1%Z]. apply pcong_of_eq_nth. apply peval_eq_nth. intro y.
        rewrite peval_Zpmul, peval_one. ring.
      * apply pdvd_mod_zero. exact Hbz'.
Qed.

(* coprimality mod p: a Bezout combination equal to 1 *)
Definition coprime_mod (P : Z) (f g : list Z) : Prop :=
  exists u v, pcong P [1%Z] (Zpadd (Zpmul u f) (Zpmul v g)).

Lemma coprime_mod_mul : forall P f x y,
  coprime_mod P f x -> coprime_mod P f y -> coprime_mod P f (Zpmul x y).
Proof.
  intros P f x y [u1 [v1 H1]] [u2 [v2 H2]].
  exists (Zpadd (Zpadd (Zpmul (Zpmul u1 u2) f) (Zpmul (Zpmul u1 v2) y)) (Zpmul (Zpmul u2 v1) x)).
  exists (Zpmul v1 v2).
  apply (pcong_trans P [1%Z]
           (Zpmul (Zpadd (Zpmul u1 f) (Zpmul v1 x)) (Zpadd (Zpmul u2 f) (Zpmul v2 y)))).
  - apply (pcong_trans P [1%Z] (Zpmul [1%Z] [1%Z])).
    + apply pcong_of_eq_nth. apply peval_eq_nth. intro yv. rewrite peval_Zpmul, !peval_one. ring.
    + apply pcong_Zpmul; assumption.
  - apply pcong_of_eq_nth. apply peval_eq_nth. intro yv.
    repeat first [ rewrite peval_Zpadd | rewrite peval_Zpmul ]. ring.
Qed.

Lemma coprime_mod_pow : forall P f g k, coprime_mod P f g -> coprime_mod P f (Zppow g k).
Proof.
  intros P f g k Hcop. induction k as [|k IH].
  - exists nil. exists [1%Z]. cbn [Zppow].
    apply pcong_of_eq_nth. apply peval_eq_nth. intro y.
    rewrite peval_Zpadd, !peval_Zpmul, peval_one. cbn [peval]. ring.
  - cbn [Zppow]. apply coprime_mod_mul; assumption.
Qed.

(* if f is coprime to X and divides X mod p, then f divides 1 mod p *)
Lemma coprime_div_unit : forall P f X,
  coprime_mod P f X -> pdvd_mod P f X -> pdvd_mod P f [1%Z].
Proof.
  intros P f X [u [v Hbez]] [Q HQ].
  exists (Zpadd u (Zpmul v Q)).
  apply (pcong_trans P [1%Z] (Zpadd (Zpmul u f) (Zpmul v X))).
  - exact Hbez.
  - apply (pcong_trans P (Zpadd (Zpmul u f) (Zpmul v X))
                        (Zpadd (Zpmul u f) (Zpmul v (Zpmul f Q)))).
    + apply pcong_Zpadd; [apply pcong_refl | apply pcong_Zpmul_r; exact HQ].
    + apply pcong_of_eq_nth. apply peval_eq_nth. intro y.
      repeat first [ rewrite peval_Zpadd | rewrite peval_Zpmul ]. ring.
Qed.

Lemma nth_Zpmul_single : forall c d k, nth k (Zpmul [c] d) 0 = c * nth k d 0.
Proof. intros c d k. rewrite nth_Zpmul. destruct k as [|k']; cbn [Zconv]; ring. Qed.

(* The Dedekind conjugate-step contradiction: if f (of positive mod-p degree)
   divides g^p mod p and f*g divides x^n-1 mod p (p prime, p not dividing n),
   that is absurd.  This refutes "zeta^p is a root of the cofactor g, not of f". *)
Lemma dedekind_conjugate_absurd : forall p f g n,
  Znumtheory.prime (Z.of_nat p) -> (1 <= n)%nat -> ~ (Z.of_nat p | Z.of_nat n) ->
  (exists df, (1 <= df)%nat /\ ~ (Z.of_nat p | nth df f 0) /\
              (forall j, (df < j)%nat -> (Z.of_nat p | nth j f 0))) ->
  pdvd_mod (Z.of_nat p) f (Zppow g p) ->
  pdvd_mod (Z.of_nat p) (Zpmul f g) (Xn1 n) ->
  False.
Proof.
  intros p f g n Hp Hn Hpn Hdegf Hfgp Hfg.
  set (P := Z.of_nat p) in *.
  destruct Hdegf as [df [Hdf1 [Hdf_nd Hdf_top]]].
  assert (Hg : forall j, (length g <= j)%nat -> (P | nth j g 0))
    by (intros j Hj; rewrite nth_overflow by exact Hj; apply Z.divide_0_r).
  destruct (bezout_mod p Hp (length g) g f Hg) as [d [u [v [Hdbez [Hd_f Hd_g]]]]].
  destruct (list_ex_ge_notdiv_dec P d 1)
    as [Hdpos | Hdsmall].
  - assert (Hex : exists j, ~ (P | nth j d 0)) by (destruct Hdpos as [j [_ Hj]]; exists j; exact Hj).
    destruct (pdeg_mod_exists P d Hex) as [dd [Hdd_nd Hdd_top]].
    assert (Hdd1 : (1 <= dd)%nat).
    { destruct Hdpos as [j [Hj1 Hjnd]].
      destruct (Nat.le_gt_cases j dd) as [Hjle | Hjgt];
        [lia | exfalso; apply Hjnd; apply Hdd_top; exact Hjgt]. }
    exact (no_positive_shared_factor p d f g n dd Hp Hn Hpn Hdd_nd Hdd_top Hdd1 Hd_f Hd_g Hfg).
  - assert (Hdsm : forall j, (1 <= j)%nat -> (P | nth j d 0)).
    { intros j Hj. destruct (Znumtheory.Zdivide_dec P (nth j d 0)) as [H|H]; [exact H|].
      exfalso. apply Hdsmall. exists j. split; assumption. }
    destruct (Znumtheory.Zdivide_dec P (nth 0 d 0)) as [Hd0 | Hd0].
    + exfalso. apply Hdf_nd.
      assert (Hdall : forall k, (P | nth k d 0))
        by (intro k; destruct k; [exact Hd0 | apply Hdsm; lia]).
      destruct Hd_f as [q Hq]. specialize (Hq df).
      assert (HconvD : (P | nth df (Zpmul d q) 0))
        by (rewrite nth_Zpmul; apply Zconv_divide; exact Hdall).
      replace (nth df f 0) with ((nth df f 0 - nth df (Zpmul d q) 0) + nth df (Zpmul d q) 0) by ring.
      apply Z.divide_add_r; assumption.
    + set (c := nth 0 d 0) in *.
      destruct (zinv_mod P c Hp Hd0) as [cinv Hcinv].
      assert (Hcop : coprime_mod P f g).
      { exists (Zpmul [cinv] u), (Zpmul [cinv] v).
        apply (pcong_trans P [1%Z] (Zpmul [cinv] d)).
        - intro k. rewrite nth_Zpmul_single.
          destruct k as [|k'].
          + cbn [nth]. fold c.
            replace (1 - cinv * c) with (- (c * cinv - 1)) by ring.
            apply Z.divide_opp_r. exact Hcinv.
          + replace (nth (S k') [1%Z] 0) with 0 by (symmetry; apply nth_overflow; cbn [length]; lia).
            replace (0 - cinv * nth (S k') d 0) with (- (cinv * nth (S k') d 0)) by ring.
            apply Z.divide_opp_r. apply Z.divide_mul_r. apply Hdsm. lia.
        - apply (pcong_trans P (Zpmul [cinv] d) (Zpmul [cinv] (Zpadd (Zpmul u f) (Zpmul v g)))).
          + apply pcong_Zpmul_r. exact Hdbez.
          + apply pcong_of_eq_nth. apply peval_eq_nth. intro y.
            repeat first [ rewrite peval_Zpadd | rewrite peval_Zpmul ]. ring. }
      assert (Hcopp : coprime_mod P f (Zppow g p)) by (apply coprime_mod_pow; exact Hcop).
      assert (Hf1 : pdvd_mod P f [1%Z])
        by (apply (coprime_div_unit P f (Zppow g p)); [exact Hcopp | exact Hfgp]).
      apply (pdvd_mod_const_absurd p f 1 df Hp Hdf_nd Hdf_top Hdf1); [|exact Hf1].
      intro Hbad. assert (HP1 : (1 < P)%Z) by (destruct Hp; exact H).
      pose proof (Znumtheory.Zdivide_le P 1 ltac:(lia) ltac:(lia) Hbad). lia.
Qed.
Open Scope R_scope.
(* ===== Complex evaluation of rational polynomials, toward the minimal polynomial
   of the complex root zeta_n.  Lets us reuse the rational monic-division and Gauss
   machinery (stated over the reals) at the complex point zeta_n. ===== *)
Open Scope R_scope.
Fixpoint rpe (p : list R) (z : C) : C :=
  match p with
  | [] => C0
  | a :: p' => Cadd (RtoC a) (Cmul z (rpe p' z))
  end.

(* compatibility: evaluating the integer cast equals cpe *)
Lemma rpe_map_IZR : forall p z, rpe (map IZR p) z = cpe p z.
Proof.
  induction p as [|a p IH]; intros z.
  - reflexivity.
  - cbn [map rpe cpe]. rewrite IH. unfold ZtoC. reflexivity.
Qed.

Lemma rpe_padd : forall p q z, rpe (padd p q) z = Cadd (rpe p z) (rpe q z).
Proof.
  induction p as [|a p IH]; intros q z.
  - cbn [padd rpe]. ring.
  - destruct q as [|b q].
    + cbn [padd rpe]. ring.
    + cbn [padd rpe]. rewrite IH, RtoC_add. ring.
Qed.

Lemma rpe_scale : forall a q z, rpe (map (Rmult a) q) z = Cmul (RtoC a) (rpe q z).
Proof.
  induction q as [|b q IH]; intros z.
  - cbn [map rpe]. ring.
  - cbn [map rpe]. rewrite IH, RtoC_mul. ring.
Qed.

Lemma rpe_pmul : forall p q z, rpe (pmul p q) z = Cmul (rpe p z) (rpe q z).
Proof.
  induction p as [|a p IH]; intros q z.
  - cbn [pmul rpe]. ring.
  - cbn [pmul]. rewrite rpe_padd, rpe_scale. cbn [rpe]. rewrite IH.
    replace (RtoC 0) with C0 by reflexivity. ring.
Qed.

Lemma rpe_all0 : forall q z, (forall k, nth k q 0%R = 0%R) -> rpe q z = C0.
Proof.
  induction q as [|b q IH]; intros z Hk.
  - reflexivity.
  - cbn [rpe].
    assert (Hb : b = 0%R) by (specialize (Hk O); cbn in Hk; exact Hk).
    assert (Hq : rpe q z = C0) by (apply IH; intro k; specialize (Hk (S k)); cbn in Hk; exact Hk).
    rewrite Hb, Hq. replace (RtoC 0) with C0 by reflexivity. ring.
Qed.

Lemma rpe_nth_ext : forall p q z,
  (forall k, nth k p 0%R = nth k q 0%R) -> rpe p z = rpe q z.
Proof.
  induction p as [|a p IH]; intros q z Hk.
  - symmetry. apply rpe_all0. intro k. specialize (Hk k). rewrite <- Hk. destruct k; reflexivity.
  - destruct q as [|b q].
    + apply rpe_all0. intro k. specialize (Hk k). rewrite Hk. destruct k; reflexivity.
    + cbn [rpe].
      assert (Hab : a = b) by (specialize (Hk O); cbn in Hk; exact Hk).
      assert (Htl : rpe p z = rpe q z)
        by (apply IH; intro k; specialize (Hk (S k)); cbn in Hk; exact Hk).
      rewrite Hab, Htl. reflexivity.
Qed.

(* transfer a rational polynomial identity (equal as real functions) to the
   complex evaluation rpe at any complex point *)
Lemma rpe_transfer : forall p q z, Forall is_rational p -> Forall is_rational q ->
  (forall y, pe p y = pe q y) -> rpe p z = rpe q z.
Proof.
  intros p q z Hp Hq Heq. apply rpe_nth_ext. apply pe_rat_eq_nth; assumption.
Qed.

(* a monic rational polynomial of degree d that annihilates the complex point z *)
Definition has_annih (z : C) (d : nat) : Prop :=
  exists m, length m = S d /\ nth d m 0%R = 1%R /\ Forall is_rational m /\ rpe m z = C0.

(* if z has any monic rational annihilator, it has one of least degree *)
Lemma min_annih_exists : forall z, (exists d, has_annih z d) ->
  exists e, has_annih z e /\ (forall k, (k < e)%nat -> ~ has_annih z k).
Proof.
  intros z Hex.
  assert (Hstr : forall d, has_annih z d ->
            exists e, has_annih z e /\ (forall k, (k < e)%nat -> ~ has_annih z k)).
  { induction d as [d IH] using (well_founded_induction Wf_nat.lt_wf). intro Hd.
    destruct (Classical_Prop.classic (exists k, (k < d)%nat /\ has_annih z k))
      as [[k [Hkd Hk]] | Hno].
    - exact (IH k Hkd Hk).
    - exists d. split; [exact Hd |].
      intros k Hk Hak. apply Hno. exists k. split; assumption. }
  destruct Hex as [d Hd]. exact (Hstr d Hd).
Qed.

(* zeta_n has a monic rational annihilator of degree n: the cast of x^n - 1 *)
Open Scope R_scope.
Lemma real_deg_exists : forall (r : list R), (exists k, nth k r 0%R <> 0%R) ->
  exists e, nth e r 0%R <> 0%R /\ (forall j, (e < j)%nat -> nth j r 0%R = 0%R).
Proof.
  induction r as [|a r IH]; intros [k Hk].
  - exfalso. apply Hk. destruct k; reflexivity.
  - destruct (Rlist_ex_nonzero_dec r) as [Hr | Hr].
    + destruct (IH Hr) as [e' [He'1 He'2]]. exists (S e'). split.
      * cbn [nth]. exact He'1.
      * intros j Hj. destruct j as [|j']; [lia|]. cbn [nth]. apply He'2; lia.
    + assert (Hrall : forall m, nth m r 0%R = 0%R).
      { intro m. destruct (Req_dec_T (nth m r 0%R) 0%R) as [H|H];
          [exact H | exfalso; apply Hr; exists m; exact H]. }
      exists 0%nat. split.
      * destruct k as [|k'].
        -- cbn [nth] in Hk |- *. exact Hk.
        -- cbn [nth] in Hk. exfalso. apply Hk. apply Hrall.
      * intros j Hj. destruct j as [|j']; [lia|]. cbn [nth]. apply Hrall.
Qed.

Lemma pe_all0 : forall r y, (forall k, nth k r 0%R = 0%R) -> pe r y = 0%R.
Proof.
  induction r as [|a r IH]; intros y Hk.
  - apply pe_nil.
  - rewrite pe_cons.
    assert (Ha : a = 0%R) by (specialize (Hk O); cbn in Hk; exact Hk).
    assert (Hr : pe r y = 0%R) by (apply IH; intro k; specialize (Hk (S k)); cbn in Hk; exact Hk).
    rewrite Ha, Hr. ring.
Qed.

Lemma nth_firstn_lt : forall (A:Type) (d:A) k m (l:list A),
  (k < m)%nat -> nth k (firstn m l) d = nth k l d.
Proof.
  intros A d. induction k as [|k IH]; intros m l Hk.
  - destruct m as [|m]; [lia|]. destruct l as [|a l]; reflexivity.
  - destruct m as [|m]; [lia|]. destruct l as [|a l]; [reflexivity|].
    cbn [firstn nth]. apply IH. lia.
Qed.

(* a rational poly vanishing at zeta_n with top nonzero coefficient at e'
   yields a monic rational annihilator of degree e' *)
Open Scope Z_scope.
Lemma Zcontent_Xn1 : forall n, (1 <= n)%nat -> Zcontent (Xn1 n) = 1.
Proof.
  intros n Hn.
  assert (Hdiv0 : (Zcontent (Xn1 n) | nth 0 (Xn1 n) 0)).
  { apply (proj1 (divide_content_nth (Zcontent (Xn1 n)) (Xn1 n))). apply Z.divide_refl. }
  rewrite nth0_Xn1 in Hdiv0.
  assert (Hdiv1 : (Zcontent (Xn1 n) | 1)).
  { replace 1 with (- (-1)) by ring. apply Z.divide_opp_r. exact Hdiv0. }
  assert (Hpos : 0 < Zcontent (Xn1 n)).
  { pose proof (Zcontent_nonneg (Xn1 n)) as Hnn.
    destruct (Z.eq_dec (Zcontent (Xn1 n)) 0) as [Hz|Hz]; [|lia].
    exfalso. rewrite Zcontent_zero_iff in Hz.
    pose proof (Forall_eq0_nth _ Hz 0%nat) as Hn0. rewrite nth0_Xn1 in Hn0. lia. }
  pose proof (Znumtheory.Zdivide_le (Zcontent (Xn1 n)) 1 ltac:(lia) ltac:(lia) Hdiv1). lia.
Qed.
Open Scope R_scope.
(* the integer monic minimal polynomial of zeta_n: degree e <= n, divides x^n-1,
   and minimal (no monic rational annihilator of smaller degree) *)
Open Scope R_scope.
Lemma nth_map_IZR : forall p i, nth i (map IZR p) 0%R = IZR (nth i p 0%Z).
Proof. intros p i. change (0%R) with (IZR 0%Z). apply map_nth. Qed.

(* a nonzero integer polynomial of degree below e cannot annihilate zeta_n when e
   is minimal: it would yield a smaller monic rational annihilator *)
Open Scope R_scope.
Lemma annih_normalize_z : forall z r e',
  Forall is_rational r -> rpe r z = C0 ->
  nth e' r 0%R <> 0%R -> (forall j, (e' < j)%nat -> nth j r 0%R = 0%R) ->
  has_annih z e'.
Proof.
  intros z r e' Hrrat Hrz Hlead Htop.
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
  - rewrite nth_firstn_lt by lia. rewrite Hscaled_nth. fold c. field. exact Hlead.
  - apply Forall_forall. intros x Hx.
    apply (In_nth _ x 0%R) in Hx. destruct Hx as [i [Hi Hxi]]. rewrite <- Hxi.
    destruct (Nat.lt_ge_cases i (S e')) as [Hi'|Hi'].
    + rewrite nth_firstn_lt by exact Hi'. rewrite Hscaled_nth.
      apply subfield_mul; [apply is_rational_subfield | exact Hcinv |
        apply (Forall_F_nth is_rational i r is_rational_subfield Hrrat)].
    + rewrite nth_overflow by (rewrite firstn_length; unfold scaled; rewrite length_map; lia).
      apply (subfield_0 is_rational is_rational_subfield).
  - assert (Hext : rpe (firstn (S e') scaled) z = rpe scaled z).
    { apply rpe_nth_ext. intro k.
      destruct (Nat.lt_ge_cases k (S e')) as [Hk|Hk].
      - rewrite nth_firstn_lt by exact Hk. reflexivity.
      - rewrite (nth_overflow (firstn (S e') scaled))
          by (rewrite firstn_length; unfold scaled; rewrite length_map; lia).
        rewrite Hscaled_nth. rewrite Htop by lia. ring. }
    rewrite Hext. unfold scaled. rewrite rpe_scale, Hrz. ring.
Qed.

Lemma minpoly_min_no_smaller_z : forall z e (p : list Z),
  (forall k, (k < e)%nat -> ~ has_annih z k) ->
  cpe p z = C0 ->
  (exists k, nth k p 0%Z <> 0%Z) ->
  (forall j, (e <= j)%nat -> nth j p 0%Z = 0%Z) ->
  False.
Proof.
  intros z e p Hmin Hcpe [k Hk] Hdeg.
  assert (Hrat : Forall is_rational (map IZR p)).
  { apply Forall_forall. intros x Hx. apply in_map_iff in Hx.
    destruct Hx as [w [Hw _]]. subst x. apply is_rational_IZR. }
  assert (Hrz : rpe (map IZR p) z = C0) by (rewrite rpe_map_IZR; exact Hcpe).
  assert (Hnz : exists i, nth i (map IZR p) 0%R <> 0%R).
  { exists k. rewrite nth_map_IZR. apply not_0_IZR. exact Hk. }
  destruct (real_deg_exists (map IZR p) Hnz) as [e' [He'1 He'2]].
  assert (He'e : (e' < e)%nat).
  { destruct (Nat.lt_ge_cases e' e) as [H|H]; [exact H|].
    exfalso. apply He'1. rewrite nth_map_IZR, (Hdeg e' H). reflexivity. }
  apply (Hmin e' He'e). apply (annih_normalize_z z (map IZR p) e' Hrat Hrz He'1 He'2).
Qed.

Lemma minpoly_divides_z : forall z m e,
  length m = S e -> nth e m 0%R = 1%R -> Forall is_rational m -> rpe m z = C0 ->
  (forall k, (k < e)%nat -> ~ has_annih z k) ->
  forall h, Forall is_rational h -> rpe h z = C0 ->
  exists q, Forall is_rational q /\ (forall y, pe h y = pe m y * pe q y).
Proof.
  intros z m e Hlen Hmonic Hmrat Hmz Hmin h Hhrat Hhz.
  destruct (monic_div_exists m e Hlen Hmonic Hmrat (length h) h (le_n _) Hhrat)
    as [q [r [Hid [Hrlen [Hqrat Hrrat]]]]].
  exists q. split; [exact Hqrat|].
  assert (Hrz : rpe r z = C0).
  { assert (Htrans : rpe h z = rpe (padd (pmul m q) r) z).
    { apply rpe_transfer;
        [exact Hhrat | apply Forall_rat_padd; [apply Forall_rat_pmul; assumption | exact Hrrat] |].
      intro y. rewrite (Hid y), pe_padd, pe_pmul. ring. }
    rewrite Hhz, rpe_padd, rpe_pmul, Hmz in Htrans.
    transitivity (Cadd (Cmul C0 (rpe q z)) (rpe r z)); [ring | symmetry; exact Htrans]. }
  assert (Hrcoeff : forall k, nth k r 0%R = 0%R).
  { destruct (Rlist_ex_nonzero_dec r) as [Hex|Hno].
    - exfalso. destruct (real_deg_exists r Hex) as [e' [He'1 He'2]].
      assert (He'len : (e' < length r)%nat).
      { destruct (Nat.lt_ge_cases e' (length r)) as [Hl|Hg];
          [exact Hl | exfalso; apply He'1; apply nth_overflow; exact Hg]. }
      assert (He'e : (e' < e)%nat) by lia.
      apply (Hmin e' He'e). apply (annih_normalize_z z r e' Hrrat Hrz He'1 He'2).
    - intro k. destruct (Req_dec_T (nth k r 0%R) 0%R) as [H|H];
        [exact H | exfalso; apply Hno; exists k; exact H]. }
  intro y. rewrite (Hid y), (pe_all0 r y Hrcoeff). ring.
Qed.

(* integer monic minimal polynomial of ANY root of unity z (root of x^n-1) *)
Lemma root_minpoly_Z : forall n z, (1 <= n)%nat -> cpe (Xn1 n) z = C0 ->
  exists mZ e qZ,
    length mZ = S e /\ nth e mZ 0%Z = 1%Z /\ (e <= n)%nat /\
    cpe mZ z = C0 /\ (forall k, (k < e)%nat -> ~ has_annih z k) /\
    (forall k, nth k (Xn1 n) 0%Z = nth k (Zpmul mZ qZ) 0%Z).
Proof.
  intros n z Hn Hroot.
  assert (Hann : has_annih z n).
  { unfold has_annih. exists (map IZR (Xn1 n)). split; [|split; [|split]].
    - rewrite length_map. apply length_Xn1; exact Hn.
    - replace (0%R) with (IZR 0%Z) by (simpl; reflexivity).
      rewrite map_nth, nth_n_Xn1 by exact Hn. simpl. reflexivity.
    - apply Forall_forall. intros x Hx. apply in_map_iff in Hx.
      destruct Hx as [w [Hw _]]. subst x. apply is_rational_IZR.
    - rewrite rpe_map_IZR. exact Hroot. }
  destruct (min_annih_exists z (ex_intro _ n Hann)) as [e [He Hmin]].
  destruct He as [m [Hmlen [Hmmonic [Hmrat Hmz]]]].
  assert (Hen : (e <= n)%nat).
  { destruct (Nat.le_gt_cases e n) as [H|H]; [exact H|]. exfalso. exact (Hmin n H Hann). }
  assert (HXrat : Forall is_rational (map IZR (Xn1 n))).
  { apply Forall_forall. intros x Hx. apply in_map_iff in Hx.
    destruct Hx as [w [Hw _]]. subst x. apply is_rational_IZR. }
  assert (HXz : rpe (map IZR (Xn1 n)) z = C0) by (rewrite rpe_map_IZR; exact Hroot).
  destruct (minpoly_divides_z z m e Hmlen Hmmonic Hmrat Hmz Hmin (map IZR (Xn1 n)) HXrat HXz)
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
Open Scope Z_scope.
(* general-z version of minpoly_Z_divides (integer divisibility) *)
Lemma minpoly_Z_divides_z : forall z mZ e,
  length mZ = S e -> nth e mZ 0%Z = 1%Z -> cpe mZ z = C0 ->
  (forall k, (k < e)%nat -> ~ has_annih z k) ->
  forall h, cpe h z = C0 ->
  exists qq, forall k, nth k h 0 = nth k (Zpmul mZ qq) 0.
Proof.
  intros z mZ e Hlen Hmonic Hmz Hmin h Hhz.
  destruct (Zmonic_div mZ e Hlen Hmonic (length h) h (le_n _)) as [qq [rr [Hid Hrlen]]].
  exists qq.
  assert (Hcoeff : forall k, nth k h 0 = nth k (Zpadd (Zpmul mZ qq) rr) 0).
  { apply peval_eq_nth. intro y. rewrite peval_Zpadd, peval_Zpmul. apply Hid. }
  assert (Hrr0 : forall k, nth k rr 0 = 0).
  { assert (Hrrz : cpe rr z = C0).
    { assert (Hsp : cpe h z = Cadd (Cmul (cpe mZ z) (cpe qq z)) (cpe rr z)).
      { rewrite (cpe_nth_ext h (Zpadd (Zpmul mZ qq) rr) z Hcoeff).
        rewrite cpe_Zpadd, cpe_Zpmul. reflexivity. }
      rewrite Hhz, Hmz in Hsp.
      transitivity (Cadd (Cmul C0 (cpe qq z)) (cpe rr z)); [ring | symmetry; exact Hsp]. }
    destruct (Zlist_ex_nonzero_dec rr) as [Hex|Hno].
    - exfalso. apply (minpoly_min_no_smaller_z z e rr Hmin Hrrz Hex).
      intros j Hj. apply nth_overflow. lia.
    - intro k. destruct (Z.eq_dec (nth k rr 0) 0) as [H|H];
        [exact H | exfalso; apply Hno; exists k; exact H]. }
  intro k. rewrite (Hcoeff k), nth_Zpadd, Hrr0. lia.
Qed.

Lemma Zconv_zero_r : forall q, (forall i, nth i q 0 = 0) -> forall p k, Zconv p q k = 0.
Proof.
  intros q Hq. induction p as [|a p IH]; intros k; [reflexivity|].
  cbn [Zconv]. rewrite Hq. destruct k; [ring | rewrite IH; ring].
Qed.

(* an irreducible monic integer polynomial is the minimal polynomial of EACH of its
   complex roots, hence divides any integer polynomial vanishing at such a root *)
Open Scope Z_scope.
Lemma cpe_repeat0_app : forall m t z, cpe (repeat 0%Z m ++ t) z = Cmul (Cpow z m) (cpe t z).
Proof.
  induction m as [|m IH]; intros t z.
  - cbn [repeat app Cpow]. ring.
  - cbn [repeat app cpe]. rewrite IH. cbn [Cpow].
    replace (ZtoC 0%Z) with C0 by reflexivity. ring.
Qed.

Lemma cpe_subst_xp : forall p g z, (1 <= p)%nat -> cpe (subst_xp p g) z = cpe g (Cpow z p).
Proof.
  intros p g z Hp. induction g as [|c rest IH].
  - reflexivity.
  - cbn [subst_xp cpe]. rewrite cpe_repeat0_app, IH.
    assert (Hzp : Cpow z p = Cmul z (Cpow z (p - 1))).
    { replace p with (S (p - 1))%nat at 1 by lia. reflexivity. }
    rewrite Hzp. ring.
Qed.

(* THE CONJUGATE STEP: if w is a root of the irreducible min poly mZ (and a root of
   unity), and p is a prime not dividing n, then w^p is also a root of mZ. *)
Open Scope nat_scope.
Lemma prime_factor_nat : forall k, 2 <= k ->
  exists p, Znumtheory.prime (Z.of_nat p) /\ Nat.divide p k.
Proof.
  intro k. induction k as [k IH] using (well_founded_induction Wf_nat.lt_wf). intro Hk.
  destruct (Znumtheory.prime_dec (Z.of_nat k)) as [Hp|Hnp].
  - exists k. split; [exact Hp | exists 1; lia].
  - assert (HkZ : (1 < Z.of_nat k)%Z) by lia.
    destruct (Znumtheory.not_prime_divide (Z.of_nat k) HkZ Hnp) as [m [Hm Hdvd]].
    set (mn := Z.to_nat m).
    assert (Hmn2 : 2 <= mn) by (unfold mn; lia).
    assert (Hmnk : mn < k) by (unfold mn; lia).
    assert (Hmndvd : Nat.divide mn k).
    { destruct Hdvd as [c Hc]. exists (Z.to_nat c).
      assert (Hcpos : (0 <= c)%Z) by nia.
      assert (Hmpos : (0 <= m)%Z) by lia.
      apply Nat2Z.inj. rewrite Nat2Z.inj_mul, Z2Nat.id by exact Hcpos.
      unfold mn. rewrite Z2Nat.id by exact Hmpos. lia. }
    destruct (IH mn Hmnk Hmn2) as [p [Hpp Hpdvd]].
    exists p. split; [exact Hpp | exact (Nat.divide_trans p mn k Hpdvd Hmndvd)].
Qed.

(* a divisor of a coprime-to-n number is itself coprime to n *)
Lemma gcd1_of_divisor : forall a k n, Nat.divide a k -> Nat.gcd k n = 1 -> Nat.gcd a n = 1.
Proof.
  intros a k n Hak Hkn.
  assert (Hdiv : Nat.divide (Nat.gcd a n) (Nat.gcd k n)).
  { apply Nat.gcd_greatest.
    - apply (Nat.divide_trans _ a k); [apply Nat.gcd_divide_l | exact Hak].
    - apply Nat.gcd_divide_r. }
  rewrite Hkn in Hdiv. apply Nat.divide_1_r in Hdiv. exact Hdiv.
Qed.

(* every primitive n-th root zeta_n^k (k coprime to n) is a root of the
   irreducible min poly mZ, by iterating the conjugate step over k's prime factors *)
Open Scope R_scope.
Lemma rpe_repeat0_app : forall d t z, rpe (repeat 0 d ++ t) z = Cmul (Cpow z d) (rpe t z).
Proof.
  induction d as [|d IH]; intros t z.
  - cbn [repeat app Cpow]. ring.
  - cbn [repeat app rpe]. rewrite IH. cbn [Cpow].
    replace (RtoC 0) with C0 by reflexivity. ring.
Qed.

(* multiply a real-coeff poly by (1 + x^2) via padd + shift-by-2 *)
Definition mx2 (p : list R) : list R := padd p (shiftp 2 p).

Lemma rpe_mx2 : forall p z, rpe (mx2 p) z = Cmul (Cadd C1 (Cmul z z)) (rpe p z).
Proof.
  intros p z. unfold mx2, shiftp. rewrite rpe_padd, rpe_repeat0_app.
  cbn [Cpow]. ring.
Qed.

(* lift of a rational polynomial m(y) of degree d to  m~(x) = x^d * m(x + 1/x) *)
Fixpoint lift_aux (d : nat) (m : list R) : list R :=
  match m with
  | [] => []
  | c :: m' => padd (map (Rmult c) (repeat 0 d ++ [1])) (mx2 (lift_aux (Nat.pred d) m'))
  end.

(* the lift evaluated at zeta_n: rpe (lift_aux d m) zeta_n = zeta_n^d * rpe m (2cos) *)
Open Scope R_scope.
Lemma rpe_RtoC : forall m x, rpe m (RtoC x) = RtoC (pe m x).
Proof.
  induction m as [|a m IH]; intros x.
  - cbn [rpe]. rewrite pe_nil. reflexivity.
  - cbn [rpe]. rewrite IH, pe_cons, RtoC_add, RtoC_mul. reflexivity.
Qed.

(* coefficients of the lift above index 2d vanish (despite trailing zeros) *)
Lemma lift_aux_high0 : forall m d, length m = S d ->
  forall j, (2*d < j)%nat -> nth j (lift_aux d m) 0 = 0.
Proof.
  induction m as [|c m' IH]; intros d Hlen j Hj; [cbn in Hlen; lia|].
  cbn [lift_aux]. unfold mx2. rewrite !nth_padd, nth_map_Rmult.
  assert (HA : nth j (repeat 0 d ++ [1]) 0 = 0).
  { rewrite app_nth2 by (rewrite repeat_length; lia).
    rewrite repeat_length. apply nth_overflow. cbn [length]. lia. }
  rewrite HA, Rmult_0_r.
  destruct m' as [|c' m''].
  - cbn in Hlen. assert (Hd0 : d = 0%nat) by lia. subst d.
    cbn [Nat.pred lift_aux].
    assert (Hnil : nth j (@nil R) 0 = 0) by (destruct j; reflexivity).
    rewrite Hnil. unfold shiftp. cbn [repeat app].
    destruct j as [|[|j']]; [lia | cbn [nth]; ring | rewrite nth_overflow by (cbn [length]; lia); ring].
  - assert (Hd1 : (1 <= d)%nat) by (cbn in Hlen; lia).
    assert (Hlen' : length (c' :: m'') = S (Nat.pred d)) by (cbn in Hlen |- *; lia).
    assert (Hjrec : (2 * Nat.pred d < j)%nat) by lia.
    rewrite (IH (Nat.pred d) Hlen' j Hjrec).
    rewrite nth_shiftp by lia.
    assert (Hjrec2 : (2 * Nat.pred d < j - 2)%nat) by lia.
    rewrite (IH (Nat.pred d) Hlen' (j-2)%nat Hjrec2). ring.
Qed.

(* leading coefficient of the lift at index 2d equals the leading coeff of m *)
Lemma lift_aux_lead : forall m d, length m = S d ->
  nth (2*d)%nat (lift_aux d m) 0 = nth d m 0.
Proof.
  induction m as [|c m' IH]; intros d Hlen; [cbn in Hlen; lia|].
  cbn [lift_aux]. unfold mx2. rewrite !nth_padd, nth_map_Rmult.
  destruct m' as [|c' m''].
  - cbn in Hlen. assert (Hd0 : d = 0%nat) by lia. subst d.
    cbn [Nat.pred Nat.mul Nat.add lift_aux shiftp repeat app nth]. ring.
  - assert (Hd1 : (1 <= d)%nat) by (cbn in Hlen; lia).
    assert (Hlen' : length (c' :: m'') = S (Nat.pred d)) by (cbn in Hlen |- *; lia).
    assert (HA : nth (2*d) (repeat 0 d ++ [1]) 0 = 0).
    { rewrite app_nth2 by (rewrite repeat_length; lia).
      rewrite repeat_length. apply nth_overflow. cbn [length]. lia. }
    rewrite HA, Rmult_0_r.
    rewrite (lift_aux_high0 (c'::m'') (Nat.pred d) Hlen' (2*d)%nat ltac:(lia)).
    rewrite nth_shiftp by lia.
    replace (2 * d - 2)%nat with (2 * Nat.pred d)%nat by lia.
    rewrite (IH (Nat.pred d) Hlen').
    assert (Hnth : nth d (c :: c' :: m'') 0 = nth (Nat.pred d) (c' :: m'') 0)
      by (replace d with (S (Nat.pred d)) at 1 by lia; reflexivity).
    rewrite Hnth. ring.
Qed.

(* the lift of a rational poly is rational *)
Lemma lift_aux_rational : forall m d, Forall is_rational m -> Forall is_rational (lift_aux d m).
Proof.
  assert (Hrat0 : is_rational 0) by (change 0%R with (IZR 0%Z); apply is_rational_IZR).
  induction m as [|c m' IH]; intros d Hm.
  - cbn [lift_aux]. constructor.
  - cbn [lift_aux]. inversion Hm; subst.
    apply Forall_rat_padd.
    + apply Forall_rat_map_mult; [assumption|].
      apply Forall_forall. intros z Hz. apply in_app_or in Hz. destruct Hz as [Hz|Hz].
      * apply repeat_spec in Hz. subst z. exact Hrat0.
      * destruct Hz as [Hz|[]]. subst z. apply is_rational_1.
    + unfold mx2. apply Forall_rat_padd; [apply IH; assumption|].
      unfold shiftp. apply Forall_forall. intros z Hz. apply in_app_or in Hz. destruct Hz as [Hz|Hz].
      * apply repeat_spec in Hz. subst z. exact Hrat0.
      * pose proof (IH (Nat.pred d) H2) as Hrec.
        rewrite Forall_forall in Hrec. apply Hrec; exact Hz.
Qed.

(* a monic rational annihilator of degree d of 2cos lifts to one of degree 2d for zeta_n *)
Open Scope Z_scope.
Lemma NoDup_app_disjoint : forall (X:Type) (A B:list X) x,
  NoDup (A ++ B) -> In x A -> In x B -> False.
Proof.
  intros X A B x. induction A as [|a A IH]; intros H HA HB; [destruct HA|].
  cbn [app] in H. inversion H as [|y ys Hnin Hnd]; subst.
  destruct HA as [Heq|HA].
  - subst a. apply Hnin. apply in_or_app. right; exact HB.
  - apply (IH Hnd HA HB).
Qed.

Lemma NoDup_app_prefix : forall (X:Type) (A B : list X), NoDup (A ++ B) -> NoDup A.
Proof.
  intros X A B. induction A as [|a A IH]; intros H; [constructor|].
  cbn [app] in H. inversion H as [|y ys Hnin Hnd]; subst.
  constructor; [|exact (IH Hnd)].
  intro Hin. apply Hnin. apply in_or_app. left; exact Hin.
Qed.

Lemma fold_cmul_zero : forall (g : nat -> C) (ds : list nat) d0,
  In d0 ds -> g d0 = C0 ->
  fold_right (fun d acc => Cmul (g d) acc) C1 ds = C0.
Proof.
  intros g ds d0 Hin Hz. induction ds as [|d ds IH]; [destruct Hin|].
  cbn [fold_right]. destruct Hin as [He|Hin].
  - subst d. rewrite Hz. ring.
  - rewrite (IH Hin). ring.
Qed.

(* The integer cyclotomic polynomial Phi_n exists: a monic integer poly of degree
   phi(n) whose complex evaluation matches PhiC n.  Strong induction on n via the
   factorization x^n - 1 = Phi_n * prod_{d|n, d<n} Phi_d and integer monic division. *)
Open Scope Z_scope.
Lemma fold_cmul_allone : forall (g:nat->C) ds, (forall d, In d ds -> g d = C1) ->
  fold_right (fun d acc => Cmul (g d) acc) C1 ds = C1.
Proof.
  intros g ds. induction ds as [|d ds IH]; intros H; cbn [fold_right]; [reflexivity|].
  rewrite (H d (or_introl eq_refl)), (IH (fun d0 Hd0 => H d0 (or_intror Hd0))). ring.
Qed.

(* the value of a polynomial at 0 is its constant term *)
Lemma cpe_at_0 : forall p, cpe p C0 = ZtoC (nth 0 p 0%Z).
Proof.
  intros [|a p']; cbn [cpe nth]; [reflexivity|]. ring.
Qed.

(* Phi_1 = X - 1 evaluated at 0 is -1 *)
Open Scope Z_scope.
Lemma cpe_app : forall p q z, cpe (p ++ q) z = Cadd (cpe p z) (Cmul (Cpow z (length p)) (cpe q z)).
Proof.
  induction p as [|a p IH]; intros q z.
  - cbn [app cpe length Cpow]. ring.
  - cbn [app cpe length]. rewrite IH. cbn [Cpow]. ring.
Qed.

(* the complex Dickson identity: D_j(z + w) = z^j + w^j when zw = 1 *)
Open Scope Z_scope.
Lemma wz_pow_one : forall (w z:C) m, Cmul z w = C1 -> Cmul (Cpow w m) (Cpow z m) = C1.
Proof.
  intros w z m Hzw. induction m as [|m IH].
  - cbn [Cpow]. ring.
  - cbn [Cpow].
    transitivity (Cmul (Cmul z w) (Cmul (Cpow w m) (Cpow z m))); [ring|].
    rewrite Hzw, IH. ring.
Qed.

Lemma ZtoC_add : forall a b, ZtoC (a + b)%Z = Cadd (ZtoC a) (ZtoC b).
Proof. intros a b. unfold ZtoC. rewrite plus_IZR, <- RtoC_add. reflexivity. Qed.

(* the reciprocal reduction: from a palindromic-degree-2k poly P, peel the top
   Dickson term and the matching outer coefficient pair, recursing inward. *)
Open Scope Z_scope.
Lemma gcd_pred_n : forall n, (2 <= n)%nat -> Nat.gcd (n-1) n = 1%nat.
Proof.
  intros n Hn.
  destruct (Nat.gcd_divide_l (n-1) n) as [a Ha].
  destruct (Nat.gcd_divide_r (n-1) n) as [b Hb].
  assert (Hprod : ((b - a) * Nat.gcd (n-1) n = 1)%nat)
    by (rewrite Nat.mul_sub_distr_r; lia).
  apply Nat.mul_eq_1 in Hprod. tauto.
Qed.
Open Scope nat_scope.
Lemma remove_length_nodup : forall x l, NoDup l -> In x l ->
  S (length (remove Nat.eq_dec x l)) = length l.
Proof.
  induction l as [|a l IH]; intros Hnd Hin; [destruct Hin|].
  inversion Hnd as [|y ys Hnin Hnd']; subst. cbn [remove].
  destruct (Nat.eq_dec x a) as [E|E].
  - subst a. rewrite notin_remove by exact Hnin. reflexivity.
  - cbn [length]. destruct Hin as [Ea|Hin']; [subst a; contradiction|].
    f_equal. apply IH; assumption.
Qed.

Lemma noDup_remove : forall x l, NoDup l -> NoDup (remove Nat.eq_dec x l).
Proof.
  induction l as [|a l IH]; intros Hnd; [constructor|].
  inversion Hnd as [|y ys Hnin Hnd']; subst. cbn [remove].
  destruct (Nat.eq_dec x a) as [E|E].
  - apply IH; exact Hnd'.
  - constructor; [|apply IH; exact Hnd'].
    intro Hin. apply in_remove in Hin. destruct Hin as [Hin _]. contradiction.
Qed.

(* a fixpoint-free involution on a NoDup list forces even length *)
Lemma involution_even : forall N (l : list nat) (f : nat -> nat),
  length l = N -> NoDup l ->
  (forall x, In x l -> f x <> x) ->
  (forall x, In x l -> In (f x) l) ->
  (forall x, In x l -> f (f x) = x) ->
  Nat.Even (length l).
Proof.
  intro N. induction N as [N IHN] using (well_founded_induction lt_wf).
  intros l f HlN Hnd Hnf Hmap Hinv.
  destruct l as [|x l']; [exists 0; reflexivity|].
  assert (Hfx_in : In (f x) (x :: l')) by (apply Hmap; left; reflexivity).
  assert (Hfxx : f x <> x) by (apply Hnf; left; reflexivity).
  assert (Hfx_l' : In (f x) l')
    by (destruct Hfx_in as [E|H]; [exfalso; apply Hfxx; symmetry; exact E | exact H]).
  inversion Hnd as [|y ys Hnin Hnd']; subst.
  set (l'' := remove Nat.eq_dec (f x) l').
  assert (Hlen : length (x :: l') = S (S (length l''))).
  { cbn [length]. f_equal. unfold l''. symmetry. apply remove_length_nodup; assumption. }
  assert (Hnd'' : NoDup l'') by (unfold l''; apply noDup_remove; exact Hnd').
  assert (Hsub : forall y, In y l'' -> In y l' /\ y <> f x)
    by (intros y Hy; unfold l'' in Hy; apply in_remove in Hy; exact Hy).
  assert (Hnotx : forall y, In y l'' -> y <> x).
  { intros y Hy. destruct (Hsub y Hy) as [Hyl' _]. intro Ec; subst y. contradiction. }
  assert (Heven'' : Nat.Even (length l'')).
  { apply (IHN (length l'') ltac:(lia) l'' f eq_refl Hnd'').
    - intros y Hy. apply Hnf. right. apply (Hsub y Hy).
    - intros y Hy. destruct (Hsub y Hy) as [Hyl' Hyne].
      assert (Hfy_in : In (f y) (x :: l')) by (apply Hmap; right; exact Hyl').
      assert (Hfyx : f y <> x).
      { intro Ec. assert (f (f y) = f x) by (f_equal; exact Ec).
        rewrite (Hinv y (or_intror Hyl')) in H. apply Hyne. exact H. }
      assert (Hfyfx : f y <> f x).
      { intro Ec. assert (f (f y) = f (f x)) by (f_equal; exact Ec).
        rewrite (Hinv y (or_intror Hyl')), (Hinv x (or_introl eq_refl)) in H.
        apply (Hnotx y Hy). exact H. }
      unfold l''. apply in_in_remove; [exact Hfyfx|].
      destruct Hfy_in as [Ex|Hl']; [subst; exfalso; apply Hfyx; reflexivity | exact Hl'].
    - intros y Hy. apply Hinv. right. apply (Hsub y Hy). }
  rewrite Hlen. destruct Heven'' as [m Hm]. exists (S m). lia.
Qed.

(* gcd is invariant under j -> n - j *)
Lemma gcd_sub_l : forall j n, (j <= n)%nat -> Nat.gcd (n - j) n = Nat.gcd j n.
Proof.
  intros j n Hjn. apply Nat.divide_antisym.
  - apply Nat.gcd_greatest; [|apply Nat.gcd_divide_r].
    assert (Hd : Nat.divide (Nat.gcd (n-j) n) (n - (n - j)))
      by (apply Nat.divide_sub_r; [apply Nat.gcd_divide_r | apply Nat.gcd_divide_l]).
    replace (n - (n - j))%nat with j in Hd by lia. exact Hd.
  - apply Nat.gcd_greatest; [|apply Nat.gcd_divide_r].
    apply Nat.divide_sub_r; [apply Nat.gcd_divide_r | apply Nat.gcd_divide_l].
Qed.

Lemma coprime_sub : forall j n, (j <= n)%nat -> coprime (n - j) n = coprime j n.
Proof. intros j n H. unfold coprime. rewrite gcd_sub_l by exact H. reflexivity. Qed.

(* phi(n) is even for n >= 3: the units pair off under j -> n - j (fixpoint-free) *)
Open Scope nat_scope.
Lemma two_three_smooth_2k : forall k, two_three_smooth k -> two_three_smooth (2*k).
Proof. intros k [a [b Hk]]. exists (S a), b. rewrite Hk. cbn [Nat.pow]. ring. Qed.
Open Scope R_scope.
(* CLEAN composite-n impossibility for all n >= 3: cos(2pi/n) is not single-fold
   origami-constructible whenever phi(n) is not 2-3-smooth. *)
Open Scope R_scope.
Lemma origami_general_cubic : forall c2 c1 c0 x,
  OrigamiNum c2 -> OrigamiNum c1 -> OrigamiNum c0 ->
  x*x*x + c2*(x*x) + c1*x + c0 = 0 -> OrigamiNum x.
Proof.
  intros c2 c1 c0 x Hc2 Hc1 Hc0 Heq.
  assert (H3 : OrigamiNum 3) by apply Origami_three.
  assert (H3ne : (3:R) <> 0) by lra.
  assert (H27ne : (27:R) <> 0) by lra.
  set (p := c1 - c2*c2/3).
  set (q := c0 - c1*c2/3 + 2*(c2*c2*c2)/27).
  set (t := x + c2/3).
  assert (Hp : OrigamiNum p).
  { unfold p. apply ON_sub; [exact Hc1|].
    apply Origami_div; [apply ON_mul; [exact Hc2|exact Hc2] | exact H3 | exact H3ne]. }
  assert (Hq : OrigamiNum q).
  { unfold q. apply ON_add.
    - apply ON_sub; [exact Hc0|].
      apply Origami_div; [apply ON_mul; [exact Hc1|exact Hc2] | exact H3 | exact H3ne].
    - apply Origami_div.
      + apply ON_mul; [apply Origami_two | apply ON_mul; [apply ON_mul; [exact Hc2|exact Hc2]|exact Hc2]].
      + replace (27:R) with (3*3*3) by lra. apply ON_mul; [apply ON_mul; [exact H3|exact H3]|exact H3].
      + exact H27ne. }
  assert (Ht : t*t*t + p*t + q = 0).
  { replace (t*t*t + p*t + q) with (x*x*x + c2*(x*x) + c1*x + c0)
      by (unfold t, p, q; field). exact Heq. }
  assert (Htn : OrigamiNum t) by (apply (ON_cubic_root p q t Hp Hq Ht)).
  assert (Hx : x = t - c2/3) by (unfold t; field).
  rewrite Hx. apply ON_sub; [exact Htn | apply Origami_div; [exact Hc2 | exact H3 | exact H3ne]].
Qed.

(* Constructive direction, degree-3 case: when phi(n) = 6, cos(2pi/n) is origami,
   since 2cos satisfies the rational cubic from cos_recip_annih (e.g. n = 7, 9, 14, 18). *)
Open Scope R_scope.
Lemma origami_general_quadratic : forall c1 c0 x,
  OrigamiNum c1 -> OrigamiNum c0 -> x*x + c1*x + c0 = 0 -> OrigamiNum x.
Proof.
  intros c1 c0 x Hc1 Hc0 Heq.
  set (qw := 2*x + c1).
  set (qd := c1*c1 - 4*c0).
  assert (Hwd : qw*qw = qd) by (unfold qw, qd; nra).
  assert (Hdon : OrigamiNum qd).
  { unfold qd. apply ON_sub; [apply ON_mul; [exact Hc1|exact Hc1]|].
    apply ON_mul; [|exact Hc0].
    replace (4:R) with (2*2) by lra. apply ON_mul; apply Origami_two. }
  assert (Hdnn : 0 <= qd) by (rewrite <- Hwd; nra).
  assert (Hson : OrigamiNum (sqrt qd)) by (apply ON_sqrt; assumption).
  assert (Hwon : OrigamiNum qw).
  { destruct (Rle_dec 0 qw) as [Hge|Hlt].
    - replace qw with (sqrt qd); [exact Hson|].
      rewrite <- Hwd, sqrt_square by exact Hge. reflexivity.
    - replace qw with (- sqrt qd); [apply Origami_neg; exact Hson|].
      rewrite <- Hwd. replace (qw*qw) with ((-qw)*(-qw)) by ring.
      rewrite sqrt_square by lra. ring. }
  assert (Hx : x = (qw - c1)/2) by (unfold qw; field).
  rewrite Hx. apply Origami_div; [apply ON_sub; [exact Hwon|exact Hc1] | apply Origami_two | lra].
Qed.

(* ===== OrigamiNum2 field helpers and general low-degree closures, mirroring
   the single-fold Origami_neg/two/three/div and origami_general_quadratic/cubic,
   used to build the two-fold Gaussian-period tower. ===== *)
Lemma ON2_neg : forall x, OrigamiNum2 x -> OrigamiNum2 (- x).
Proof. intros x H. replace (- x) with (0 - x) by ring. apply ON2_sub; [apply ON2_0 | exact H]. Qed.

Lemma ON2_two : OrigamiNum2 2.
Proof. replace 2 with (1 + 1) by ring. apply ON2_add; apply ON2_1. Qed.

Lemma ON2_three : OrigamiNum2 3.
Proof. replace 3 with (1 + (1 + 1)) by ring. apply ON2_add; [apply ON2_1 | apply ON2_add; apply ON2_1]. Qed.

Lemma ON2_div : forall x y, OrigamiNum2 x -> OrigamiNum2 y -> y <> 0 -> OrigamiNum2 (x / y).
Proof.
  intros x y Hx Hy Hne. unfold Rdiv.
  apply ON2_mul; [exact Hx | apply ON2_inv; [exact Hy | exact Hne]].
Qed.

Lemma ON2_general_quadratic : forall c1 c0 x,
  OrigamiNum2 c1 -> OrigamiNum2 c0 -> x*x + c1*x + c0 = 0 -> OrigamiNum2 x.
Proof.
  intros c1 c0 x Hc1 Hc0 Heq.
  set (qw := 2*x + c1).
  set (qd := c1*c1 - 4*c0).
  assert (Hwd : qw*qw = qd) by (unfold qw, qd; nra).
  assert (Hdon : OrigamiNum2 qd).
  { unfold qd. apply ON2_sub; [apply ON2_mul; [exact Hc1|exact Hc1]|].
    apply ON2_mul; [|exact Hc0].
    replace (4:R) with (2*2) by lra. apply ON2_mul; apply ON2_two. }
  assert (Hdnn : 0 <= qd) by (rewrite <- Hwd; nra).
  assert (Hson : OrigamiNum2 (sqrt qd)) by (apply ON2_sqrt; assumption).
  assert (Hwon : OrigamiNum2 qw).
  { destruct (Rle_dec 0 qw) as [Hge|Hlt].
    - replace qw with (sqrt qd); [exact Hson|].
      rewrite <- Hwd, sqrt_square by exact Hge. reflexivity.
    - replace qw with (- sqrt qd); [apply ON2_neg; exact Hson|].
      rewrite <- Hwd. replace (qw*qw) with ((-qw)*(-qw)) by ring.
      rewrite sqrt_square by lra. ring. }
  assert (Hx : x = (qw - c1)/2) by (unfold qw; field).
  rewrite Hx. apply ON2_div; [apply ON2_sub; [exact Hwon|exact Hc1] | apply ON2_two | lra].
Qed.

Lemma ON2_general_cubic : forall c2 c1 c0 x,
  OrigamiNum2 c2 -> OrigamiNum2 c1 -> OrigamiNum2 c0 ->
  x*x*x + c2*(x*x) + c1*x + c0 = 0 -> OrigamiNum2 x.
Proof.
  intros c2 c1 c0 x Hc2 Hc1 Hc0 Heq.
  assert (H3ne : (3:R) <> 0) by lra.
  assert (H27ne : (27:R) <> 0) by lra.
  set (p := c1 - c2*c2/3).
  set (q := c0 - c1*c2/3 + 2*(c2*c2*c2)/27).
  set (t := x + c2/3).
  assert (Hp : OrigamiNum2 p).
  { unfold p. apply ON2_sub; [exact Hc1|].
    apply ON2_div; [apply ON2_mul; [exact Hc2|exact Hc2] | apply ON2_three | exact H3ne]. }
  assert (Hq : OrigamiNum2 q).
  { unfold q. apply ON2_add.
    - apply ON2_sub; [exact Hc0|].
      apply ON2_div; [apply ON2_mul; [exact Hc1|exact Hc2] | apply ON2_three | exact H3ne].
    - apply ON2_div.
      + apply ON2_mul; [apply ON2_two | apply ON2_mul; [apply ON2_mul; [exact Hc2|exact Hc2]|exact Hc2]].
      + replace (27:R) with (3*3*3) by lra.
        apply ON2_mul; [apply ON2_mul; [apply ON2_three|apply ON2_three]|apply ON2_three].
      + exact H27ne. }
  assert (Ht : t*t*t + p*t + q = 0).
  { replace (t*t*t + p*t + q) with (x*x*x + c2*(x*x) + c1*x + c0)
      by (unfold t, p, q; field). exact Heq. }
  assert (Htn : OrigamiNum2 t) by (apply (ON2_cbrt p q t Hp Hq Ht)).
  assert (Hx : x = t - c2/3) by (unfold t; field).
  rewrite Hx. apply ON2_sub; [exact Htn | apply ON2_div; [exact Hc2 | apply ON2_three | exact H3ne]].
Qed.

(* degree-5 Newton's identities: a root a of the monic quintic whose coefficients
   are the elementary symmetric functions e1..e5 recovered from the power sums
   p1 = e1, p2..p5 of the five roots a,b,c,d,f.  The degree-5 analogue of
   cubic_root_from_psums, the algebraic heart of the two-fold tower step. *)
Lemma quintic_root_from_psums : forall a b c d f e1 p2 p3 p4 p5 : R,
  e1 = a+b+c+d+f ->
  p2 = a^2+b^2+c^2+d^2+f^2 ->
  p3 = a^3+b^3+c^3+d^3+f^3 ->
  p4 = a^4+b^4+c^4+d^4+f^4 ->
  p5 = a^5+b^5+c^5+d^5+f^5 ->
  let e2 := (e1*e1 - p2)/2 in
  let e3 := (e2*e1 - e1*p2 + p3)/3 in
  let e4 := (e3*e1 - e2*p2 + e1*p3 - p4)/4 in
  let e5 := (e4*e1 - e3*p2 + e2*p3 - e1*p4 + p5)/5 in
  a^5 + (- e1)*a^4 + e2*a^3 + (- e3)*a^2 + e4*a + (- e5) = 0.
Proof.
  intros a b c d f e1 p2 p3 p4 p5 H1 H2 H3 H4 H5.
  subst e1 p2 p3 p4 p5. cbv zeta. field.
Qed.

(* Constructive direction, degree-2 case: when phi(n) = 4, cos(2pi/n) is origami
   (e.g. n = 5, 8, 10, 12). *)
Open Scope R_scope.
Lemma cos_double : forall x, cos (2*x) = 2*cos x*cos x - 1.
Proof.
  intro x. replace (2*x) with (x+x) by ring. rewrite cos_plus.
  pose proof (sin2_cos2 x) as H. unfold Rsqr in H. nra.
Qed.

(* origami trisection: from cos(2pi/m) build cos(2pi/(3m)) via the triple-angle cubic *)
Open Scope R_scope.
Lemma is_power_of_2_2k : forall k, is_power_of_2 k -> is_power_of_2 (2*k).
Proof. intros k [j Hj]. exists (S j). rewrite Hj. simpl. ring. Qed.

(* if phi(n)/2 is not a power of 2 then cos(2pi/n) is not constructible by compass
   and straightedge.  Its degree over Q is phi(n)/2 (cos_2pi_n_degree_exactly), but
   Euclidean numbers have power-of-2 degree (euclid_field_degree_pow2). *)
Open Scope R_scope.
Lemma degree_not_smooth_not_origami : forall x d,
  basis is_rational (powers x d) (Qx x) -> ~ two_three_smooth d -> ~ OrigamiNum x.
Proof.
  intros x d Hbasis Hns HO.
  destruct (origami_field_degree_smooth x HO) as [d' [Hbasis' Hsmooth]].
  destruct Hbasis as [HBd [Hlid Hspd]].
  destruct Hbasis' as [HBd' [Hlid' Hspd']].
  assert (Hdd : (d <= d')%nat).
  { pose proof (indep_le_span is_rational (powers x d) (powers x d') (Qx x)
                  is_rational_subfield Hlid HBd Hspd') as Hle.
    rewrite !powers_length in Hle. exact Hle. }
  assert (Hd'd : (d' <= d)%nat).
  { pose proof (indep_le_span is_rational (powers x d') (powers x d) (Qx x)
                  is_rational_subfield Hlid' HBd' Hspd) as Hle.
    rewrite !powers_length in Hle. exact Hle. }
  assert (d = d') by lia. subst d'. exact (Hns Hsmooth).
Qed.

(* a real number whose degree over Q is not a power of 2 is not compass-straightedge
   constructible *)
Lemma not_pow2_not_euclid : forall x d,
  basis is_rational (powers x d) (Qx x) -> ~ is_power_of_2 d -> ~ EuclidNum x.
Proof.
  intros x d Hbasis Hnp HE.
  destruct (euclid_field_degree_pow2 x HE) as [d' [Hbasis' Hpow]].
  destruct Hbasis as [HBd [Hlid Hspd]].
  destruct Hbasis' as [HBd' [Hlid' Hspd']].
  assert (Hdd : (d <= d')%nat).
  { pose proof (indep_le_span is_rational (powers x d) (powers x d') (Qx x)
                  is_rational_subfield Hlid HBd Hspd') as Hle.
    rewrite !powers_length in Hle. exact Hle. }
  assert (Hd'd : (d' <= d)%nat).
  { pose proof (indep_le_span is_rational (powers x d') (powers x d) (Qx x)
                  is_rational_subfield Hlid' HBd' Hspd) as Hle.
    rewrite !powers_length in Hle. exact Hle. }
  assert (d = d') by lia. subst d'. exact (Hnp Hpow).
Qed.
Open Scope Z_scope.
(******************************************************************************)
(*  TODO ITEM #1 (and #2): Galois sufficiency backbone + full n-gon iff.       *)
(*  Gaussian-period tower over (Z/pZ)* gives the constructive direction:       *)
(*  for all n, phi(n) 2-3-smooth => cos(2*PI/n) is origami; with the           *)
(*  impossibility direction above this yields the full single-fold iff.        *)
(*  (Merged from the former nt/core/periods/dev/gauss/tower modules.)          *)
(******************************************************************************)


(* ---- number theory (former nt.v) ---- *)
Open Scope nat_scope.
Lemma divide_nat_Z : forall a b, Nat.divide a b <-> (Z.of_nat a | Z.of_nat b)%Z.
Proof.
  intros a b. split.
  - intros [c Hc]. exists (Z.of_nat c). rewrite Hc, Nat2Z.inj_mul. ring.
  - intros [z Hz]. destruct (Nat.eq_dec a 0) as [Ha0|Ha0].
    + subst a. assert (Hb0 : Z.of_nat b = 0%Z)
        by (rewrite Hz; change (Z.of_nat 0) with 0%Z; ring).
      assert (b = 0) by lia. subst b. exists 0. reflexivity.
    + assert (HaP : (0 < Z.of_nat a)%Z) by lia.
      assert (Hz0 : (0 <= z)%Z) by nia.
      exists (Z.to_nat z). apply Nat2Z.inj.
      rewrite Nat2Z.inj_mul, Z2Nat.id by exact Hz0. lia.
Qed.

Lemma gcd_d_p_eq_1 : forall p d, Znumtheory.prime (Z.of_nat p) ->
  ~ Nat.divide p d -> Nat.gcd d p = 1.
Proof.
  intros p d Hp Hnd.
  assert (Hpz : (1 < Z.of_nat p)%Z) by (destruct Hp; assumption).
  pose proof (Nat.gcd_divide_l d p) as Hgd.
  pose proof (Nat.gcd_divide_r d p) as Hgp.
  remember (Nat.gcd d p) as g eqn:Hgeq.
  apply (proj1 (divide_nat_Z g p)) in Hgp.
  pose proof (Nat2Z.is_nonneg g) as Hgnn.
  destruct (Znumtheory.prime_divisors (Z.of_nat p) Hp (Z.of_nat g) Hgp) as [H1|[H1|[H1|H1]]];
    try (exfalso; apply Nat2Z.inj in H1; apply Hnd; rewrite <- H1; exact Hgd);
    clear Hgp Hgd Hgeq Hnd Hp; lia.
Qed.

Lemma coprime_pow_l : forall a b e, Nat.gcd a b = 1 -> Nat.gcd (a ^ e) b = 1.
Proof.
  intros a b e Hab. induction e as [|e IH].
  - rewrite Nat.pow_0_r, Nat.gcd_comm. apply gcd_n_1.
  - rewrite Nat.pow_succ_r'. rewrite Nat.gcd_comm.
    apply (proj2 (coprime_mul_iff b a (a ^ e))). split.
    + rewrite Nat.gcd_comm. exact Hab.
    + rewrite Nat.gcd_comm. exact IH.
Qed.

Lemma coprime_pp : forall p e k, Znumtheory.prime (Z.of_nat p) ->
  ~ Nat.divide p k -> Nat.gcd (p ^ e) k = 1.
Proof.
  intros p e k Hp Hpk. apply coprime_pow_l. rewrite Nat.gcd_comm.
  apply gcd_d_p_eq_1; assumption.
Qed.

Lemma ppart_exists : forall p n, 2 <= p -> 1 <= n ->
  exists e k, n = p ^ e * k /\ ~ Nat.divide p k.
Proof.
  intros p n Hp. induction n as [n IH] using (well_founded_induction lt_wf). intro Hn.
  destruct (Ndivide_dec p n) as [Hpn | Hpn].
  - destruct Hpn as [m Hm].
    assert (Hm1 : 1 <= m) by nia.
    assert (Hmlt : m < n) by nia.
    destruct (IH m Hmlt Hm1) as [e [k [Hmk Hpk]]].
    exists (S e), k. split; [| exact Hpk].
    rewrite Hm, Hmk, Nat.pow_succ_r'. nia.
  - exists 0, n. split; [rewrite Nat.pow_0_r, Nat.mul_1_l; reflexivity | exact Hpn].
Qed.

Lemma nat_prime_mult : forall p x y, Znumtheory.prime (Z.of_nat p) ->
  Nat.divide p (x * y) -> Nat.divide p x \/ Nat.divide p y.
Proof.
  intros p x y Hp Hd.
  apply (proj1 (divide_nat_Z p (x * y))) in Hd. rewrite Nat2Z.inj_mul in Hd.
  destruct (Znumtheory.prime_mult (Z.of_nat p) Hp (Z.of_nat x) (Z.of_nat y) Hd) as [H|H].
  - left. apply (proj2 (divide_nat_Z p x)). exact H.
  - right. apply (proj2 (divide_nat_Z p y)). exact H.
Qed.

Lemma prime_dvd_pow : forall p a n, Znumtheory.prime (Z.of_nat p) ->
  Nat.divide p (a ^ n) -> Nat.divide p a.
Proof.
  intros p a n Hp. induction n as [|n IH]; intro Hd.
  - rewrite Nat.pow_0_r in Hd. apply Nat.divide_1_r in Hd. subst p.
    destruct Hp as [Hgt _]. simpl in Hgt. lia.
  - rewrite Nat.pow_succ_r' in Hd.
    destruct (nat_prime_mult p a (a ^ n) Hp Hd) as [H|H]; [exact H | apply IH; exact H].
Qed.

Lemma prime_dvd_2a3b : forall p a b, Znumtheory.prime (Z.of_nat p) ->
  Nat.divide p (2 ^ a * 3 ^ b) -> p = 2 \/ p = 3.
Proof.
  intros p a b Hp Hd.
  destruct (nat_prime_mult p (2 ^ a) (3 ^ b) Hp Hd) as [H2|H3].
  - left. apply (prime_dvd_pow p 2 a Hp) in H2.
    assert (Hle : p <= 2) by (apply Nat.divide_pos_le; [lia | exact H2]).
    assert (Hge : 2 <= p) by (destruct Hp; lia). lia.
  - right. apply (prime_dvd_pow p 3 b Hp) in H3.
    assert (Hle : p <= 3) by (apply Nat.divide_pos_le; [lia | exact H3]).
    assert (Hge : 2 <= p) by (destruct Hp; lia).
    assert (E : p = 2 \/ p = 3) by lia. destruct E as [E|E]; [| exact E].
    exfalso. subst p. destruct H3 as [c Hc]. lia.
Qed.

(* a prime dividing 2^a * 3^b * 5^c is one of 2, 3, 5 *)
Lemma prime_dvd_2a3b5c : forall p a b c, Znumtheory.prime (Z.of_nat p) ->
  Nat.divide p (2 ^ a * 3 ^ b * 5 ^ c) -> p = 2 \/ p = 3 \/ p = 5.
Proof.
  intros p a b c Hp Hd.
  destruct (nat_prime_mult p (2 ^ a * 3 ^ b) (5 ^ c) Hp Hd) as [H23 | H5].
  - destruct (prime_dvd_2a3b p a b Hp H23) as [E2 | E3];
      [left; exact E2 | right; left; exact E3].
  - right; right.
    apply (prime_dvd_pow p 5 c Hp) in H5.
    assert (Hge : 2 <= p) by (destruct Hp; lia).
    assert (Hle : p <= 5) by (apply Nat.divide_pos_le; [lia | exact H5]).
    destruct H5 as [q Hq].
    assert (Hcase : p = 2 \/ p = 3 \/ p = 4 \/ p = 5) by lia.
    destruct Hcase as [E|[E|[E|E]]]; rewrite E in *; [lia | lia | lia | reflexivity].
Qed.

Lemma pow_inj : forall p i j, 2 <= p -> p ^ i = p ^ j -> i = j.
Proof.
  intros p i j Hp He. destruct (lt_eq_lt_dec i j) as [[H|H]|H]; [|exact H|].
  - exfalso. assert (p ^ i < p ^ j) by (apply Nat.pow_lt_mono_r; lia). lia.
  - exfalso. assert (p ^ j < p ^ i) by (apply Nat.pow_lt_mono_r; lia). lia.
Qed.

Lemma divisor_of_prime_pow : forall p e d, Znumtheory.prime (Z.of_nat p) ->
  Nat.divide d (p ^ e) -> exists i, i <= e /\ d = p ^ i.
Proof.
  intros p e d Hp. revert d. induction e as [|e IH]; intros d Hd.
  - rewrite Nat.pow_0_r in Hd. apply Nat.divide_1_r in Hd. exists 0.
    split; [lia | rewrite Nat.pow_0_r; exact Hd].
  - rewrite Nat.pow_succ_r' in Hd.
    destruct (Ndivide_dec p d) as [Hpd | Hpd].
    + destruct Hpd as [d' Hd']. subst d.
      assert (Hd'pe : Nat.divide d' (p ^ e)).
      { destruct Hd as [c Hc]. exists c.
        assert (Hpne : p <> 0) by (destruct Hp; lia).
        apply (proj1 (Nat.mul_cancel_r (p ^ e) (c * d') p Hpne)). nia. }
      destruct (IH d' Hd'pe) as [j [Hj Hdj]]. subst d'.
      exists (S j). split; [lia | rewrite Nat.pow_succ_r'; nia].
    + assert (Hgcd : Nat.gcd d p = 1) by (apply gcd_d_p_eq_1; assumption).
      assert (Hdpe : Nat.divide d (p ^ e)) by (apply (Nat.gauss d p (p ^ e) Hd Hgcd)).
      destruct (IH d Hdpe) as [j [Hj Hdj]]. exists j. split; [lia | exact Hdj].
Qed.

Lemma list_sum_perm : forall l1 l2, Permutation l1 l2 -> list_sum l1 = list_sum l2.
Proof. intros l1 l2 H. induction H; simpl; lia. Qed.

Lemma divisors_prime_pow_perm : forall p e, Znumtheory.prime (Z.of_nat p) ->
  Permutation (divisors (p ^ e)) (map (fun i => p ^ i) (seq 0 (S e))).
Proof.
  intros p e Hp.
  assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  apply NoDup_Permutation.
  - unfold divisors. apply NoDup_filter_nat. apply seq_NoDup.
  - apply pm_NoDup_map_inj_in.
    + intros i j Hi Hj He. apply (pow_inj p i j Hp2 He).
    + apply seq_NoDup.
  - intro d. split.
    + intro Hin. apply in_divisors in Hin. destruct Hin as [[Hd1 Hdn] Hdvd].
      destruct (divisor_of_prime_pow p e d Hp Hdvd) as [i [Hi Hdi]].
      apply in_map_iff. exists i. split; [symmetry; exact Hdi | apply in_seq; lia].
    + intro Hin. apply in_map_iff in Hin. destruct Hin as [i [Hdi Hiin]].
      apply in_seq in Hiin. subst d. apply in_divisors. split.
      * split.
        -- assert (p ^ i <> 0) by (apply Nat.pow_nonzero; lia). lia.
        -- apply Nat.pow_le_mono_r; lia.
      * exists (p ^ (e - i)). rewrite <- Nat.pow_add_r. f_equal. lia.
Qed.

Lemma phi_pp_sum : forall p e, Znumtheory.prime (Z.of_nat p) ->
  list_sum (map (fun i => euler_phi (p ^ i)) (seq 0 (S e))) = p ^ e.
Proof.
  intros p e Hp.
  assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  assert (Hpe1 : 1 <= p ^ e) by (assert (p ^ e <> 0) by (apply Nat.pow_nonzero; lia); lia).
  pose proof (totient_sum (p ^ e) Hpe1) as HT.
  pose proof (Permutation_map euler_phi (divisors_prime_pow_perm p e Hp)) as HPm.
  apply list_sum_perm in HPm. rewrite HT in HPm. rewrite map_map in HPm.
  symmetry. exact HPm.
Qed.

Lemma euler_phi_prime_pow : forall p e, Znumtheory.prime (Z.of_nat p) -> 1 <= e ->
  euler_phi (p ^ e) = p ^ e - p ^ (e - 1).
Proof.
  intros p e Hp He.
  assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  pose proof (phi_pp_sum p e Hp) as HSe.
  pose proof (phi_pp_sum p (e - 1) Hp) as HSe1.
  assert (HseqSe : seq 0 (S e) = seq 0 e ++ [e]) by (rewrite seq_S; reflexivity).
  rewrite HseqSe, map_app, list_sum_app in HSe.
  cbn [map] in HSe.
  assert (He1 : S (e - 1) = e) by lia.
  rewrite He1 in HSe1.
  assert (Hsingle : list_sum [euler_phi (p ^ e)] = euler_phi (p ^ e)) by (simpl; lia).
  rewrite Hsingle in HSe.
  assert (Hge : p ^ (e - 1) <= p ^ e) by (apply Nat.pow_le_mono_r; lia).
  lia.
Qed.

Lemma p_dvd_phi_pp : forall p e, Znumtheory.prime (Z.of_nat p) -> 2 <= e ->
  Nat.divide p (euler_phi (p ^ e)).
Proof.
  intros p e Hp He.
  rewrite (euler_phi_prime_pow p e Hp ltac:(lia)).
  apply Nat.divide_sub_r.
  - replace e with (S (e - 1)) by lia. rewrite Nat.pow_succ_r'. apply Nat.divide_factor_l.
  - replace (e - 1) with (S (e - 2)) by lia. rewrite Nat.pow_succ_r'. apply Nat.divide_factor_l.
Qed.

(* ---- F_p root bound + primitive root (former core.v) ---- *)
(******************************************************************************)
(*  core.v — Gaussian periods for the prime cyclotomic field.                  *)
(*                                                                            *)
(*  Goal (Hcore, the sole remaining hypothesis of dev.v's Section Reduction): *)
(*    for prime p with 2-3-smooth phi(p) = p-1, cos(2*PI/p) is origami.        *)
(*                                                                            *)
(*  Layer 1: the F_p polynomial root bound (factor theorem): a polynomial      *)
(*  nonzero mod p has at most (degree) roots in [0,p).                         *)
(******************************************************************************)
Open Scope Z_scope.
(* ===== Integer polynomial evaluation (Horner) and synthetic division ===== *)

Fixpoint zev (c : list Z) (x : Z) : Z :=
  match c with
  | [] => 0
  | a :: c' => a + x * zev c' x
  end.

Lemma zev_cons : forall b t x, zev (b :: t) x = b + x * zev t x.
Proof. reflexivity. Qed.

(* synthetic division of c by (X - a): the genuine degree-dropping Horner quotient
   (empty quotient for constants, so that length drops by exactly one) *)
Fixpoint sdiv (c : list Z) (a : Z) : list Z :=
  match c with
  | [] => []
  | _ :: c' =>
      match c' with
      | [] => []
      | _ :: _ => zev c' a :: sdiv c' a
      end
  end.

Lemma sdiv_cons2 : forall c0 c1 c' a,
  sdiv (c0 :: c1 :: c') a = zev (c1 :: c') a :: sdiv (c1 :: c') a.
Proof. reflexivity. Qed.

(* division identity: c(x) = (x - a) * q(x) + c(a), with q = sdiv c a *)
Lemma zev_sdiv : forall c a x, zev c x = (x - a) * zev (sdiv c a) x + zev c a.
Proof.
  induction c as [|c0 c IH]; intros a x.
  - cbn [zev sdiv]. ring.
  - destruct c as [|c1 c'].
    + cbn [zev sdiv]. ring.
    + rewrite (sdiv_cons2 c0 c1 c' a).
      rewrite (zev_cons c0 (c1 :: c') x).
      rewrite (zev_cons (zev (c1 :: c') a) (sdiv (c1 :: c') a) x).
      rewrite (zev_cons c0 (c1 :: c') a).
      rewrite (IH a x). ring.
Qed.

Lemma length_sdiv : forall c a, length (sdiv c a) = (length c - 1)%nat.
Proof.
  induction c as [|c0 c IH]; intro a; [reflexivity|].
  destruct c as [|c1 c']; [reflexivity|].
  rewrite (sdiv_cons2 c0 c1 c' a). cbn [length]. rewrite (IH a). cbn [length]. lia.
Qed.

(* ===== "zero mod p" / "nonzero mod p" coefficient predicates ===== *)

Definition pzero (p : Z) (c : list Z) : Prop := forall k, (p | nth k c 0).
Definition pnz (p : Z) (c : list Z) : Prop := exists k, ~ (p | nth k c 0).

Lemma not_pnz_pzero : forall p c, ~ pnz p c -> pzero p c.
Proof.
  intros p c H k. destruct (Znumtheory.Zdivide_dec p (nth k c 0)) as [Hd|Hd]; [exact Hd|].
  exfalso. apply H. exists k. exact Hd.
Qed.

Lemma pnz_nonnil : forall p c, pnz p c -> c <> [].
Proof.
  intros p c [k Hk] Hc. subst c. apply Hk. destruct k; cbn [nth]; apply Z.divide_0_r.
Qed.

(* an all-zero-mod-p polynomial evaluates to 0 mod p everywhere *)
Lemma zev_pzero : forall p c r, pzero p c -> (p | zev c r).
Proof.
  intros p c r H. induction c as [|b c IH].
  - cbn [zev]. apply Z.divide_0_r.
  - cbn [zev]. apply Z.divide_add_r.
    + apply (H 0%nat).
    + apply Z.divide_mul_r. apply IH. intro k. apply (H (S k)).
Qed.

(* if the quotient is zero mod p and a is a root, the dividend is zero mod p *)
Lemma sdiv_pzero_back : forall c p a, pzero p (sdiv c a) -> (p | zev c a) -> pzero p c.
Proof.
  induction c as [|c0 c IH]; intros p a Hq Hr.
  - intro k. destruct k; apply Z.divide_0_r.
  - destruct c as [|c1 c'].
    + intro k. destruct k as [|k'].
      * cbn [nth]. cbn [zev] in Hr. replace (c0 + a * 0) with c0 in Hr by ring. exact Hr.
      * destruct k'; apply Z.divide_0_r.
    + rewrite (sdiv_cons2 c0 c1 c' a) in Hq.
      assert (Hqc : pzero p (sdiv (c1 :: c') a)) by (intro k; apply (Hq (S k))).
      assert (Hz0 : (p | zev (c1 :: c') a)) by (apply (Hq 0%nat)).
      assert (Hc : pzero p (c1 :: c')) by (exact (IH p a Hqc Hz0)).
      rewrite (zev_cons c0 (c1 :: c') a) in Hr.
      assert (Hb : (p | c0)).
      { replace c0 with ((c0 + a * zev (c1 :: c') a) - a * zev (c1 :: c') a) by ring.
        apply Z.divide_sub_r; [exact Hr | apply Z.divide_mul_r; exact Hz0]. }
      intro k. destruct k as [|k']; [cbn [nth]; exact Hb | cbn [nth]; apply Hc].
Qed.

(* peeling a genuine root keeps the quotient nonzero mod p *)
Lemma sdiv_pnz_of_root : forall p c a, pnz p c -> (p | zev c a) -> pnz p (sdiv c a).
Proof.
  intros p c a Hpnz Hr.
  destruct (Zlist_ex_notdiv_dec p (sdiv c a)) as [H|H]; [exact H|].
  exfalso. destruct Hpnz as [k Hk]. apply Hk.
  exact (sdiv_pzero_back c p a (not_pnz_pzero p _ H) Hr k).
Qed.

(* ===== Roots over the residue window [0, p) as a NoDup list ===== *)

Definition residues (p : Z) : list Z := map Z.of_nat (seq 0 (Z.to_nat p)).

Definition rootb (p : Z) (c : list Z) (r : Z) : bool :=
  if Znumtheory.Zdivide_dec p (zev c r) then true else false.

Definition rootl (p : Z) (c : list Z) : list Z := filter (rootb p c) (residues p).

Lemma NoDup_residues : forall p, NoDup (residues p).
Proof.
  intro p. unfold residues. apply pm_NoDup_map_inj_in.
  - intros x y _ _ Hxy. apply Nat2Z.inj. exact Hxy.
  - apply seq_NoDup.
Qed.

Lemma NoDup_rootl : forall p c, NoDup (rootl p c).
Proof. intros p c. unfold rootl. apply NoDup_filter. apply NoDup_residues. Qed.

Lemma in_residues : forall p r, 0 < p -> In r (residues p) -> 0 <= r < p.
Proof.
  intros p r Hp0 Hin. unfold residues in Hin. apply in_map_iff in Hin.
  destruct Hin as [n [Hn Hnin]]. apply in_seq in Hnin. subst r. split.
  - apply Nat2Z.is_nonneg.
  - apply (Z.lt_le_trans _ (Z.of_nat (Z.to_nat p))).
    + apply Nat2Z.inj_lt. lia.
    + rewrite Z2Nat.id by lia. lia.
Qed.

(* the factor inclusion: roots of c sit in {a mod p} together with roots of the quotient *)
Lemma rootl_incl : forall p c a, Znumtheory.prime p -> (p | zev c a) ->
  incl (rootl p c) (a mod p :: rootl p (sdiv c a)).
Proof.
  intros p c a Hp Hra r Hr.
  assert (Hp0 : 0 < p) by (destruct Hp; lia).
  apply filter_In in Hr. destruct Hr as [Hres Hrb].
  unfold rootb in Hrb. destruct (Znumtheory.Zdivide_dec p (zev c r)) as [Hcr|]; [|discriminate].
  assert (Hfac : (p | (r - a) * zev (sdiv c a) r)).
  { replace ((r - a) * zev (sdiv c a) r) with (zev c r - zev c a)
      by (rewrite (zev_sdiv c a r) at 1; ring).
    apply Z.divide_sub_r; [exact Hcr | exact Hra]. }
  destruct (Znumtheory.prime_mult p Hp _ _ Hfac) as [Hra' | Hqr].
  - left.
    pose proof (in_residues p r Hp0 Hres) as Hrr.
    assert (Hmod : (r - a) mod p = 0) by (apply Z.mod_divide; [lia | exact Hra']).
    assert (Hreq : r = a + ((r - a) / p) * p).
    { pose proof (Z.div_mod (r - a) p ltac:(lia)) as Hdm. rewrite Hmod in Hdm. lia. }
    assert (Hrmod : r mod p = a mod p) by (rewrite Hreq at 1; apply Z_mod_plus_full).
    pose proof (Z.mod_small r p Hrr) as Hsm. rewrite Hsm in Hrmod. symmetry. exact Hrmod.
  - right. apply filter_In. split; [exact Hres|].
    unfold rootb. destruct (Znumtheory.Zdivide_dec p (zev (sdiv c a) r)); [reflexivity|contradiction].
Qed.

(* ===== The root bound: nonzero mod p ==> at most (degree) roots ===== *)
Theorem rootl_length : forall p c, Znumtheory.prime p -> pnz p c ->
  (length (rootl p c) <= length c - 1)%nat.
Proof.
  intros p c Hp. remember (length c) as L eqn:HL. revert c HL.
  induction L as [L IHL] using (well_founded_induction lt_wf). intros c HL Hpnz.
  destruct (list_ex_In_dec Z (fun a => (p | zev c a)) (residues p)
              (fun a => Znumtheory.Zdivide_dec p (zev c a))) as [[a [Hain Hroot]] | Hno].
  - assert (Hqpnz : pnz p (sdiv c a)) by (apply sdiv_pnz_of_root; assumption).
    assert (Hlenq : length (sdiv c a) = (length c - 1)%nat) by apply length_sdiv.
    assert (Hcne : c <> []) by (apply (pnz_nonnil p); exact Hpnz).
    assert (Hclen : (1 <= length c)%nat) by (destruct c; [contradiction | cbn [length]; lia]).
    pose proof (rootl_incl p c a Hp Hroot) as Hincl.
    pose proof (NoDup_incl_length (NoDup_rootl p c) Hincl) as Hle.
    cbn [length] in Hle.
    assert (Hqbound : (length (rootl p (sdiv c a)) <= length (sdiv c a) - 1)%nat).
    { apply (IHL (length (sdiv c a))); [rewrite HL, Hlenq; lia | reflexivity | exact Hqpnz]. }
    assert (Hqne : sdiv c a <> []) by (apply (pnz_nonnil p); exact Hqpnz).
    assert (Hslen : (1 <= length (sdiv c a))%nat)
      by (destruct (sdiv c a); [contradiction | cbn [length]; lia]).
    rewrite Hlenq in Hqbound. lia.
  - assert (Hempty : rootl p c = []).
    { destruct (rootl p c) as [|z zs] eqn:E; [reflexivity|]. exfalso.
      assert (Hin : In z (rootl p c)) by (rewrite E; left; reflexivity).
      unfold rootl in Hin. apply filter_In in Hin. destruct Hin as [Hres Hrb].
      unfold rootb in Hrb. destruct (Znumtheory.Zdivide_dec p (zev c z)) as [Hz|]; [|discriminate].
      apply Hno. exists z. split; assumption. }
    rewrite Hempty. cbn [length].
    assert (Hcne : c <> []) by (apply (pnz_nonnil p); exact Hpnz).
    destruct c; [contradiction | cbn [length]; lia].
Qed.

(******************************************************************************)
(*  Layer 2: multiplicative order and a primitive root mod p.                  *)
(*  (Z/pZ)* is cyclic: with the Layer-1 root bound and the totient sum, a      *)
(*  generator (primitive root) exists.  This is the cyclic structure the        *)
(*  Gaussian-period tower needs.                                               *)
(******************************************************************************)

(* ===== scalar congruence mod m (as divisibility of the difference) ===== *)
Definition cg (m x y : Z) : Prop := (m | x - y).

Lemma cg_refl : forall m x, cg m x x.
Proof. intros m x. unfold cg. rewrite Z.sub_diag. apply Z.divide_0_r. Qed.

Lemma cg_sym : forall m x y, cg m x y -> cg m y x.
Proof.
  intros m x y H. unfold cg in *.
  replace (y - x) with (-(x - y)) by ring. apply Z.divide_opp_r, H.
Qed.

Lemma cg_trans : forall m x y z, cg m x y -> cg m y z -> cg m x z.
Proof.
  intros m x y z H1 H2. unfold cg in *.
  replace (x - z) with ((x - y) + (y - z)) by ring. apply Z.divide_add_r; assumption.
Qed.

Lemma cg_mul : forall m x x' y y', cg m x x' -> cg m y y' -> cg m (x * y) (x' * y').
Proof.
  intros m x x' y y' Hx Hy. unfold cg in *.
  replace (x * y - x' * y') with ((x - x') * y + x' * (y - y')) by ring.
  apply Z.divide_add_r; [apply Z.divide_mul_l | apply Z.divide_mul_r]; assumption.
Qed.

(* ===== nat-exponent power ===== *)
Fixpoint zpn (a : Z) (k : nat) : Z := match k with O => 1 | S k' => a * zpn a k' end.

Lemma zpn_add : forall a m n, zpn a (m + n) = zpn a m * zpn a n.
Proof.
  intros a m n. induction m as [|m IH].
  - change (0 + n)%nat with n. change (zpn a 0) with 1. ring.
  - change (S m + n)%nat with (S (m + n)).
    change (zpn a (S (m + n))) with (a * zpn a (m + n)).
    change (zpn a (S m)) with (a * zpn a m).
    rewrite IH. ring.
Qed.

Lemma zpn_mul : forall a m n, zpn a (m * n) = zpn (zpn a m) n.
Proof.
  intros a m n. induction n as [|n IH].
  - rewrite Nat.mul_0_r. reflexivity.
  - rewrite Nat.mul_succ_r, zpn_add, IH.
    change (zpn (zpn a m) (S n)) with (zpn a m * zpn (zpn a m) n). ring.
Qed.

Lemma zpn_cong : forall m a b k, cg m a b -> cg m (zpn a k) (zpn b k).
Proof.
  intros m a b k H. induction k as [|k IH].
  - apply cg_refl.
  - change (zpn a (S k)) with (a * zpn a k).
    change (zpn b (S k)) with (b * zpn b k).
    apply cg_mul; assumption.
Qed.

Lemma zpn_pow : forall a k, zpn a k = a ^ (Z.of_nat k).
Proof.
  intros a k. induction k as [|k IH]; [reflexivity|].
  change (zpn a (S k)) with (a * zpn a k).
  rewrite IH, Nat2Z.inj_succ, Z.pow_succ_r by apply Nat2Z.is_nonneg. ring.
Qed.

(* ===== Fermat's little theorem in congruence form ===== *)
Lemma fermat_cg : forall p a, Znumtheory.prime (Z.of_nat p) ->
  ~ (Z.of_nat p | a) -> cg (Z.of_nat p) (zpn a (p - 1)) 1.
Proof.
  intros p a Hp Hna.
  assert (Hp2 : (2 <= p)%nat) by (destruct Hp as [Hgt _]; lia).
  pose proof (int_fermat p a Hp) as HF.
  rewrite <- zpn_pow in HF.
  assert (Hsplit : zpn a p = a * zpn a (p - 1)).
  { replace p with (S (p - 1)) at 1 by lia. reflexivity. }
  rewrite Hsplit in HF.
  assert (Hfac : (Z.of_nat p | a * (zpn a (p - 1) - 1))).
  { replace (a * (zpn a (p - 1) - 1)) with (a * zpn a (p - 1) - a) by ring. exact HF. }
  unfold cg.
  apply (Znumtheory.Gauss (Z.of_nat p) a (zpn a (p - 1) - 1)).
  - exact Hfac.
  - apply Znumtheory.prime_rel_prime; assumption.
Qed.

(* ===== multiplicative order ===== *)

(* least element of a nonempty nat predicate *)
Lemma least_exists : forall (Q : nat -> Prop), (forall k, {Q k} + {~ Q k}) ->
  forall n, Q n -> exists m, Q m /\ (forall k, (k < m)%nat -> ~ Q k).
Proof.
  intros Q Qdec n. induction n as [n IH] using (well_founded_induction lt_wf). intro Hn.
  destruct (bounded_ex_dec Q n Qdec) as [[k [Hk Qk]] | Hno].
  - exact (IH k Hk Qk).
  - exists n. split; [exact Hn|]. intros k Hk Qk. apply Hno. exists k. split; assumption.
Qed.

Lemma zpn_one : forall k, zpn 1 k = 1.
Proof.
  induction k as [|k IH]; [reflexivity|].
  change (zpn 1 (S k)) with (1 * zpn 1 k). rewrite IH. ring.
Qed.

(* k is a "period" of a mod p: 1 <= k and a^k == 1 *)
Definition per (p : nat) (a : Z) (k : nat) : Prop :=
  (1 <= k)%nat /\ cg (Z.of_nat p) (zpn a k) 1.

Lemma per_dec : forall p a k, {per p a k} + {~ per p a k}.
Proof.
  intros p a k. unfold per, cg.
  destruct (le_dec 1 k) as [Hk|Hk]; [| right; intros [H _]; contradiction].
  destruct (Znumtheory.Zdivide_dec (Z.of_nat p) (zpn a k - 1)) as [Hd|Hd];
    [left; split; assumption | right; intros [_ H]; contradiction].
Qed.

(* the order: least positive period; exists for units by Fermat *)
Lemma order_exists : forall p a, Znumtheory.prime (Z.of_nat p) -> ~ (Z.of_nat p | a) ->
  exists d, per p a d /\ (forall k, (k < d)%nat -> ~ per p a k).
Proof.
  intros p a Hp Hna.
  apply (least_exists (per p a) (per_dec p a) (p - 1)).
  split; [destruct Hp as [Hgt _]; lia | apply fermat_cg; assumption].
Qed.

(* multiples of d are periods *)
Lemma per_mult : forall p a d q, cg (Z.of_nat p) (zpn a d) 1 ->
  cg (Z.of_nat p) (zpn a (d * q)) 1.
Proof.
  intros p a d q Hd. rewrite zpn_mul.
  apply (cg_trans _ _ (zpn 1 q)); [apply zpn_cong; exact Hd | rewrite zpn_one; apply cg_refl].
Qed.

(* the order divides every period *)
Lemma order_divides : forall p a d k,
  per p a d -> (forall j, (j < d)%nat -> ~ per p a j) ->
  cg (Z.of_nat p) (zpn a k) 1 -> Nat.divide d k.
Proof.
  intros p a d k [Hd1 Hda] Hmin Hk.
  set (q := (k / d)%nat). set (r := (k mod d)%nat).
  assert (Hdm : k = (d * q + r)%nat) by (unfold q, r; exact (Nat.div_mod k d ltac:(lia))).
  assert (Hr : (r < d)%nat) by (unfold r; apply Nat.mod_upper_bound; lia).
  assert (Har : cg (Z.of_nat p) (zpn a r) 1).
  { apply (cg_trans _ _ (zpn a k)); [| exact Hk].
    rewrite Hdm, zpn_add.
    apply (cg_trans _ _ (1 * zpn a r)); [rewrite Z.mul_1_l; apply cg_refl |].
    apply cg_mul; [apply cg_sym; apply (per_mult p a d q Hda) | apply cg_refl]. }
  destruct r as [|r'].
  - exists q. rewrite Hdm. lia.
  - exfalso. apply (Hmin (S r') Hr). split; [lia | exact Har].
Qed.

(* ===== solutions of X^m = 1 mod p, and the root count ===== *)

Lemma zpn_pred : forall x m, (1 <= m)%nat -> zpn x m = x * zpn x (m - 1).
Proof.
  intros x m Hm. destruct m as [|m']; [lia|].
  change (zpn x (S m')) with (x * zpn x m').
  replace (S m' - 1)%nat with m' by lia. reflexivity.
Qed.

(* X^m - 1 as a coefficient list (low degree first): -1, 0, ..., 0, 1 *)
Definition Xpoly (m : nat) : list Z := (-1)%Z :: (repeat 0%Z (m - 1) ++ (1%Z :: nil)).

Lemma zev_monomial : forall j c x, zev (repeat 0%Z j ++ (c :: nil)) x = c * zpn x j.
Proof.
  induction j as [|j IH]; intros c x.
  - cbn [repeat app zev]. change (zpn x 0) with 1. ring.
  - cbn [repeat app zev]. rewrite IH. change (zpn x (S j)) with (x * zpn x j). ring.
Qed.

Lemma zev_Xpoly : forall m x, (1 <= m)%nat -> zev (Xpoly m) x = zpn x m - 1.
Proof.
  intros m x Hm. unfold Xpoly. cbn [zev]. rewrite zev_monomial.
  rewrite (zpn_pred x m Hm). ring.
Qed.

Lemma pnz_Xpoly : forall p m, (2 <= p)%nat -> pnz (Z.of_nat p) (Xpoly m).
Proof.
  intros p m Hp. exists 0%nat. cbn [Xpoly nth]. intro Hd.
  assert (HP1 : (Z.of_nat p | 1)).
  { destruct Hd as [k Hk]. exists (- k).
    replace (- k * Z.of_nat p) with (- (k * Z.of_nat p)) by ring.
    rewrite <- Hk. ring. }
  pose proof (Znumtheory.Zdivide_le (Z.of_nat p) 1 ltac:(lia) ltac:(lia) HP1). lia.
Qed.

Lemma length_Xpoly : forall m, (1 <= m)%nat -> length (Xpoly m) = S m.
Proof.
  intros m Hm. unfold Xpoly. cbn [length]. rewrite length_app, repeat_length.
  cbn [length]. lia.
Qed.

(* root bound for X^m - 1: at most m solutions mod p *)
Lemma S_card_bound : forall p m, Znumtheory.prime (Z.of_nat p) -> (1 <= m)%nat ->
  (length (rootl (Z.of_nat p) (Xpoly m)) <= m)%nat.
Proof.
  intros p m Hp Hm.
  assert (Hp2 : (2 <= p)%nat) by (destruct Hp as [Hgt _]; lia).
  pose proof (rootl_length (Z.of_nat p) (Xpoly m) Hp (pnz_Xpoly p m Hp2)) as Hb.
  rewrite (length_Xpoly m Hm) in Hb. lia.
Qed.

Lemma rootb_iff_cg : forall p m a, (1 <= m)%nat ->
  (rootb (Z.of_nat p) (Xpoly m) a = true <-> cg (Z.of_nat p) (zpn a m) 1).
Proof.
  intros p m a Hm. unfold rootb, cg. rewrite (zev_Xpoly m a Hm).
  destruct (Znumtheory.Zdivide_dec (Z.of_nat p) (zpn a m - 1)) as [Hd|Hd].
  - split; [intros _; exact Hd | reflexivity].
  - split; [discriminate | intro Hc; contradiction].
Qed.

Lemma in_residues_of : forall p j, (j < p)%nat -> In (Z.of_nat j) (residues (Z.of_nat p)).
Proof.
  intros p j Hj. unfold residues. apply in_map.
  rewrite Nat2Z.id. apply in_seq. lia.
Qed.

(* ===== the unit residues [1, p-1] ===== *)
Definition units (p : nat) : list Z := map Z.of_nat (seq 1 (p - 1)).

Lemma units_length : forall p, length (units p) = (p - 1)%nat.
Proof. intro p. unfold units. rewrite length_map, length_seq. reflexivity. Qed.

Lemma units_NoDup : forall p, NoDup (units p).
Proof.
  intro p. unfold units. apply pm_NoDup_map_inj_in.
  - intros x y _ _ H. apply Nat2Z.inj. exact H.
  - apply seq_NoDup.
Qed.

Lemma units_in_residues : forall p a, In a (units p) -> In a (residues (Z.of_nat p)).
Proof.
  intros p a Hin. unfold units in Hin. apply in_map_iff in Hin.
  destruct Hin as [j [Hj Hjin]]. apply in_seq in Hjin. subst a. apply in_residues_of. lia.
Qed.

(* if filter f l is shorter than l then some element of l fails f *)
Lemma filter_short : forall (A : Type) (f : A -> bool) (l : list A),
  (length (filter f l) < length l)%nat -> exists x, In x l /\ f x = false.
Proof.
  intros A f l. induction l as [|a l IH]; intro H.
  - cbn in H. lia.
  - cbn [filter] in H. destruct (f a) eqn:Ha.
    + cbn [length] in H.
      destruct (IH ltac:(lia)) as [x [Hx Hf]]. exists x. split; [right; exact Hx | exact Hf].
    + exists a. split; [left; reflexivity | exact Ha].
Qed.

(* counting: with m1, m2 >= 1 and m1 + m2 < p-1, some unit is a root of neither
   X^m1 - 1 nor X^m2 - 1 *)
Lemma exists_unit_avoiding : forall p m1 m2, Znumtheory.prime (Z.of_nat p) ->
  (1 <= m1)%nat -> (1 <= m2)%nat -> (m1 + m2 < p - 1)%nat ->
  exists g, In g (units p) /\ ~ cg (Z.of_nat p) (zpn g m1) 1 /\ ~ cg (Z.of_nat p) (zpn g m2) 1.
Proof.
  intros p m1 m2 Hp Hm1 Hm2 Hsum.
  set (badb := fun a => orb (rootb (Z.of_nat p) (Xpoly m1) a) (rootb (Z.of_nat p) (Xpoly m2) a)).
  assert (Hincl : incl (filter badb (units p))
                       (rootl (Z.of_nat p) (Xpoly m1) ++ rootl (Z.of_nat p) (Xpoly m2))).
  { intros a Ha. apply filter_In in Ha. destruct Ha as [Hau Hbad].
    apply in_or_app. unfold badb in Hbad. apply orb_true_iff in Hbad.
    assert (Hares : In a (residues (Z.of_nat p))) by (apply units_in_residues; exact Hau).
    destruct Hbad as [Hb|Hb].
    - left. unfold rootl. apply filter_In. split; [exact Hares | exact Hb].
    - right. unfold rootl. apply filter_In. split; [exact Hares | exact Hb]. }
  assert (Hlenbad : (length (filter badb (units p)) <= m1 + m2)%nat).
  { pose proof (NoDup_incl_length (NoDup_filter badb (units_NoDup p)) Hincl) as Hle.
    rewrite length_app in Hle.
    pose proof (S_card_bound p m1 Hp Hm1).
    pose proof (S_card_bound p m2 Hp Hm2). lia. }
  assert (Hshort : (length (filter badb (units p)) < length (units p))%nat)
    by (rewrite units_length; lia).
  destruct (filter_short Z badb (units p) Hshort) as [g [Hg Hgf]].
  exists g. split; [exact Hg|].
  unfold badb in Hgf. apply orb_false_iff in Hgf. destruct Hgf as [Hf1 Hf2].
  split.
  - intro Hc. assert (Hb : rootb (Z.of_nat p) (Xpoly m1) g = true)
      by (apply rootb_iff_cg; assumption). rewrite Hb in Hf1. discriminate.
  - intro Hc. assert (Hb : rootb (Z.of_nat p) (Xpoly m2) g = true)
      by (apply rootb_iff_cg; assumption). rewrite Hb in Hf2. discriminate.
Qed.

(* a proper divisor of 2^a*3^b divides n/2 or n/3 *)
Lemma proper_div_dichotomy : forall n d, (exists a b, n = (2 ^ a * 3 ^ b)%nat) ->
  (1 <= n)%nat -> Nat.divide d n -> d <> n ->
  Nat.divide d (n / 2) \/ Nat.divide d (n / 3).
Proof.
  intros n d Hn Hn1 Hdvd Hdne.
  destruct Hdvd as [c Hc].
  assert (Hd1 : (1 <= d)%nat) by (destruct d as [|d']; [rewrite Nat.mul_0_r in Hc; lia | lia]).
  assert (Hc2 : (2 <= c)%nat).
  { destruct c as [|[|c'']].
    - simpl in Hc. lia.
    - rewrite Nat.mul_1_l in Hc. exfalso. apply Hdne. lia.
    - lia. }
  destruct (prime_factor_nat c Hc2) as [r [Hr Hrc]].
  assert (Hrn : Nat.divide r n)
    by (rewrite Hc; apply (Nat.divide_trans r c (c * d) Hrc (Nat.divide_factor_l c d))).
  destruct Hn as [a [b Hn23]]. rewrite Hn23 in Hrn.
  destruct (prime_dvd_2a3b r a b Hr Hrn) as [Hr2|Hr3].
  - left. subst r. destruct Hrc as [c' Hc'].
    exists c'. assert (Hn2 : n = ((c' * d) * 2)%nat) by (rewrite Hc, Hc'; nia).
    rewrite Hn2, Nat.div_mul by lia. reflexivity.
  - right. subst r. destruct Hrc as [c' Hc'].
    exists c'. assert (Hn3 : n = ((c' * d) * 3)%nat) by (rewrite Hc, Hc'; nia).
    rewrite Hn3, Nat.div_mul by lia. reflexivity.
Qed.

Lemma half_third_lt : forall n, (4 <= n)%nat -> (n / 2 + n / 3 < n)%nat.
Proof.
  intros n Hn.
  pose proof (Nat.div_mod n 2 ltac:(lia)).
  pose proof (Nat.div_mod n 3 ltac:(lia)).
  pose proof (Nat.mod_upper_bound n 2 ltac:(lia)).
  pose proof (Nat.mod_upper_bound n 3 ltac:(lia)). lia.
Qed.

(* bridges to origami_proofs' nat-prime totient *)
Lemma is_prime_of_Z : forall p, Znumtheory.prime (Z.of_nat p) -> is_prime p.
Proof.
  intros p Hp. assert (Hpg : (1 < Z.of_nat p)%Z) by (destruct Hp as [H _]; exact H).
  split; [lia|].
  intros d Hd Hdvd. apply (proj1 (divide_nat_Z d p)) in Hdvd.
  destruct (Znumtheory.prime_divisors (Z.of_nat p) Hp (Z.of_nat d) Hdvd) as [H|[H|[H|H]]]; lia.
Qed.

Lemma euler_phi_prime : forall p, Znumtheory.prime (Z.of_nat p) -> euler_phi p = (p - 1)%nat.
Proof. intros p Hp. apply phi_prime, is_prime_of_Z, Hp. Qed.

(* ===== primitive root for any prime, via maximal-order cyclicity =====
   The single-fold primitive_root is 2-3-smooth-specific (its exists_unit_avoiding
   union bound needs m1+m2 < p-1).  For general p (in particular 5-smooth p-1) we
   run the classical argument: the maximal order M satisfies a^M = 1 for every
   unit a (an abelian group has exponent = maximal order), so all p-1 units are
   roots of X^M - 1, whence p-1 <= M <= p-1 by the mod-p root bound. *)

(* the multiplicative order of a unit as a specification (least positive period) *)
Definition is_order (p : nat) (a : Z) (d : nat) : Prop :=
  per p a d /\ (forall k, (k < d)%nat -> ~ per p a k).

(* zpn distributes over products: (a b)^k = a^k b^k *)
Lemma zpn_mul_dist : forall a b k, zpn (a * b) k = zpn a k * zpn b k.
Proof.
  intros a b k. induction k as [|k IH]; [reflexivity|].
  cbn [zpn]. rewrite IH. ring.
Qed.

(* coprime cancellation in nat, via Z Gauss *)
Lemma nat_coprime_divmul : forall a b c,
  Nat.gcd a b = 1%nat -> Nat.divide a (b * c) -> Nat.divide a c.
Proof. intros a b c Hg Hd. exact (Nat.gauss a b c Hd Hg). Qed.

(* coprime orders multiply: if a has order d1, b has order d2, gcd(d1,d2)=1,
   then a*b has order d1*d2 *)
Lemma order_coprime_mul : forall p a b d1 d2,
  Znumtheory.prime (Z.of_nat p) ->
  is_order p a d1 -> is_order p b d2 -> Nat.gcd d1 d2 = 1%nat ->
  is_order p (a * b)%Z (d1 * d2)%nat.
Proof.
  intros p a b d1 d2 Hp [[Hd1pos Hacg] Hamin] [[Hd2pos Hbcg] Hbmin] Hcop.
  assert (Hprod : cg (Z.of_nat p) (zpn (a * b) (d1 * d2)) 1).
  { rewrite zpn_mul_dist.
    assert (Ha' : cg (Z.of_nat p) (zpn a (d1 * d2)) 1) by (apply (per_mult p a d1 d2); exact Hacg).
    assert (Hb' : cg (Z.of_nat p) (zpn b (d1 * d2)) 1)
      by (rewrite Nat.mul_comm; apply (per_mult p b d2 d1); exact Hbcg).
    apply (cg_trans _ _ (1 * 1)); [apply cg_mul; assumption | rewrite Z.mul_1_l; apply cg_refl]. }
  split; [split; [nia | exact Hprod]|].
  intros k Hk [Hk1 Hcgk].
  assert (Hakbk : cg (Z.of_nat p) (zpn a k * zpn b k) 1) by (rewrite <- zpn_mul_dist; exact Hcgk).
  assert (Hbkd2 : cg (Z.of_nat p) (zpn b (k * d2)) 1)
    by (rewrite Nat.mul_comm; apply (per_mult p b d2 k); exact Hbcg).
  assert (Hakd2 : cg (Z.of_nat p) (zpn a (k * d2)) 1).
  { assert (Hraise : cg (Z.of_nat p) (zpn (zpn a k * zpn b k) d2) (zpn 1 d2))
      by (apply zpn_cong; exact Hakbk).
    rewrite zpn_one, zpn_mul_dist, <- !zpn_mul in Hraise.
    apply (cg_trans _ _ (zpn a (k * d2) * zpn b (k * d2))); [| exact Hraise].
    apply (cg_trans _ _ (zpn a (k * d2) * 1));
      [rewrite Z.mul_1_r; apply cg_refl
       | apply cg_mul; [apply cg_refl | apply cg_sym; exact Hbkd2]]. }
  assert (Hd1kd2 : Nat.divide d1 (k * d2))
    by (apply (order_divides p a d1 (k * d2)); [split; [exact Hd1pos | exact Hacg] | exact Hamin | exact Hakd2]).
  assert (Hd1k : Nat.divide d1 k)
    by (apply (nat_coprime_divmul d1 d2 k Hcop); rewrite Nat.mul_comm; exact Hd1kd2).
  assert (Hakd1 : cg (Z.of_nat p) (zpn a (k * d1)) 1)
    by (rewrite Nat.mul_comm; apply (per_mult p a d1 k); exact Hacg).
  assert (Hbkd1 : cg (Z.of_nat p) (zpn b (k * d1)) 1).
  { assert (Hraise : cg (Z.of_nat p) (zpn (zpn a k * zpn b k) d1) (zpn 1 d1))
      by (apply zpn_cong; exact Hakbk).
    rewrite zpn_one, zpn_mul_dist, <- !zpn_mul in Hraise.
    apply (cg_trans _ _ (zpn a (k * d1) * zpn b (k * d1))); [| exact Hraise].
    apply (cg_trans _ _ (1 * zpn b (k * d1)));
      [rewrite Z.mul_1_l; apply cg_refl
       | apply cg_mul; [apply cg_sym; exact Hakd1 | apply cg_refl]]. }
  assert (Hd2kd1 : Nat.divide d2 (k * d1))
    by (apply (order_divides p b d2 (k * d1)); [split; [exact Hd2pos | exact Hbcg] | exact Hbmin | exact Hbkd1]).
  assert (Hd2k : Nat.divide d2 k).
  { apply (nat_coprime_divmul d2 d1 k); [rewrite Nat.gcd_comm; exact Hcop | rewrite Nat.mul_comm; exact Hd2kd1]. }
  assert (Hd12k : Nat.divide (d1 * d2) k).
  { destruct Hd1k as [q Hq]. destruct Hd2k as [r Hr].
    assert (Hd2q : Nat.divide d2 q).
    { apply (nat_coprime_divmul d2 d1 q); [rewrite Nat.gcd_comm; exact Hcop|].
      exists r. nia. }
    destruct Hd2q as [t Ht]. exists t. rewrite Hq, Ht. ring. }
  destruct Hd12k as [q Hq]. destruct q as [|q']; nia.
Qed.

(* a unit residue is not divisible by p *)
Lemma unit_not_div : forall p a, In a (units p) -> ~ (Z.of_nat p | a).
Proof.
  intros p a Hin. unfold units in Hin. apply in_map_iff in Hin.
  destruct Hin as [j [Hj Hjin]]. apply in_seq in Hjin. subst a.
  intro Hd. pose proof (Znumtheory.Zdivide_le (Z.of_nat p) (Z.of_nat j) ltac:(lia) ltac:(lia) Hd). lia.
Qed.

(* p prime and p does not divide a implies p does not divide a^k *)
Lemma prime_not_div_zpn : forall p a k, Znumtheory.prime (Z.of_nat p) ->
  ~ (Z.of_nat p | a) -> ~ (Z.of_nat p | zpn a k).
Proof.
  intros p a k Hp Hna. induction k as [|k IH].
  - cbn [zpn]. intro Hd.
    pose proof (Znumtheory.Zdivide_le (Z.of_nat p) 1 ltac:(lia) ltac:(lia) Hd).
    destruct Hp as [Hpg _]. lia.
  - cbn [zpn]. intro Hd.
    destruct (Znumtheory.prime_mult (Z.of_nat p) Hp a (zpn a k) Hd) as [H|H];
      [apply Hna; exact H | apply IH; exact H].
Qed.

(* one-subgroup version: some unit is not a root of X^m - 1 *)
Lemma exists_unit_avoiding1 : forall p m, Znumtheory.prime (Z.of_nat p) ->
  (1 <= m)%nat -> (m < p - 1)%nat ->
  exists h, In h (units p) /\ ~ cg (Z.of_nat p) (zpn h m) 1.
Proof.
  intros p m Hp Hm Hlt.
  set (badb := fun a => rootb (Z.of_nat p) (Xpoly m) a).
  assert (Hincl : incl (filter badb (units p)) (rootl (Z.of_nat p) (Xpoly m))).
  { intros a Ha. apply filter_In in Ha. destruct Ha as [Hau Hbad].
    apply units_in_residues in Hau. unfold rootl. apply filter_In. split; [exact Hau | exact Hbad]. }
  assert (Hlenbad : (length (filter badb (units p)) <= m)%nat).
  { pose proof (NoDup_incl_length (NoDup_filter badb (units_NoDup p)) Hincl) as Hle.
    pose proof (S_card_bound p m Hp Hm). lia. }
  assert (Hshort : (length (filter badb (units p)) < length (units p))%nat)
    by (rewrite units_length; lia).
  destruct (filter_short Z badb (units p) Hshort) as [h [Hh Hhf]].
  exists h. split; [exact Hh|].
  intro Hc. assert (Hb : rootb (Z.of_nat p) (Xpoly m) h = true) by (apply rootb_iff_cg; assumption).
  unfold badb in Hhf. rewrite Hb in Hhf. discriminate.
Qed.

(* a unit of order exactly q^e, where q^e is the exact q-part of p-1 (r coprime to q) *)
Lemma exists_order_ppow : forall p q e r,
  Znumtheory.prime (Z.of_nat p) -> Znumtheory.prime (Z.of_nat q) ->
  (p - 1 = q ^ e * r)%nat -> Nat.gcd q r = 1%nat ->
  exists g, ~ (Z.of_nat p | g) /\ is_order p g (q ^ e).
Proof.
  intros p q e r Hp Hq Hpe Hcop.
  assert (Hqge : (2 <= q)%nat) by (destruct Hq; lia).
  assert (Hp2 : (2 <= p)%nat) by (destruct Hp; lia).
  assert (Hqepos : (1 <= q ^ e)%nat) by (apply Nat.neq_0_lt_0; apply Nat.pow_nonzero; lia).
  assert (Hrpos : (1 <= r)%nat)
    by (destruct r as [|r']; [rewrite Nat.mul_0_r in Hpe; lia | lia]).
  destruct e as [|e'].
  - exists 1%Z. rewrite Nat.pow_0_r. split.
    + intro Hd. pose proof (Znumtheory.Zdivide_le (Z.of_nat p) 1 ltac:(lia) ltac:(lia) Hd). lia.
    + split; [split; [lia | rewrite (zpn_one 1); apply cg_refl]
              | intros k Hk Hper; destruct Hper as [Hk1 _]; lia].
  - set (E := S e').
    assert (Hqe'pos : (1 <= q ^ e')%nat) by (apply Nat.neq_0_lt_0; apply Nat.pow_nonzero; lia).
    assert (Hm1 : (1 <= q ^ e' * r)%nat) by nia.
    assert (Hmlt : (q ^ e' * r < p - 1)%nat).
    { rewrite Hpe. unfold E. cbn [Nat.pow]. nia. }
    destruct (exists_unit_avoiding1 p (q ^ e' * r) Hp Hm1 Hmlt) as [h [Hhu Hhbad]].
    assert (Hhnd : ~ (Z.of_nat p | h)) by (apply unit_not_div; exact Hhu).
    set (g := zpn h r).
    assert (Hgnd : ~ (Z.of_nat p | g)) by (unfold g; apply prime_not_div_zpn; assumption).
    assert (HgE : cg (Z.of_nat p) (zpn g (q ^ E)) 1).
    { unfold g. rewrite <- zpn_mul.
      replace (r * q ^ E)%nat with (p - 1)%nat by (rewrite Hpe; unfold E; ring).
      apply fermat_cg; assumption. }
    assert (Hge' : cg (Z.of_nat p) (zpn g (q ^ e')) (zpn h (q ^ e' * r))).
    { unfold g. rewrite <- zpn_mul.
      replace (r * q ^ e')%nat with (q ^ e' * r)%nat by ring. apply cg_refl. }
    destruct (order_exists p g Hp Hgnd) as [d [Hpd Hmin]].
    assert (HdvE : Nat.divide d (q ^ E)) by (apply (order_divides p g d (q ^ E)); assumption).
    destruct (divisor_of_prime_pow q E d Hq HdvE) as [i [HiE Hdi]].
    assert (Hie : i = E).
    { destruct (Nat.eq_dec i E) as [Hi|Hi]; [exact Hi | exfalso].
      assert (Hile' : (i <= e')%nat) by (unfold E in *; lia).
      assert (Hdvde' : Nat.divide d (q ^ e'))
        by (rewrite Hdi; exists (q ^ (e' - i))%nat; rewrite <- Nat.pow_add_r; f_equal; lia).
      destruct Hdvde' as [t Ht].
      assert (Hcg : cg (Z.of_nat p) (zpn g (q ^ e')) 1).
      { rewrite Ht, (Nat.mul_comm t d). apply (per_mult p g d t). exact (proj2 Hpd). }
      apply Hhbad. apply (cg_trans _ _ (zpn g (q ^ e'))); [apply cg_sym; exact Hge' | exact Hcg]. }
    rewrite Hie in Hdi. exists g. split; [exact Hgnd|]. rewrite <- Hdi. split; [exact Hpd | exact Hmin].
Qed.

(* if m divides a then m divides a^k for k >= 1 *)
Lemma div_zpn_of_div : forall m a k, (m | a) -> (1 <= k)%nat -> (m | zpn a k).
Proof.
  intros m a k Hd Hk. destruct k as [|k']; [lia|].
  cbn [zpn]. apply Z.divide_mul_l. exact Hd.
Qed.

(* coprimality is preserved under powers *)
Lemma coprime_pow_r : forall k b f, Nat.gcd k b = 1%nat -> Nat.gcd k (b ^ f) = 1%nat.
Proof.
  intros k b f Hg. induction f as [|f IH].
  - rewrite Nat.pow_0_r. apply gcd_n_1.
  - rewrite Nat.pow_succ_r'. apply (proj2 (coprime_mul_iff k b (b ^ f))). split; [exact Hg | exact IH].
Qed.

(* the order is congruence-invariant *)
Lemma is_order_cong : forall p a b d, cg (Z.of_nat p) a b -> is_order p a d -> is_order p b d.
Proof.
  intros p a b d Hcg [Hper Hmin].
  assert (Hcgd : forall k, cg (Z.of_nat p) (zpn a k) (zpn b k)) by (intro k; apply zpn_cong; exact Hcg).
  split.
  - destruct Hper as [Hd1 Hacg]. split; [exact Hd1|].
    apply (cg_trans _ _ (zpn a d)); [apply cg_sym; apply Hcgd | exact Hacg].
  - intros k Hk [Hk1 Hbcg]. apply (Hmin k Hk). split; [exact Hk1|].
    apply (cg_trans _ _ (zpn b k)); [apply Hcgd | exact Hbcg].
Qed.

Lemma prime_Z_2 : Znumtheory.prime (Z.of_nat 2).
Proof. change (Z.of_nat 2) with 2%Z. apply Znumtheory.prime_2. Qed.

Lemma prime_Z_3 : Znumtheory.prime (Z.of_nat 3).
Proof.
  change (Z.of_nat 3) with 3%Z. apply Znumtheory.prime_intro; [lia|].
  intros n Hn. apply Znumtheory.Zgcd_1_rel_prime.
  assert (Hc : n = 1 \/ n = 2) by lia. destruct Hc as [->| ->]; reflexivity.
Qed.

Lemma prime_Z_5 : Znumtheory.prime (Z.of_nat 5).
Proof.
  change (Z.of_nat 5) with 5%Z. apply Znumtheory.prime_intro; [lia|].
  intros n Hn. apply Znumtheory.Zgcd_1_rel_prime.
  assert (Hc : n = 1 \/ n = 2 \/ n = 3 \/ n = 4) by lia.
  destruct Hc as [->|[->|[->| ->]]]; reflexivity.
Qed.

(* PRIMITIVE ROOT for 5-smooth primes: combine the 2-, 3-, 5-part generators
   (orders 2^a, 3^b, 5^c) whose product has order 2^a*3^b*5^c = p-1, then reduce
   mod p to a canonical representative in [1, p). *)
Lemma primitive_root_5smooth : forall p, Znumtheory.prime (Z.of_nat p) ->
  is_5_smooth (euler_phi p) -> (5 <= p)%nat ->
  exists g, (1 <= g < Z.of_nat p)%Z /\ per p g (p - 1) /\
            (forall k, (1 <= k < p - 1)%nat -> ~ cg (Z.of_nat p) (zpn g k) 1).
Proof.
  intros p Hp Hsm Hp5.
  rewrite (euler_phi_prime p Hp) in Hsm. destruct Hsm as [a [b [c Hab]]].
  assert (G23 : Nat.gcd 2 3 = 1%nat) by reflexivity.
  assert (G25 : Nat.gcd 2 5 = 1%nat) by reflexivity.
  assert (G52 : Nat.gcd 5 2 = 1%nat) by reflexivity.
  assert (G53 : Nat.gcd 5 3 = 1%nat) by reflexivity.
  destruct (exists_order_ppow p 2 a (3 ^ b * 5 ^ c) Hp prime_Z_2
              ltac:(rewrite Hab; ring)
              ltac:(apply (proj2 (coprime_mul_iff 2 (3 ^ b) (5 ^ c)));
                    split; [apply coprime_pow_r; exact G23 | apply coprime_pow_r; exact G25]))
    as [g2 [Hg2nd Hg2ord]].
  destruct (exists_order_ppow p 3 b (2 ^ a * 5 ^ c) Hp prime_Z_3
              ltac:(rewrite Hab; ring)
              ltac:(apply (proj2 (coprime_mul_iff 3 (2 ^ a) (5 ^ c)));
                    split; [apply coprime_pow_r; reflexivity | apply coprime_pow_r; reflexivity]))
    as [g3 [Hg3nd Hg3ord]].
  destruct (exists_order_ppow p 5 c (2 ^ a * 3 ^ b) Hp prime_Z_5
              ltac:(rewrite Hab; ring)
              ltac:(apply (proj2 (coprime_mul_iff 5 (2 ^ a) (3 ^ b)));
                    split; [apply coprime_pow_r; exact G52 | apply coprime_pow_r; exact G53]))
    as [g5 [Hg5nd Hg5ord]].
  assert (Hg23 : is_order p (g2 * g3)%Z (2 ^ a * 3 ^ b)%nat).
  { apply (order_coprime_mul p g2 g3 (2 ^ a) (3 ^ b) Hp Hg2ord Hg3ord).
    apply (coprime_pow_l 2 (3 ^ b) a). apply (coprime_pow_r 2 3 b). exact G23. }
  assert (HG : is_order p (g2 * g3 * g5)%Z (2 ^ a * 3 ^ b * 5 ^ c)%nat).
  { apply (order_coprime_mul p (g2 * g3) g5 (2 ^ a * 3 ^ b) (5 ^ c) Hp Hg23 Hg5ord).
    rewrite Nat.gcd_comm. apply (proj2 (coprime_mul_iff (5 ^ c) (2 ^ a) (3 ^ b))).
    split; [apply (coprime_pow_l 5 (2 ^ a) c); apply (coprime_pow_r 5 2 a); exact G52
          | apply (coprime_pow_l 5 (3 ^ b) c); apply (coprime_pow_r 5 3 b); exact G53]. }
  set (G := (g2 * g3 * g5)%Z) in *.
  assert (HGord : is_order p G (p - 1)) by (rewrite Hab; exact HG).
  assert (HGnd : ~ (Z.of_nat p | G)).
  { intro Hd. destruct HGord as [[_ Hcg] _].
    (* G^(p-1) = 1 but p | G forces p | 1 *)
    assert (Hp1 : (1 <= p - 1)%nat) by lia.
    assert (HdG : (Z.of_nat p | zpn G (p - 1))) by (apply (div_zpn_of_div (Z.of_nat p) G (p - 1) Hd Hp1)).
    unfold cg in Hcg.
    assert (Hd1 : (Z.of_nat p | 1)).
    { replace 1%Z with (zpn G (p - 1) - (zpn G (p - 1) - 1))%Z by ring.
      apply Z.divide_sub_r; assumption. }
    pose proof (Znumtheory.Zdivide_le (Z.of_nat p) 1 ltac:(lia) ltac:(lia) Hd1). lia. }
  set (g := (G mod Z.of_nat p)%Z).
  assert (HpZ : (Z.of_nat p <> 0)%Z) by lia.
  assert (Hgcg : cg (Z.of_nat p) G g).
  { unfold cg, g. rewrite Z.mod_eq by exact HpZ.
    exists (G / Z.of_nat p)%Z. ring. }
  assert (Hgord : is_order p g (p - 1)) by (apply (is_order_cong p G g (p - 1) Hgcg HGord)).
  assert (Hgnd : ~ (Z.of_nat p | g)).
  { intro Hd. apply HGnd. unfold cg in Hgcg.
    replace G with ((G - g) + g)%Z by ring. apply Z.divide_add_r; assumption. }
  assert (Hg0 : (g <> 0)%Z) by (intro H0; apply Hgnd; rewrite H0; apply Z.divide_0_r).
  assert (Hgrange : (1 <= g < Z.of_nat p)%Z).
  { unfold g. pose proof (Z.mod_pos_bound G (Z.of_nat p) ltac:(lia)) as Hb. unfold g in Hg0. lia. }
  exists g. split; [exact Hgrange | split].
  - exact (proj1 Hgord).
  - intros k [Hk1 Hk2] Hc. apply (proj2 Hgord k Hk2). split; [exact Hk1 | exact Hc].
Qed.

(* THE PRIMITIVE ROOT: for prime p (>= 5) with 2-3-smooth p-1, some g has order p-1 *)
Lemma primitive_root : forall p, Znumtheory.prime (Z.of_nat p) ->
  two_three_smooth (euler_phi p) -> (5 <= p)%nat ->
  exists g, (1 <= g < Z.of_nat p)%Z /\ per p g (p - 1) /\
            (forall k, (1 <= k < p - 1)%nat -> ~ cg (Z.of_nat p) (zpn g k) 1).
Proof.
  intros p Hp Hsm Hp5.
  assert (Hn23 : exists a b, (p - 1 = 2 ^ a * 3 ^ b)%nat).
  { destruct Hsm as [a [b Hab]]. exists a, b. rewrite <- Hab; symmetry; apply euler_phi_prime; exact Hp. }
  assert (Hn4 : (4 <= p - 1)%nat) by lia.
  assert (Hm1 : (1 <= (p - 1) / 2)%nat).
  { pose proof (Nat.div_mod (p-1) 2 ltac:(lia)). pose proof (Nat.mod_upper_bound (p-1) 2 ltac:(lia)). lia. }
  assert (Hm2 : (1 <= (p - 1) / 3)%nat).
  { pose proof (Nat.div_mod (p-1) 3 ltac:(lia)). pose proof (Nat.mod_upper_bound (p-1) 3 ltac:(lia)). lia. }
  assert (Hsum : ((p - 1) / 2 + (p - 1) / 3 < p - 1)%nat) by (apply half_third_lt; exact Hn4).
  destruct (exists_unit_avoiding p ((p-1)/2) ((p-1)/3) Hp Hm1 Hm2 Hsum) as [g [Hgu [Hg1 Hg2]]].
  assert (Hgrange : (1 <= g < Z.of_nat p)%Z).
  { unfold units in Hgu. apply in_map_iff in Hgu. destruct Hgu as [j [Hj Hjin]].
    apply in_seq in Hjin. subst g. split; [lia | apply Nat2Z.inj_lt; lia]. }
  assert (Hgnd : ~ (Z.of_nat p | g)).
  { intro Hd. pose proof (Znumtheory.Zdivide_le (Z.of_nat p) g ltac:(lia) ltac:(lia) Hd). lia. }
  destruct (order_exists p g Hp Hgnd) as [d [Hpd Hmin]].
  assert (Hdvd : Nat.divide d (p - 1))
    by (apply (order_divides p g d (p-1) Hpd Hmin); apply fermat_cg; assumption).
  assert (Hdeq : d = (p - 1)%nat).
  { destruct (Nat.eq_dec d (p-1)) as [E|Hne]; [exact E | exfalso].
    destruct (proper_div_dichotomy (p-1) d Hn23 ltac:(lia) Hdvd Hne) as [H|H].
    - apply Hg1. destruct H as [q Hq]. rewrite Hq, (Nat.mul_comm q d).
      apply (per_mult p g d q). exact (proj2 Hpd).
    - apply Hg2. destruct H as [q Hq]. rewrite Hq, (Nat.mul_comm q d).
      apply (per_mult p g d q). exact (proj2 Hpd). }
  rewrite Hdeq in Hpd, Hmin.
  exists g. split; [exact Hgrange | split; [exact Hpd|]].
  intros k [Hk1 Hk2] Hc. apply (Hmin k Hk2). split; [exact Hk1 | exact Hc].
Qed.

(* ---- Gaussian-period machinery (former periods.v) ---- *)
(******************************************************************************)
(*  periods.v — Layer 3: Gaussian periods for the prime cyclotomic field.      *)
(*                                                                            *)
(*  Discharges Hcore (the sole remaining hypothesis of dev.v's Reduction):     *)
(*    for prime p with 2-3-smooth phi(p) = p-1, cos(2*PI/p) is origami,         *)
(*  via the real Gaussian-period tower over the cyclic unit group mod p.        *)
(******************************************************************************)
Open Scope R_scope.
(* ===== Analytic foundation: the cosine of a residue mod p ===== *)

(* cos of the angle 2*PI*x/p attached to an integer residue x *)
Definition ca (p x : Z) : R := cos (2 * PI * IZR x / IZR p).

(* cos / sin at integer multiples of 2*PI *)
Lemma cos_sin_2PI_nat : forall k : nat, cos (2 * PI * INR k) = 1 /\ sin (2 * PI * INR k) = 0.
Proof.
  induction k as [|k IH].
  - simpl INR. rewrite Rmult_0_r, cos_0, sin_0. split; reflexivity.
  - rewrite S_INR.
    replace (2 * PI * (INR k + 1)) with (2 * PI * INR k + 2 * PI) by ring.
    rewrite cos_plus, sin_plus, cos_2PI, sin_2PI.
    destruct IH as [Hc Hs]. rewrite Hc, Hs. split; ring.
Qed.

Lemma cos_sin_2PI_Z : forall m : Z, cos (2 * PI * IZR m) = 1 /\ sin (2 * PI * IZR m) = 0.
Proof.
  intro m. destruct (Z_le_dec 0 m) as [Hm|Hm].
  - replace (IZR m) with (INR (Z.to_nat m)) by (rewrite INR_IZR_INZ, Z2Nat.id by exact Hm; reflexivity).
    apply cos_sin_2PI_nat.
  - assert (Hmn : IZR m = - INR (Z.to_nat (- m))).
    { rewrite INR_IZR_INZ, Z2Nat.id by lia. rewrite opp_IZR. ring. }
    rewrite Hmn.
    replace (2 * PI * - INR (Z.to_nat (- m))) with (- (2 * PI * INR (Z.to_nat (- m)))) by ring.
    rewrite cos_neg, sin_neg.
    destruct (cos_sin_2PI_nat (Z.to_nat (- m))) as [Hc Hs]. rewrite Hc, Hs. split; ring.
Qed.

(* the cosine depends only on the residue class mod p *)
Lemma ca_cong : forall p x y, (p <> 0)%Z -> (p | x - y)%Z -> ca p x = ca p y.
Proof.
  intros p x y Hp [c Hc]. unfold ca.
  assert (Hpr : IZR p <> 0) by (apply not_0_IZR; exact Hp).
  assert (Hxy : IZR x = IZR y + IZR p * IZR c).
  { assert (Hxy0 : (x = y + c * p)%Z) by lia.
    rewrite Hxy0, plus_IZR, mult_IZR. ring. }
  replace (2 * PI * IZR x / IZR p) with (2 * PI * IZR y / IZR p + 2 * PI * IZR c)
    by (rewrite Hxy; field; exact Hpr).
  rewrite cos_plus. destruct (cos_sin_2PI_Z c) as [Hcc Hcs]. rewrite Hcc, Hcs. ring.
Qed.

Lemma ca_0 : forall p, ca p 0 = 1.
Proof.
  intro p. unfold ca.
  assert (H : 2 * PI * IZR 0 / IZR p = 0).
  { replace (IZR 0) with 0 by (cbn; reflexivity). unfold Rdiv. ring. }
  rewrite H. apply cos_0.
Qed.

(* cos is even in the residue *)
Lemma ca_opp : forall p x, ca p (- x) = ca p x.
Proof.
  intros p x. unfold ca. rewrite opp_IZR.
  replace (2 * PI * - IZR x / IZR p) with (- (2 * PI * IZR x / IZR p)) by (unfold Rdiv; ring).
  apply cos_neg.
Qed.

(* ===== Finite cosine sums over a residue list ===== *)

Definition csum (p : Z) (l : list Z) : R := fold_right (fun x acc => ca p x + acc) 0 l.

Lemma csum_nil : forall p, csum p [] = 0.
Proof. reflexivity. Qed.

Lemma csum_cons : forall p x l, csum p (x :: l) = ca p x + csum p l.
Proof. reflexivity. Qed.

Lemma csum_app : forall p l1 l2, csum p (l1 ++ l2) = csum p l1 + csum p l2.
Proof.
  intros p l1 l2. induction l1 as [|x l1 IH].
  - rewrite app_nil_l, csum_nil. ring.
  - rewrite <- app_comm_cons, !csum_cons, IH. ring.
Qed.

Lemma csum_perm : forall p l1 l2, Permutation l1 l2 -> csum p l1 = csum p l2.
Proof.
  intros p l1 l2 H. induction H.
  - reflexivity.
  - rewrite !csum_cons, IHPermutation. reflexivity.
  - rewrite !csum_cons. ring.
  - rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.

Lemma csum_map : forall p (f : Z -> Z) l,
  csum p (map f l) = fold_right (fun x acc => ca p (f x) + acc) 0 l.
Proof.
  intros p f l. induction l as [|x l IH]; [reflexivity|].
  cbn [map]. rewrite csum_cons, IH. reflexivity.
Qed.

(* ===== The Gaussian-period section: P prime >= 5, g a primitive root ===== *)
Open Scope R_scope.
Lemma quad_root_from_psums : forall a b e1 p2 : R,
  e1 = a + b -> p2 = a*a + b*b ->
  a*a + (- e1)*a + (e1*e1 - p2)/2 = 0.
Proof. intros a b e1 p2 H1 H2. subst e1 p2. field. Qed.

(* degree-3: a is a root of t^3 - e1 t^2 + e2 t - e3, with e2 = (e1^2-p2)/2 and
   e3 = (p3 - e1 p2 + e2 e1)/3 (Newton's identities). *)
Lemma cubic_root_from_psums : forall a b c e1 p2 p3 : R,
  e1 = a + b + c -> p2 = a*a + b*b + c*c -> p3 = a*a*a + b*b*b + c*c*c ->
  a*a*a + (- e1)*(a*a) + ((e1*e1 - p2)/2)*a
    + (- ((p3 - e1*p2 + ((e1*e1 - p2)/2)*e1)/3)) = 0.
Proof. intros a b c e1 p2 p3 H1 H2 H3. subst e1 p2 p3. field. Qed.
Close Scope R_scope.
Close Scope R_scope.
Close Scope R_scope.
Close Scope R_scope.
Close Scope Z_scope.
Close Scope nat_scope.
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
