(* geometry.v -- the Huzita-Hatori axioms O1-O7, folds, constructibility and its
   enumeration, the Gaussian-period tower, the regular n-gon iff, and casus
   irreducibilis for real square+cube-root towers.  Depends on foundations,
   cyclotomic. *)
From Stdlib Require Import Reals Lra Field R_sqr Psatz Nsatz Ring Ranalysis1 RingMicromega List ProofIrrelevance ClassicalDescription PeanoNat ZArith Classical Permutation Bool Arith.Wf_nat.
From Stdlib Require Znumtheory.
Import ListNotations.
Require Import foundations cyclotomic.
Open Scope R_scope.
Definition Point : Type := R * R.

(** Implicit line Ax + By + C = 0 *)
Record Line : Type := {
  A : R;
  B : R;
  C : R
}.

(** A ≠ 0 ∨ B ≠ 0 *)
Definition line_wf (l : Line) : Prop := A l <> 0 \/ B l <> 0.

(** Constructor with well-formedness witness *)
Definition mkLine (a b c : R) (H : a <> 0 \/ b <> 0) : Line :=
  {| A := a; B := b; C := c |}.

(** (A,B,C) ↦ (A,B,C)/√(A²+B²) *)
Definition normalize_line (l : Line) : Line :=
  let a := A l in
  let b := B l in
  let c := C l in
  let n := sqrt (a * a + b * b) in
  {| A := a / n; B := b / n; C := c / n |}.

(** Normalization preserves well-formedness *)
Lemma normalize_line_wf : forall l, line_wf l -> line_wf (normalize_line l).
Proof.
  intros l Hnz.
  unfold line_wf, normalize_line. simpl.
  set (a := A l). set (b := B l).
  set (n := sqrt (a * a + b * b)).
  assert (Hn : n <> 0).
  { unfold n; intro Hz; apply sqrt_eq_0 in Hz.
    - assert (Ha2nn : 0 <= a * a) by apply Rle_0_sqr.
      assert (Hb2nn : 0 <= b * b) by apply Rle_0_sqr.
      assert (Ha2 : a * a = 0) by lra.
      assert (Hb2 : b * b = 0) by lra.
      assert (Ha0 : a = 0).
      { destruct (Rmult_integral _ _ Ha2) as [H0 | H0]; lra. }
      assert (Hb0 : b = 0).
      { destruct (Rmult_integral _ _ Hb2) as [H0 | H0]; lra. }
      unfold a, b in *. destruct Hnz; contradiction.
    - apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
  destruct Hnz as [Ha | Hb].
  - left; unfold Rdiv; apply Rmult_integral_contrapositive_currified; auto.
    intro Hinv; apply Rinv_neq_0_compat in Hn; contradiction.
  - right; unfold Rdiv; apply Rmult_integral_contrapositive_currified; auto.
    intro Hinv; apply Rinv_neq_0_compat in Hn; contradiction.
Qed.



(** p ∈ l ⟺ Ax + By + C = 0 *)
Definition on_line (p : Point) (l : Line) : Prop :=
  let '(x, y) := p in A l * x + B l * y + C l = 0.

(** p ∈ l ⟺ p ∈ normalize(l) *)
Lemma normalize_line_on_line : forall p l, line_wf l -> (on_line p l <-> on_line p (normalize_line l)).
Proof.
  intros [x y] l Hwf; unfold on_line, normalize_line; simpl.
  set (a := A l). set (b := B l). set (c := C l).
  set (n := sqrt (a * a + b * b)).
  assert (Hn : n <> 0).
  { unfold n; intro Hz; apply sqrt_eq_0 in Hz.
    - assert (Ha2nn : 0 <= a * a) by apply Rle_0_sqr.
      assert (Hb2nn : 0 <= b * b) by apply Rle_0_sqr.
      assert (Ha2 : a * a = 0) by lra.
      assert (Hb2 : b * b = 0) by lra.
      assert (Ha0 : a = 0).
      { destruct (Rmult_integral _ _ Ha2) as [H0 | H0]; lra. }
      assert (Hb0 : b = 0).
      { destruct (Rmult_integral _ _ Hb2) as [H0 | H0]; lra. }
      unfold a, b in *. unfold line_wf in Hwf. destruct Hwf; contradiction.
    - apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
  split; intro H.
  - unfold Rdiv.
    replace (a * / n * x + b * / n * y + c * / n) with (/ n * (a * x + b * y + c)) by (field; assumption).
    rewrite H; ring.
  - assert (Heq : a * x + b * y + c = n * (a / n * x + b / n * y + c / n)).
    { unfold Rdiv; field; assumption. }
    rewrite Heq, H; ring.
Qed.

(** p = q as points *)
Definition point_eq (p q : Point) : Prop :=
  fst p = fst q /\ snd p = snd q.

(** l₁ ∥ l₂ ⟺ A₁B₂ = A₂B₁ *)
Definition line_parallel (l1 l2 : Line) : Prop :=
  A l1 * B l2 = A l2 * B l1.

(** l₁ ⊥ l₂ ⟺ A₁A₂ + B₁B₂ = 0 *)
Definition line_perp (l1 l2 : Line) : Prop :=
  A l1 * A l2 + B l1 * B l2 = 0.


(** Decidable predicates for computation *)

(** {p = q} + {p ≠ q} *)
Definition point_eq_dec (p q : Point) : {p = q} + {p <> q}.
Proof.
  destruct p as [x1 y1], q as [x2 y2].
  destruct (Req_EM_T x1 x2) as [Hx | Hx].
  - destruct (Req_EM_T y1 y2) as [Hy | Hy].
    + left. rewrite Hx, Hy. reflexivity.
    + right. intro H. injection H as H1 H2. contradiction.
  - right. intro H. injection H as H1 H2. contradiction.
Defined.

(** {p ∈ l} + {p ∉ l} *)
Definition on_line_dec (p : Point) (l : Line) : {on_line p l} + {~on_line p l}.
Proof. unfold on_line. destruct p as [x y]. apply Req_EM_T. Defined.

(** {l₁ ∥ l₂} + {l₁ ∦ l₂} *)
Definition line_parallel_dec (l1 l2 : Line) : {line_parallel l1 l2} + {~line_parallel l1 l2}.
Proof. unfold line_parallel. apply Req_EM_T. Defined.

(** {l₁ ⊥ l₂} + {l₁ ⊥̸ l₂} *)
Definition line_perp_dec (l1 l2 : Line) : {line_perp l1 l2} + {~line_perp l1 l2}.
Proof. unfold line_perp. apply Req_EM_T. Defined.



(** x² *)
Definition dist (p q : Point) : R :=
  let '(x1, y1) := p in
  let '(x2, y2) := q in
  sqrt (sqr (x1 - x2) + sqr (y1 - y2)).

(** (x₁-x₂)² + (y₁-y₂)² *)
Definition dist2 (p q : Point) : R :=
  let '(x1, y1) := p in
  let '(x2, y2) := q in
  sqr (x1 - x2) + sqr (y1 - y2).

(** x ≠ 0 → x² > 0 *)
Definition line_norm (l : Line) : R :=
  sqrt (sqr (A l) + sqr (B l)).

(** |Ax + By + C| / √(A² + B²) *)
Definition dist_point_line (p : Point) (l : Line) : R :=
  Rabs (let '(x, y) := p in A l * x + B l * y + C l) / line_norm l.


(** Folds as reflection lines, point/line reflection operations *)

(** A fold is determined by its crease line *)
Inductive Fold : Type :=
| fold_line_ctor : Line -> Fold.

(** Extract crease line from fold *)
Definition fold_line (f : Fold) : Line :=
  match f with
  | fold_line_ctor l => l
  end.

(** Reflection of p across l *)
Definition reflect_point (p : Point) (l : Line) : Point :=
  let '(x, y) := p in
  let a := A l in
  let b := B l in
  let c := C l in
  let denom := a * a + b * b in
  let factor := (a * x + b * y + c) / denom in
  let xr := x - 2 * a * factor in
  let yr := y - 2 * b * factor in
  (xr, yr).

(** Two distinct points on l for parametrizing the line *)
Definition base_points (l : Line) : Point * Point :=
  match Req_EM_T (B l) 0 with
  | left Hb =>
      let x0 := - C l / A l in
      ((x0, 0), (x0, 1))
  | right Hb =>
      let y0 := - C l / B l in
      let y1 := - (A l + C l) / B l in
      ((0, y0), (1, y1))
  end.

(** Image of p under fold f *)
Definition map_point (f : Fold) (p : Point) : Point :=
  reflect_point p (fold_line f).

(** Unique line containing p₁ and p₂ *)
Definition line_through (p1 p2 : Point) : Line :=
  let '(x1, y1) := p1 in
  let '(x2, y2) := p2 in
  match Req_EM_T x1 x2 with
  | left Heq =>
      {| A := 1; B := 0; C := - x1 |}
  | right Hneq =>
      let a := y1 - y2 in
      let b := x2 - x1 in
      let c := x1 * y2 - x2 * y1 in
      {| A := a; B := b; C := c |}
  end.

(** line_through(p₁,p₂) is well-formed *)
Lemma line_through_wf : forall p1 p2, line_wf (line_through p1 p2).
Proof.
  intros [x1 y1] [x2 y2].
  unfold line_wf, line_through.
  destruct (Req_EM_T x1 x2) as [Heq | Hneq]; simpl.
  - left. apply R1_neq_R0.
  - right. assert (Hgoal: x2 - x1 <> 0) by lra. exact Hgoal.
Qed.

(** p₁ ∈ line_through(p₁,p₂) *)
Lemma line_through_on_line_fst : forall p1 p2,
  on_line p1 (line_through p1 p2).
Proof.
  intros [x1 y1] [x2 y2].
  unfold on_line, line_through; simpl.
  destruct (Req_EM_T x1 x2); simpl; ring.
Qed.

(** p₂ ∈ line_through(p₁,p₂) *)
Lemma line_through_on_line_snd : forall p1 p2,
  on_line p2 (line_through p1 p2).
Proof.
  intros [x1 y1] [x2 y2].
  unfold on_line, line_through; simpl.
  destruct (Req_EM_T x1 x2) as [Hx|Hx]; simpl.
  - subst. ring.
  - ring.
Qed.

(** Reflection of line l across fold f *)
Definition map_line (f : Fold) (l : Line) : Line :=
  let '(p1, p2) := base_points l in
  line_through (map_point f p1) (map_point f p2).

(** Orthogonal projection of p onto l *)
Definition foot_on_line (p : Point) (l : Line) : Point :=
  let '(x, y) := p in
  let a := A l in
  let b := B l in
  let c := C l in
  let denom := a * a + b * b in
  let factor := (a * x + b * y + c) / denom in
  (x - a * factor, y - b * factor).

(** base_points(l) ⊂ l *)
Lemma base_points_on_line : forall l,
  line_wf l -> on_line (fst (base_points l)) l /\ on_line (snd (base_points l)) l.
Proof.
  intros l Hwf; unfold base_points, on_line; simpl.
  destruct (Req_EM_T (B l) 0) as [Hb | Hb].
  - assert (Ha : A l <> 0).
    { unfold line_wf in Hwf. destruct Hwf as [Ha | Hb0]; [assumption | contradiction]. }
    split; simpl.
    + rewrite Hb. rewrite mul_div_cancel_l by exact Ha. lra.
    + rewrite Hb. rewrite mul_div_cancel_l by exact Ha. lra.
  - split; simpl.
    + rewrite mul_div_cancel_l by exact Hb. lra.
    + rewrite mul_div_cancel_l by exact Hb. lra.
Qed.

(** fst(base_points(l)) ≠ snd(base_points(l)) *)
Lemma base_points_distinct : forall l,
  fst (base_points l) <> snd (base_points l).
Proof.
  intro l; unfold base_points; simpl.
  destruct (Req_EM_T (B l) 0) as [Hb | Hb].
  - intro Heq. injection Heq. intros. lra.
  - intro Heq. injection Heq. intros. lra.
Qed.

(** x-coordinate difference under reflection *)
Definition midpoint (p1 p2 : Point) : Point :=
  let '(x1, y1) := p1 in
  let '(x2, y2) := p2 in
  ((x1 + x2) / 2, (y1 + y2) / 2).

(** l₁ ∩ l₂ via Cramer's rule; returns (0,0) if parallel *)
Definition line_intersection (l1 l2 : Line) : Point :=
  let D := A l1 * B l2 - A l2 * B l1 in
  let Dx := (- C l1) * B l2 - (- C l2) * B l1 in
  let Dy := A l1 * (- C l2) - A l2 * (- C l1) in
  match Req_EM_T D 0 with
  | left _ => (0, 0)
  | right Hnz => (Dx / D, Dy / D)
  end.

(** l₁ ∥ l₂ → line_intersection returns (0,0) *)
Lemma line_intersection_parallel : forall l1 l2,
  A l1 * B l2 - A l2 * B l1 = 0 -> line_intersection l1 l2 = (0, 0).
Proof.
  intros l1 l2 HD.
  unfold line_intersection.
  destruct (Req_EM_T (A l1 * B l2 - A l2 * B l1) 0).
  - reflexivity.
  - contradiction.
Qed.

(** y = 0 *)
Definition line_xaxis : Line := {| A := 0; B := 1; C := 0 |}.

(** x = 0 *)
Definition line_yaxis : Line := {| A := 1; B := 0; C := 0 |}.

Lemma line_xaxis_wf : line_wf line_xaxis.
Proof. unfold line_wf, line_xaxis. simpl. right. apply R1_neq_R0. Qed.

Lemma line_yaxis_wf : line_wf line_yaxis.
Proof. unfold line_wf, line_yaxis. simpl. left. apply R1_neq_R0. Qed.

(** Origin *)
Definition point_O : Point := (0, 0).

(** Unit point on x-axis *)
Definition point_X : Point := (1, 0).

(** line_wf l → A² + B² > 0 *)
Lemma line_norm_pos : forall l : Line, line_wf l -> A l * A l + B l * B l > 0.
Proof.
  intros l Hwf.
  unfold line_wf in Hwf.
  destruct Hwf as [HA | HB].
  - set (A2 := A l * A l).
    set (B2 := B l * B l).
    assert (HApos : 0 < A2) by (subst A2; apply square_pos; exact HA).
    assert (HBge : 0 <= B2) by (subst B2; apply Rle_0_sqr).
    lra.
  - set (A2 := A l * A l).
    set (B2 := B l * B l).
    assert (HBpos : 0 < B2) by (subst B2; apply square_pos; exact HB).
    assert (HAge : 0 <= A2) by (subst A2; apply Rle_0_sqr).
    lra.
Qed.

(** line_wf l → ‖l‖ ≠ 0 *)
Lemma line_norm_nonzero : forall l, line_wf l -> line_norm l <> 0.
Proof.
  intros l Hwf.
  unfold line_norm.
  intro Hz.
  apply sqrt_eq_0 in Hz.
  + replace (sqr (A l) + sqr (B l)) with (A l * A l + B l * B l) in Hz by (unfold sqr; ring).
    pose proof (line_norm_pos l Hwf) as Hpos.
    lra.
  + apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

(** foot(p,l) ∈ l *)
Lemma foot_on_line_incident : forall p l, line_wf l -> on_line (foot_on_line p l) l.
Proof.
  intros [x y] l Hwf; unfold foot_on_line, on_line; simpl.
  apply proj_eval.
  exact Hwf.
Qed.

(** p ∈ l → reflect(p,l) = p *)
Lemma reflect_point_on_line : forall p l, on_line p l -> reflect_point p l = p.
Proof.
  intros [x y] l H.
  unfold reflect_point, on_line in *; simpl in *.
  rewrite H.
  simpl.
  repeat rewrite Rdiv_0_l.
  repeat rewrite Rmult_0_l.
  repeat rewrite Rmult_0_r.
  repeat rewrite Rplus_0_l.
  repeat rewrite Rplus_0_r.
  repeat rewrite Rminus_0_r.
  repeat rewrite Rminus_0_l.
  reflexivity.
Qed.

(** p ∈ fold_line(f) → map_point(f,p) = p *)
Lemma map_point_fix : forall f p, on_line p (fold_line f) -> map_point f p = p.
Proof.
  intros f p H.
  destruct f; simpl in *.
  apply reflect_point_on_line; exact H.
Qed.

(** reflect(reflect(p,l),l) = p *)
Lemma reflect_point_involutive : forall p l, line_wf l -> reflect_point (reflect_point p l) l = p.
Proof.
  intros [x y] l Hwf; unfold reflect_point; simpl.
  set (a := A l).
  set (b := B l).
  set (c := C l).
  set (d := a * a + b * b).
  set (r := a * x + b * y + c).
  assert (Hd : d <> 0) by (unfold d, a, b; apply Rgt_not_eq, line_norm_pos; exact Hwf).
  set (x1 := x - 2 * a * (r / d)).
  set (y1 := y - 2 * b * (r / d)).
  replace (a * x1 + b * y1 + c) with (- r).
  - unfold x1, y1; simpl.
    apply f_equal2; field; auto.
  - unfold x1, y1, r, d; field; auto.
Qed.

(** map_point is an involution *)
Lemma map_point_involutive : forall f p, line_wf (fold_line f) -> map_point f (map_point f p) = p.
Proof.
  intros [l] p Hwf; simpl in *.
  apply reflect_point_involutive. exact Hwf.
Qed.

(** Reflection is an isometry: dist²(p',q') = dist²(p,q) *)
Lemma reflect_point_isometry_dist2 : forall p q l,
  line_wf l -> dist2 (reflect_point p l) (reflect_point q l) = dist2 p q.
Proof.
  intros [x1 y1] [x2 y2] l Hwf.
  unfold reflect_point, dist2; simpl.
  set (a := A l); set (b := B l); set (c := C l).
  set (d := a * a + b * b).
  assert (Hd : d <> 0) by (unfold d, a, b; apply Rgt_not_eq, line_norm_pos; exact Hwf).
  set (dx := x1 - x2).
  set (dy := y1 - y2).
  assert (Hx := delta_reflect_x a b c d x1 x2 y1 y2 Hd).
  assert (Hy := delta_reflect_y a b c d x1 x2 y1 y2 Hd).
  rewrite Hx, Hy.
  apply reflect_delta_sq; unfold a, b, d; assumption.
Qed.

(** Three points are collinear iff this orientation cross-product vanishes *)
Definition collinear3 (p q r : Point) : Prop :=
  (fst q - fst p) * (snd r - snd p) - (snd q - snd p) * (fst r - fst p) = 0.

(** Reflection across a well-formed line negates the orientation cross-product *)
Lemma reflect_cross_neg : forall l p q r,
  line_wf l ->
  (fst (reflect_point q l) - fst (reflect_point p l)) *
  (snd (reflect_point r l) - snd (reflect_point p l)) -
  (snd (reflect_point q l) - snd (reflect_point p l)) *
  (fst (reflect_point r l) - fst (reflect_point p l)) =
  - ((fst q - fst p) * (snd r - snd p) - (snd q - snd p) * (fst r - fst p)).
Proof.
  intros l [px py] [qx qy] [rx ry] Hwf.
  unfold reflect_point. simpl.
  assert (Hd : A l * A l + B l * B l <> 0)
    by (apply Rgt_not_eq; apply line_norm_pos; exact Hwf).
  field. exact Hd.
Qed.

(** Reflection across a well-formed line preserves collinearity *)
Lemma reflect_preserves_collinear : forall l p q r,
  line_wf l ->
  (collinear3 p q r <->
   collinear3 (reflect_point p l) (reflect_point q l) (reflect_point r l)).
Proof.
  intros l p q r Hwf. unfold collinear3.
  rewrite (reflect_cross_neg l p q r Hwf).
  split; intro H; lra.
Qed.

(** On a well-formed line, incidence of p equals collinearity with two distinct points of the line *)
Lemma on_line_collinear_general : forall l b1 b2 p,
  line_wf l -> on_line b1 l -> on_line b2 l -> b1 <> b2 ->
  (on_line p l <-> collinear3 b1 b2 p).
Proof.
  intros l [b1x b1y] [b2x b2y] [px py] Hwf Hb1 Hb2 Hbne.
  unfold on_line in Hb1, Hb2 |- *. unfold collinear3. simpl in *.
  assert (Hu : b2x - b1x <> 0 \/ b2y - b1y <> 0).
  { destruct (Req_EM_T b2x b1x) as [Hx|Hx].
    - destruct (Req_EM_T b2y b1y) as [Hy|Hy].
      + exfalso. apply Hbne. subst. reflexivity.
      + right. lra.
    - left. lra. }
  split.
  - intro Hp.
    destruct (Req_EM_T (A l) 0) as [Ha0|Ha0].
    + assert (Hb' : B l <> 0).
      { unfold line_wf in Hwf. destruct Hwf as [Ha|Hb]; [contradiction|exact Hb]. }
      apply (Rmult_eq_reg_l (B l)); [|exact Hb']. rewrite Rmult_0_r.
      replace (B l * ((b2x - b1x) * (py - b1y) - (b2y - b1y) * (px - b1x)))
        with ((b2x - b1x) * ((A l * px + B l * py + C l) - (A l * b1x + B l * b1y + C l))
            - (px - b1x) * ((A l * b2x + B l * b2y + C l) - (A l * b1x + B l * b1y + C l)))
        by ring.
      rewrite Hb1, Hb2, Hp. ring.
    + apply (Rmult_eq_reg_l (A l)); [|exact Ha0]. rewrite Rmult_0_r.
      replace (A l * ((b2x - b1x) * (py - b1y) - (b2y - b1y) * (px - b1x)))
        with ((py - b1y) * ((A l * b2x + B l * b2y + C l) - (A l * b1x + B l * b1y + C l))
            - (b2y - b1y) * ((A l * px + B l * py + C l) - (A l * b1x + B l * b1y + C l)))
        by ring.
      rewrite Hb1, Hb2, Hp. ring.
  - intro Hcol.
    destruct Hu as [Hux|Huy].
    + apply (Rmult_eq_reg_l (b2x - b1x)); [|exact Hux]. rewrite Rmult_0_r.
      replace ((b2x - b1x) * (A l * px + B l * py + C l))
        with ((px - b1x) * ((A l * b2x + B l * b2y + C l) - (A l * b1x + B l * b1y + C l))
            + B l * ((b2x - b1x) * (py - b1y) - (b2y - b1y) * (px - b1x))
            + (b2x - b1x) * (A l * b1x + B l * b1y + C l))
        by ring.
      rewrite Hb1, Hb2, Hcol. ring.
    + apply (Rmult_eq_reg_l (b2y - b1y)); [|exact Huy]. rewrite Rmult_0_r.
      replace ((b2y - b1y) * (A l * px + B l * py + C l))
        with ((py - b1y) * ((A l * b2x + B l * b2y + C l) - (A l * b1x + B l * b1y + C l))
            - A l * ((b2x - b1x) * (py - b1y) - (b2y - b1y) * (px - b1x))
            + (b2y - b1y) * (A l * b1x + B l * b1y + C l))
        by ring.
      rewrite Hb1, Hb2, Hcol. ring.
Qed.

(** A point lies on the join of two distinct points iff it is collinear with them *)
Lemma on_line_line_through_iff_collinear : forall r1 r2 q,
  r1 <> r2 ->
  (on_line q (line_through r1 r2) <-> collinear3 r1 r2 q).
Proof.
  intros [x1 y1] [x2 y2] [qx qy] Hneq.
  unfold on_line, line_through, collinear3. simpl.
  destruct (Req_EM_T x1 x2) as [Hx|Hx]; simpl.
  - subst x2.
    assert (Hy : y1 <> y2) by (intro Hyy; apply Hneq; subst; reflexivity).
    split; intro H.
    + assert (Hq : qx = x1) by lra.
      rewrite Hq. ring.
    + assert (Hq : (y2 - y1) * (qx - x1) = 0) by nra.
      apply Rmult_integral in Hq. destruct Hq as [H1|H1]; lra.
  - assert (Heq : (y1 - y2) * qx + (x2 - x1) * qy + (x1 * y2 - x2 * y1) =
                  (x2 - x1) * (qy - y1) - (y2 - y1) * (qx - x1)) by ring.
    rewrite Heq. tauto.
Qed.

(** Reflection across a well-formed line is injective *)
Lemma reflect_point_injective : forall l p q,
  line_wf l -> reflect_point p l = reflect_point q l -> p = q.
Proof.
  intros l p q Hwf Heq.
  rewrite <- (reflect_point_involutive p l Hwf).
  rewrite <- (reflect_point_involutive q l Hwf).
  rewrite Heq. reflexivity.
Qed.

(** map_line is the genuine mirror image: p lies on l iff its reflection lies on map_line f l *)
Lemma map_line_correct : forall f l p,
  line_wf l -> line_wf (fold_line f) ->
  (on_line p l <->
   on_line (reflect_point p (fold_line f)) (map_line f l)).
Proof.
  intros f l p Hwfl Hwff.
  pose proof (base_points_on_line l Hwfl) as [Hb1 Hb2].
  pose proof (base_points_distinct l) as Hbne.
  assert (Hml : map_line f l =
                line_through (reflect_point (fst (base_points l)) (fold_line f))
                             (reflect_point (snd (base_points l)) (fold_line f))).
  { unfold map_line, map_point. destruct (base_points l). simpl. reflexivity. }
  rewrite Hml.
  assert (Hrne : reflect_point (fst (base_points l)) (fold_line f)
              <> reflect_point (snd (base_points l)) (fold_line f)).
  { intro Hc. apply Hbne. exact (reflect_point_injective (fold_line f) _ _ Hwff Hc). }
  rewrite (on_line_collinear_general l (fst (base_points l)) (snd (base_points l)) p Hwfl Hb1 Hb2 Hbne).
  rewrite (on_line_line_through_iff_collinear
             (reflect_point (fst (base_points l)) (fold_line f))
             (reflect_point (snd (base_points l)) (fold_line f))
             (reflect_point p (fold_line f)) Hrne).
  exact (reflect_preserves_collinear (fold_line f)
           (fst (base_points l)) (snd (base_points l)) p Hwff).
Qed.


(** Huzita-Hatori origami axioms O1-O7 *)

(** O1: Line through two points *)
Definition fold_O1 (p1 p2 : Point) : Fold :=
  fold_line_ctor (line_through p1 p2).

(** Perpendicular bisector of p₁p₂ *)
Definition perp_bisector (p1 p2 : Point) : Line :=
  let '(x1, y1) := p1 in
  let '(x2, y2) := p2 in
  match Req_EM_T x1 x2 with
  | left Hx =>
      match Req_EM_T y1 y2 with
      | left Hy =>
          {| A := 1; B := 0; C := - x1 |}
      | right Hy =>
          let a := 0 in
          let b := 2 * (y2 - y1) in
          let c := (x1 * x1 + y1 * y1 - x2 * x2 - y2 * y2) in
          {| A := a; B := b; C := c |}
      end
  | right Hx =>
      let a := 2 * (x2 - x1) in
      let b := 2 * (y2 - y1) in
      let c := (x1 * x1 + y1 * y1 - x2 * x2 - y2 * y2) in
      {| A := a; B := b; C := c |}
  end.

(** perp_bisector(p₁,p₂) is well-formed *)
Lemma perp_bisector_wf : forall p1 p2, line_wf (perp_bisector p1 p2).
Proof.
  intros [x1 y1] [x2 y2].
  unfold line_wf, perp_bisector. simpl.
  destruct (Req_EM_T x1 x2) as [Hx | Hx].
  - destruct (Req_EM_T y1 y2) as [Hy | Hy].
    + left. apply R1_neq_R0.
    + right. intro Hb0.
      assert (H: 2 = 0 \/ y2 - y1 = 0) by (apply Rmult_integral; exact Hb0).
      destruct H as [H2 | Hdy]; [lra | apply Hy; lra].
  - left. intro Ha0.
    assert (H: 2 = 0 \/ x2 - x1 = 0) by (apply Rmult_integral; exact Ha0).
    destruct H as [H2 | Hdx]; [lra | apply Hx; lra].
Qed.

(** O2: Fold p₁ onto p₂ *)
Definition fold_O2 (p1 p2 : Point) : Fold :=
  fold_line_ctor (perp_bisector p1 p2).

(** Midpoint of p₁p₂ lies on perpendicular bisector *)
Lemma perp_bisector_midpoint : forall p1 p2,
  on_line (midpoint p1 p2) (perp_bisector p1 p2).
Proof.
  intros [x1 y1] [x2 y2].
  unfold on_line, midpoint, perp_bisector; simpl.
  destruct (Req_EM_T x1 x2) as [Hx|Hx].
  - subst. destruct (Req_EM_T y1 y2) as [Hy|Hy].
    + subst. simpl. field.
    + simpl. field.
  - simpl. field.
Qed.

(** fold_line(fold_O1(p₁,p₂)) = line_through(p₁,p₂) *)
Lemma fold_line_O1 : forall p1 p2, fold_line (fold_O1 p1 p2) = line_through p1 p2.
Proof. reflexivity. Qed.

(** fold_line(fold_O2(p₁,p₂)) = perp_bisector(p₁,p₂) *)
Lemma fold_line_O2 : forall p1 p2, fold_line (fold_O2 p1 p2) = perp_bisector p1 p2.
Proof. reflexivity. Qed.

(** Line through p perpendicular to l *)
Definition perp_through (p : Point) (l : Line) : Line :=
  let '(x, y) := p in
  let c := A l * y - B l * x in
  {| A := B l; B := - A l; C := c |}.

Lemma perp_through_wf : forall p l, line_wf l -> line_wf (perp_through p l).
Proof.
  intros [x y] l Hwf.
  unfold line_wf, perp_through. simpl.
  unfold line_wf in Hwf.
  destruct Hwf as [Ha | Hb].
  - right. intro H. apply Ha. lra.
  - left. exact Hb.
Qed.

(** O4: Fold through p perpendicular to l *)
Definition fold_O4 (p : Point) (l : Line) : Fold :=
  fold_line_ctor (perp_through p l).

Lemma fold_line_O4 : forall p l, fold_line (fold_O4 p l) = perp_through p l.
Proof. reflexivity. Qed.

(** (Ax + By + C) / √(A² + B²), positive on one side of l, negative on other *)
Definition signed_dist (p : Point) (l : Line) : R :=
  let '(x, y) := p in
  (A l * x + B l * y + C l) / line_norm l.

(** signed_dist(p,l) = 0 ⟺ p ∈ l *)
Lemma signed_dist_zero_iff_on_line : forall p l,
  line_wf l -> (signed_dist p l = 0 <-> on_line p l).
Proof.
  intros [x y] l Hwf.
  unfold signed_dist, on_line, line_norm. simpl.
  assert (Hnorm_pos : sqrt (A l * A l + B l * B l) > 0).
  { apply sqrt_lt_R0. destruct Hwf as [Ha | Hb]; nra. }
  split; intro H.
  - unfold Rdiv in H.
    assert (Hinv_nz : / sqrt (sqr (A l) + sqr (B l)) <> 0) by (apply Rinv_neq_0_compat; unfold sqr; lra).
    apply Rmult_integral in H.
    destruct H as [H | H]; [exact H | contradiction].
  - unfold Rdiv. rewrite H. ring.
Qed.

Lemma signed_dist_abs_eq_dist : forall p l,
  line_wf l ->
  Rabs (signed_dist p l) * line_norm l = Rabs (A l * fst p + B l * snd p + C l).
Proof.
  intros [x y] l Hwf.
  unfold signed_dist, line_norm. simpl.
  assert (Hnorm_pos : sqrt (A l * A l + B l * B l) > 0).
  { apply sqrt_lt_R0. destruct Hwf as [Ha | Hb]; nra. }
  unfold Rdiv. rewrite Rabs_mult.
  rewrite Rabs_inv.
  assert (Habs_sqrt : Rabs (sqrt (sqr (A l) + sqr (B l))) = sqrt (sqr (A l) + sqr (B l))).
  { apply Rabs_pos_eq. apply Rlt_le. unfold sqr. exact Hnorm_pos. }
  rewrite Habs_sqrt.
  replace (Rabs (A l * x + B l * y + C l) * / sqrt (sqr (A l) + sqr (B l)) *
           sqrt (sqr (A l) + sqr (B l)))
    with (Rabs (A l * x + B l * y + C l)).
  - reflexivity.
  - field. unfold sqr. lra.
Qed.

(** signed_dist(reflect(p,l), l) = -signed_dist(p,l) *)
Lemma signed_dist_reflect : forall p l,
  line_wf l -> signed_dist (reflect_point p l) l = - signed_dist p l.
Proof.
  intros [x y] l Hwf.
  unfold signed_dist, reflect_point, line_norm.
  simpl.
  set (a := A l); set (b := B l); set (c := C l).
  set (d := a * a + b * b).
  set (v := a * x + b * y + c).
  assert (Hd : d > 0) by (unfold d, a, b; apply line_norm_pos; exact Hwf).
  assert (Hd_ne : d <> 0) by lra.
  assert (Hsqrt_ne : sqrt d <> 0) by (apply Rgt_not_eq, sqrt_lt_R0; exact Hd).
  assert (Hkey : a * (x - 2 * a * (v / d)) + b * (y - 2 * b * (v / d)) + c = - v).
  { unfold v.
    assert (Heq : a * (x - 2 * a * ((a * x + b * y + c) / d)) +
                  b * (y - 2 * b * ((a * x + b * y + c) / d)) + c =
                  (a * x + b * y + c) * (1 - 2 * (a * a + b * b) / d)).
    { field. exact Hd_ne. }
    rewrite Heq. unfold d. field. exact Hd_ne. }
  replace (sqr a + sqr b) with d by (unfold d, sqr; ring).
  rewrite Hkey.
  field. exact Hsqrt_ne.
Qed.

(** Angle bisector of l₁ and l₂ (locus where signed distances equal) *)
Definition bisector (l1 l2 : Line) : Line :=
  let n1 := line_norm l1 in
  let n2 := line_norm l2 in
  let a := A l1 / n1 - A l2 / n2 in
  let b := B l1 / n1 - B l2 / n2 in
  let c := C l1 / n1 - C l2 / n2 in
  match Req_EM_T a 0 with
  | left Ha0 =>
      match Req_EM_T b 0 with
      | left _ => perp_through (line_intersection l1 l2) l1
      | right Hb0 => {| A := a; B := b; C := c |}
      end
  | right Han0 => {| A := a; B := b; C := c |}
  end.

Lemma bisector_wf : forall l1 l2, line_wf l1 -> line_wf (bisector l1 l2).
Proof.
  intros l1 l2 Hwf1.
  unfold bisector.
  destruct (Req_EM_T (A l1 / line_norm l1 - A l2 / line_norm l2) 0) as [Ha0 | Han0].
  - destruct (Req_EM_T (B l1 / line_norm l1 - B l2 / line_norm l2) 0) as [Hb0 | Hbn0].
    + apply perp_through_wf. exact Hwf1.
    + unfold line_wf. simpl. right. exact Hbn0.
  - unfold line_wf. simpl. left. exact Han0.
Qed.

(** O3: Fold l₁ onto l₂ *)
Definition fold_O3 (l1 l2 : Line) : Fold :=
  fold_line_ctor (bisector l1 l2).

Lemma fold_line_O3 : forall l1 l2, fold_line (fold_O3 l1 l2) = bisector l1 l2.
Proof. reflexivity. Qed.

(** p ∈ bisector(l₁,l₂) → signed_dist(p,l₁) = signed_dist(p,l₂) *)
Theorem bisector_equidistant : forall p l1 l2,
  line_wf l1 -> line_wf l2 ->
  A l1 / line_norm l1 - A l2 / line_norm l2 <> 0 \/
  B l1 / line_norm l1 - B l2 / line_norm l2 <> 0 ->
  on_line p (bisector l1 l2) -> signed_dist p l1 = signed_dist p l2.
Proof.
  intros [x y] l1 l2 Hwf1 Hwf2 Hnondeg Hon.
  unfold bisector in Hon.
  destruct (Req_EM_T (A l1 / line_norm l1 - A l2 / line_norm l2) 0) as [Ha0 | Han0].
  - destruct (Req_EM_T (B l1 / line_norm l1 - B l2 / line_norm l2) 0) as [Hb0 | Hbn0].
    + destruct Hnondeg as [Hcontra | Hcontra]; contradiction.
    + unfold on_line in Hon. simpl in Hon.
      unfold signed_dist.
      assert (Hn1 : line_norm l1 <> 0) by (apply line_norm_nonzero; exact Hwf1).
      assert (Hn2 : line_norm l2 <> 0) by (apply line_norm_nonzero; exact Hwf2).
      unfold Rdiv.
      assert (Heq : (A l1 / line_norm l1 - A l2 / line_norm l2) * x +
                    (B l1 / line_norm l1 - B l2 / line_norm l2) * y +
                    (C l1 / line_norm l1 - C l2 / line_norm l2) = 0 ->
                    (A l1 * x + B l1 * y + C l1) * / line_norm l1 =
                    (A l2 * x + B l2 * y + C l2) * / line_norm l2).
      { intro Hzero. unfold Rdiv in Hzero. nra. }
      apply Heq. exact Hon.
  - unfold on_line in Hon. simpl in Hon.
    unfold signed_dist.
    assert (Hn1 : line_norm l1 <> 0) by (apply line_norm_nonzero; exact Hwf1).
    assert (Hn2 : line_norm l2 <> 0) by (apply line_norm_nonzero; exact Hwf2).
    unfold Rdiv.
    assert (Heq : (A l1 / line_norm l1 - A l2 / line_norm l2) * x +
                  (B l1 / line_norm l1 - B l2 / line_norm l2) * y +
                  (C l1 / line_norm l1 - C l2 / line_norm l2) = 0 ->
                  (A l1 * x + B l1 * y + C l1) * / line_norm l1 =
                  (A l2 * x + B l2 * y + C l2) * / line_norm l2).
    { intro Hzero. unfold Rdiv in Hzero. nra. }
    apply Heq. exact Hon.
Qed.

(** signed_dist(p,l₁) = signed_dist(p,l₂) → p ∈ bisector(l₁,l₂) *)
Theorem equidistant_on_bisector : forall p l1 l2,
  line_wf l1 -> line_wf l2 ->
  A l1 / line_norm l1 - A l2 / line_norm l2 <> 0 \/
  B l1 / line_norm l1 - B l2 / line_norm l2 <> 0 ->
  signed_dist p l1 = signed_dist p l2 -> on_line p (bisector l1 l2).
Proof.
  intros [x y] l1 l2 Hwf1 Hwf2 Hnondeg Hdist.
  unfold bisector.
  destruct (Req_EM_T (A l1 / line_norm l1 - A l2 / line_norm l2) 0) as [Ha0 | Han0].
  - destruct (Req_EM_T (B l1 / line_norm l1 - B l2 / line_norm l2) 0) as [Hb0 | Hbn0].
    + destruct Hnondeg as [Hcontra | Hcontra]; contradiction.
    + unfold on_line. simpl.
      unfold signed_dist in Hdist.
      assert (Hn1 : line_norm l1 <> 0) by (apply line_norm_nonzero; exact Hwf1).
      assert (Hn2 : line_norm l2 <> 0) by (apply line_norm_nonzero; exact Hwf2).
      unfold Rdiv in Hdist.
      assert (Heq : (A l1 * x + B l1 * y + C l1) * / line_norm l1 =
                    (A l2 * x + B l2 * y + C l2) * / line_norm l2) by exact Hdist.
      unfold Rdiv. nra.
  - unfold on_line. simpl.
    unfold signed_dist in Hdist.
    assert (Hn1 : line_norm l1 <> 0) by (apply line_norm_nonzero; exact Hwf1).
    assert (Hn2 : line_norm l2 <> 0) by (apply line_norm_nonzero; exact Hwf2).
    unfold Rdiv in Hdist.
    assert (Heq : (A l1 * x + B l1 * y + C l1) * / line_norm l1 =
                  (A l2 * x + B l2 * y + C l2) * / line_norm l2) by exact Hdist.
    unfold Rdiv. nra.
Qed.

(** l₁ ∩ l₂ ∈ bisector(l₁,l₂) when l₁ ∦ l₂ *)
Lemma bisector_through_intersection : forall l1 l2,
  line_wf l1 -> line_wf l2 ->
  A l1 * B l2 - A l2 * B l1 <> 0 ->
  on_line (line_intersection l1 l2) (bisector l1 l2).
Proof.
  intros l1 l2 Hwf1 Hwf2 Hnonpar.
  apply equidistant_on_bisector; try assumption.
  - assert (Hn1_sq : A l1 * A l1 + B l1 * B l1 > 0) by (apply line_norm_pos; exact Hwf1).
    assert (Hn2_sq : A l2 * A l2 + B l2 * B l2 > 0) by (apply line_norm_pos; exact Hwf2).
    assert (Hn1 : line_norm l1 > 0) by (unfold line_norm; apply sqrt_lt_R0; exact Hn1_sq).
    assert (Hn2 : line_norm l2 > 0) by (unfold line_norm; apply sqrt_lt_R0; exact Hn2_sq).
    destruct (Req_dec (A l1 / line_norm l1 - A l2 / line_norm l2) 0) as [Ha0|Han0].
    + right. intro Hb0.
      assert (Ha_prop : A l1 / line_norm l1 = A l2 / line_norm l2) by lra.
      assert (Hb_prop : B l1 / line_norm l1 = B l2 / line_norm l2) by lra.
      assert (Hdet : A l1 * B l2 - A l2 * B l1 = 0).
      { assert (Ha1 : A l1 = (A l2 / line_norm l2) * line_norm l1).
        { rewrite <- Ha_prop. field. lra. }
        assert (Hb1 : B l1 = (B l2 / line_norm l2) * line_norm l1).
        { rewrite <- Hb_prop. field. lra. }
        rewrite Ha1, Hb1. field. lra. }
      contradiction.
    + left. exact Han0.
  - unfold signed_dist.
    assert (Hn1 : line_norm l1 <> 0) by (apply line_norm_nonzero; exact Hwf1).
    assert (Hn2 : line_norm l2 <> 0) by (apply line_norm_nonzero; exact Hwf2).
    unfold line_intersection.
    destruct (Req_EM_T (A l1 * B l2 - A l2 * B l1) 0) as [Heq|Hneq]; [contradiction|].
    simpl. field. repeat split; assumption.
Qed.

(** p ∈ bisector(l₁,l₂) → |signed_dist(p,l₁)| = |signed_dist(p,l₂)| *)
Lemma bisector_abs_equidistant : forall p l1 l2,
  line_wf l1 -> line_wf l2 ->
  A l1 / line_norm l1 - A l2 / line_norm l2 <> 0 \/
  B l1 / line_norm l1 - B l2 / line_norm l2 <> 0 ->
  on_line p (bisector l1 l2) ->
  Rabs (signed_dist p l1) = Rabs (signed_dist p l2).
Proof.
  intros p l1 l2 Hwf1 Hwf2 Hnondeg Hon.
  rewrite (bisector_equidistant p l1 l2 Hwf1 Hwf2 Hnondeg Hon).
  reflexivity.
Qed.

Lemma fold_O3_wf : forall l1 l2,
  line_wf l1 -> line_wf (fold_line (fold_O3 l1 l2)).
Proof.
  intros l1 l2 Hwf1.
  rewrite fold_line_O3.
  apply bisector_wf. exact Hwf1.
Qed.

(** p ∈ bisector(l₁,l₂) ⟺ p ∈ bisector(l₂,l₁) *)
Lemma bisector_symmetric : forall p l1 l2,
  line_wf l1 -> line_wf l2 ->
  A l1 / line_norm l1 - A l2 / line_norm l2 <> 0 \/
  B l1 / line_norm l1 - B l2 / line_norm l2 <> 0 ->
  on_line p (bisector l1 l2) <-> on_line p (bisector l2 l1).
Proof.
  intros [x y] l1 l2 Hwf1 Hwf2 Hnondeg.
  unfold bisector.
  assert (Hn1 : line_norm l1 <> 0) by (apply line_norm_nonzero; exact Hwf1).
  assert (Hn2 : line_norm l2 <> 0) by (apply line_norm_nonzero; exact Hwf2).
  destruct (Req_EM_T (A l1 / line_norm l1 - A l2 / line_norm l2) 0) as [Ha12|Ha12].
  - destruct (Req_EM_T (B l1 / line_norm l1 - B l2 / line_norm l2) 0) as [Hb12|Hb12].
    + destruct Hnondeg; contradiction.
    + destruct (Req_EM_T (A l2 / line_norm l2 - A l1 / line_norm l1) 0) as [Ha21|Ha21].
      * destruct (Req_EM_T (B l2 / line_norm l2 - B l1 / line_norm l1) 0) as [Hb21|Hb21].
        { exfalso. lra. }
        { unfold on_line. simpl. split; intro H; lra. }
      * exfalso. lra.
  - destruct (Req_EM_T (A l2 / line_norm l2 - A l1 / line_norm l1) 0) as [Ha21|Ha21].
    + exfalso. lra.
    + unfold on_line. simpl. split; intro H; lra.
Qed.

(** Parallel lines: bisector degenerates to perpendicular through intersection *)
Lemma bisector_parallel_case : forall l1 l2,
  line_wf l1 ->
  A l1 / line_norm l1 - A l2 / line_norm l2 = 0 ->
  B l1 / line_norm l1 - B l2 / line_norm l2 = 0 ->
  bisector l1 l2 = perp_through (line_intersection l1 l2) l1.
Proof.
  intros l1 l2 Hwf1 Ha0 Hb0.
  unfold bisector.
  destruct (Req_EM_T (A l1 / line_norm l1 - A l2 / line_norm l2) 0) as [Ha|Ha].
  - destruct (Req_EM_T (B l1 / line_norm l1 - B l2 / line_norm l2) 0) as [Hb|Hb].
    + reflexivity.
    + contradiction.
  - contradiction.
Qed.

(** Second angle bisector (perpendicular to first), via sum of normalized equations *)
Definition bisector2 (l1 l2 : Line) : Line :=
  let n1 := line_norm l1 in
  let n2 := line_norm l2 in
  let a := A l1 / n1 + A l2 / n2 in
  let b := B l1 / n1 + B l2 / n2 in
  let c := C l1 / n1 + C l2 / n2 in
  {| A := a; B := b; C := c |}.

(** bisector(l₁,l₂) ⊥ bisector2(l₁,l₂) *)
Lemma bisector_bisector2_perp : forall l1 l2,
  line_wf l1 -> line_wf l2 ->
  A l1 / line_norm l1 - A l2 / line_norm l2 <> 0 \/
  B l1 / line_norm l1 - B l2 / line_norm l2 <> 0 ->
  line_perp (bisector l1 l2) (bisector2 l1 l2).
Proof.
  intros l1 l2 Hwf1 Hwf2 Hnondeg.
  unfold bisector, bisector2, line_perp.
  assert (Hn1 : line_norm l1 <> 0) by (apply line_norm_nonzero; exact Hwf1).
  assert (Hn2 : line_norm l2 <> 0) by (apply line_norm_nonzero; exact Hwf2).
  assert (Hn1_pos : A l1 * A l1 + B l1 * B l1 > 0) by (apply line_norm_pos; exact Hwf1).
  assert (Hn2_pos : A l2 * A l2 + B l2 * B l2 > 0) by (apply line_norm_pos; exact Hwf2).
  assert (Hsq1 : line_norm l1 * line_norm l1 = A l1 * A l1 + B l1 * B l1).
  { unfold line_norm. apply sqrt_sqrt. lra. }
  assert (Hsq2 : line_norm l2 * line_norm l2 = A l2 * A l2 + B l2 * B l2).
  { unfold line_norm. apply sqrt_sqrt. lra. }
  destruct (Req_EM_T (A l1 / line_norm l1 - A l2 / line_norm l2) 0) as [Ha0|Ha0].
  - destruct (Req_EM_T (B l1 / line_norm l1 - B l2 / line_norm l2) 0) as [Hb0|Hb0].
    + destruct Hnondeg; contradiction.
    + simpl.
      assert (H1 : A l1 * A l1 + B l1 * B l1 = line_norm l1 * line_norm l1) by lra.
      assert (H2 : A l2 * A l2 + B l2 * B l2 = line_norm l2 * line_norm l2) by lra.
      assert (Hdot : (A l1 / line_norm l1 - A l2 / line_norm l2) *
                     (A l1 / line_norm l1 + A l2 / line_norm l2) +
                     (B l1 / line_norm l1 - B l2 / line_norm l2) *
                     (B l1 / line_norm l1 + B l2 / line_norm l2) =
                     (A l1 * A l1 + B l1 * B l1) / (line_norm l1 * line_norm l1) -
                     (A l2 * A l2 + B l2 * B l2) / (line_norm l2 * line_norm l2)).
      { field. split; assumption. }
      rewrite Hdot, H1, H2. field. split; assumption.
  - simpl.
    assert (H1 : A l1 * A l1 + B l1 * B l1 = line_norm l1 * line_norm l1) by lra.
    assert (H2 : A l2 * A l2 + B l2 * B l2 = line_norm l2 * line_norm l2) by lra.
    assert (Hdot : (A l1 / line_norm l1 - A l2 / line_norm l2) *
                   (A l1 / line_norm l1 + A l2 / line_norm l2) +
                   (B l1 / line_norm l1 - B l2 / line_norm l2) *
                   (B l1 / line_norm l1 + B l2 / line_norm l2) =
                   (A l1 * A l1 + B l1 * B l1) / (line_norm l1 * line_norm l1) -
                   (A l2 * A l2 + B l2 * B l2) / (line_norm l2 * line_norm l2)).
    { field. split; assumption. }
    rewrite Hdot, H1, H2. field. split; assumption.
Qed.

(** reflect(l₁∩l₂, bisector) = l₁∩l₂ *)
Lemma bisector_reflect_intersection_fixed : forall l1 l2,
  line_wf l1 -> line_wf l2 ->
  A l1 * B l2 - A l2 * B l1 <> 0 ->
  A l1 / line_norm l1 - A l2 / line_norm l2 <> 0 \/
  B l1 / line_norm l1 - B l2 / line_norm l2 <> 0 ->
  line_wf (bisector l1 l2) ->
  reflect_point (line_intersection l1 l2) (bisector l1 l2) = line_intersection l1 l2.
Proof.
  intros l1 l2 Hwf1 Hwf2 Hnonpar Hnondeg Hwfb.
  apply reflect_point_on_line.
  apply bisector_through_intersection; assumption.
Qed.

(** cos(angle between l₁ and l₂) via dot product of unit normals *)
Definition line_cos_angle (l1 l2 : Line) : R :=
  (A l1 / line_norm l1) * (A l2 / line_norm l2) +
  (B l1 / line_norm l1) * (B l2 / line_norm l2).

(** line_cos_angle(l₁,l₂) = line_cos_angle(l₂,l₁) *)
Lemma line_cos_angle_sym : forall l1 l2,
  line_cos_angle l1 l2 = line_cos_angle l2 l1.
Proof.
  intros l1 l2. unfold line_cos_angle. ring.
Qed.

(** cos(angle(x-axis, y-axis)) = 0 *)
Lemma perpendicular_axes_angle :
  line_cos_angle line_xaxis line_yaxis = 0.
Proof.
  unfold line_cos_angle, line_xaxis, line_yaxis, line_norm. simpl.
  assert (H1 : sqrt 1 = 1) by exact sqrt_1.
  assert (H2 : 1 <> 0) by lra.
  lra.
Qed.

Lemma bisector_axes_wf :
  line_wf (bisector line_xaxis line_yaxis).
Proof.
  apply bisector_wf.
  unfold line_wf, line_xaxis. simpl. right. lra.
Qed.

(** ∀ well-formed l₁, ∃ fold with crease = bisector(l₁,l₂) *)
Theorem O3_always_solvable : forall l1 l2,
  line_wf l1 ->
  exists f, fold_line f = bisector l1 l2 /\ line_wf (fold_line f).
Proof.
  intros l1 l2 Hwf1.
  exists (fold_O3 l1 l2).
  split.
  - apply fold_line_O3.
  - apply fold_O3_wf. exact Hwf1.
Qed.

(** reflect(l₁∩l₂, bisector(l₁,l₂)) = l₁∩l₂ *)
Theorem O3_preserves_intersection : forall l1 l2,
  line_wf l1 -> line_wf l2 ->
  A l1 * B l2 - A l2 * B l1 <> 0 ->
  line_wf (bisector l1 l2) ->
  reflect_point (line_intersection l1 l2) (bisector l1 l2) = line_intersection l1 l2.
Proof.
  intros l1 l2 Hwf1 Hwf2 Hnonpar Hwfb.
  apply reflect_point_on_line.
  assert (Hnondeg : A l1 / line_norm l1 - A l2 / line_norm l2 <> 0 \/
                    B l1 / line_norm l1 - B l2 / line_norm l2 <> 0).
  { assert (Hn1_sq : A l1 * A l1 + B l1 * B l1 > 0) by (apply line_norm_pos; exact Hwf1).
    assert (Hn2_sq : A l2 * A l2 + B l2 * B l2 > 0) by (apply line_norm_pos; exact Hwf2).
    assert (Hn1 : line_norm l1 > 0) by (unfold line_norm; apply sqrt_lt_R0; exact Hn1_sq).
    assert (Hn2 : line_norm l2 > 0) by (unfold line_norm; apply sqrt_lt_R0; exact Hn2_sq).
    destruct (Req_dec (A l1 / line_norm l1 - A l2 / line_norm l2) 0) as [Ha0|Ha0].
    - right. intro Hb0.
      assert (Ha_eq : A l1 / line_norm l1 = A l2 / line_norm l2) by lra.
      assert (Hb_eq : B l1 / line_norm l1 = B l2 / line_norm l2) by lra.
      assert (Hcross : A l1 * B l2 - A l2 * B l1 =
                       line_norm l1 * line_norm l2 * (A l1 / line_norm l1 * (B l2 / line_norm l2) -
                                                      A l2 / line_norm l2 * (B l1 / line_norm l1))).
      { field. split; lra. }
      rewrite Ha_eq, Hb_eq in Hcross.
      assert (Hzero : A l1 * B l2 - A l2 * B l1 = 0).
      { rewrite Hcross. ring. }
      lra.
    - left. exact Ha0. }
  apply bisector_through_intersection; assumption.
Qed.

(** ∀ p, l well-formed, ∃ fold through p perpendicular to l *)
Theorem O4_always_solvable : forall p l,
  line_wf l ->
  exists f, fold_line f = perp_through p l /\ line_wf (fold_line f).
Proof.
  intros p l Hwf.
  exists (fold_O4 p l).
  split.
  - apply fold_line_O4.
  - rewrite fold_line_O4. apply perp_through_wf. exact Hwf.
Qed.

(** fold_O4(p,l) ⊥ l *)
Theorem O4_perpendicular : forall p l,
  line_wf l ->
  line_perp (fold_line (fold_O4 p l)) l.
Proof.
  intros [px py] l Hwf.
  rewrite fold_line_O4.
  unfold line_perp, perp_through. simpl.
  ring.
Qed.

(** p ∈ fold_O4(p,l) *)
Theorem O4_through_point : forall p l,
  on_line p (fold_line (fold_O4 p l)).
Proof.
  intros [px py] l.
  rewrite fold_line_O4.
  unfold on_line, perp_through. simpl.
  ring.
Qed.

(** O5: Fold through p₂ placing p₁ onto l *)
Definition fold_O5 (p1 : Point) (l : Line) (p2 : Point) : Fold :=
  let proj := foot_on_line p1 l in
  let aux_line := line_through p1 proj in
  fold_line_ctor (perp_through p2 aux_line).

Lemma fold_line_O5 : forall p1 l p2, fold_line (fold_O5 p1 l p2) = perp_through p2 (line_through p1 (foot_on_line p1 l)).
Proof. reflexivity. Qed.

(** y-coordinate of p reflected onto vertical line x=c through q *)
Definition O5_vert_image_y (p q : Point) (c : R) : R :=
  let d2 := (fst p - fst q)^2 + (snd p - snd q)^2 in
  let dx2 := (c - fst q)^2 in
  snd q + sqrt (d2 - dx2).

(** (c, O5_vert_image_y p q c) *)
Definition O5_vert_image (p q : Point) (c : R) : Point :=
  (c, O5_vert_image_y p q c).

(** O5 fold for vertical target line x = c *)
Definition fold_O5_vert (p q : Point) (c : R) : Fold :=
  fold_line_ctor (perp_bisector p (O5_vert_image p q c)).

(** √(4x) = 2√x *)
Lemma O5_vert_image_sqrt_case : forall x,
  0 < x ->
  O5_vert_image (0, 0) (1 + x, 0) 2 = (2, 2 * sqrt x).
Proof.
  intros x Hpos.
  unfold O5_vert_image, O5_vert_image_y. simpl.
  f_equal.
  replace ((0 - (1 + x)) * ((0 - (1 + x)) * 1) + (0 - 0) * ((0 - 0) * 1))
    with ((1 + x) ^ 2) by ring.
  replace ((2 - (1 + x)) * ((2 - (1 + x)) * 1)) with ((1 - x) ^ 2) by ring.
  replace ((1 + x) ^ 2 - (1 - x) ^ 2) with (4 * x) by ring.
  rewrite sqrt_4x_eq by lra.
  ring.
Qed.

(** O6 (Beloch fold) solves t³ + pt + q = 0 via parabola tangent construction *)

(** (0, 1): focus of reference parabola y = x²/4 *)
Definition beloch_P1 : Point := (0, 1).

(** y = -1 (directrix of reference parabola) *)
Definition beloch_L1 : Line := {| A := 0; B := 1; C := 1 |}.

(** (q, p) *)
Definition beloch_P2 (p q : R) : Point := (q, p).

(** x = -q *)
Definition beloch_L2 (q : R) : Line := {| A := 1; B := 0; C := q |}.

(** tx - y - t² = 0 (tangent to parabola at slope t) *)
Definition beloch_fold_line (t : R) : Line := {| A := t; B := -1; C := -(t*t) |}.

Definition fold_O6_beloch (p q t : R) : Fold :=
  fold_line_ctor (beloch_fold_line t).

Lemma beloch_L1_wf : line_wf beloch_L1.
Proof. unfold line_wf, beloch_L1; simpl; right; lra. Qed.

Lemma beloch_L2_wf : forall q, line_wf (beloch_L2 q).
Proof. intro q; unfold line_wf, beloch_L2; simpl; left; lra. Qed.

Lemma beloch_fold_line_wf : forall t, line_wf (beloch_fold_line t).
Proof. intro t; unfold line_wf, beloch_fold_line; simpl; right; lra. Qed.

(** reflect(P₁, beloch_fold_line(t)) ∈ L₁ *)
Lemma beloch_P1_reflects_to_L1 : forall t,
  on_line (reflect_point beloch_P1 (beloch_fold_line t)) beloch_L1.
Proof.
  intro t.
  unfold reflect_point, beloch_P1, beloch_fold_line, on_line, beloch_L1; simpl.
  assert (Ht2 : 0 <= t * t) by apply Rle_0_sqr.
  assert (Hd_nz : t * t + (-1) * (-1) <> 0) by lra.
  field_simplify; [|lra].
  lra.
Qed.

(** t³ + pt + q = 0 → reflect(P₂, beloch_fold_line(t)) ∈ L₂ *)
Lemma beloch_P2_reflects_to_L2 : forall p q t,
  t * t * t + p * t + q = 0 ->
  on_line (reflect_point (beloch_P2 p q) (beloch_fold_line t)) (beloch_L2 q).
Proof.
  intros p q t Hcubic.
  unfold reflect_point, beloch_P2, beloch_fold_line, on_line, beloch_L2; simpl.
  assert (Ht2 : 0 <= t * t) by apply Rle_0_sqr.
  assert (Hd_nz : t * t + (-1) * (-1) <> 0) by lra.
  field_simplify; [|lra].
  nra.
Qed.

(** O6 constraint: reflect(p₁,f) ∈ l₁ ∧ reflect(p₂,f) ∈ l₂ *)
Definition satisfies_O6_constraint (f : Fold) (p1 : Point) (l1 : Line) (p2 : Point) (l2 : Line) : Prop :=
  let crease := fold_line f in
  on_line (reflect_point p1 crease) l1 /\ on_line (reflect_point p2 crease) l2.

Definition satisfies_O6_line_constraint (crease : Line) (p1 : Point) (l1 : Line) (p2 : Point) (l2 : Line) : Prop :=
  on_line (reflect_point p1 crease) l1 /\ on_line (reflect_point p2 crease) l2.

Lemma O6_line_to_fold_constraint : forall crease p1 l1 p2 l2,
  satisfies_O6_line_constraint crease p1 l1 p2 l2 ->
  satisfies_O6_constraint (fold_line_ctor crease) p1 l1 p2 l2.
Proof.
  intros crease p1 l1 p2 l2 H.
  unfold satisfies_O6_constraint, fold_line; simpl.
  exact H.
Qed.

(** t³ + pt + q = 0 → beloch_fold satisfies O6 *)
Theorem beloch_fold_satisfies_O6 : forall p q t,
  t * t * t + p * t + q = 0 ->
  satisfies_O6_constraint (fold_O6_beloch p q t) beloch_P1 beloch_L1 (beloch_P2 p q) (beloch_L2 q).
Proof.
  intros p q t Hcubic.
  unfold satisfies_O6_constraint, fold_O6_beloch, fold_line; simpl.
  split.
  - apply beloch_P1_reflects_to_L1.
  - apply beloch_P2_reflects_to_L2. exact Hcubic.
Qed.

(** p₁,p₂ ∈ l ∧ p₁ ≠ p₂ → perp_bisector(p₁,p₂) ⊥ l *)
Lemma perp_bisector_perp_to_connecting_line : forall p1 p2 l,
  on_line p1 l -> on_line p2 l -> p1 <> p2 ->
  line_perp (perp_bisector p1 p2) l.
Proof.
  intros [x1 y1] [x2 y2] l Hp1 Hp2 Hneq.
  unfold line_perp, perp_bisector, on_line in *.
  simpl in *.
  destruct (Req_EM_T x1 x2) as [Hx|Hx].
  - subst. destruct (Req_EM_T y1 y2) as [Hy|Hy].
    + subst. exfalso. apply Hneq. reflexivity.
    + simpl.
      assert (Hdiff: B l * (y1 - y2) = 0) by lra.
      destruct (Req_EM_T (B l) 0) as [HB|HB].
      * rewrite HB. ring.
      * assert (Hy12: y1 = y2) by nra. contradiction.
  - simpl.
    assert (Hline: A l * (x1 - x2) + B l * (y1 - y2) = 0) by lra.
    lra.
Qed.

(** l₁ ⊥ l₂ → l₂ ⊥ l₁ *)
Lemma line_perp_comm : forall l1 l2,
  line_perp l1 l2 -> line_perp l2 l1.
Proof.
  intros l1 l2 H.
  unfold line_perp in *.
  lra.
Qed.

(** perp_through(p,l) ⊥ l *)
Lemma perp_through_perp : forall p l,
  line_perp (perp_through p l) l.
Proof.
  intros [x y] l.
  unfold line_perp, perp_through.
  destruct (Req_EM_T (A l) 0); simpl; ring.
Qed.


(** Line through p parallel to l *)
Definition parallel_line_through (p : Point) (l : Line) : Line :=
  {| A := A l; B := B l; C := - A l * (fst p) - B l * (snd p) |}.

Lemma parallel_line_through_wf : forall p l, line_wf l -> line_wf (parallel_line_through p l).
Proof.
  intros p l Hwf.
  unfold line_wf, parallel_line_through. simpl.
  exact Hwf.
Qed.

(** parallel_line_through(p,l) ∥ l *)
Lemma parallel_line_through_parallel : forall p l,
  line_parallel (parallel_line_through p l) l.
Proof.
  intros p l.
  unfold line_parallel, parallel_line_through. simpl.
  ring.
Qed.

(** p ∈ parallel_line_through(p,l) *)
Lemma parallel_line_through_incident : forall p l,
  on_line p (parallel_line_through p l).
Proof.
  intros [x y] l.
  unfold on_line, parallel_line_through.
  destruct l as [a b c]; simpl.
  ring.
Qed.

(** l₁ ⊥ l₂ ⟺ A₁A₂ + B₁B₂ = 0 *)
Lemma perp_to_line_perp : forall l1 l2,
  line_perp l1 l2 <-> A l1 * A l2 + B l1 * B l2 = 0.
Proof.
  intros l1 l2.
  unfold line_perp. split; intro H; exact H.
Qed.

(** Alias for perp_through *)
Definition construct_perp_line_at (p : Point) (l : Line) : Line :=
  perp_through p l.

Lemma construct_perp_line_at_perp : forall p l,
  line_perp (construct_perp_line_at p l) l.
Proof.
  intros p l.
  unfold construct_perp_line_at.
  apply perp_through_perp.
Qed.

Lemma construct_perp_line_at_incident : forall p l,
  on_line p (construct_perp_line_at p l).
Proof.
  intros [x y] l.
  unfold construct_perp_line_at, on_line, perp_through.
  destruct (Req_EM_T (A l) 0); simpl; ring.
Qed.

(** p₁ ≠ p₂ → reflect(p₁, perp_bisector(p₁,p₂)) = p₂ *)
Lemma perp_bisector_reflects_to_other : forall p1 p2,
  p1 <> p2 -> reflect_point p1 (perp_bisector p1 p2) = p2.
Proof.
  intros p1 p2 Hneq.
  destruct p1 as [x1 y1], p2 as [x2 y2].
  unfold reflect_point, perp_bisector.
  destruct (Req_EM_T x1 x2) as [Hx|Hx].
  + subst. destruct (Req_EM_T y1 y2) as [Hy|Hy].
    * subst. exfalso. apply Hneq. reflexivity.
    * simpl. f_equal; field; intro H; apply Hy; lra.
  + simpl. assert (Hden: 2 * (x2 - x1) * (2 * (x2 - x1)) + 2 * (y2 - y1) * (2 * (y2 - y1)) <> 0).
    { intro Heq.
      assert (H0: (x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1) = 0) by lra.
      assert (Hx2: 0 <= (x2 - x1) * (x2 - x1)) by apply Rle_0_sqr.
      assert (Hy2: 0 <= (y2 - y1) * (y2 - y1)) by apply Rle_0_sqr.
      assert (Hxz: (x2 - x1) * (x2 - x1) = 0) by lra.
      assert (Hyz: (y2 - y1) * (y2 - y1) = 0) by lra.
      apply Rmult_integral in Hxz.
      apply Rmult_integral in Hyz.
      destruct Hxz as [Hx0|Hx0]; destruct Hyz as [Hy0|Hy0]; lra. }
    f_equal; field; assumption.
Qed.

(** p ∈ l → reflect(p,l) = p *)
Lemma reflect_point_on_line_stays : forall p l,
  on_line p l -> reflect_point p l = p.
Proof.
  intros p l Hp.
  apply reflect_point_on_line.
  exact Hp.
Qed.


(** l₁ ⊥ l₂ → l₂ ⊥ l₁ *)
Theorem perpendicularity_symmetric : forall l1 l2,
  line_perp l1 l2 -> line_perp l2 l1.
Proof.
  intros l1 l2 H.
  apply line_perp_comm.
  exact H.
Qed.

(** l₁ ∥ l₂ → l₂ ∥ l₁ *)
Theorem parallel_is_symmetric : forall l1 l2,
  line_parallel l1 l2 -> line_parallel l2 l1.
Proof.
  intros l1 l2 H.
  unfold line_parallel in *.
  lra.
Qed.

(** p ∈ parallel_line_through(p,l) *)
Theorem point_on_parallel_line : forall p l,
  on_line p (parallel_line_through p l).
Proof.
  intros p l.
  apply parallel_line_through_incident.
Qed.

(** parallel_line_through(p,l) ∥ l *)
Theorem constructed_line_is_parallel : forall p l,
  line_parallel (parallel_line_through p l) l.
Proof.
  intros p l.
  apply parallel_line_through_parallel.
Qed.

(** construct_perp_line_at(p,l) ⊥ l ∧ p ∈ construct_perp_line_at(p,l) *)
Theorem perpendicular_construction_works : forall p l,
  line_perp (construct_perp_line_at p l) l /\
  on_line p (construct_perp_line_at p l).
Proof.
  intros p l.
  split.
  - apply construct_perp_line_at_perp.
  - apply construct_perp_line_at_incident.
Qed.

(** l₁ ∦ l₂ → l₁ ∩ l₂ ∈ l₁ ∧ l₁ ∩ l₂ ∈ l₂ *)
Theorem line_intersection_on_both_lines : forall l1 l2,
  A l1 * B l2 - A l2 * B l1 <> 0 ->
  on_line (line_intersection l1 l2) l1 /\
  on_line (line_intersection l1 l2) l2.
Proof.
  intros l1 l2 Hnonpar.
  split.
  - unfold line_intersection, on_line.
    destruct (Req_EM_T (A l1 * B l2 - A l2 * B l1) 0) as [Heq|Hneq]; [contradiction|].
    simpl. field. exact Hneq.
  - unfold line_intersection, on_line.
    destruct (Req_EM_T (A l1 * B l2 - A l2 * B l1) 0) as [Heq|Hneq]; [contradiction|].
    simpl. field. exact Hneq.
Qed.


(** dist²(p₁,p₂) = dist²(reflect(p₁,l), reflect(p₂,l)) *)
Theorem reflection_is_isometry : forall p1 p2 l,
  line_wf l -> dist2 p1 p2 = dist2 (reflect_point p1 l) (reflect_point p2 l).
Proof.
  intros [x1 y1] [x2 y2] l Hwf.
  unfold dist2, reflect_point, sqr.
  destruct l as [a b c]; simpl.
  set (d1 := a * x1 + b * y1 + c).
  set (d2 := a * x2 + b * y2 + c).
  set (n := a * a + b * b).
  unfold line_wf in Hwf. simpl in Hwf.
  destruct Hwf as [Ha|Hb]; assert (Hn: n <> 0) by (unfold n; nra);
  unfold d1, d2, n; field; exact Hn.
Qed.

(** foot(p,l) ∈ l *)
Theorem foot_on_line_minimizes_distance : forall p l,
  line_wf l -> on_line (foot_on_line p l) l.
Proof.
  intros p l Hwf.
  apply foot_on_line_incident. exact Hwf.
Qed.

(** ∃ fold through p₁ and p₂ *)
Theorem origami_axiom_O1_always_exists : forall p1 p2,
  exists f, on_line p1 (fold_line f) /\ on_line p2 (fold_line f).
Proof.
  intros p1 p2.
  exists (fold_line_ctor (line_through p1 p2)).
  split; unfold fold_line; simpl.
  - apply line_through_on_line_fst.
  - apply line_through_on_line_snd.
Qed.

(** ∃ fold mapping p₁ to p₂ *)
Theorem origami_axiom_O2_always_exists : forall p1 p2,
  exists f, reflect_point p1 (fold_line f) = p2.
Proof.
  intros p1 p2.
  exists (fold_line_ctor (perp_bisector p1 p2)).
  unfold fold_line; simpl.
  destruct (point_eq_dec p1 p2) as [Heq|Hneq].
  - subst. apply reflect_point_on_line_stays.
    destruct p2 as [x y].
    unfold on_line, perp_bisector. simpl.
    destruct (Req_EM_T x x); [|contradiction].
    destruct (Req_EM_T y y); simpl; ring.
  - apply perp_bisector_reflects_to_other.
    exact Hneq.
Qed.


(** l₁ ∦ l₂ → l₁ ∩ l₂ ∈ l₂ *)
Lemma line_intersection_on_line_snd : forall l1 l2,
  A l1 * B l2 - A l2 * B l1 <> 0 ->
  on_line (line_intersection l1 l2) l2.
Proof.
  intros l1 l2 HD.
  unfold line_intersection, on_line.
  destruct (Req_EM_T (A l1 * B l2 - A l2 * B l1) 0) as [Heq|Hneq]; [contradiction|].
  simpl. field. exact Hneq.
Qed.




(** O6 constraint ⟹ map_point(f,pᵢ) ∈ lᵢ *)
Lemma O6_constraint_verification : forall f p1 l1 p2 l2,
  satisfies_O6_constraint f p1 l1 p2 l2 ->
  on_line (map_point f p1) l1 /\ on_line (map_point f p2) l2.
Proof.
  intros f p1 l1 p2 l2 [H1 H2].
  unfold map_point, satisfies_O6_constraint in *.
  split; assumption.
Qed.

(** O6 approximation via midpoints of point-to-projection segments *)
Definition fold_O6_approx (p1 : Point) (l1 : Line) (p2 : Point) (l2 : Line) : Fold :=
  let proj1 := foot_on_line p1 l1 in
  let proj2 := foot_on_line p2 l2 in
  let mid1 := midpoint p1 proj1 in
  let mid2 := midpoint p2 proj2 in
  fold_line_ctor (line_through mid1 mid2).

Lemma on_line_preserved_by_eq : forall p1 p2 l,
  p1 = p2 -> on_line p1 l -> on_line p2 l.
Proof.
  intros p1 p2 l Heq H.
  rewrite <- Heq. exact H.
Qed.

Lemma fold_O6_approx_on_midpoint1 : forall p1 l1 p2 l2,
  on_line (midpoint p1 (foot_on_line p1 l1)) (fold_line (fold_O6_approx p1 l1 p2 l2)).
Proof.
  intros p1 l1 p2 l2.
  unfold fold_O6_approx, fold_line; simpl.
  apply line_through_on_line_fst.
Qed.

Lemma fold_O6_approx_on_midpoint2 : forall p1 l1 p2 l2,
  on_line (midpoint p2 (foot_on_line p2 l2)) (fold_line (fold_O6_approx p1 l1 p2 l2)).
Proof.
  intros p1 l1 p2 l2.
  unfold fold_O6_approx, fold_line; simpl.
  apply line_through_on_line_snd.
Qed.

(** p₁ ∈ l₁ ∧ p₂ ∈ l₂ → fold_O6_approx satisfies O6 *)
Lemma fold_O6_approx_satisfies_when_on_lines : forall p1 l1 p2 l2,
  on_line p1 l1 -> on_line p2 l2 ->
  satisfies_O6_constraint (fold_O6_approx p1 l1 p2 l2) p1 l1 p2 l2.
Proof.
  intros p1 l1 p2 l2 H1 H2.
  unfold satisfies_O6_constraint, fold_O6_approx, fold_line; simpl.
  split.
  - assert (Hfoot1: foot_on_line p1 l1 = p1).
    { destruct p1 as [x y].
      unfold foot_on_line, on_line in *.
      simpl in *.
      rewrite H1.
      simpl.
      repeat rewrite Rdiv_0_l.
      repeat rewrite Rmult_0_r.
      repeat rewrite Rminus_0_r.
      reflexivity. }
    rewrite Hfoot1.
    assert (Hmid1: midpoint p1 p1 = p1).
    { destruct p1 as [x y].
      unfold midpoint.
      simpl.
      f_equal; field. }
    rewrite Hmid1.
    assert (Hrefl: reflect_point p1 (line_through p1 (midpoint p2 (foot_on_line p2 l2))) = p1).
    { apply reflect_point_on_line.
      apply line_through_on_line_fst. }
    rewrite Hrefl.
    exact H1.
  - assert (Hfoot2: foot_on_line p2 l2 = p2).
    { destruct p2 as [x y].
      unfold foot_on_line, on_line in *.
      simpl in *.
      rewrite H2.
      simpl.
      repeat rewrite Rdiv_0_l.
      repeat rewrite Rmult_0_r.
      repeat rewrite Rminus_0_r.
      reflexivity. }
    rewrite Hfoot2.
    assert (Hmid2: midpoint p2 p2 = p2).
    { destruct p2 as [x y].
      unfold midpoint.
      simpl.
      f_equal; field. }
    rewrite Hmid2.
    assert (Hfoot1: foot_on_line p1 l1 = p1).
    { destruct p1 as [x y].
      unfold foot_on_line, on_line in *.
      simpl in *.
      rewrite H1.
      simpl.
      repeat rewrite Rdiv_0_l.
      repeat rewrite Rmult_0_r.
      repeat rewrite Rminus_0_r.
      reflexivity. }
    rewrite Hfoot1.
    assert (Hmid1: midpoint p1 p1 = p1).
    { destruct p1 as [x y].
      unfold midpoint.
      simpl.
      f_equal; field. }
    rewrite Hmid1.
    assert (Hrefl: reflect_point p2 (line_through p1 p2) = p2).
    { apply reflect_point_on_line.
      apply line_through_on_line_snd. }
    rewrite Hrefl.
    exact H2.
Qed.

(** fold_O6_approx passes through midpoint(pᵢ, foot(pᵢ,lᵢ)) *)
Lemma fold_O6_approx_geometric_property : forall p1 l1 p2 l2,
  let f := fold_O6_approx p1 l1 p2 l2 in
  let m1 := midpoint p1 (foot_on_line p1 l1) in
  let m2 := midpoint p2 (foot_on_line p2 l2) in
  on_line m1 (fold_line f) /\ on_line m2 (fold_line f).
Proof.
  intros p1 l1 p2 l2.
  unfold fold_O6_approx, fold_line; simpl.
  split.
  - apply line_through_on_line_fst.
  - apply line_through_on_line_snd.
Qed.

(** [fold_O6] is the common-perpendicular fold.  It satisfies the O6 incidence
    constraint exactly when both points lie on their target lines
    ([O6_exact_when_both_on_lines]) and approximates it otherwise; [CF_O6] is the
    matching constructor.  The cubic-solving O6 fold is the Beloch fold
    [fold_O6_beloch], with constructor [CF_O6_beloch], whose creases the depth
    enumeration produces through [cubic_real_roots].  For general-position inputs,
    [O6_general_constructible] gives a constructible crease meeting the O6
    constraint for any constructible foci and directrices. *)
Definition fold_O6 := fold_O6_approx.

Lemma fold_line_O6 : forall p1 l1 p2 l2,
  fold_line (fold_O6 p1 l1 p2 l2) = line_through (midpoint p1 (foot_on_line p1 l1)) (midpoint p2 (foot_on_line p2 l2)).
Proof. reflexivity. Qed.

(** p₁ ∈ l₁ ∧ p₂ ∈ l₂ → fold_O6 satisfies O6 *)
Theorem O6_approx_correctness : forall p1 l1 p2 l2,
  on_line p1 l1 -> on_line p2 l2 ->
  satisfies_O6_constraint (fold_O6 p1 l1 p2 l2) p1 l1 p2 l2.
Proof.
  intros p1 l1 p2 l2 H1 H2.
  apply fold_O6_approx_satisfies_when_on_lines; assumption.
Qed.

(** p₁ ∈ l₁ ∧ p₂ ∈ l₂ → ∃ crease satisfying O6 *)
Lemma O6_solution_exists_special_case : forall p1 l1 p2 l2,
  on_line p1 l1 -> on_line p2 l2 ->
  exists crease, satisfies_O6_line_constraint crease p1 l1 p2 l2.
Proof.
  intros p1 l1 p2 l2 H1 H2.
  exists (fold_line (fold_O6 p1 l1 p2 l2)).
  unfold fold_O6, fold_O6_approx, fold_line; simpl.
  apply fold_O6_approx_satisfies_when_on_lines; assumption.
Qed.

(** midpoint(p,p) = p *)
Lemma midpoint_self : forall p,
  midpoint p p = p.
Proof.
  intro p. destruct p as [x y].
  unfold midpoint. simpl. f_equal; field.
Qed.

(** p ∈ l → foot(p,l) = p *)
Lemma foot_on_line_when_on_line : forall p l,
  on_line p l -> foot_on_line p l = p.
Proof.
  intros [x y] l H.
  unfold foot_on_line, on_line in *. simpl in *.
  rewrite H. simpl.
  repeat rewrite Rdiv_0_l.
  repeat rewrite Rmult_0_r.
  repeat rewrite Rminus_0_r.
  reflexivity.
Qed.

(** p₁ ∈ l₁ → reflect(p₁, fold_O6) ∈ l₁ *)
Lemma O6_approx_first_constraint : forall p1 l1 p2 l2,
  on_line p1 l1 ->
  on_line (reflect_point p1 (fold_line (fold_O6 p1 l1 p2 l2))) l1.
Proof.
  intros p1 l1 p2 l2 H1.
  unfold fold_O6, fold_O6_approx, fold_line. simpl.
  rewrite foot_on_line_when_on_line by exact H1.
  rewrite midpoint_self.
  rewrite reflect_point_on_line by apply line_through_on_line_fst.
  exact H1.
Qed.

(** p₁ ∈ l₁ ∧ p₂ ∈ l₂ → reflect(p₂, fold_O6) ∈ l₂ *)
Lemma O6_approx_second_constraint : forall p1 l1 p2 l2,
  on_line p1 l1 -> on_line p2 l2 ->
  on_line (reflect_point p2 (fold_line (fold_O6 p1 l1 p2 l2))) l2.
Proof.
  intros p1 l1 p2 l2 H1 H2.
  unfold fold_O6, fold_O6_approx, fold_line. simpl.
  rewrite foot_on_line_when_on_line by exact H1.
  rewrite midpoint_self.
  rewrite foot_on_line_when_on_line by exact H2.
  rewrite midpoint_self.
  rewrite reflect_point_on_line by apply line_through_on_line_snd.
  exact H2.
Qed.

(** p₁ ∈ l₁ ∧ p₂ ∈ l₂ → fold_O6 satisfies O6 line constraint *)
Theorem O6_exact_when_both_on_lines : forall p1 l1 p2 l2,
  on_line p1 l1 -> on_line p2 l2 ->
  satisfies_O6_line_constraint (fold_line (fold_O6 p1 l1 p2 l2)) p1 l1 p2 l2.
Proof.
  intros p1 l1 p2 l2 H1 H2.
  unfold satisfies_O6_line_constraint.
  split.
  - apply O6_approx_first_constraint. exact H1.
  - apply O6_approx_second_constraint; assumption.
Qed.

(** O7 constraint: reflect(p₁,f) ∈ l₁ ∧ f ⊥ l₂ *)
Definition satisfies_O7_constraint (f : Fold) (p1 : Point) (l1 : Line) (l2 : Line) : Prop :=
  let crease := fold_line f in
  on_line (reflect_point p1 crease) l1 /\ line_perp crease l2.

(** Alias for perp_through *)
Definition line_perp_through (p : Point) (l : Line) : Line :=
  perp_through p l.

(** perp_through(p,l) ⊥ l *)
Lemma perp_through_is_perp : forall p l,
  line_perp (perp_through p l) l.
Proof.
  intros [x y] l.
  unfold line_perp, perp_through.
  destruct (Req_EM_T (A l) 0); simpl; ring.
Qed.

(** p ∈ perp_through(p,l) *)
Lemma perp_through_incident : forall p l,
  on_line p (perp_through p l).
Proof.
  intros [x y] l.
  unfold on_line, perp_through.
  destruct (Req_EM_T (A l) 0); simpl; ring.
Qed.

(** dist²(p₁, midpoint(p₁,p₂)) = dist²(p₂, midpoint(p₁,p₂)) *)
Lemma perp_bisector_dist2_eq : forall p1 p2,
  dist2 p1 (midpoint p1 p2) = dist2 p2 (midpoint p1 p2).
Proof.
  intros [x1 y1] [x2 y2].
  unfold dist2, midpoint; simpl.
  unfold sqr. field.
Qed.

(** O7: Fold ⊥ l₂ placing p₁ onto l₁ *)
Definition fold_O7_simple (p1 : Point) (l1 : Line) (l2 : Line) : Fold :=
  let perp_l2 := perp_through p1 l2 in
  let target := line_intersection perp_l2 l1 in
  fold_line_ctor (perp_bisector p1 target).

(** reflect(p₁, fold_O7_simple) ∈ l₁ when lines not parallel *)
Lemma fold_O7_simple_satisfies_reflection : forall p1 l1 l2,
  A (perp_through p1 l2) * B l1 - A l1 * B (perp_through p1 l2) <> 0 ->
  on_line (reflect_point p1 (fold_line (fold_O7_simple p1 l1 l2))) l1.
Proof.
  intros p1 l1 l2 Hnpar.
  unfold fold_O7_simple, fold_line; simpl.
  set (perp_l2 := perp_through p1 l2).
  set (target := line_intersection perp_l2 l1).
  assert (Htarget_l1: on_line target l1).
  { unfold target.
    apply line_intersection_on_both_lines in Hnpar.
    destruct Hnpar as [_ H2].
    exact H2. }
  destruct (point_eq_dec p1 target) as [Heq|Hneq].
  - (* If p1 = target, then p1 is already on l1 *)
    rewrite Heq.
    rewrite reflect_point_on_line.
    + exact Htarget_l1.
    + unfold on_line, perp_bisector.
      destruct target as [x y].
      destruct (Req_EM_T x x); [|contradiction].
      destruct (Req_EM_T y y); simpl; ring.
  - rewrite perp_bisector_reflects_to_other; [|exact Hneq].
    exact Htarget_l1.
Qed.

(** O7 via parametric intersection with l₁ along direction ⊥ l₂ *)
Definition fold_O7_corrected (p1 : Point) (l1 : Line) (l2 : Line) : Fold :=
  let dir_x := B l2 in
  let dir_y := - A l2 in
  let p1_x := fst p1 in
  let p1_y := snd p1 in
  let denom := A l1 * dir_x + B l1 * dir_y in
  match Req_EM_T denom 0 with
  | left _ => fold_line_ctor (perp_through p1 l2) (* Degenerate case *)
  | right Hdenom =>
      let t := - (A l1 * p1_x + B l1 * p1_y + C l1) / denom in
      let q := (p1_x + t * dir_x, p1_y + t * dir_y) in
      fold_line_ctor (perp_bisector p1 q)
  end.

(** (p₂-p₁) ∥ direction(l) → perp_bisector(p₁,p₂) ⊥ l *)
Lemma perp_bisector_parallel_direction_perp : forall (p1 p2 : Point) (l : Line),
  let dx := fst p2 - fst p1 in
  let dy := snd p2 - snd p1 in
  (* If (dx, dy) is parallel to l (i.e., perpendicular to normal of l) *)
  A l * dx + B l * dy = 0 ->
  p1 <> p2 ->
  line_perp (perp_bisector p1 p2) l.
Proof.
  intros [x1 y1] [x2 y2] l dx dy Hpar Hneq.
  unfold perp_bisector, line_perp.
  simpl in *.
  unfold dx, dy in Hpar. simpl in Hpar.
  destruct (Req_EM_T x1 x2) as [Hx|Hx].
  - subst x2.
    destruct (Req_EM_T y1 y2) as [Hy|Hy].
    + (* x1 = x2 and y1 = y2 means p1 = p2 *)
      subst y2.
      exfalso. apply Hneq. reflexivity.
    + simpl.
      (* perp_bisector has A=0, B=2*(y2-y1) *)
      (* line_perp means: 0*A_l + 2*(y2-y1)*B_l = 0 *)
      (* From Hpar: A_l*0 + B_l*(y2-y1) = 0, so B_l*(y2-y1) = 0 *)
      assert (Hbl: B l * (y2 - y1) = 0) by lra.
      lra.
  - simpl.
    (* perp_bisector has A=2*(x2-x1), B=2*(y2-y1) *)
    (* line_perp means: 2*(x2-x1)*A_l + 2*(y2-y1)*B_l = 0 *)
    (* From Hpar: A_l*(x2-x1) + B_l*(y2-y1) = 0 *)
    lra.
Qed.

(** fold_O7_corrected ⊥ l₂ *)
Lemma fold_O7_corrected_perp_to_l2 : forall p1 l1 l2,
  line_wf l2 ->
  A l1 * B l2 - B l1 * A l2 <> 0 ->
  ~on_line p1 l1 ->
  line_perp (fold_line (fold_O7_corrected p1 l1 l2)) l2.
Proof.
  intros p1 l1 l2 Hwf2 Hdenom_nz Hnot_on_l1.
  unfold fold_O7_corrected, fold_line.
  set (dir_x := B l2).
  set (dir_y := - A l2).
  set (p1_x := fst p1).
  set (p1_y := snd p1).
  set (denom := A l1 * dir_x + B l1 * dir_y).

  assert (Hdenom: denom <> 0).
  { unfold denom, dir_x, dir_y.
    replace (A l1 * B l2 + B l1 * - A l2) with (A l1 * B l2 - B l1 * A l2) by ring.
    assumption. }

  destruct (Req_EM_T denom 0) as [Heq|Hneq].
  - contradiction.
  - set (t := - (A l1 * p1_x + B l1 * p1_y + C l1) / denom).
    set (q := (p1_x + t * dir_x, p1_y + t * dir_y) : Point).

    (* Show that direction p1 -> q is parallel to l2 *)
    assert (Hpar: A l2 * (fst q - fst p1) + B l2 * (snd q - snd p1) = 0).
    { unfold q. simpl.
      unfold p1_x, p1_y, dir_x, dir_y.
      ring. }

    (* Prove p1 <> q using the assumption that p1 is not on l1 *)
    assert (Hneq_q: p1 <> q).
    { intro Heq.
      (* If p1 = q, then p1 = (p1_x + t*dir_x, p1_y + t*dir_y) *)
      (* This means t*dir_x = 0 and t*dir_y = 0 *)
      (* Since dir = (B_l2, -A_l2) and l2 has nonzero normal, either dir_x or dir_y is nonzero *)
      (* So t = 0, which means A_l1*p1_x + B_l1*p1_y + C_l1 = 0, i.e., p1 is on l1 *)
      assert (Ht_zero: t = 0).
      { unfold q, p1_x, p1_y, dir_x, dir_y in Heq.
        destruct p1 as [px py]. simpl in *.
        injection Heq as Hx Hy.
        assert (Htdx: t * B l2 = 0) by lra.
        assert (Htdy: t * - A l2 = 0) by lra.
        destruct Hwf2 as [Ha2 | Hb2].
        - (* A l2 <> 0, so from t * (-A l2) = 0 we get t = 0 *)
          assert (Hneg: - A l2 <> 0) by lra.
          apply Rmult_integral in Htdy.
          destruct Htdy as [Ht | Hcontra]; [exact Ht | lra].
        - (* B l2 <> 0, so from t * B l2 = 0 we get t = 0 *)
          apply Rmult_integral in Htdx.
          destruct Htdx as [Ht | Hcontra]; [exact Ht | contradiction]. }
      (* Now if t = 0, then p1 is on l1 *)
      unfold t in Ht_zero.
      assert (Hon_l1: A l1 * p1_x + B l1 * p1_y + C l1 = 0).
      { unfold t, Rdiv in Ht_zero.
        assert (Heq_prod: - (A l1 * p1_x + B l1 * p1_y + C l1) * / denom = 0) by (rewrite Ht_zero; reflexivity).
        apply Rmult_integral in Heq_prod.
        destruct Heq_prod as [Hneg | Hinv].
        - lra.
        - exfalso. apply Rinv_neq_0_compat in Hdenom. contradiction. }
      unfold p1_x, p1_y, on_line in Hon_l1.
      destruct p1. simpl in *. contradiction. }

    (* Non-degenerate case *)
    apply (perp_bisector_parallel_direction_perp p1 q l2 Hpar Hneq_q).
Qed.

(** Alias for fold_O7_corrected *)
Definition fold_O7 := fold_O7_corrected.

(** l₁ ∥ l₂ → fold_O7 ⊥ l₂ *)
Lemma fold_O7_degenerate_perp : forall p1 l1 l2,
  A l1 * B l2 - B l1 * A l2 = 0 ->
  line_perp (fold_line (fold_O7 p1 l1 l2)) l2.
Proof.
  intros p1 l1 l2 Hdenom.
  unfold fold_O7, fold_O7_corrected, fold_line.
  set (denom := A l1 * B l2 + B l1 * - A l2).
  assert (Hdenom_eq: denom = 0).
  { unfold denom. ring_simplify. exact Hdenom. }
  destruct (Req_EM_T denom 0).
  - simpl. apply perp_through_is_perp.
  - contradiction.
Qed.

(** p ∈ perp_through(p,l) *)
Lemma point_on_perp_through : forall p l,
  on_line p (perp_through p l).
Proof.
  intros [x y] l.
  unfold perp_through, on_line. simpl.
  destruct (Req_EM_T (A l) 0); simpl; ring.
Qed.

(** l₁ ∥ l₂ ∧ p₁ ∈ l₁ → reflect(p₁, fold_O7) ∈ l₁ *)
Lemma fold_O7_degenerate_reflection : forall p1 l1 l2,
  A l1 * B l2 - B l1 * A l2 = 0 ->
  on_line p1 l1 ->
  on_line (reflect_point p1 (fold_line (fold_O7 p1 l1 l2))) l1.
Proof.
  intros p1 l1 l2 Hdenom Hp1.
  unfold fold_O7, fold_O7_corrected, fold_line.
  set (denom := A l1 * B l2 + B l1 * - A l2).
  assert (Hdenom_eq: denom = 0).
  { unfold denom. ring_simplify. exact Hdenom. }
  destruct (Req_EM_T denom 0).
  - simpl. rewrite reflect_point_on_line by apply point_on_perp_through. exact Hp1.
  - contradiction.
Qed.

(** p₁ ∈ l₁ → t = 0 in fold_O7_corrected *)
Lemma fold_O7_t_zero_when_on_line : forall p1 l1 l2,
  on_line p1 l1 ->
  A l1 * B l2 - B l1 * A l2 <> 0 ->
  - (A l1 * fst p1 + B l1 * snd p1 + C l1) / (A l1 * B l2 + B l1 * - A l2) = 0.
Proof.
  intros [px py] l1 l2 Hon Hnonpar.
  unfold on_line in Hon. simpl in *.
  rewrite Hon. field. lra.
Qed.

(** p₁ ∈ l₁ ∧ l₁ ∦ l₂ → p₁ ∈ fold_O7 *)
Lemma fold_O7_p1_on_fold_when_on_l1 : forall p1 l1 l2,
  on_line p1 l1 ->
  A l1 * B l2 - B l1 * A l2 <> 0 ->
  on_line p1 (fold_line (fold_O7 p1 l1 l2)).
Proof.
  intros [px py] l1 l2 Hon Hnonpar.
  unfold fold_O7, fold_O7_corrected, fold_line.
  set (denom := A l1 * B l2 + B l1 * - A l2).
  assert (Hdenom: denom <> 0) by (unfold denom; lra).
  destruct (Req_EM_T denom 0); [contradiction|].
  simpl.
  assert (Ht: - (A l1 * px + B l1 * py + C l1) / denom = 0).
  { unfold on_line in Hon. simpl in Hon. rewrite Hon. field. exact Hdenom. }
  unfold perp_bisector, on_line. simpl.
  rewrite Ht.
  replace (px + 0 * B l2) with px by ring.
  replace (py + 0 * - A l2) with py by ring.
  destruct (Req_EM_T px px) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  destruct (Req_EM_T py py) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  simpl. ring.
Qed.

(** p₁ ∈ l₁ ∧ l₁ ∦ l₂ → reflect(p₁, fold_O7) ∈ l₁ *)
Lemma fold_O7_reflection_when_on_l1 : forall p1 l1 l2,
  on_line p1 l1 ->
  A l1 * B l2 - B l1 * A l2 <> 0 ->
  on_line (reflect_point p1 (fold_line (fold_O7 p1 l1 l2))) l1.
Proof.
  intros p1 l1 l2 Hon Hnonpar.
  rewrite reflect_point_on_line.
  - exact Hon.
  - apply fold_O7_p1_on_fold_when_on_l1; assumption.
Qed.

(** l₁ ∥ l₂ ∧ p₁ ∈ l₁ → fold_O7 satisfies O7 *)
Theorem O7_degenerate_case_complete : forall p1 l1 l2,
  A l1 * B l2 - B l1 * A l2 = 0 ->
  on_line p1 l1 ->
  satisfies_O7_constraint (fold_O7 p1 l1 l2) p1 l1 l2.
Proof.
  intros p1 l1 l2 Hdeg Hp1.
  unfold satisfies_O7_constraint.
  split.
  - apply fold_O7_degenerate_reflection; assumption.
  - apply fold_O7_degenerate_perp; assumption.
Qed.

(** (a+b)/2 = (a+b)·(1/2) *)
Lemma perp_bisector_midpoint_on : forall p1 p2,
  on_line (midpoint p1 p2) (perp_bisector p1 p2).
Proof.
  intros [x1 y1] [x2 y2].
  unfold on_line, midpoint, perp_bisector. simpl.
  destruct (Req_EM_T x1 x2) as [Hx|Hx]; destruct (Req_EM_T y1 y2) as [Hy|Hy].
  - subst. simpl. lra.
  - subst. simpl. field.
  - subst. simpl. field.
  - simpl. field.
Qed.

(** y₁ ≠ y₂ → reflect((x,y₁), perp_bisector) = (x,y₂) *)
Lemma refl_vert_bisector : forall x y1 y2,
  y1 <> y2 ->
  reflect_point (x, y1) (perp_bisector (x, y1) (x, y2)) = (x, y2).
Proof.
  intros x y1 y2 Hy.
  unfold reflect_point, perp_bisector.
  destruct (Req_EM_T x x); [|lra].
  destruct (Req_EM_T y1 y2); [lra|].
  simpl. f_equal; field; intro; apply Hy; lra.
Qed.

(** a ≠ 0 → a² + b² ≠ 0 *)
Lemma refl_gen_bisector_horiz_x : forall x1 x2 y1 y2,
  x1 <> x2 ->
  fst (reflect_point (x1, y1) (perp_bisector (x1, y1) (x2, y2))) = x2.
Proof.
  intros x1 x2 y1 y2 Hx.
  unfold reflect_point, perp_bisector.
  destruct (Req_EM_T x1 x2); [lra|].
  simpl. field. apply sum_sq_nz_l. lra.
Qed.

(** x₁ ≠ x₂ → snd(reflect((x₁,y₁), perp_bisector)) = y₂ *)
Lemma refl_gen_bisector_horiz_y : forall x1 x2 y1 y2,
  x1 <> x2 ->
  snd (reflect_point (x1, y1) (perp_bisector (x1, y1) (x2, y2))) = y2.
Proof.
  intros x1 x2 y1 y2 Hx.
  unfold reflect_point, perp_bisector.
  destruct (Req_EM_T x1 x2); [lra|].
  simpl. field. apply sum_sq_nz_l. lra.
Qed.

(** x₁ ≠ x₂ → reflect((x₁,y₁), perp_bisector) = (x₂,y₂) *)
Lemma refl_gen_bisector_horiz : forall x1 x2 y1 y2,
  x1 <> x2 ->
  reflect_point (x1, y1) (perp_bisector (x1, y1) (x2, y2)) = (x2, y2).
Proof.
  intros x1 x2 y1 y2 Hx.
  assert (Hfst: fst (reflect_point (x1, y1) (perp_bisector (x1, y1) (x2, y2))) = x2).
  { apply refl_gen_bisector_horiz_x. assumption. }
  assert (Hsnd: snd (reflect_point (x1, y1) (perp_bisector (x1, y1) (x2, y2))) = y2).
  { apply refl_gen_bisector_horiz_y. assumption. }
  destruct (reflect_point (x1, y1) (perp_bisector (x1, y1) (x2, y2))) as [rx ry].
  simpl in Hfst, Hsnd. subst. reflexivity.
Qed.

(** (x₁,y₁) ≠ (x₂,y₂) → reflect across perp_bisector swaps points *)
Lemma refl_gen_bisector : forall x1 y1 x2 y2,
  x1 <> x2 \/ y1 <> y2 ->
  reflect_point (x1, y1) (perp_bisector (x1, y1) (x2, y2)) = (x2, y2).
Proof.
  intros x1 y1 x2 y2 Hneq.
  destruct (Req_EM_T x1 x2) as [Hxeq | Hxneq].
  - destruct (Req_EM_T y1 y2) as [Hyeq | Hyneq].
    + destruct Hneq; lra.
    + subst. apply refl_vert_bisector. assumption.
  - apply refl_gen_bisector_horiz. assumption.
Qed.

(** O6 validity: img₁ ∈ l₁, img₂ ∈ l₂, and perp_bisectors coincide *)
Definition O6_general_valid (p1 : Point) (l1 : Line) (p2 : Point) (l2 : Line)
                            (img1 : Point) (img2 : Point) : Prop :=
  on_line img1 l1 /\
  on_line img2 l2 /\
  p1 <> img1 /\
  p2 <> img2 /\
  perp_bisector p1 img1 = perp_bisector p2 img2.

(** O6 fold via perp_bisector(p₁, img₁) *)
Definition fold_O6_general (p1 : Point) (img1 : Point) : Fold :=
  fold_line_ctor (perp_bisector p1 img1).

(** p₁ ≠ img₁ → reflect(p₁, fold_O6_general) = img₁ *)
Lemma fold_O6_general_reflects_p1 : forall p1 img1,
  p1 <> img1 ->
  reflect_point p1 (fold_line (fold_O6_general p1 img1)) = img1.
Proof.
  intros p1 img1 Hneq.
  unfold fold_O6_general, fold_line.
  apply perp_bisector_reflects_to_other. exact Hneq.
Qed.

(** perp_bisectors equal → reflect(p₂, fold_O6_general(p₁,img₁)) = img₂ *)
Lemma fold_O6_general_reflects_p2 : forall p1 p2 img1 img2,
  p1 <> img1 ->
  p2 <> img2 ->
  perp_bisector p1 img1 = perp_bisector p2 img2 ->
  reflect_point p2 (fold_line (fold_O6_general p1 img1)) = img2.
Proof.
  intros p1 p2 img1 img2 Hneq1 Hneq2 Heq.
  unfold fold_O6_general, fold_line.
  rewrite Heq.
  apply perp_bisector_reflects_to_other. exact Hneq2.
Qed.

(** O6_general_valid → fold_O6_general satisfies O6 line constraint *)
Theorem fold_O6_general_satisfies : forall p1 l1 p2 l2 img1 img2,
  O6_general_valid p1 l1 p2 l2 img1 img2 ->
  satisfies_O6_line_constraint (fold_line (fold_O6_general p1 img1)) p1 l1 p2 l2.
Proof.
  intros p1 l1 p2 l2 img1 img2 Hvalid.
  destruct Hvalid as [Himg1 [Himg2 [Hneq1 [Hneq2 Heq]]]].
  unfold satisfies_O6_line_constraint.
  split.
  - rewrite fold_O6_general_reflects_p1 by exact Hneq1. exact Himg1.
  - rewrite (fold_O6_general_reflects_p2 p1 p2 img1 img2 Hneq1 Hneq2 Heq). exact Himg2.
Qed.

(** O6_general_valid → ∃ crease satisfying O6 *)
Theorem O6_general_existence : forall p1 l1 p2 l2 img1 img2,
  O6_general_valid p1 l1 p2 l2 img1 img2 ->
  exists crease, satisfies_O6_line_constraint crease p1 l1 p2 l2.
Proof.
  intros p1 l1 p2 l2 img1 img2 Hvalid.
  exists (fold_line (fold_O6_general p1 img1)).
  exact (fold_O6_general_satisfies p1 l1 p2 l2 img1 img2 Hvalid).
Qed.

(** Constructed point q in fold_O7_corrected lies on l₁ *)
Lemma fold_O7_corrected_q_on_l1 : forall p1 l1 l2,
  A l1 * B l2 - B l1 * A l2 <> 0 ->
  let dir_x := B l2 in
  let dir_y := - A l2 in
  let p1_x := fst p1 in
  let p1_y := snd p1 in
  let denom := A l1 * dir_x + B l1 * dir_y in
  let t := - (A l1 * p1_x + B l1 * p1_y + C l1) / denom in
  let q := (p1_x + t * dir_x, p1_y + t * dir_y) in
  denom <> 0 ->
  on_line q l1.
Proof.
  intros p1 l1 l2 Hdenom_nz dir_x dir_y p1_x p1_y denom t q Hdenom.
  unfold on_line, q; simpl.
  unfold t, denom, dir_x, dir_y, p1_x, p1_y.
  destruct p1 as [x y]; simpl.
  field; auto.
Qed.

(** q ∈ l ∧ p₁ ≠ q → reflect(p₁, perp_bisector(p₁,q)) ∈ l *)
Lemma perp_bisector_reflects_onto_line : forall p1 q l,
  on_line q l ->
  p1 <> q ->
  on_line (reflect_point p1 (perp_bisector p1 q)) l.
Proof.
  intros p1 q l Hq_on_l Hneq.
  rewrite perp_bisector_reflects_to_other; auto.
Qed.

(** line_wf l ∧ t·B = 0 ∧ t·(-A) = 0 → t = 0 *)
Lemma product_both_zero_implies_zero : forall t l,
  line_wf l -> t * B l = 0 -> t * (- A l) = 0 -> t = 0.
Proof.
  intros t l Hwf Htb Hta.
  destruct (Req_EM_T (B l) 0) as [HB|HB].
  - destruct (Req_EM_T (A l) 0) as [HA|HA].
    + unfold line_wf in Hwf. destruct Hwf; contradiction.
    + assert (H: - A l <> 0) by lra.
      apply Rmult_integral in Hta.
      destruct Hta as [Ht|Hcontra]; auto.
      lra.
  - apply Rmult_integral in Htb.
    destruct Htb as [Ht|Hcontra]; auto.
    lra.
Qed.

(** (x + ta, y + tb) = (x, y) → ta = 0 ∧ tb = 0 *)
Lemma fold_O7_corrected_p1_neq_q : forall p1 l1 l2,
  line_wf l2 ->
  A l1 * B l2 - B l1 * A l2 <> 0 ->
  ~on_line p1 l1 ->
  let dir_x := B l2 in
  let dir_y := - A l2 in
  let p1_x := fst p1 in
  let p1_y := snd p1 in
  let denom := A l1 * dir_x + B l1 * dir_y in
  let t := - (A l1 * p1_x + B l1 * p1_y + C l1) / denom in
  let q := (p1_x + t * dir_x, p1_y + t * dir_y) in
  denom <> 0 ->
  p1 <> q.
Proof.
  intros p1 l1 l2 Hwf2 Hdenom_nz Hnot_on_l1 dir_x dir_y p1_x p1_y denom t q Hdenom Heq.
  subst q p1_x p1_y.
  destruct p1 as [x y]; simpl in *.
  symmetry in Heq.
  pose proof (point_eq_implies_offset_zero x y (- (A l1 * x + B l1 * y + C l1) / denom) (B l2) (- A l2) Heq) as [Htx Hty].
  pose proof (product_both_zero_implies_zero (- (A l1 * x + B l1 * y + C l1) / denom) l2 Hwf2 Htx Hty) as Htz.
  pose proof (fraction_zero_num (- (A l1 * x + B l1 * y + C l1)) denom Hdenom Htz) as Hnum.
  apply Hnot_on_l1.
  unfold on_line; simpl.
  lra.
Qed.

(** fold_O7 satisfies O7: reflect(p₁) ∈ l₁ ∧ crease ⊥ l₂ *)
Lemma fold_O7_satisfies_O7_constraint : forall p1 l1 l2,
  line_wf l2 ->
  A l1 * B l2 - B l1 * A l2 <> 0 ->
  ~on_line p1 l1 ->
  satisfies_O7_constraint (fold_O7 p1 l1 l2) p1 l1 l2.
Proof.
  intros p1 l1 l2 Hwf2 Hdenom Hnot_on.
  unfold satisfies_O7_constraint, fold_O7, fold_O7_corrected, fold_line.
  set (dir_x := B l2).
  set (dir_y := - A l2).
  set (p1_x := fst p1).
  set (p1_y := snd p1).
  set (denom := A l1 * dir_x + B l1 * dir_y).
  assert (Hdenom_neq: denom <> 0).
  { unfold denom, dir_x, dir_y.
    replace (A l1 * B l2 + B l1 * - A l2) with (A l1 * B l2 - B l1 * A l2) by ring.
    exact Hdenom. }
  destruct (Req_EM_T denom 0) as [Heq | Hneq].
  - contradiction.
  - set (t := - (A l1 * p1_x + B l1 * p1_y + C l1) / denom).
    set (q := (p1_x + t * dir_x, p1_y + t * dir_y)).
    split.
    + (* Reflection: p1 maps onto l1 *)
      simpl.
      apply perp_bisector_reflects_onto_line.
      * apply (fold_O7_corrected_q_on_l1 p1 l1 l2 Hdenom Hdenom_neq).
      * apply (fold_O7_corrected_p1_neq_q p1 l1 l2 Hwf2 Hdenom Hnot_on Hdenom_neq).
    + (* Perpendicularity *)
      simpl.
      assert (Hpar: A l2 * (fst q - fst p1) + B l2 * (snd q - snd p1) = 0).
      { unfold q, p1_x, p1_y, t, denom, dir_x, dir_y; simpl.
        destruct p1; simpl. ring. }
      assert (Hneq_q: p1 <> q).
      { apply (fold_O7_corrected_p1_neq_q p1 l1 l2 Hwf2 Hdenom Hnot_on Hdenom_neq). }
      apply (perp_bisector_parallel_direction_perp p1 q l2 Hpar Hneq_q).
Qed.

(** fold_O7 satisfies O7 in both degenerate and general cases *)
Theorem O7_unified : forall p1 l1 l2,
  line_wf l2 ->
  (A l1 * B l2 - B l1 * A l2 = 0 /\ on_line p1 l1) \/
  (A l1 * B l2 - B l1 * A l2 <> 0 /\ ~on_line p1 l1) ->
  satisfies_O7_constraint (fold_O7 p1 l1 l2) p1 l1 l2.
Proof.
  intros p1 l1 l2 Hwf2 [[Hpar Hon] | [Hnpar Hnot_on]].
  - apply O7_degenerate_case_complete; assumption.
  - apply fold_O7_satisfies_O7_constraint; assumption.
Qed.


(** Connection between O6 (Beloch fold) and cubic equations *)

Lemma O6_constraint_unfold : forall p1 l1 p2 l2 f,
  satisfies_O6_constraint f p1 l1 p2 l2 ->
  on_line (reflect_point p1 (fold_line f)) l1 /\
  on_line (reflect_point p2 (fold_line f)) l2.
Proof.
  intros p1 l1 p2 l2 f H.
  exact H.
Qed.

(** t³ + pt + q *)
Definition construct_reflection (p : Point) (f : Fold) : Point :=
  map_point f p.

(** midpoint(p₁,p₂) *)
Definition construct_midpoint (p1 p2 : Point) : Point :=
  midpoint p1 p2.

(** l₁ ∩ l₂ *)
Definition construct_intersection (l1 l2 : Line) : Point :=
  line_intersection l1 l2.

(** Line through p₁ and p₂ *)
Definition construct_line_through (p1 p2 : Point) : Line :=
  line_through p1 p2.

(** Perpendicular bisector of p₁p₂ *)
Definition construct_perp_bisector (p1 p2 : Point) : Line :=
  perp_bisector p1 p2.


(** Origami constructibility predicates *)

(** (c - qₓ)² ≤ dist²(p,q) *)
Definition O5_vert_valid (p q : Point) (c : R) : Prop :=
  let px := fst p in let py := snd p in
  let qx := fst q in let qy := snd q in
  (c - qx)^2 <= (px - qx)^2 + (py - qy)^2.

(** Image of p on l at distance dist(p,q) from q *)
Definition O5_general_image (p : Point) (l : Line) (q : Point) : Point :=
  let px := fst p in let py := snd p in
  let qx := fst q in let qy := snd q in
  let a := A l in let b := B l in let c := C l in
  let r2 := (px - qx)*(px - qx) + (py - qy)*(py - qy) in
  let d := (a * qx + b * qy + c) / (a*a + b*b) in
  let h2 := r2 - d*d * (a*a + b*b) in
  let t := sqrt h2 / sqrt (a*a + b*b) in
  let foot_x := qx - a * d in
  let foot_y := qy - b * d in
  (foot_x + b * t, foot_y - a * t).

(** dist(q,l)² ≤ dist²(p,q) *)
Definition O5_general_valid (p : Point) (l : Line) (q : Point) : Prop :=
  let px := fst p in let py := snd p in
  let qx := fst q in let qy := snd q in
  let a := A l in let b := B l in let c := C l in
  let r2 := (px - qx)^2 + (py - qy)^2 in
  let dist_to_line := Rabs (a * qx + b * qy + c) / sqrt (a^2 + b^2) in
  dist_to_line^2 <= r2.

(** O5 general: fold placing p onto l through q *)
Definition fold_O5_general (p : Point) (l : Line) (q : Point) : Fold :=
  let p' := O5_general_image p l q in
  fold_line_ctor (perp_bisector p p').

(** Mutually inductive constructibility predicates for points, lines, folds *)
Inductive ConstructiblePoint : Point -> Prop :=
| CP_O : ConstructiblePoint point_O
| CP_X : ConstructiblePoint point_X
| CP_inter :
    forall l1 l2,
      ConstructibleLine l1 -> ConstructibleLine l2 ->
      ConstructiblePoint (line_intersection l1 l2)
| CP_map :
    forall f p,
      ConstructibleFold f -> ConstructiblePoint p ->
      ConstructiblePoint (map_point f p)

with ConstructibleLine : Line -> Prop :=
| CL_x : ConstructibleLine line_xaxis
| CL_y : ConstructibleLine line_yaxis
| CL_fold :
    forall f, ConstructibleFold f -> ConstructibleLine (fold_line f)

with ConstructibleFold : Fold -> Prop :=
| CF_O1 :
    forall p1 p2,
      ConstructiblePoint p1 -> ConstructiblePoint p2 ->
      ConstructibleFold (fold_O1 p1 p2)
| CF_O2 :
    forall p1 p2,
      ConstructiblePoint p1 -> ConstructiblePoint p2 ->
      ConstructibleFold (fold_O2 p1 p2)
| CF_O3 :
    forall l1 l2,
      ConstructibleLine l1 -> ConstructibleLine l2 ->
      ConstructibleFold (fold_O3 l1 l2)
| CF_O4 :
    forall p l,
      ConstructiblePoint p -> ConstructibleLine l ->
      ConstructibleFold (fold_O4 p l)
| CF_O5 :
    forall p1 l p2,
      ConstructiblePoint p1 -> ConstructibleLine l -> ConstructiblePoint p2 ->
      ConstructibleFold (fold_O5 p1 l p2)
| CF_O6 :
    forall p1 l1 p2 l2,
      ConstructiblePoint p1 -> ConstructibleLine l1 ->
      ConstructiblePoint p2 -> ConstructibleLine l2 ->
      ConstructibleFold (fold_O6 p1 l1 p2 l2)
| CF_O7 :
    forall p1 l1 l2,
      ConstructiblePoint p1 -> ConstructibleLine l1 -> ConstructibleLine l2 ->
      ConstructibleFold (fold_O7 p1 l1 l2)
| CF_O5_vert :
    forall p q c,
      ConstructiblePoint p -> ConstructiblePoint q -> ConstructiblePoint (c, 0) ->
      O5_vert_valid p q c ->
      ConstructibleFold (fold_O5_vert p q c)
| CF_O6_beloch :
    forall p q t,
      ConstructiblePoint (p, 0) -> ConstructiblePoint (q, 0) ->
      t * t * t + p * t + q = 0 ->
      ConstructibleFold (fold_O6_beloch p q t)
| CF_O5_general :
    forall p l q,
      ConstructiblePoint p -> ConstructibleLine l -> ConstructiblePoint q ->
      line_wf l -> O5_general_valid p l q -> p <> O5_general_image p l q ->
      ConstructibleFold (fold_O5_general p l q).

(** Mutual induction scheme for constructibility *)
Scheme Constructible_mut :=
  Induction for ConstructiblePoint Sort Prop
  with ConstructibleLine_mut := Induction for ConstructibleLine Sort Prop
  with ConstructibleFold_mut := Induction for ConstructibleFold Sort Prop.

(** ConstructibleFold f → ConstructibleLine (fold_line f) *)
Lemma ConstructibleLine_of_fold : forall f, ConstructibleFold f -> ConstructibleLine (fold_line f).
Proof. intros f Hf; now constructor. Qed.

(** Line through O and X is constructible *)
Lemma ConstructibleLine_OX : ConstructibleLine (line_through point_O point_X).
Proof.
  rewrite <- fold_line_O1.
  apply CL_fold.
  apply CF_O1; constructor; constructor.
Qed.

(** x ∈ ℝ is constructible ⟺ ∃ y, (x,y) is constructible *)
Definition ConstructibleR (x : R) : Prop :=
  exists y, ConstructiblePoint (x, y).

(** 0 ∈ ConstructibleR *)
Lemma constructible_0 : ConstructibleR 0.
Proof. exists 0; constructor. Qed.

(** 1 ∈ ConstructibleR *)
Lemma constructible_1 : ConstructibleR 1.
Proof. exists 0; constructor 2. Qed.

(** A = 0 case: x-coord of foot equals x-coord of intersection *)
Lemma foot_x_eq_case_a0 : forall x y l,
  A l = 0 -> B l <> 0 ->
  fst (foot_on_line (x, y) l) = fst (line_intersection (perp_through (x, y) l) l).
Proof.
  intros x y l Ha0 Hb.
  transitivity x.
  - unfold foot_on_line. simpl.
    rewrite Ha0. field. exact Hb.
  - unfold perp_through.
    destruct (Req_EM_T (A l) 0) as [Ha0' | Hcontra]; [| contradiction].
    unfold line_intersection. simpl.
    rewrite Ha0.
    destruct (Req_EM_T (B l * B l - 0 * - 0) 0) as [Hcontra | Hbb]; [nra |].
    simpl. field. exact Hb.
Qed.

(** A = 0 case: y-coord of foot equals y-coord of intersection *)
Lemma foot_y_eq_case_a0 : forall x y l,
  A l = 0 -> B l <> 0 ->
  snd (foot_on_line (x, y) l) = snd (line_intersection (perp_through (x, y) l) l).
Proof.
  intros x y l Ha0 Hb.
  assert (Hwf : line_wf l) by (unfold line_wf; right; exact Hb).
  transitivity (- C l / B l).
  - unfold foot_on_line. simpl. rewrite Ha0. field. exact Hb.
  - unfold perp_through.
    destruct (Req_EM_T (A l) 0) as [Ha0' | Han0']; [| contradiction].
    unfold line_intersection. simpl.
    destruct (Req_EM_T (B l * B l - A l * - A l) 0) as [Hcontra | _].
    + exfalso. assert (H: A l * A l + B l * B l > 0) by (apply line_norm_pos; exact Hwf). nra.
    + simpl. rewrite Ha0. field. exact Hb.
Qed.

(** foot(p,l) = perp_through(p,l) ∩ l *)
Lemma foot_is_intersection : forall p l,
  line_wf l -> foot_on_line p l = line_intersection (perp_through p l) l.
Proof.
  intros [x y] [a b c] Hnz.
  unfold foot_on_line, line_intersection, perp_through. simpl.
  unfold line_wf in Hnz. simpl in Hnz.
  set (d := a * a + b * b).
  assert (Hd_nz: d <> 0).
  { unfold d. intro HC.
    assert (Ha2: 0 <= a * a) by apply Rle_0_sqr.
    assert (Hb2: 0 <= b * b) by apply Rle_0_sqr.
    assert (Hsum: a * a + b * b = 0) by exact HC.
    assert (Ha_z: a * a = 0) by lra.
    assert (Hb_z: b * b = 0) by lra.
    apply Rmult_integral in Ha_z. apply Rmult_integral in Hb_z.
    destruct Hnz as [Hna|Hnb]; [destruct Ha_z | destruct Hb_z]; contradiction. }
  destruct (Req_EM_T a 0) as [Ha0|Han0].
  - subst a. simpl in *. unfold d in Hd_nz. simpl in Hd_nz.
    destruct Hnz as [Hcontra|Hb]; [contradiction|].
    destruct (Req_EM_T (b * b - 0 * - 0) 0).
    + exfalso. assert (Hb2: b * b = 0) by lra. apply Rmult_integral in Hb2. destruct Hb2; contradiction.
    + simpl. unfold d. assert (Heq: 0 * 0 + b * b = b * b) by ring. rewrite Heq.
      unfold Rdiv. apply injective_projections; simpl; field; lra.
  - assert (Hdet_nz: b * b - a * - a <> 0).
    { intro HC. assert (Hsq: b * b + a * a = 0) by lra.
      assert (Hb2: 0 <= b * b) by apply Rle_0_sqr.
      assert (Ha2: 0 <= a * a) by apply Rle_0_sqr.
      assert (Hbz: b * b = 0) by lra.
      assert (Haz: a * a = 0) by lra.
      apply Rmult_integral in Hbz. apply Rmult_integral in Haz.
      destruct Hbz; destruct Haz; lra. }
    destruct (Req_EM_T (b * b - a * - a) 0); [contradiction|].
    simpl.
    unfold line_intersection.
    destruct (Req_EM_T (b * b - a * - a) 0); [contradiction|].
    simpl. unfold d.
    f_equal; field; assumption.
Qed.

(** foot(p,l) constructible when p, l constructible *)
Lemma foot_constructible : forall p l,
  line_wf l ->
  ConstructiblePoint p -> ConstructibleLine l ->
  ConstructiblePoint (foot_on_line p l).
Proof.
  intros p l Hwf Hp Hl.
  rewrite foot_is_intersection by exact Hwf.
  apply CP_inter with (l1 := perp_through p l) (l2 := l).
  - rewrite <- fold_line_O4. apply CL_fold. apply CF_O4; assumption.
  - exact Hl.
Qed.


(** Enumeration-based decidability for bounded depth constructibility *)

(** A real root of the depressed cubic t^3 + p t + q (depressed_cubic_root_sig),
    and the list of all its real roots: that root plus the two quotient-quadratic
    roots when their discriminant is nonnegative.  Enumerates the Beloch (O6)
    creases. *)
Definition some_cubic_root (p q : R) : R :=
  proj1_sig (depressed_cubic_root_sig p q).

Definition cubic_root_list (p q : R) : list R :=
  let r0 := some_cubic_root p q in
  let disc := -3 * r0 * r0 - 4 * p in
  match Rle_dec 0 disc with
  | left _ => r0 :: (- r0 + sqrt disc) / 2 :: (- r0 - sqrt disc) / 2 :: nil
  | right _ => r0 :: nil
  end.

Definition cubic_real_roots (p q : R) : list Line :=
  map beloch_fold_line (cubic_root_list p q).

(** Deciders for the O5_vert / O5_general fold-validity side conditions, so the
    enumeration can emit those creases exactly when the constructor applies. *)
Definition O5_vert_valid_dec (p q : Point) (c : R) :
  {O5_vert_valid p q c} + {~ O5_vert_valid p q c}.
Proof. unfold O5_vert_valid. apply Rle_dec. Defined.

Definition O5_general_guard (p : Point) (l : Line) (q : Point) :
  {line_wf l /\ O5_general_valid p l q /\ p <> O5_general_image p l q} +
  {~ (line_wf l /\ O5_general_valid p l q /\ p <> O5_general_image p l q)}.
Proof.
  destruct (Req_EM_T (A l) 0) as [Ha | Ha];
  [ destruct (Req_EM_T (B l) 0) as [Hb | Hb] | ].
  - right. intros [[H | H] _]; contradiction.
  - destruct (Rle_dec (let px := fst p in let py := snd p in
        let qx := fst q in let qy := snd q in
        let a := A l in let b := B l in let c := C l in
        let r2 := (px - qx)^2 + (py - qy)^2 in
        let dist_to_line := Rabs (a * qx + b * qy + c) / sqrt (a^2 + b^2) in
        dist_to_line^2) ((fst p - fst q)^2 + (snd p - snd q)^2)) as [Hv | Hv].
    + destruct (point_eq_dec p (O5_general_image p l q)) as [He | He].
      * right. intros [_ [_ Hne]]. contradiction.
      * left. split; [right; exact Hb | split; [exact Hv | exact He]].
    + right. intros [_ [Hval _]]. unfold O5_general_valid in Hval. contradiction.
  - destruct (Rle_dec (let px := fst p in let py := snd p in
        let qx := fst q in let qy := snd q in
        let a := A l in let b := B l in let c := C l in
        let r2 := (px - qx)^2 + (py - qy)^2 in
        let dist_to_line := Rabs (a * qx + b * qy + c) / sqrt (a^2 + b^2) in
        dist_to_line^2) ((fst p - fst q)^2 + (snd p - snd q)^2)) as [Hv | Hv].
    + destruct (point_eq_dec p (O5_general_image p l q)) as [He | He].
      * right. intros [_ [_ Hne]]. contradiction.
      * left. split; [left; exact Ha | split; [exact Hv | exact He]].
    + right. intros [_ [Hval _]]. unfold O5_general_valid in Hval. contradiction.
Defined.

(** Lines constructible at depth d *)
Fixpoint enum_lines (depth : nat) : list Line :=
  match depth with
  | O => [line_xaxis; line_yaxis]
  | S d =>
      let prev_lines := enum_lines d in
      let prev_points := enum_points d in
      prev_lines ++
      flat_map (fun p1 => flat_map (fun p2 =>
        [line_through p1 p2; perp_bisector p1 p2]) prev_points) prev_points ++
      flat_map (fun l1 => flat_map (fun l2 => [bisector l1 l2]) prev_lines) prev_lines ++
      flat_map (fun p => flat_map (fun l => [perp_through p l]) prev_lines) prev_points ++
      (* O5 crease: fold p1 onto l with crease through p2 *)
      flat_map (fun p1 => flat_map (fun l => flat_map (fun p2 =>
        [fold_line (fold_O5 p1 l p2)]) prev_points) prev_lines) prev_points ++
      (* O6 crease (midpoint construction): common perpendicular fold *)
      flat_map (fun p1 => flat_map (fun l1 => flat_map (fun p2 => flat_map (fun l2 =>
        [fold_line (fold_O6 p1 l1 p2 l2)]) prev_lines) prev_points) prev_lines) prev_points ++
      (* O7 crease: fold p1 onto l1 perpendicular to l2 *)
      flat_map (fun p1 => flat_map (fun l1 => flat_map (fun l2 =>
        [fold_line (fold_O7 p1 l1 l2)]) prev_lines) prev_lines) prev_points ++
      (* O5 onto a vertical target line x = c, guarded by validity *)
      flat_map (fun p => flat_map (fun q => flat_map (fun pc =>
        match O5_vert_valid_dec p q (fst pc) with
        | left _ => [fold_line (fold_O5_vert p q (fst pc))]
        | right _ => nil
        end) prev_points) prev_points) prev_points ++
      (* O6 Beloch creases: tangents solving t^3 + (fst pp) t + (fst pq) = 0 *)
      flat_map (fun pp => flat_map (fun pq =>
        cubic_real_roots (fst pp) (fst pq)) prev_points) prev_points ++
      (* general O5 fold placing p onto l through q, guarded by validity *)
      flat_map (fun p => flat_map (fun l => flat_map (fun q =>
        match O5_general_guard p l q with
        | left _ => [fold_line (fold_O5_general p l q)]
        | right _ => nil
        end) prev_points) prev_lines) prev_points
  end

(** Points constructible at depth d *)
with enum_points (depth : nat) : list Point :=
  match depth with
  | O => [point_O; point_X]
  | S d =>
      let prev_points := enum_points d in
      let prev_lines := enum_lines d in
      prev_points ++
      flat_map (fun l1 => flat_map (fun l2 =>
        [line_intersection l1 l2]) prev_lines) prev_lines ++
      flat_map (fun p => flat_map (fun l =>
        [reflect_point p l]) prev_lines) prev_points
  end.

(** |enum_points(0)| = 2 *)
Lemma enum_points_0_size : length (enum_points 0) = 2%nat.
Proof.
  simpl. reflexivity.
Qed.

(** |enum_lines(0)| = 2 *)
Lemma enum_lines_0_size : length (enum_lines 0) = 2%nat.
Proof.
  simpl. reflexivity.
Qed.

(** |enum_points(d)| ≤ |enum_points(S d)| *)
Lemma enum_points_size_monotone : forall d,
  (length (enum_points d) <= length (enum_points (S d)))%nat.
Proof.
  intro d. simpl.
  rewrite length_app.
  apply Nat.le_add_r.
Qed.

(** |enum_lines(d)| ≤ |enum_lines(S d)| *)
Lemma enum_lines_size_monotone : forall d,
  (length (enum_lines d) <= length (enum_lines (S d)))%nat.
Proof.
  intro d. simpl.
  rewrite length_app.
  apply Nat.le_add_r.
Qed.

(** 2 ≤ |enum_points(d)| *)
Lemma enum_points_size_lower_bound : forall d,
  (2 <= length (enum_points d))%nat.
Proof.
  intro d.
  induction d.
  - rewrite enum_points_0_size. apply Nat.le_refl.
  - apply Nat.le_trans with (m := length (enum_points d)).
    + exact IHd.
    + apply enum_points_size_monotone.
Qed.

(** p ∈ enum_points(d) *)
Definition point_constructible_depth (p : Point) (depth : nat) : bool :=
  existsb (fun q => if point_eq_dec p q then true else false) (enum_points depth).

(** Decidability of point_constructible_depth *)
Theorem enum_algorithm_decidable : forall p d,
  {point_constructible_depth p d = true} + {point_constructible_depth p d = false}.
Proof.
  intros p d.
  unfold point_constructible_depth.
  destruct (existsb (fun q => if point_eq_dec p q then true else false) (enum_points d)) eqn:E.
  - left. reflexivity.
  - right. reflexivity.
Qed.

(** 10 ≤ |enum_points(1)| *)
Theorem enum_exponential_lower_bound :
  (10 <= length (enum_points 1))%nat.
Proof.
  vm_compute. apply Nat.le_refl.
Qed.

(** ∃ b, point_constructible_depth p d = b *)
Lemma point_constructible_depth_terminates : forall p d,
  exists b, point_constructible_depth p d = b.
Proof.
  intros p d.
  exists (point_constructible_depth p d).
  reflexivity.
Qed.

(** point_constructible_depth p 0 = true → p = O ∨ p = X *)
Lemma point_constructible_depth_base : forall p,
  point_constructible_depth p 0 = true ->
  p = point_O \/ p = point_X.
Proof.
  intros p H.
  unfold point_constructible_depth in H.
  simpl in H.
  destruct (point_eq_dec p point_O) as [HO | HnO].
  - left. exact HO.
  - simpl in H.
    destruct (point_eq_dec p point_X) as [HX | HnX].
    + right. exact HX.
    + simpl in H. discriminate.
Qed.

(** enum_points(d) ⊆ enum_points(S d) *)
Lemma enum_points_monotone : forall d, incl (enum_points d) (enum_points (S d)).
Proof.
  intro d. simpl. unfold incl. intros a Ha.
  apply in_or_app. left. exact Ha.
Qed.

(** enum_lines(d) ⊆ enum_lines(S d) *)
Lemma enum_lines_monotone : forall d, incl (enum_lines d) (enum_lines (S d)).
Proof.
  intro d. simpl. unfold incl. intros a Ha.
  apply in_or_app. left. exact Ha.
Qed.

(** p ∈ enum_points(0) → ConstructiblePoint p *)
Lemma In_enum_points_base : forall p,
  In p (enum_points 0) -> ConstructiblePoint p.
Proof.
  intros p H.
  simpl in H.
  destruct H as [H | [H | H]].
  - subst. constructor.
  - subst. constructor.
  - contradiction.
Qed.

(** l ∈ enum_lines(0) → ConstructibleLine l *)
Lemma In_enum_lines_base : forall l,
  In l (enum_lines 0) -> ConstructibleLine l.
Proof.
  intros l H.
  simpl in H.
  destruct H as [H | [H | H]].
  - subst. constructor.
  - subst. constructor.
  - contradiction.
Qed.

(** ConstructiblePoint p₁ → ConstructiblePoint p₂ → ConstructibleLine (line_through p₁ p₂) *)
Lemma line_through_constructible : forall p1 p2,
  ConstructiblePoint p1 -> ConstructiblePoint p2 ->
  ConstructibleLine (line_through p1 p2).
Proof.
  intros p1 p2 H1 H2.
  rewrite <- fold_line_O1.
  apply CL_fold.
  apply CF_O1; assumption.
Qed.

Lemma perp_bisector_constructible : forall p1 p2,
  ConstructiblePoint p1 -> ConstructiblePoint p2 ->
  ConstructibleLine (perp_bisector p1 p2).
Proof.
  intros p1 p2 H1 H2.
  rewrite <- fold_line_O2.
  apply CL_fold.
  apply CF_O2; assumption.
Qed.

Lemma bisector_constructible : forall l1 l2,
  ConstructibleLine l1 -> ConstructibleLine l2 ->
  ConstructibleLine (bisector l1 l2).
Proof.
  intros l1 l2 H1 H2.
  rewrite <- fold_line_O3.
  apply CL_fold.
  apply CF_O3; assumption.
Qed.

Lemma perp_through_constructible : forall p l,
  ConstructiblePoint p -> ConstructibleLine l ->
  ConstructibleLine (perp_through p l).
Proof.
  intros p l Hp Hl.
  rewrite <- fold_line_O4.
  apply CL_fold.
  apply CF_O4; assumption.
Qed.

Lemma line_intersection_constructible : forall l1 l2,
  ConstructibleLine l1 -> ConstructibleLine l2 ->
  ConstructiblePoint (line_intersection l1 l2).
Proof.
  intros l1 l2 H1 H2.
  apply CP_inter; assumption.
Qed.

Lemma line_eq_record : forall l1 l2,
  A l1 = A l2 -> B l1 = B l2 -> C l1 = C l2 -> l1 = l2.
Proof.
  intros [a1 b1 c1] [a2 b2 c2] Ha Hb Hc.
  simpl in *. subst. reflexivity.
Qed.

Lemma fold_O1_line_xaxis : fold_line (fold_O1 point_O point_X) = line_xaxis.
Proof.
  apply line_eq_record; unfold fold_O1, fold_line, line_through, point_O, point_X, line_xaxis; simpl.
  - destruct (Req_EM_T 0 1); [lra|]. simpl. ring.
  - destruct (Req_EM_T 0 1); [lra|]. simpl. ring.
  - destruct (Req_EM_T 0 1); [lra|]. simpl. ring.
Qed.

Lemma fold_O4_line_yaxis : fold_line (fold_O4 point_O line_xaxis) = line_yaxis.
Proof.
  apply line_eq_record; unfold fold_O4, fold_line, perp_through, point_O, line_xaxis, line_yaxis; simpl.
  - destruct (Req_EM_T 0 0); [|contradiction]. simpl. ring.
  - destruct (Req_EM_T 0 0); [|contradiction]. simpl. ring.
  - destruct (Req_EM_T 0 0); [|contradiction]. simpl. ring.
Qed.

Lemma ConstructibleLine_has_fold : forall l,
  ConstructibleLine l -> exists f, ConstructibleFold f /\ fold_line f = l.
Proof.
  intros l Hl. induction Hl.
  - exists (fold_O1 point_O point_X). split.
    + constructor; constructor.
    + apply fold_O1_line_xaxis.
  - exists (fold_O4 point_O line_xaxis). split.
    + constructor; constructor.
    + apply fold_O4_line_yaxis.
  - exists f. auto.
Qed.

Lemma reflect_point_constructible : forall p l,
  ConstructiblePoint p -> ConstructibleLine l -> ConstructiblePoint (reflect_point p l).
Proof.
  intros p l Hp Hl.
  destruct (ConstructibleLine_has_fold l Hl) as [f [Hf Heq]].
  rewrite <- Heq. unfold reflect_point.
  replace (A l) with (A (fold_line f)) by (rewrite Heq; reflexivity).
  replace (B l) with (B (fold_line f)) by (rewrite Heq; reflexivity).
  replace (C l) with (C (fold_line f)) by (rewrite Heq; reflexivity).
  apply CP_map; assumption.
Qed.

(* In_enum_points_constructible and In_enum_lines_constructible (enumeration
   soundness) are proved later, in the "Single-fold decision procedure" section
   after the depressed-cubic root machinery, since the Beloch-crease generator
   in enum_lines emits roots whose soundness needs depressed_cubic_root_exists. *)
Lemma point_O_in_enum_0 : In point_O (enum_points 0).
Proof.
  simpl. left. reflexivity.
Qed.

Lemma point_X_in_enum_0 : In point_X (enum_points 0).
Proof.
  simpl. right. left. reflexivity.
Qed.

Lemma line_xaxis_in_enum_0 : In line_xaxis (enum_lines 0).
Proof.
  simpl. left. reflexivity.
Qed.

Lemma line_yaxis_in_enum_0 : In line_yaxis (enum_lines 0).
Proof.
  simpl. right. left. reflexivity.
Qed.
Lemma enum_points_monotone_le : forall d1 d2, (d1 <= d2)%nat -> incl (enum_points d1) (enum_points d2).
Proof.
  intros d1 d2 Hle. induction Hle.
  - unfold incl. intros. assumption.
  - unfold incl in *. intros. apply enum_points_monotone. apply IHHle. assumption.
Qed.

Lemma enum_lines_monotone_le : forall d1 d2, (d1 <= d2)%nat -> incl (enum_lines d1) (enum_lines d2).
Proof.
  intros d1 d2 Hle. induction Hle.
  - unfold incl. intros. assumption.
  - unfold incl in *. intros. apply enum_lines_monotone. apply IHHle. assumption.
Qed.

Lemma CP_O_in_enum : exists d, In point_O (enum_points d).
Proof.
  exists 0%nat. apply point_O_in_enum_0.
Qed.

Lemma CP_X_in_enum : exists d, In point_X (enum_points d).
Proof.
  exists 0%nat. apply point_X_in_enum_0.
Qed.

Lemma CL_x_in_enum : exists d, In line_xaxis (enum_lines d).
Proof.
  exists 0%nat. apply line_xaxis_in_enum_0.
Qed.

Lemma CL_y_in_enum : exists d, In line_yaxis (enum_lines d).
Proof.
  exists 0%nat. apply line_yaxis_in_enum_0.
Qed.

Lemma line_intersection_in_enum_S : forall d1 d2 l1 l2,
  In l1 (enum_lines d1) -> In l2 (enum_lines d2) ->
  In (line_intersection l1 l2) (enum_points (S (Nat.max d1 d2))).
Proof.
  intros d1 d2 l1 l2 H1 H2. simpl.
  apply incl_appr. apply incl_appl.
  apply in_flat_map_intro with (x := l1).
  - apply (enum_lines_monotone_le d1 (Nat.max d1 d2)); [apply max_le_l|assumption].
  - apply in_flat_map_intro with (x := l2).
    + apply (enum_lines_monotone_le d2 (Nat.max d1 d2)); [apply max_le_r|assumption].
    + simpl. left. reflexivity.
Qed.

Lemma CP_inter_in_enum : forall l1 l2,
  (exists d1, In l1 (enum_lines d1)) ->
  (exists d2, In l2 (enum_lines d2)) ->
  exists d, In (line_intersection l1 l2) (enum_points d).
Proof.
  intros l1 l2 [d1 H1] [d2 H2].
  exists (S (Nat.max d1 d2)).
  apply line_intersection_in_enum_S; assumption.
Qed.

Lemma reflect_point_in_enum_S : forall dp dl p l,
  In p (enum_points dp) -> In l (enum_lines dl) ->
  In (reflect_point p l) (enum_points (S (Nat.max dp dl))).
Proof.
  intros dp dl p l Hp Hl. simpl.
  apply incl_appr. apply incl_appr.
  apply in_flat_map_intro with (x := p).
  - apply (enum_points_monotone_le dp (Nat.max dp dl)); [apply max_le_l|assumption].
  - apply in_flat_map_intro with (x := l).
    + apply (enum_lines_monotone_le dl (Nat.max dp dl)); [apply max_le_r|assumption].
    + simpl. left. reflexivity.
Qed.

Lemma CP_map_in_enum : forall f p,
  (exists df, In (fold_line f) (enum_lines df)) ->
  (exists dp, In p (enum_points dp)) ->
  exists d, In (map_point f p) (enum_points d).
Proof.
  intros f p [df Hf] [dp Hp].
  exists (S (Nat.max dp df)).
  unfold map_point.
  apply reflect_point_in_enum_S; assumption.
Qed.

Lemma line_through_in_enum_S : forall d1 d2 p1 p2,
  In p1 (enum_points d1) -> In p2 (enum_points d2) ->
  In (line_through p1 p2) (enum_lines (S (Nat.max d1 d2))).
Proof.
  intros d1 d2 p1 p2 H1 H2. simpl.
  apply incl_appr. apply incl_appl.
  apply in_flat_map_intro with (x := p1).
  - apply (enum_points_monotone_le d1 (Nat.max d1 d2)); [apply max_le_l|assumption].
  - apply in_flat_map_intro with (x := p2).
    + apply (enum_points_monotone_le d2 (Nat.max d1 d2)); [apply max_le_r|assumption].
    + simpl. left. reflexivity.
Qed.

Lemma CF_O1_in_enum : forall p1 p2,
  (exists d1, In p1 (enum_points d1)) ->
  (exists d2, In p2 (enum_points d2)) ->
  exists d, In (fold_line (fold_O1 p1 p2)) (enum_lines d).
Proof.
  intros p1 p2 [d1 H1] [d2 H2].
  exists (S (Nat.max d1 d2)).
  rewrite fold_line_O1.
  apply line_through_in_enum_S; assumption.
Qed.

Lemma perp_bisector_in_enum_S : forall d1 d2 p1 p2,
  In p1 (enum_points d1) -> In p2 (enum_points d2) ->
  In (perp_bisector p1 p2) (enum_lines (S (Nat.max d1 d2))).
Proof.
  intros d1 d2 p1 p2 H1 H2. simpl.
  apply incl_appr. apply incl_appl.
  apply in_flat_map_intro with (x := p1).
  - apply (enum_points_monotone_le d1 (Nat.max d1 d2)); [apply max_le_l|assumption].
  - apply in_flat_map_intro with (x := p2).
    + apply (enum_points_monotone_le d2 (Nat.max d1 d2)); [apply max_le_r|assumption].
    + simpl. right. left. reflexivity.
Qed.

Lemma CF_O2_in_enum : forall p1 p2,
  (exists d1, In p1 (enum_points d1)) ->
  (exists d2, In p2 (enum_points d2)) ->
  exists d, In (fold_line (fold_O2 p1 p2)) (enum_lines d).
Proof.
  intros p1 p2 [d1 H1] [d2 H2].
  exists (S (Nat.max d1 d2)).
  rewrite fold_line_O2.
  apply perp_bisector_in_enum_S; assumption.
Qed.

Lemma bisector_in_enum_S : forall d1 d2 l1 l2,
  In l1 (enum_lines d1) -> In l2 (enum_lines d2) ->
  In (bisector l1 l2) (enum_lines (S (Nat.max d1 d2))).
Proof.
  intros d1 d2 l1 l2 H1 H2. simpl.
  apply incl_appr. apply incl_appr. apply incl_appl.
  apply in_flat_map_intro with (x := l1).
  - apply (enum_lines_monotone_le d1 (Nat.max d1 d2)); [apply max_le_l|assumption].
  - apply in_flat_map_intro with (x := l2).
    + apply (enum_lines_monotone_le d2 (Nat.max d1 d2)); [apply max_le_r|assumption].
    + simpl. left. reflexivity.
Qed.

Lemma CF_O3_in_enum : forall l1 l2,
  (exists d1, In l1 (enum_lines d1)) ->
  (exists d2, In l2 (enum_lines d2)) ->
  exists d, In (fold_line (fold_O3 l1 l2)) (enum_lines d).
Proof.
  intros l1 l2 [d1 H1] [d2 H2].
  exists (S (Nat.max d1 d2)).
  rewrite fold_line_O3.
  apply bisector_in_enum_S; assumption.
Qed.

Lemma perp_through_in_enum_S : forall dp dl p l,
  In p (enum_points dp) -> In l (enum_lines dl) ->
  In (perp_through p l) (enum_lines (S (Nat.max dp dl))).
Proof.
  intros dp dl p l Hp Hl. simpl.
  apply incl_appr. apply incl_appr. apply incl_appr. apply incl_appl.
  apply in_flat_map_intro with (x := p).
  - apply (enum_points_monotone_le dp (Nat.max dp dl)); [apply max_le_l|assumption].
  - apply in_flat_map_intro with (x := l).
    + apply (enum_lines_monotone_le dl (Nat.max dp dl)); [apply max_le_r|assumption].
    + simpl. left. reflexivity.
Qed.

Lemma CF_O4_in_enum : forall p l,
  (exists dp, In p (enum_points dp)) ->
  (exists dl, In l (enum_lines dl)) ->
  exists d, In (fold_line (fold_O4 p l)) (enum_lines d).
Proof.
  intros p l [dp Hp] [dl Hl].
  exists (S (Nat.max dp dl)).
  rewrite fold_line_O4.
  apply perp_through_in_enum_S; assumption.
Qed.

Lemma CL_fold_in_enum : forall f,
  (exists d, In (fold_line f) (enum_lines d)) ->
  (exists d, In (fold_line f) (enum_lines d)).
Proof.
  intros f H. exact H.
Qed.

Inductive RestrictedConstructibleFold : Fold -> Prop :=
| RCF_O1 : forall p1 p2,
    ConstructiblePoint p1 -> ConstructiblePoint p2 ->
    RestrictedConstructibleFold (fold_O1 p1 p2)
| RCF_O2 : forall p1 p2,
    ConstructiblePoint p1 -> ConstructiblePoint p2 ->
    RestrictedConstructibleFold (fold_O2 p1 p2)
| RCF_O3 : forall l1 l2,
    ConstructibleLine l1 -> ConstructibleLine l2 ->
    RestrictedConstructibleFold (fold_O3 l1 l2)
| RCF_O4 : forall p l,
    ConstructiblePoint p -> ConstructibleLine l ->
    RestrictedConstructibleFold (fold_O4 p l).

Lemma ConstructibleFold_O1_in_enum : forall p1 p2,
  (exists d1, In p1 (enum_points d1)) ->
  (exists d2, In p2 (enum_points d2)) ->
  exists d, In (fold_line (fold_O1 p1 p2)) (enum_lines d).
Proof.
  intros p1 p2 H1 H2. apply CF_O1_in_enum; assumption.
Qed.

Lemma line_intersection_in_enum : forall l1 l2 d1 d2,
  In l1 (enum_lines d1) ->
  In l2 (enum_lines d2) ->
  In (line_intersection l1 l2) (enum_points (S (Nat.max d1 d2))).
Proof.
  intros l1 l2 d1 d2 H1 H2.
  simpl.
  apply incl_appr.
  apply incl_appl.
  apply in_flat_map_intro with (x := l1).
  - apply (enum_lines_monotone_le d1 (Nat.max d1 d2)).
    + apply max_le_l.
    + exact H1.
  - apply in_flat_map_intro with (x := l2).
    + apply (enum_lines_monotone_le d2 (Nat.max d1 d2)).
      * apply max_le_r.
      * exact H2.
    + simpl. left. reflexivity.
Qed.

Lemma reflect_point_in_enum : forall p l dp dl,
  In p (enum_points dp) ->
  In l (enum_lines dl) ->
  In (reflect_point p l) (enum_points (S (Nat.max dp dl))).
Proof.
  intros p l dp dl Hp Hl.
  simpl.
  apply incl_appr.
  apply incl_appr.
  apply in_flat_map_intro with (x := p).
  - apply (enum_points_monotone_le dp (Nat.max dp dl)).
    + apply max_le_l.
    + exact Hp.
  - apply in_flat_map_intro with (x := l).
    + apply (enum_lines_monotone_le dl (Nat.max dp dl)).
      * apply max_le_r.
      * exact Hl.
    + simpl. left. reflexivity.
Qed.
(** foot(p,l) ∈ enum_points(S(S(max dp dl))) *)
Lemma CF_O5_helper_foot_in_enum : forall p l dp dl,
  line_wf l ->
  In p (enum_points dp) -> In l (enum_lines dl) ->
  In (foot_on_line p l) (enum_points (S (S (Nat.max dp dl)))).
Proof.
  intros p l dp dl Hwf Hp Hl.
  set (d1 := S (Nat.max dp dl)).
  assert (Hperp: In (perp_through p l) (enum_lines d1)).
  { unfold d1. apply perp_through_in_enum_S; assumption. }
  assert (Hl': In l (enum_lines d1)).
  { unfold d1. apply (enum_lines_monotone_le dl (S (Nat.max dp dl))).
    - apply le_S, Nat.le_max_r.
    - exact Hl. }
  rewrite foot_is_intersection by exact Hwf.
  assert (Hgoal: In (line_intersection (perp_through p l) l) (enum_points (S (Nat.max d1 d1)))).
  { apply line_intersection_in_enum_S; assumption. }
  assert (Heq: S (Nat.max d1 d1) = S d1).
  { f_equal. apply Nat.max_id. }
  rewrite <- Heq.
  exact Hgoal.
Qed.

(** line_through(p₁,p₂) ∈ enum_lines(S(max d₁ d₂)) *)
Lemma CF_O5_helper_line_through_in_enum : forall p1 p2 d1 d2,
  In p1 (enum_points d1) -> In p2 (enum_points d2) ->
  In (line_through p1 p2) (enum_lines (S (Nat.max d1 d2))).
Proof.
  intros p1 p2 d1 d2 H1 H2.
  apply line_through_in_enum_S; assumption.
Qed.

(** fold_O5 crease eventually in enum_lines *)
Lemma CF_O5_in_enum : forall p1 l p2,
  line_wf l ->
  (exists d1, In p1 (enum_points d1)) ->
  (exists d2, In l (enum_lines d2)) ->
  (exists d3, In p2 (enum_points d3)) ->
  exists d, In (fold_line (fold_O5 p1 l p2)) (enum_lines d).
Proof.
  intros p1 l p2 Hwf [d1 H1] [d2 H2] [d3 H3].
  rewrite fold_line_O5.
  set (proj := foot_on_line p1 l).
  set (d_proj := S (S (Nat.max d1 d2))).
  assert (Hproj: In proj (enum_points d_proj)).
  { unfold proj, d_proj. apply CF_O5_helper_foot_in_enum; assumption. }
  assert (H1': In p1 (enum_points d_proj)).
  { apply (enum_points_monotone_le d1 d_proj).
    - unfold d_proj. apply le_S, le_S, Nat.le_max_l.
    - exact H1. }
  set (aux := line_through p1 proj).
  set (d_aux := S d_proj).
  assert (Haux: In aux (enum_lines d_aux)).
  { unfold aux, d_aux.
    replace (S d_proj) with (S (Nat.max d_proj d_proj)) by (rewrite Nat.max_id; reflexivity).
    apply CF_O5_helper_line_through_in_enum; [exact H1' | exact Hproj]. }
  exists (S (Nat.max d3 d_aux)).
  unfold aux. apply perp_through_in_enum_S; assumption.
Qed.

(** perp_bisector(p₁,p₂) ∈ enum_lines(S(max d₁ d₂)) *)
Lemma CF_O7_helper_perp_bisector_in_enum : forall p1 p2 d1 d2,
  In p1 (enum_points d1) -> In p2 (enum_points d2) ->
  In (perp_bisector p1 p2) (enum_lines (S (Nat.max d1 d2))).
Proof.
  intros p1 p2 d1 d2 H1 H2.
  apply perp_bisector_in_enum_S; assumption.
Qed.

(** -0 = 0 *)
Lemma perp_through_A_when_a_zero : forall px py b c,
  A (perp_through (px, py) {| A := 0; B := b; C := c |}) = b.
Proof.
  intros. unfold perp_through. simpl.
  destruct (Req_EM_T 0 0); [|contradiction]. simpl. reflexivity.
Qed.

(** B(perp_through(p, {A:=0,B:=b,C:=c})) = 0 *)
Lemma perp_through_B_when_a_zero : forall px py b c,
  B (perp_through (px, py) {| A := 0; B := b; C := c |}) = 0.
Proof.
  intros. unfold perp_through. simpl.
  destruct (Req_EM_T 0 0); [|contradiction]. simpl. rewrite neg_zero. reflexivity.
Qed.

(** a ≠ 0 → B(perp_through(p, {A:=a,B:=0,C:=c})) = -a *)
Lemma perp_through_B_when_b_zero : forall px py a c,
  a <> 0 ->
  B (perp_through (px, py) {| A := a; B := 0; C := c |}) = - a.
Proof.
  intros. unfold perp_through. simpl.
  destruct (Req_EM_T a 0); [contradiction|]. simpl. reflexivity.
Qed.

(** a ≠ 0 → A(perp_through(p, {A:=a,B:=b,C:=c})) = b *)
Lemma perp_through_A_general : forall px py a b c,
  a <> 0 ->
  A (perp_through (px, py) {| A := a; B := b; C := c |}) = b.
Proof.
  intros. unfold perp_through. simpl.
  destruct (Req_EM_T a 0); [contradiction|]. simpl. reflexivity.
Qed.

(** a ≠ 0 → B(perp_through(p, {A:=a,B:=b,C:=c})) = -a *)
Lemma perp_through_B_general : forall px py a b c,
  a <> 0 ->
  B (perp_through (px, py) {| A := a; B := b; C := c |}) = - a.
Proof.
  intros. unfold perp_through. simpl.
  destruct (Req_EM_T a 0); [contradiction|]. simpl. reflexivity.
Qed.

(** ∃ d, O ∈ enum_points(d) *)
Lemma ConstructiblePoint_O_eventually : exists d, In point_O (enum_points d).
Proof.
  exact CP_O_in_enum.
Qed.

(** ∃ d, X ∈ enum_points(d) *)
Lemma ConstructiblePoint_X_eventually : exists d, In point_X (enum_points d).
Proof.
  exact CP_X_in_enum.
Qed.

(** ∃ d, x-axis ∈ enum_lines(d) *)
Lemma ConstructibleLine_xaxis_eventually : exists d, In line_xaxis (enum_lines d).
Proof.
  exact CL_x_in_enum.
Qed.

(** ∃ d, y-axis ∈ enum_lines(d) *)
Lemma ConstructibleLine_yaxis_eventually : exists d, In line_yaxis (enum_lines d).
Proof.
  exact CL_y_in_enum.
Qed.

(** foot(p,l) ∈ enum_points(S(S(max dp dl))) *)
Lemma foot_in_enum_from_point_line : forall p l dp dl,
  line_wf l ->
  In p (enum_points dp) -> In l (enum_lines dl) ->
  In (foot_on_line p l) (enum_points (S (S (Nat.max dp dl)))).
Proof.
  intros p l dp dl Hwf Hp Hl.
  apply CF_O5_helper_foot_in_enum; assumption.
Qed.

(** p ∈ enum_points(d₁) → p ∈ enum_points(S(S(max d₁ d₂))) *)
Lemma point_monotone_to_SS_max : forall p d1 d2,
  In p (enum_points d1) ->
  In p (enum_points (S (S (Nat.max d1 d2)))).
Proof.
  intros p d1 d2 H.
  apply (enum_points_monotone_le d1).
  - apply le_S, le_S, Nat.le_max_l.
  - exact H.
Qed.

(** p ∈ enum_points(d₂) → p ∈ enum_points(S(S(max d₁ d₂))) *)
Lemma point_monotone_to_SS_max_r : forall p d1 d2,
  In p (enum_points d2) ->
  In p (enum_points (S (S (Nat.max d1 d2)))).
Proof.
  intros p d1 d2 H.
  apply (enum_points_monotone_le d2).
  - apply le_S, le_S, Nat.le_max_r.
  - exact H.
Qed.


(** Fold sequences as explicit construction traces *)

(** Single origami fold step *)
Inductive FoldStep : Type :=
| FS_O1 : Point -> Point -> FoldStep
| FS_O2 : Point -> Point -> FoldStep
| FS_O3 : Line -> Line -> FoldStep
| FS_O4 : Point -> Line -> FoldStep
| FS_O5 : Point -> Line -> Point -> FoldStep
| FS_O6 : Point -> Line -> Point -> Line -> FoldStep
| FS_O7 : Point -> Line -> Line -> FoldStep.

(** Sequence of fold steps *)
Definition FoldSequence : Type := list FoldStep.

(** Crease line of a fold step *)
Definition execute_fold_step (step : FoldStep) : Line :=
  match step with
  | FS_O1 p1 p2 => fold_line (fold_O1 p1 p2)
  | FS_O2 p1 p2 => fold_line (fold_O2 p1 p2)
  | FS_O3 l1 l2 => fold_line (fold_O3 l1 l2)
  | FS_O4 p l => fold_line (fold_O4 p l)
  | FS_O5 p l q => fold_line (fold_O5_general p l q)
  | FS_O6 p1 l1 p2 l2 => beloch_fold_line (fst p1)
  | FS_O7 p l1 l2 => fold_line (fold_O7 p l1 l2)
  end.

(** State: accumulated points and lines *)
Record ConstructionState : Type := mkState {
  state_points : list Point;
  state_lines : list Line
}.

(** Initial state: O, X, x-axis *)
Definition initial_state : ConstructionState :=
  mkState ((0, 0) :: (1, 0) :: nil) (line_xaxis :: nil).

(** Add fold crease to state *)
Definition add_fold_to_state (st : ConstructionState) (step : FoldStep) : ConstructionState :=
  let new_line := execute_fold_step step in
  mkState (state_points st) (new_line :: state_lines st).

(** Execute fold sequence from state *)
Fixpoint execute_sequence (st : ConstructionState) (seq : FoldSequence) : ConstructionState :=
  match seq with
  | nil => st
  | step :: rest => execute_sequence (add_fold_to_state st step) rest
  end.

(** [O2(p₁,p₂)] *)
Definition midpoint_fold_sequence (p1 p2 : Point) : FoldSequence :=
  FS_O2 p1 p2 :: nil.

(** execute_fold_step(O2(p₁,p₂)) = perp_bisector(p₁,p₂) *)
Lemma midpoint_fold_produces_bisector : forall p1 p2,
  p1 <> p2 ->
  execute_fold_step (FS_O2 p1 p2) = perp_bisector p1 p2.
Proof.
  intros p1 p2 Hneq.
  unfold execute_fold_step, fold_O2, fold_line. simpl.
  reflexivity.
Qed.

(** O6 configuration for ∛a *)
Definition cbrt_construction_setup (a : R) : Point * Line * Point * Line :=
  let p1 := (-1, 0) in
  let l1 := line_yaxis in
  let p2 := (-a, 0) in
  let l2 := {| A := 0; B := 1; C := -2 |} in
  (p1, l1, p2, l2).

(** Fold sequence for ∛a *)
Definition cbrt_fold_sequence (a : R) : FoldSequence :=
  let '(p1, l1, p2, l2) := cbrt_construction_setup a in
  FS_O6 p1 l1 p2 l2 :: nil.

(** O6 configuration for angle trisection *)
Definition trisection_setup (theta : R) : Point * Line * Point * Line :=
  let c := cos theta in
  let p1 := (0, 1) in
  let l1 := line_xaxis in
  let p2 := (0, c) in
  let l2 := {| A := 0; B := 1; C := 1 |} in
  (p1, l1, p2, l2).

(** Fold sequence for trisecting θ *)
Definition trisection_fold_sequence (theta : R) : FoldSequence :=
  let '(p1, l1, p2, l2) := trisection_setup theta in
  FS_O6 p1 l1 p2 l2 :: nil.

(** [O4(p,l)] *)
Definition perpendicular_fold_sequence (p : Point) (l : Line) : FoldSequence :=
  FS_O4 p l :: nil.

(** [O1(p₁,p₂)] *)
Definition line_through_points_sequence (p1 p2 : Point) : FoldSequence :=
  FS_O1 p1 p2 :: nil.

(** Reflect p across fold crease *)
Definition reflect_point_via_fold (p : Point) (step : FoldStep) : Point :=
  reflect_point p (execute_fold_step step).

(** |seq| *)
Definition fold_sequence_length (seq : FoldSequence) : nat := length seq.

(** (0,0) ∈ initial_state *)
Lemma initial_state_has_origin : In (0, 0) (state_points initial_state).
Proof.
  unfold initial_state. simpl. left. reflexivity.
Qed.

(** (1,0) ∈ initial_state *)
Lemma initial_state_has_unit : In (1, 0) (state_points initial_state).
Proof.
  unfold initial_state. simpl. right. left. reflexivity.
Qed.

(** [O3(l₁,l₂)] *)
Definition angle_bisector_fold_sequence (l1 l2 : Line) : FoldSequence :=
  FS_O3 l1 l2 :: nil.

(** [O4(p,l), O4(p, perp_through(p,l))] *)
Definition parallel_through_point_sequence (p : Point) (l : Line) : FoldSequence :=
  let perp := FS_O4 p l in
  let perp_line := execute_fold_step perp in
  perp :: FS_O4 p perp_line :: nil.

(** execute_sequence st [] = st *)
Lemma execute_sequence_nil : forall st,
  execute_sequence st nil = st.
Proof.
  intro st. reflexivity.
Qed.

Lemma execute_sequence_cons : forall st step rest,
  execute_sequence st (step :: rest) =
  execute_sequence (add_fold_to_state st step) rest.
Proof.
  intros. reflexivity.
Qed.

Lemma fold_sequence_length_nil : fold_sequence_length nil = O.
Proof.
  reflexivity.
Qed.

Lemma fold_sequence_length_cons : forall step rest,
  fold_sequence_length (step :: rest) = S (fold_sequence_length rest).
Proof.
  intros. reflexivity.
Qed.

(** Add point to state *)
Definition add_point_to_state (st : ConstructionState) (p : Point) : ConstructionState :=
  mkState (p :: state_points st) (state_lines st).

(** Add l₁ ∩ l₂ to state *)
Definition add_intersection_to_state (st : ConstructionState) (l1 l2 : Line) : ConstructionState :=
  add_point_to_state st (line_intersection l1 l2).

(** Heptagon cubic: t³ + at + b = 0 where cos(2π/7) is a root *)
Definition heptagon_cos_setup : Point * Line * Point * Line :=
  let p1 := (0, 1) in
  let l1 := line_xaxis in
  let p2 := (0, heptagon_cubic_b / 2) in
  let l2 := {| A := 0; B := 1; C := - heptagon_cubic_a / 3 |} in
  (p1, l1, p2, l2).

(** Fold sequence for cos(2π/7) *)
Definition heptagon_cos_fold_sequence : FoldSequence :=
  let '(p1, l1, p2, l2) := heptagon_cos_setup in
  FS_O6 p1 l1 p2 l2 :: nil.

(** Rotate p by angle about origin *)
Definition rotate_point (p : Point) (angle : R) : Point :=
  let x := fst p in
  let y := snd p in
  (x * cos angle - y * sin angle, x * sin angle + y * cos angle).

(** k-th vertex of unit heptagon *)
Definition heptagon_vertex (k : nat) : Point :=
  rotate_point (1, 0) (2 * PI * INR k / 7).

(** All 7 vertices *)
Definition heptagon_vertices : list Point :=
  map heptagon_vertex (seq 0 7).

(** Fold for edge k to k+1 *)
Definition heptagon_edge_fold (k : nat) : FoldStep :=
  FS_O1 (heptagon_vertex k) (heptagon_vertex (S k mod 7)).

(** Complete heptagon construction *)
Definition heptagon_full_sequence : FoldSequence :=
  heptagon_cos_fold_sequence ++
  map heptagon_edge_fold (seq 0 7).

(** |heptagon_vertices| = 7 *)
Lemma heptagon_has_seven_vertices : length heptagon_vertices = 7%nat.
Proof.
  unfold heptagon_vertices. rewrite length_map, length_seq. reflexivity.
Qed.

(** |heptagon_full_sequence| = 8 *)
Lemma heptagon_full_sequence_length :
  fold_sequence_length heptagon_full_sequence = 8%nat.
Proof.
  reflexivity.
Qed.


(** Algebraic characterization of origami-constructible numbers *)

(** Origami numbers: closed under +, -, ×, /, √, and cubic roots *)
Definition GoodPoint (p : Point) : Prop :=
  OrigamiNum (fst p) /\ OrigamiNum (snd p).

(** All coefficients A, B, C are origami-constructible *)
Definition GoodLine (l : Line) : Prop :=
  OrigamiNum (A l) /\ OrigamiNum (B l) /\ OrigamiNum (C l).

(** Crease line is a GoodLine *)
Definition GoodFold (f : Fold) : Prop :=
  GoodLine (fold_line f).

(** (0,0) ∈ GoodPoint *)
Lemma GoodPoint_O : GoodPoint point_O.
Proof. split; constructor. Qed.

(** (1,0) ∈ GoodPoint *)
Lemma GoodPoint_X : GoodPoint point_X.
Proof. split; constructor; constructor. Qed.

(** x-axis ∈ GoodLine *)
Lemma GoodLine_xaxis : GoodLine line_xaxis.
Proof.
  unfold GoodLine, line_xaxis; simpl.
  repeat split; constructor.
Qed.

(** y-axis ∈ GoodLine *)
Lemma GoodLine_yaxis : GoodLine line_yaxis.
Proof.
  unfold GoodLine, line_yaxis; simpl.
  repeat split; constructor.
Qed.

(** GoodPoint p₁ ∧ GoodPoint p₂ → GoodPoint midpoint(p₁,p₂) *)
Lemma GoodPoint_midpoint : forall p1 p2,
  GoodPoint p1 -> GoodPoint p2 -> GoodPoint (midpoint p1 p2).
Proof.
  intros [x1 y1] [x2 y2] [Hx1 Hy1] [Hx2 Hy2].
  unfold midpoint; simpl.
  split.
  - apply Origami_div; [apply ON_add; assumption|apply Origami_two|lra].
  - apply Origami_div; [apply ON_add; assumption|apply Origami_two|lra].
Qed.

(** GoodPoint p₁ ∧ GoodPoint p₂ → GoodLine line_through(p₁,p₂) *)
Lemma GoodLine_through : forall p1 p2,
  GoodPoint p1 -> GoodPoint p2 -> GoodLine (line_through p1 p2).
Proof.
  intros [x1 y1] [x2 y2] [Hx1 Hy1] [Hx2 Hy2].
  unfold line_through; simpl.
  destruct (Req_EM_T x1 x2) as [Heq | Hneq].
  - repeat split; try constructor.
    + apply Origami_neg; assumption.
  - set (a := y1 - y2).
    set (b := x2 - x1).
    set (c := x1 * y2 - x2 * y1).
    repeat split.
    + subst a; apply ON_sub; assumption.
    + subst b; apply ON_sub; assumption.
    + subst c; apply ON_sub.
      * apply ON_mul; assumption.
      * apply ON_mul; assumption.
Qed.

(** GoodPoint p ∧ GoodLine l → GoodLine perp_through(p,l) *)
Lemma GoodLine_perp_through : forall p l,
  GoodPoint p -> GoodLine l -> GoodLine (perp_through p l).
Proof.
  intros [x y] l [Hx Hy] [Ha [Hb Hc]].
  unfold perp_through; simpl.
  destruct (Req_EM_T (A l) 0) as [Ha0 | Han0].
  - repeat split.
    + exact Hb.
    + apply Origami_neg; exact Ha.
    + apply ON_sub; apply ON_mul; assumption.
  - repeat split.
    + exact Hb.
    + apply Origami_neg; exact Ha.
    + apply ON_sub; apply ON_mul; assumption.
Qed.

(** GoodPoint p₁ ∧ GoodPoint p₂ → GoodLine perp_bisector(p₁,p₂) *)
Lemma GoodLine_perp_bisector : forall p1 p2,
  GoodPoint p1 -> GoodPoint p2 -> GoodLine (perp_bisector p1 p2).
Proof.
  intros [x1 y1] [x2 y2] [Hx1 Hy1] [Hx2 Hy2].
  unfold perp_bisector; simpl.
  destruct (Req_EM_T x1 x2) as [Hx | Hx].
  - subst x2.
    destruct (Req_EM_T y1 y2) as [Hy | Hy].
    + subst y2.
      repeat split; try apply ON_1; try apply ON_0.
      apply Origami_neg; exact Hx1.
    + repeat split.
      * constructor; apply Origami_two.
      * apply ON_mul; [apply Origami_two|apply ON_sub; assumption].
      * replace (x1 * x1 + y1 * y1 - x1 * x1 - y2 * y2) with (y1 * y1 - y2 * y2) by ring.
        apply ON_sub; apply ON_mul; assumption.
  - repeat split.
    + apply ON_mul; [apply Origami_two|apply ON_sub; assumption].
    + apply ON_mul; [apply Origami_two|apply ON_sub; assumption].
    + replace (x1 * x1 + y1 * y1 - x2 * x2 - y2 * y2)
      with ((x1 * x1 - x2 * x2) + (y1 * y1 - y2 * y2)) by ring.
      apply ON_add; apply ON_sub; apply ON_mul; assumption.
Qed.

(** GoodLine l₁ ∧ GoodLine l₂ → GoodPoint l₁∩l₂ *)
Lemma GoodPoint_intersection : forall l1 l2,
  GoodLine l1 -> GoodLine l2 -> GoodPoint (line_intersection l1 l2).
Proof.
  intros l1 l2 [Ha1 [Hb1 Hc1]] [Ha2 [Hb2 Hc2]].
  unfold line_intersection; simpl.
  set (D := A l1 * B l2 - A l2 * B l1).
  set (Dx := (- C l1) * B l2 - (- C l2) * B l1).
  set (Dy := A l1 * (- C l2) - A l2 * (- C l1)).
  destruct (Req_EM_T D 0) as [HD0 | HDnz].
  - apply GoodPoint_O.
  - split.
    + apply Origami_div.
      * unfold Dx.
        apply ON_sub.
        -- apply ON_mul; [apply Origami_neg; exact Hc1 | exact Hb2].
        -- apply ON_mul; [apply Origami_neg; exact Hc2 | exact Hb1].
      * replace D with (A l1 * B l2 - A l2 * B l1) by reflexivity.
        apply ON_sub; apply ON_mul; assumption.
      * exact HDnz.
    + apply Origami_div.
      * unfold Dy.
        apply ON_sub.
        -- apply ON_mul; [exact Ha1 | apply Origami_neg; exact Hc2].
        -- apply ON_mul; [exact Ha2 | apply Origami_neg; exact Hc1].
      * replace D with (A l1 * B l2 - A l2 * B l1) by reflexivity.
        apply ON_sub; apply ON_mul; assumption.
      * exact HDnz.
Qed.

(** GoodPoint p₁ ∧ GoodPoint p₂ → GoodLine fold_O2(p₁,p₂) *)
Lemma GoodLine_fold_O2 : forall p1 p2,
  GoodPoint p1 -> GoodPoint p2 -> GoodLine (fold_line (fold_O2 p1 p2)).
Proof.
  intros p1 p2 Hp1 Hp2.
  rewrite fold_line_O2.
  apply GoodLine_perp_bisector; assumption.
Qed.

(** GoodPoint p₁ ∧ GoodPoint p₂ → GoodFold fold_O2(p₁,p₂) *)
Lemma GoodFold_O2 : forall p1 p2,
  GoodPoint p1 -> GoodPoint p2 -> GoodFold (fold_O2 p1 p2).
Proof.
  intros p1 p2 Hp1 Hp2.
  unfold GoodFold.
  apply GoodLine_fold_O2; assumption.
Qed.

(** GoodLine l₁ ∧ GoodLine l₂ → GoodLine fold_O3(l₁,l₂) *)
Lemma GoodLine_fold_O3 : forall l1 l2,
  line_wf l1 -> line_wf l2 ->
  GoodLine l1 -> GoodLine l2 -> GoodLine (fold_line (fold_O3 l1 l2)).
Proof.
  intros l1 l2 Hwf1 Hwf2 [Ha1 [Hb1 Hc1]] [Ha2 [Hb2 Hc2]].
  rewrite fold_line_O3.
  unfold bisector; simpl.
  set (n1 := line_norm l1).
  set (n2 := line_norm l2).
  assert (Hn1_num : OrigamiNum n1).
  { unfold n1, line_norm.
    apply ON_sqrt.
    - apply ON_add; apply ON_mul; assumption.
    - apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
  assert (Hn2_num : OrigamiNum n2).
  { unfold n2, line_norm.
    apply ON_sqrt.
    - apply ON_add; apply ON_mul; assumption.
    - apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
  assert (Hn1_nz : n1 <> 0) by (unfold n1; apply line_norm_nonzero; exact Hwf1).
  assert (Hn2_nz : n2 <> 0) by (unfold n2; apply line_norm_nonzero; exact Hwf2).
  assert (Ha1d : OrigamiNum (A l1 / n1)) by (apply Origami_div; try assumption; exact Hn1_nz).
  assert (Ha2d : OrigamiNum (A l2 / n2)) by (apply Origami_div; try assumption; exact Hn2_nz).
  assert (Hb1d : OrigamiNum (B l1 / n1)) by (apply Origami_div; try assumption; exact Hn1_nz).
  assert (Hb2d : OrigamiNum (B l2 / n2)) by (apply Origami_div; try assumption; exact Hn2_nz).
  assert (Hc1d : OrigamiNum (C l1 / n1)) by (apply Origami_div; try assumption; exact Hn1_nz).
  assert (Hc2d : OrigamiNum (C l2 / n2)) by (apply Origami_div; try assumption; exact Hn2_nz).
  set (a := A l1 / n1 - A l2 / n2).
  set (b := B l1 / n1 - B l2 / n2).
  set (c := C l1 / n1 - C l2 / n2).
  destruct (Req_EM_T a 0) as [Ha0 | Han0].
  - destruct (Req_EM_T b 0) as [Hb0 | Hb0].
    + apply GoodLine_perp_through.
      * apply GoodPoint_intersection; [split; [exact Ha1|split; [exact Hb1|exact Hc1]]|split; [exact Ha2|split; [exact Hb2|exact Hc2]]].
      * split; [exact Ha1|split; [exact Hb1|exact Hc1]].
    + repeat split.
      * subst a; apply ON_sub; assumption.
      * subst b; apply ON_sub; assumption.
      * subst c; apply ON_sub; assumption.
  - repeat split.
    + subst a; apply ON_sub; assumption.
    + subst b; apply ON_sub; assumption.
    + subst c; apply ON_sub; assumption.
Qed.

(** GoodLine l₁ ∧ GoodLine l₂ → GoodFold fold_O3(l₁,l₂) *)
Lemma GoodFold_O3 : forall l1 l2,
  line_wf l1 -> line_wf l2 ->
  GoodLine l1 -> GoodLine l2 -> GoodFold (fold_O3 l1 l2).
Proof.
  intros l1 l2 Hwf1 Hwf2 Hl1 Hl2.
  unfold GoodFold.
  apply GoodLine_fold_O3; assumption.
Qed.



(** GoodPoint p₁ ∧ GoodPoint p₂ → GoodLine fold_O1(p₁,p₂) *)
Lemma GoodLine_fold_O1 : forall p1 p2,
  GoodPoint p1 -> GoodPoint p2 -> GoodLine (fold_line (fold_O1 p1 p2)).
Proof.
  intros p1 p2 Hp1 Hp2.
  rewrite fold_line_O1.
  apply GoodLine_through; assumption.
Qed.

(** GoodPoint p ∧ GoodLine l → GoodLine fold_O4(p,l) *)
Lemma GoodLine_fold_O4 : forall p l,
  GoodPoint p -> GoodLine l -> GoodLine (fold_line (fold_O4 p l)).
Proof.
  intros p l Hp Hl.
  rewrite fold_line_O4.
  apply GoodLine_perp_through; assumption.
Qed.

(** GoodPoint p ∧ GoodLine l → GoodPoint reflect(p,l) *)
Lemma GoodPoint_reflect : forall p l,
  line_wf l ->
  GoodPoint p -> GoodLine l -> GoodPoint (reflect_point p l).
Proof.
  intros [x y] l Hwf [Hx Hy] [Ha [Hb Hc]].
  unfold reflect_point; simpl.
  set (a := A l); set (b := B l); set (c := C l).
  set (d := a * a + b * b).
  assert (Hd : d <> 0) by (unfold d, a, b; apply Rgt_not_eq, line_norm_pos; exact Hwf).
  assert (Hd_num : OrigamiNum d).
  { unfold d, a, b; apply ON_add; apply ON_mul; assumption. }
  assert (Hfactor : OrigamiNum ((a * x + b * y + c) / d)).
  { apply Origami_div; [apply ON_add; [apply ON_add; apply ON_mul; assumption|exact Hc]|exact Hd_num|exact Hd]. }
  split.
  - apply ON_sub; [exact Hx|].
    apply ON_mul; [apply ON_mul; [apply Origami_two|assumption]|exact Hfactor].
  - apply ON_sub; [exact Hy|].
    apply ON_mul; [apply ON_mul; [apply Origami_two|assumption]|exact Hfactor].
Qed.

(** ConstructibleLine l → line_wf l (mutual with ConstructibleFold) *)
Lemma ConstructibleLine_wf : forall l, ConstructibleLine l -> line_wf l
with ConstructibleFold_line_wf_aux : forall f, ConstructibleFold f -> line_wf (fold_line f).
Proof.
  - intros l Hl.
    induction Hl.
    + apply line_xaxis_wf.
    + apply line_yaxis_wf.
    + apply ConstructibleFold_line_wf_aux. exact H.
  - intros f Hf.
    induction Hf.
    + rewrite fold_line_O1. apply line_through_wf.
    + rewrite fold_line_O2. apply perp_bisector_wf.
    + rewrite fold_line_O3. apply bisector_wf; apply ConstructibleLine_wf; assumption.
    + rewrite fold_line_O4. apply perp_through_wf; apply ConstructibleLine_wf; assumption.
    + rewrite fold_line_O5. apply perp_through_wf. apply line_through_wf.
    + rewrite fold_line_O6. apply line_through_wf.
    + unfold fold_O7, fold_O7_corrected. simpl.
      destruct (Req_EM_T (A l1 * B l2 + B l1 * - A l2) 0).
      * apply perp_through_wf; apply ConstructibleLine_wf; assumption.
      * apply perp_bisector_wf.
    + unfold fold_O5_vert; simpl. apply perp_bisector_wf.
    + unfold fold_O6_beloch; simpl. apply beloch_fold_line_wf.
    + unfold fold_O5_general; simpl. apply perp_bisector_wf.
Qed.

(** ConstructibleFold f → line_wf (fold_line f) *)
Lemma ConstructibleFold_line_wf : forall f, ConstructibleFold f -> line_wf (fold_line f).
Proof.
  intros f Hf.
  apply ConstructibleLine_wf.
  apply CL_fold. exact Hf.
Qed.

(** GoodFold f ∧ GoodPoint p → GoodPoint map_point(f,p) *)
Lemma GoodPoint_map_point : forall f p,
  line_wf (fold_line f) ->
  GoodFold f -> GoodPoint p -> GoodPoint (map_point f p).
Proof.
  intros [l] p Hwf Hf Hp; simpl in *.
  unfold GoodFold in Hf.
  apply GoodPoint_reflect; assumption.
Qed.

(** GoodPoint p ∧ GoodLine l → GoodPoint foot(p,l) *)
Lemma GoodPoint_foot : forall p l,
  line_wf l ->
  GoodPoint p -> GoodLine l -> GoodPoint (foot_on_line p l).
Proof.
  intros [x y] l Hwf [Hx Hy] [Ha [Hb Hc]].
  unfold foot_on_line; simpl.
  set (a := A l); set (b := B l); set (c := C l).
  set (d := a * a + b * b).
  assert (Hd_pos : d > 0).
  { unfold d, a, b.
    apply line_norm_pos; exact Hwf. }
  assert (Hd : d <> 0) by lra.
  assert (Hd_num : OrigamiNum d).
  { unfold d, a, b; apply ON_add; apply ON_mul; assumption. }
  assert (Hfactor : OrigamiNum ((a * x + b * y + c) / d)).
  { apply Origami_div; [apply ON_add; [apply ON_add; apply ON_mul; assumption|exact Hc]|exact Hd_num|exact Hd]. }
  split.
  - apply ON_sub; [exact Hx|].
    apply ON_mul; [assumption|exact Hfactor].
  - apply ON_sub; [exact Hy|].
    apply ON_mul; [assumption|exact Hfactor].
Qed.

(** GoodPoint/GoodLine inputs → GoodLine fold_O5 *)
Lemma GoodLine_fold_O5 : forall p1 l p2,
  line_wf l ->
  GoodPoint p1 -> GoodLine l -> GoodPoint p2 ->
  GoodLine (fold_line (fold_O5 p1 l p2)).
Proof.
  intros p1 l p2 Hwf Hp1 Hl Hp2.
  rewrite fold_line_O5.
  unfold fold_O5; simpl.
  pose proof (GoodPoint_foot p1 l Hwf Hp1 Hl) as Hproj.
  pose proof (GoodLine_through p1 (foot_on_line p1 l) Hp1 Hproj) as Haux.
  apply GoodLine_perp_through; assumption.
Qed.

(** GoodPoint/GoodLine inputs → GoodFold fold_O5 *)
Lemma GoodFold_O5 : forall p1 l p2,
  line_wf l ->
  GoodPoint p1 -> GoodLine l -> GoodPoint p2 ->
  GoodFold (fold_O5 p1 l p2).
Proof.
  intros p1 l p2 Hwf Hp1 Hl Hp2.
  unfold GoodFold.
  apply GoodLine_fold_O5; auto.
Qed.

(** GoodPoint/GoodLine inputs → GoodLine fold_O6 *)
Lemma GoodLine_fold_O6 : forall p1 l1 p2 l2,
  line_wf l1 -> line_wf l2 ->
  GoodPoint p1 -> GoodLine l1 -> GoodPoint p2 -> GoodLine l2 ->
  GoodLine (fold_line (fold_O6 p1 l1 p2 l2)).
Proof.
  intros p1 l1 p2 l2 Hwf1 Hwf2 Hp1 Hl1 Hp2 Hl2.
  rewrite fold_line_O6.
  unfold fold_O6; simpl.
  pose proof (GoodPoint_foot p1 l1 Hwf1 Hp1 Hl1) as Hproj1.
  pose proof (GoodPoint_foot p2 l2 Hwf2 Hp2 Hl2) as Hproj2.
  pose proof (GoodPoint_midpoint p1 (foot_on_line p1 l1) Hp1 Hproj1) as Hmid1.
  pose proof (GoodPoint_midpoint p2 (foot_on_line p2 l2) Hp2 Hproj2) as Hmid2.
  apply GoodLine_through; assumption.
Qed.

(** GoodPoint/GoodLine inputs → GoodFold fold_O6 *)
Lemma GoodFold_O6 : forall p1 l1 p2 l2,
  line_wf l1 -> line_wf l2 ->
  GoodPoint p1 -> GoodLine l1 -> GoodPoint p2 -> GoodLine l2 ->
  GoodFold (fold_O6 p1 l1 p2 l2).
Proof.
  intros p1 l1 p2 l2 Hwf1 Hwf2 Hp1 Hl1 Hp2 Hl2.
  unfold GoodFold.
  apply GoodLine_fold_O6; auto.
Qed.

(** GoodPoint/GoodLine inputs → GoodLine fold_O7 *)
Lemma GoodLine_fold_O7 : forall p1 l1 l2,
  GoodPoint p1 -> GoodLine l1 -> GoodLine l2 ->
  GoodLine (fold_line (fold_O7 p1 l1 l2)).
Proof.
  intros p1 l1 l2 Hp1 Hl1 Hl2.
  unfold fold_O7, fold_O7_corrected, fold_line.
  set (dir_x := B l2).
  set (dir_y := - A l2).
  set (p1_x := fst p1).
  set (p1_y := snd p1).
  set (denom := A l1 * dir_x + B l1 * dir_y).
  destruct (Req_EM_T denom 0) as [Heq | Hneq].
  - (* Degenerate case: use perp_through *)
    apply GoodLine_perp_through; assumption.
  - (* General case: perp_bisector of p1 and q *)
    set (t := - (A l1 * p1_x + B l1 * p1_y + C l1) / denom).
    set (q := (p1_x + t * dir_x, p1_y + t * dir_y)).
    assert (Hq: GoodPoint q).
    { split.
      - (* fst q = p1_x + t * dir_x *)
        unfold q. simpl.
        destruct Hp1 as [Hpx Hpy].
        apply ON_add; [exact Hpx|].
        apply ON_mul.
        + (* t is OrigamiNum *)
          apply Origami_div.
          * apply Origami_neg. apply ON_add. apply ON_add.
            -- apply ON_mul; [destruct Hl1 as [Ha1 [Hb1 Hc1]]; exact Ha1 | exact Hpx].
            -- apply ON_mul; [destruct Hl1 as [Ha1 [Hb1 Hc1]]; exact Hb1 | exact Hpy].
            -- destruct Hl1 as [Ha1 [Hb1 Hc1]]. exact Hc1.
          * unfold denom, dir_x, dir_y.
            apply ON_add.
            -- apply ON_mul. destruct Hl1 as [Ha1 [Hb1 Hc1]]. exact Ha1. destruct Hl2 as [Ha2 [Hb2 Hc2]]. exact Hb2.
            -- apply ON_mul. destruct Hl1 as [Ha1 [Hb1 Hc1]]. exact Hb1.
               apply Origami_neg. destruct Hl2 as [Ha2 [Hb2 Hc2]]. exact Ha2.
          * exact Hneq.
        + (* dir_x is OrigamiNum *)
          unfold dir_x. destruct Hl2 as [Ha2 [Hb2 Hc2]]. exact Hb2.
      - (* snd q = p1_y + t * dir_y *)
        unfold q. simpl.
        destruct Hp1 as [Hpx Hpy].
        apply ON_add; [exact Hpy|].
        apply ON_mul.
        + (* t is OrigamiNum *)
          apply Origami_div.
          * apply Origami_neg. apply ON_add. apply ON_add.
            -- apply ON_mul; [destruct Hl1 as [Ha1 [Hb1 Hc1]]; exact Ha1 | exact Hpx].
            -- apply ON_mul; [destruct Hl1 as [Ha1 [Hb1 Hc1]]; exact Hb1 | exact Hpy].
            -- destruct Hl1 as [Ha1 [Hb1 Hc1]]. exact Hc1.
          * unfold denom, dir_x, dir_y.
            apply ON_add.
            -- apply ON_mul. destruct Hl1 as [Ha1 [Hb1 Hc1]]. exact Ha1. destruct Hl2 as [Ha2 [Hb2 Hc2]]. exact Hb2.
            -- apply ON_mul. destruct Hl1 as [Ha1 [Hb1 Hc1]]. exact Hb1.
               apply Origami_neg. destruct Hl2 as [Ha2 [Hb2 Hc2]]. exact Ha2.
          * exact Hneq.
        + (* dir_y is OrigamiNum *)
          unfold dir_y. apply Origami_neg. destruct Hl2 as [Ha2 [Hb2 Hc2]]. exact Ha2. }
    apply GoodLine_perp_bisector; assumption.
Qed.

(** GoodPoint/GoodLine inputs → GoodFold fold_O7 *)
Lemma GoodFold_O7 : forall p1 l1 l2,
  GoodPoint p1 -> GoodLine l1 -> GoodLine l2 ->
  GoodFold (fold_O7 p1 l1 l2).
Proof.
  intros p1 l1 l2 Hp1 Hl1 Hl2.
  unfold GoodFold.
  apply GoodLine_fold_O7; assumption.
Qed.

(** GoodPoint p₁ ∧ GoodPoint p₂ → GoodFold fold_O1(p₁,p₂) *)
Lemma GoodFold_O1 : forall p1 p2,
  GoodPoint p1 -> GoodPoint p2 -> GoodFold (fold_O1 p1 p2).
Proof.
  intros p1 p2 Hp1 Hp2.
  unfold GoodFold.
  apply GoodLine_fold_O1; assumption.
Qed.

(** GoodPoint p ∧ GoodLine l → GoodFold fold_O4(p,l) *)
Lemma GoodFold_O4 : forall p l,
  GoodPoint p -> GoodLine l -> GoodFold (fold_O4 p l).
Proof.
  intros p l Hp Hl.
  unfold GoodFold.
  apply GoodLine_fold_O4; assumption.
Qed.

(** GoodPoint inputs ∧ valid config → GoodPoint O5_vert_image *)
Lemma GoodPoint_O5_vert_image : forall p q c,
  GoodPoint p -> GoodPoint q -> OrigamiNum c ->
  O5_vert_valid p q c ->
  GoodPoint (O5_vert_image p q c).
Proof.
  intros [px py] [qx qy] c [Hpx Hpy] [Hqx Hqy] Hc Hvalid.
  unfold O5_vert_image, O5_vert_image_y. simpl.
  split.
  - exact Hc.
  - apply ON_add.
    + exact Hqy.
    + apply ON_sqrt.
      * set (d2 := (px - qx) * ((px - qx) * 1) + (py - qy) * ((py - qy) * 1)).
        set (dx2 := (c - qx) * ((c - qx) * 1)).
        assert (Hd2_num : OrigamiNum d2).
        { unfold d2.
          apply ON_add; apply ON_mul; try apply ON_mul; try apply ON_sub; try constructor; assumption. }
        assert (Hdx2_num : OrigamiNum dx2).
        { unfold dx2.
          apply ON_mul; try apply ON_mul; try apply ON_sub; try constructor; assumption. }
        apply ON_sub; assumption.
      * unfold O5_vert_valid in Hvalid. simpl in Hvalid.
        replace ((px - qx) * ((px - qx) * 1)) with ((px - qx)^2) by ring.
        replace ((py - qy) * ((py - qy) * 1)) with ((py - qy)^2) by ring.
        replace ((c - qx) * ((c - qx) * 1)) with ((c - qx)^2) by ring.
        lra.
Qed.

(** GoodPoint inputs ∧ valid config → GoodFold fold_O5_vert *)
Lemma GoodFold_O5_vert : forall p q c,
  GoodPoint p -> GoodPoint q -> OrigamiNum c ->
  O5_vert_valid p q c ->
  GoodFold (fold_O5_vert p q c).
Proof.
  intros p q c Hp Hq Hc Hvalid.
  unfold GoodFold, fold_O5_vert. simpl.
  apply GoodLine_perp_bisector.
  - exact Hp.
  - apply GoodPoint_O5_vert_image; assumption.
Qed.

(** t³ + pt + q = 0 ∧ p,q ∈ OrigamiNum → GoodFold fold_O6_beloch(p,q,t) *)
Lemma GoodFold_O6_beloch : forall p q t,
  OrigamiNum p -> OrigamiNum q ->
  t * t * t + p * t + q = 0 ->
  GoodFold (fold_O6_beloch p q t).
Proof.
  intros p q t Hp Hq Hcubic.
  assert (Ht : OrigamiNum t) by (apply (ON_cubic_root p q t Hp Hq Hcubic)).
  unfold GoodFold, fold_O6_beloch, beloch_fold_line; simpl.
  repeat split.
  - exact Ht.
  - apply Origami_neg. constructor.
  - apply Origami_neg. apply ON_mul; assumption.
Qed.

(** r² - d²·‖l‖² ≥ 0 when O5_general_valid *)
Lemma O5_general_h2_nonneg : forall px py l qx qy,
  line_wf l -> O5_general_valid (px, py) l (qx, qy) ->
  let a := A l in let b := B l in let c := C l in
  let r2 := (px - qx)*(px - qx) + (py - qy)*(py - qy) in
  let norm2 := a*a + b*b in
  let d := (a * qx + b * qy + c) / norm2 in
  0 <= r2 - d*d * norm2.
Proof.
  intros px py l qx qy Hwf Hvalid. simpl.
  unfold O5_general_valid in Hvalid. simpl in Hvalid.
  pose proof (line_norm_pos l Hwf) as Hn.
  pose proof (sqrt_lt_R0 (A l * A l + B l * B l) Hn) as Hs.
  pose proof (sqrt_sqrt (A l * A l + B l * B l) (Rlt_le _ _ Hn)) as Hsq.
  pose proof (Rsqr_abs (A l * qx + B l * qy + C l)) as Habs.
  unfold Rsqr in Habs.
  assert (Hvalid' : (A l * qx + B l * qy + C l)*(A l * qx + B l * qy + C l) / (A l * A l + B l * B l) <=
                    (px - qx)*(px - qx) + (py - qy)*(py - qy)).
  { replace (A l * (A l * 1) + B l * (B l * 1)) with (A l * A l + B l * B l) in Hvalid by ring.
    replace (Rabs (A l * qx + B l * qy + C l) / sqrt (A l * A l + B l * B l) *
             (Rabs (A l * qx + B l * qy + C l) / sqrt (A l * A l + B l * B l) * 1)) with
            (Rabs (A l * qx + B l * qy + C l) * Rabs (A l * qx + B l * qy + C l) /
             (sqrt (A l * A l + B l * B l) * sqrt (A l * A l + B l * B l))) in Hvalid
      by (unfold Rdiv; field; lra).
    rewrite <- Habs in Hvalid. rewrite Hsq in Hvalid.
    replace ((px - qx) * ((px - qx) * 1) + (py - qy) * ((py - qy) * 1)) with
            ((px - qx) * (px - qx) + (py - qy) * (py - qy)) in Hvalid by ring.
    exact Hvalid. }
  set (num := A l * qx + B l * qy + C l) in *.
  set (norm := A l * A l + B l * B l) in *.
  assert (Hsimp : num * num * / norm * norm = num * num) by (field; lra).
  unfold Rdiv in Hvalid'.
  assert (H : (px - qx) * (px - qx) + (py - qy) * (py - qy) - num * / norm * (num * / norm) * norm >= 0).
  { replace (num * / norm * (num * / norm) * norm) with (num * num * / norm * norm * / norm) by (field; lra).
    rewrite Hsimp.
    replace (num * num * / norm) with (num * num / norm) by (unfold Rdiv; ring).
    lra. }
  unfold Rdiv. lra.
Qed.

(** GoodPoint/GoodLine inputs ∧ valid config → GoodPoint O5_general_image *)
Lemma GoodPoint_O5_general_image : forall p l q,
  GoodPoint p -> GoodLine l -> GoodPoint q ->
  line_wf l -> O5_general_valid p l q ->
  GoodPoint (O5_general_image p l q).
Proof.
  intros [px py] l [qx qy] [Hpx Hpy] [Ha [Hb Hc]] [Hqx Hqy] Hwf Hvalid.
  unfold O5_general_image; simpl.
  pose proof (line_norm_pos l Hwf) as Hn.
  pose proof (O5_general_h2_nonneg px py l qx qy Hwf Hvalid) as Hh2.
  simpl in Hh2.
  set (a := A l) in *. set (b := B l) in *. set (cc := C l) in *.
  set (norm2 := a*a + b*b) in *.
  set (num := a * qx + b * qy + cc) in *.
  set (d := num / norm2) in *.
  set (r2 := (px - qx)*(px - qx) + (py - qy)*(py - qy)) in *.
  set (h2 := r2 - d*d * norm2) in *.
  assert (Hnorm2 : OrigamiNum norm2) by (unfold norm2, a, b; apply ON_add; apply ON_mul; assumption).
  assert (Hn' : norm2 > 0).
  { unfold norm2, a, b. exact Hn. }
  assert (Hd_num : OrigamiNum d).
  { unfold d, num. apply Origami_div.
    - apply ON_add; [apply ON_add; unfold a, b; apply ON_mul; simpl; assumption|unfold cc; exact Hc].
    - exact Hnorm2.
    - lra. }
  assert (Hr2 : OrigamiNum r2).
  { unfold r2. apply ON_add; apply ON_mul; apply ON_sub; simpl; assumption. }
  assert (Hh2_orig : OrigamiNum h2).
  { unfold h2. apply ON_sub; [exact Hr2|apply ON_mul; [apply ON_mul|]; assumption]. }
  assert (Hsqrt_norm2 : OrigamiNum (sqrt norm2)) by (apply ON_sqrt; [exact Hnorm2|lra]).
  assert (Hsqrt_h2 : OrigamiNum (sqrt h2)) by (apply ON_sqrt; assumption).
  assert (Ht : OrigamiNum (sqrt h2 / sqrt norm2)).
  { apply Origami_div; [exact Hsqrt_h2|exact Hsqrt_norm2|apply Rgt_not_eq; apply sqrt_lt_R0; lra]. }
  split.
  - apply ON_add.
    + apply ON_sub; [simpl; exact Hqx|unfold a; apply ON_mul; [exact Ha|exact Hd_num]].
    + unfold b. apply ON_mul; [exact Hb|exact Ht].
  - apply ON_sub.
    + apply ON_sub; [simpl; exact Hqy|unfold b; apply ON_mul; [exact Hb|exact Hd_num]].
    + unfold a. apply ON_mul; [exact Ha|exact Ht].
Qed.

(** GoodPoint/GoodLine inputs ∧ valid config → GoodFold fold_O5_general *)
Lemma GoodFold_O5_general : forall p l q,
  GoodPoint p -> GoodLine l -> GoodPoint q ->
  line_wf l -> O5_general_valid p l q -> p <> O5_general_image p l q ->
  GoodFold (fold_O5_general p l q).
Proof.
  intros p l q Hp Hl Hq Hwf Hvalid Hneq.
  unfold GoodFold, fold_O5_general; simpl.
  apply GoodLine_perp_bisector.
  - exact Hp.
  - apply GoodPoint_O5_general_image; assumption.
Qed.

(** Mutual fixpoint: ConstructiblePoint/Line/Fold → GoodPoint/Line/Fold *)
Fixpoint ConstructiblePoint_good (p : Point) (Hp : ConstructiblePoint p) {struct Hp} : GoodPoint p :=
  match Hp in ConstructiblePoint p0 return GoodPoint p0 with
  | CP_O => GoodPoint_O
  | CP_X => GoodPoint_X
  | CP_inter l1 l2 Hl1 Hl2 => 
      GoodPoint_intersection l1 l2 
        (ConstructibleLine_good l1 Hl1) 
        (ConstructibleLine_good l2 Hl2)
  | CP_map f p Hf Hp =>
      GoodPoint_map_point f p
        (ConstructibleFold_line_wf_aux f Hf)
        (ConstructibleFold_good f Hf)
        (ConstructiblePoint_good p Hp)
  end

with ConstructibleLine_good (l : Line) (Hl : ConstructibleLine l) {struct Hl} : GoodLine l :=
  match Hl in ConstructibleLine l0 return GoodLine l0 with
  | CL_x => GoodLine_xaxis
  | CL_y => GoodLine_yaxis
  | CL_fold f Hf => ConstructibleFold_good f Hf
  end

with ConstructibleFold_good (f : Fold) (Hf : ConstructibleFold f) {struct Hf} : GoodFold f :=
  match Hf in ConstructibleFold f0 return GoodFold f0 with
  | CF_O1 p1 p2 Hp1 Hp2 => 
      GoodFold_O1 p1 p2 
        (ConstructiblePoint_good p1 Hp1) 
        (ConstructiblePoint_good p2 Hp2)
  | CF_O2 p1 p2 Hp1 Hp2 => 
      GoodFold_O2 p1 p2 
        (ConstructiblePoint_good p1 Hp1) 
        (ConstructiblePoint_good p2 Hp2)
  | CF_O3 l1 l2 Hl1 Hl2 =>
      GoodFold_O3 l1 l2
        (ConstructibleLine_wf l1 Hl1)
        (ConstructibleLine_wf l2 Hl2)
        (ConstructibleLine_good l1 Hl1)
        (ConstructibleLine_good l2 Hl2)
  | CF_O4 p l Hp Hl => 
      GoodFold_O4 p l 
        (ConstructiblePoint_good p Hp) 
        (ConstructibleLine_good l Hl)
  | CF_O5 p1 l p2 Hp1 Hl Hp2 =>
      GoodFold_O5 p1 l p2
        (ConstructibleLine_wf l Hl)
        (ConstructiblePoint_good p1 Hp1)
        (ConstructibleLine_good l Hl)
        (ConstructiblePoint_good p2 Hp2)
  | CF_O6 p1 l1 p2 l2 Hp1 Hl1 Hp2 Hl2 =>
      GoodFold_O6 p1 l1 p2 l2
        (ConstructibleLine_wf l1 Hl1)
        (ConstructibleLine_wf l2 Hl2)
        (ConstructiblePoint_good p1 Hp1)
        (ConstructibleLine_good l1 Hl1)
        (ConstructiblePoint_good p2 Hp2)
        (ConstructibleLine_good l2 Hl2)
  | CF_O7 p1 l1 l2 Hp1 Hl1 Hl2 =>
      GoodFold_O7 p1 l1 l2
        (ConstructiblePoint_good p1 Hp1)
        (ConstructibleLine_good l1 Hl1)
        (ConstructibleLine_good l2 Hl2)
  | CF_O5_vert p q c Hp Hq Hc Hvalid =>
      GoodFold_O5_vert p q c
        (ConstructiblePoint_good p Hp)
        (ConstructiblePoint_good q Hq)
        (proj1 (ConstructiblePoint_good (c, 0) Hc))
        Hvalid
  | CF_O6_beloch p q t Hp Hq Hcubic =>
      GoodFold_O6_beloch p q t
        (proj1 (ConstructiblePoint_good (p, 0) Hp))
        (proj1 (ConstructiblePoint_good (q, 0) Hq))
        Hcubic
  | CF_O5_general p l q Hp Hl Hq Hwf Hvalid Hneq =>
      GoodFold_O5_general p l q
        (ConstructiblePoint_good p Hp)
        (ConstructibleLine_good l Hl)
        (ConstructiblePoint_good q Hq)
        Hwf Hvalid Hneq
  end.

(** ConstructiblePoint p → GoodPoint p *)
Theorem constructible_implies_origami : forall p,
  ConstructiblePoint p -> GoodPoint p.
Proof.
  intros p Hp.
  apply (ConstructiblePoint_good p Hp).
Qed.

(** ConstructibleR x → OrigamiNum x *)
Corollary constructible_R_implies_origami : forall x,
  ConstructibleR x -> OrigamiNum x.
Proof.
  intros x [y Hxy].
  apply constructible_implies_origami in Hxy.
  destruct Hxy as [Hx _].
  exact Hx.
Qed.

(** EuclidNum x ∧ x ≥ 0 → EuclidNum √x *)
Lemma constructible_from_0 : ConstructibleR 0.
Proof.
  exists 0. constructor.
Qed.

(** 1 ∈ ConstructibleR *)
Lemma constructible_from_1 : ConstructibleR 1.
Proof.
  exists 0. constructor.
Qed.

(** OrigamiNum closed under + *)
Lemma line_through_x_axis : forall x1 x2,
  ConstructiblePoint (x1, 0) ->
  ConstructiblePoint (x2, 0) ->
  ConstructibleLine (line_through (x1, 0) (x2, 0)).
Proof.
  intros x1 x2 H1 H2.
  rewrite <- fold_line_O1.
  apply CL_fold.
  apply CF_O1; assumption.
Qed.

(** ConstructiblePoint (xᵢ,0) → ConstructibleLine perp_bisector *)
Lemma perp_bisector_x_axis : forall x1 x2,
  ConstructiblePoint (x1, 0) ->
  ConstructiblePoint (x2, 0) ->
  ConstructibleLine (perp_bisector (x1, 0) (x2, 0)).
Proof.
  intros x1 x2 H1 H2.
  rewrite <- fold_line_O2.
  apply CL_fold.
  apply CF_O2; assumption.
Qed.

(** midpoint((x₁,0),(x₂,0)) = ((x₁+x₂)/2, 0) *)
Lemma midpoint_x_coords : forall x1 x2,
  midpoint (x1, 0) (x2, 0) = ((x1 + x2) / 2, 0).
Proof.
  intros. unfold midpoint. simpl. f_equal. lra.
Qed.

(** midpoint((x₁,0),(x₂,0)) ∈ perp_bisector((x₁,0),(x₂,0)) *)
Lemma perp_bisector_inter_x : forall x1 x2,
  on_line (midpoint (x1, 0) (x2, 0)) (perp_bisector (x1, 0) (x2, 0)).
Proof.
  intros x1 x2.
  unfold on_line, midpoint, perp_bisector. simpl.
  destruct (Req_EM_T x1 x2).
  - subst. destruct (Req_EM_T 0 0); simpl; lra.
  - simpl. unfold Rdiv. nra.
Qed.

(** bisector(x-axis, y-axis) = -x + y = 0 *)
Lemma bisector_xy_coeffs :
  A (bisector line_xaxis line_yaxis) = -1 /\
  B (bisector line_xaxis line_yaxis) = 1 /\
  C (bisector line_xaxis line_yaxis) = 0.
Proof.
  unfold bisector, line_xaxis, line_yaxis, line_norm. simpl.
  unfold sqr. simpl.
  replace (0 * 0 + 1 * 1) with 1 by ring.
  replace (1 * 1 + 0 * 0) with 1 by ring.
  assert (Hsqrt1: sqrt 1 = 1) by apply sqrt_1.
  rewrite Hsqrt1.
  unfold Rdiv.
  rewrite Rinv_1.
  repeat rewrite Rmult_1_r.
  destruct (Req_EM_T (0 - 1) 0) as [H0 | H0].
  - lra.
  - destruct (Req_EM_T (1 - 0) 0) as [H1 | H1].
    + lra.
    + simpl. split; [|split]; ring.
Qed.

(** perp_through((1,0), x-axis) = x - 1 = 0 *)
Lemma perp_X_xaxis_coeffs :
  A (perp_through point_X line_xaxis) = 1 /\
  B (perp_through point_X line_xaxis) = 0 /\
  C (perp_through point_X line_xaxis) = -1.
Proof.
  unfold perp_through, point_X, line_xaxis.
  simpl.
  destruct (Req_EM_T 0 0).
  - simpl. repeat split; ring.
  - exfalso. auto.
Qed.

(** (-x+y=0) ∩ (x-1=0) = (1,1) *)
Lemma inter_bisector_vert : forall l1 l2,
  A l1 = -1 -> B l1 = 1 -> C l1 = 0 ->
  A l2 = 1 -> B l2 = 0 -> C l2 = -1 ->
  line_intersection l1 l2 = (1, 1).
Proof.
  intros l1 l2 Ha1 Hb1 Hc1 Ha2 Hb2 Hc2.
  unfold line_intersection.
  rewrite Ha1, Hb1, Hc1, Ha2, Hb2, Hc2. simpl.
  destruct (Req_dec_T (-1) 0); [exfalso; lra|].
  destruct (Req_dec_T (-1 * 0 - 1 * 1) 0); [exfalso; lra|].
  simpl. f_equal; unfold Rdiv; nra.
Qed.

(** (1,1) ∈ ConstructiblePoint *)
Lemma construct_point_1_1 : ConstructiblePoint (1, 1).
Proof.
  pose proof bisector_xy_coeffs as [Ha1 [Hb1 Hc1]].
  pose proof perp_X_xaxis_coeffs as [Ha2 [Hb2 Hc2]].
  rewrite <- (inter_bisector_vert (bisector line_xaxis line_yaxis)
                                   (perp_through point_X line_xaxis) Ha1 Hb1 Hc1 Ha2 Hb2 Hc2).
  apply CP_inter.
  - rewrite <- fold_line_O3. apply CL_fold. apply CF_O3. apply CL_x. apply CL_y.
  - rewrite <- fold_line_O4. apply CL_fold. apply CF_O4. constructor. apply CL_x.
Qed.

(** 0 ∈ ConstructibleR ∧ 0 ∈ OrigamiNum *)
Theorem construct_0_is_origami_num : ConstructibleR 0 /\ OrigamiNum 0.
Proof.
  split.
  - exists 0. constructor.
  - constructor.
Qed.

(** 1 ∈ ConstructibleR ∧ 1 ∈ OrigamiNum *)
Theorem construct_1_is_origami_num : ConstructibleR 1 /\ OrigamiNum 1.
Proof.
  split.
  - exists 0. constructor.
  - constructor.
Qed.

(** (1,1) ∈ ConstructiblePoint ∧ (1,1) ∈ GoodPoint *)
Theorem construct_pt_1_1_is_good : ConstructiblePoint (1, 1) /\ GoodPoint (1, 1).
Proof.
  split.
  - apply construct_point_1_1.
  - apply constructible_implies_origami. apply construct_point_1_1.
Qed.

(** ConstructibleR x → OrigamiNum x *)
Theorem any_constructible_is_origami : forall x,
  ConstructibleR x -> OrigamiNum x.
Proof.
  apply constructible_R_implies_origami.
Qed.

(** x ∈ OrigamiNum ∧ x ≥ 0 → √x ∈ OrigamiNum *)
Lemma reflect_across_diagonal_1_1 :
  reflect_point (0, 0) (line_through (0, 0) (1, 1)) = (0, 0).
Proof.
  apply reflect_point_on_line.
  apply line_through_on_line_fst.
Qed.

(** reflect((1,0), y=x) = (0,1) *)
Lemma reflect_point_X_across_diagonal :
  reflect_point (1, 0) (line_through (0, 0) (1, 1)) = (0, 1).
Proof.
  unfold reflect_point, line_through. simpl.
  destruct (Req_EM_T 0 1); [exfalso; lra|]. simpl.
  set (a := 0 - 1).
  set (b := 1 - 0).
  set (c := 0 * 1 - 1 * 0).
  assert (Ha: a = -1) by (unfold a; ring).
  assert (Hb: b = 1) by (unfold b; ring).
  assert (Hc: c = 0) by (unfold c; ring).
  rewrite Ha, Hb, Hc.
  assert (Hdenom: (-1) * (-1) + 1 * 1 = 2) by ring.
  rewrite Hdenom.
  assert (Hfactor: ((-1) * 1 + 1 * 0 + 0) / 2 = -1/2) by (unfold Rdiv; field).
  rewrite Hfactor.
  f_equal; unfold Rdiv; field.
Qed.

(** (0,1) ∈ ConstructiblePoint *)
Lemma construct_point_0_1 : ConstructiblePoint (0, 1).
Proof.
  replace (0, 1) with (map_point (fold_O1 (0, 0) (1, 1)) (1, 0)).
  - apply CP_map.
    + apply CF_O1; [constructor | apply construct_point_1_1].
    + constructor.
  - unfold map_point, fold_O1, fold_line. simpl.
    apply reflect_point_X_across_diagonal.
Qed.

(** beloch_P1 = (0,1) ∈ ConstructiblePoint *)
Lemma beloch_P1_constructible : ConstructiblePoint beloch_P1.
Proof.
  unfold beloch_P1. apply construct_point_0_1.
Qed.

(** midpoint((x₁,0), (x₂,0)) has y-coordinate 0 *)
Lemma midpoint_on_x_axis : forall x1 x2,
  snd (midpoint (x1, 0) (x2, 0)) = 0.
Proof.
  intros. unfold midpoint. simpl. unfold Rdiv. ring.
Qed.

(** fst(midpoint((x₁,0), (x₂,0))) = (x₁+x₂)/2 *)
Lemma midpoint_x_coord : forall x1 x2,
  fst (midpoint (x1, 0) (x2, 0)) = (x1 + x2) / 2.
Proof.
  intros. unfold midpoint. simpl. reflexivity.
Qed.

(** midpoint((0,0), (2,0)) = (1,0) *)
Lemma midpoint_0_2 : midpoint (0, 0) (2, 0) = (1, 0).
Proof.
  unfold midpoint. simpl. f_equal; unfold Rdiv; field.
Qed.

(** (1,0) ∈ perp_bisector((0,0), (2,0)) *)
Lemma perp_bisector_of_0_2_passes_through_1_0 :
  on_line (1, 0) (perp_bisector (0, 0) (2, 0)).
Proof.
  unfold on_line, perp_bisector. simpl.
  destruct (Req_EM_T 0 2); [exfalso; lra|]. simpl. ring.
Qed.

(** perp_bisector((0,0), (2,0)) is vertical: A=4, B=0 *)
Lemma perp_bisector_0_2_is_vertical :
  A (perp_bisector (0, 0) (2, 0)) = 2 * 2 /\ B (perp_bisector (0, 0) (2, 0)) = 0.
Proof.
  unfold perp_bisector. simpl.
  destruct (Req_EM_T 0 2); [exfalso; lra|].
  split; simpl; ring.
Qed.

(** perp_bisector((0,0), (2,0)) is the line x = 1 *)
Lemma vertical_line_at_x1 :
  forall x y, A (perp_bisector (0, 0) (2, 0)) * x + B (perp_bisector (0, 0) (2, 0)) * y + C (perp_bisector (0, 0) (2, 0)) = 0 <-> x = 1.
Proof.
  intros x y.
  assert (H: A (perp_bisector (0, 0) (2, 0)) = 4) by (apply perp_bisector_0_2_is_vertical).
  assert (H2: B (perp_bisector (0, 0) (2, 0)) = 0) by (apply perp_bisector_0_2_is_vertical).
  assert (H3: C (perp_bisector (0, 0) (2, 0)) = -4).
  { unfold perp_bisector. simpl.
    destruct (Req_EM_T 0 2); [exfalso; lra|]. simpl. ring. }
  rewrite H, H2, H3.
  split; intro; lra.
Qed.

(** Algebraic simplification of reflection x-coordinate *)
Lemma reflect_0_across_perp_12 : reflect_point (0, 0) (perp_bisector (1, 0) (2, 0)) = (3, 0).
Proof.
  unfold reflect_point, perp_bisector. simpl.
  destruct (Req_EM_T 1 2); [exfalso; lra|]. simpl.
  f_equal; unfold Rdiv; field_simplify; try lra; ring.
Qed.

(** reflect((0,0), x=1) = (2,0) *)
Lemma reflect_0_across_x_eq_1 : reflect_point (0, 0) (perp_bisector (0, 0) (2, 0)) = (2, 0).
Proof.
  unfold reflect_point, perp_bisector. simpl.
  destruct (Req_EM_T 0 2); [exfalso; lra|]. simpl.
  f_equal; unfold Rdiv; field_simplify; try lra; ring.
Qed.

(** perp_through((1,1), x-axis) ∩ x-axis = (1,0) *)
Lemma line_perp_at_1_1_intersects_xaxis_at_1_0 :
  line_intersection (perp_through (1, 1) line_xaxis) line_xaxis = (1, 0).
Proof.
  unfold line_intersection, perp_through, line_xaxis. simpl.
  destruct (Req_EM_T 0 0); [|contradiction]. simpl.
  destruct (Req_EM_T (1 * 1 - 0 * 0) 0); [exfalso; lra|]. simpl.
  destruct (Req_EM_T (1 * 1 - 0 * - 0) 0); [exfalso; lra|]. simpl.
  f_equal.
  - replace (- (0 * 1 - 1 * 1) * 1 - - 0 * - 0) with 1 by ring.
    replace (1 * 1 - 0 * - 0) with 1 by ring.
    unfold Rdiv. replace (1 * / 1) with 1 by (field; lra).
    reflexivity.
  - replace (1 * - 0 - 0 * - (0 * 1 - 1 * 1)) with 0 by ring.
    replace (1 * 1 - 0 * - 0) with 1 by ring.
    unfold Rdiv. replace (0 * / 1) with 0 by ring.
    reflexivity.
Qed.

(** perp_through((1,1), x-axis) ∈ ConstructibleLine *)
Lemma line_perp_at_1_1_is_constructible :
  ConstructibleLine (perp_through (1, 1) line_xaxis).
Proof.
  rewrite <- fold_line_O4.
  apply CL_fold.
  apply CF_O4.
  - apply construct_point_1_1.
  - apply CL_x.
Qed.

(** (1,0) ∈ ConstructiblePoint *)
Lemma construct_point_1_0 : ConstructiblePoint (1, 0).
Proof.
  replace (1, 0) with (line_intersection (perp_through (1, 1) line_xaxis) line_xaxis).
  - apply CP_inter.
    + apply line_perp_at_1_1_is_constructible.
    + apply CL_x.
  - apply line_perp_at_1_1_intersects_xaxis_at_1_0.
Qed.

(** x ≠ y → perp_bisector((x,0), (y,0)) is vertical *)
Lemma perp_bisector_vertical : forall x y,
  x <> y -> A (perp_bisector (x, 0) (y, 0)) <> 0.
Proof.
  intros x y Hneq.
  unfold perp_bisector. simpl.
  destruct (Req_EM_T x y); [contradiction|].
  simpl. lra.
Qed.

(** reflect((0,0), x=x₀) = (2x₀, 0) *)
Lemma reflect_origin_across_vertical : forall x,
  reflect_point (0, 0) (perp_through (x, 0) line_xaxis) = (2 * x, 0).
Proof.
  intro x. unfold reflect_point, perp_through, line_xaxis. simpl.
  destruct (Req_EM_T 0 0); [|contradiction]. simpl.
  f_equal; field.
Qed.

(** (x,0) constructible → (2x,0) constructible *)
Lemma double_xaxis_constructible : forall x,
  ConstructiblePoint (x, 0) ->
  ConstructiblePoint (2 * x, 0).
Proof.
  intros x Hx.
  replace (2 * x, 0) with (map_point (fold_O4 (x, 0) line_xaxis) (0, 0)).
  - apply CP_map; [apply CF_O4; [exact Hx | apply CL_x] | constructor].
  - unfold map_point, fold_O4, fold_line. apply reflect_origin_across_vertical.
Qed.

(** reflect((x,0), y-axis) = (-x, 0) *)
Lemma reflect_across_yaxis : forall x,
  reflect_point (x, 0) line_yaxis = (- x, 0).
Proof.
  intro x. unfold reflect_point, line_yaxis. simpl. f_equal; field.
Qed.

(** fold_O4(origin, x-axis) = y-axis *)
Lemma fold_O4_origin_xaxis_is_yaxis :
  fold_line (fold_O4 point_O line_xaxis) = line_yaxis.
Proof.
  unfold fold_O4, fold_line, perp_through, point_O, line_xaxis, line_yaxis. simpl.
  destruct (Req_EM_T 0 0); [|contradiction]. simpl. f_equal; ring.
Qed.

(** (x,0) constructible → (-x,0) constructible *)
Lemma neg_xaxis_constructible : forall x,
  ConstructiblePoint (x, 0) -> ConstructiblePoint (- x, 0).
Proof.
  intros x Hx.
  replace (- x, 0) with (map_point (fold_O4 point_O line_xaxis) (x, 0)).
  - apply CP_map; [apply CF_O4; [constructor | apply CL_x] | exact Hx].
  - unfold map_point. rewrite fold_O4_origin_xaxis_is_yaxis. apply reflect_across_yaxis.
Qed.

(** reflect((x,0), x=a) = (2a-x, 0) *)
Lemma reflect_xaxis_across_vertical : forall x a,
  reflect_point (x, 0) (perp_through (a, 0) line_xaxis) = (2 * a - x, 0).
Proof.
  intros. unfold reflect_point, perp_through, line_xaxis. simpl.
  destruct (Req_EM_T 0 0); [|contradiction]. simpl. f_equal; field.
Qed.

(** reflect((z,0), perp_bisector((x,0),(y,0))) = (x+y-z, 0) *)
Lemma reflect_across_perp_bisector_xaxis : forall x y z,
  x <> y ->
  reflect_point (z, 0) (perp_bisector (x, 0) (y, 0)) = (x + y - z, 0).
Proof.
  intros x y z Hneq.
  unfold reflect_point, perp_bisector. simpl.
  destruct (Req_EM_T x y); [contradiction|]. simpl.
  f_equal; field; lra.
Qed.

(** x ≠ y ∧ (x,0),(y,0) constructible → (x+y,0) constructible *)
Lemma add_xaxis_constructible_neq : forall x y,
  x <> y ->
  ConstructiblePoint (x, 0) ->
  ConstructiblePoint (y, 0) ->
  ConstructiblePoint (x + y, 0).
Proof.
  intros x y Hneq Hx Hy.
  replace (x + y, 0) with (map_point (fold_O2 (x, 0) (y, 0)) (0, 0)).
  - apply CP_map.
    + apply CF_O2; assumption.
    + constructor.
  - unfold map_point, fold_O2, fold_line.
    rewrite reflect_across_perp_bisector_xaxis by assumption. f_equal; ring.
Qed.

(** (x,0),(y,0) constructible → (x+y,0) constructible *)
Lemma add_xaxis_constructible : forall x y,
  ConstructiblePoint (x, 0) ->
  ConstructiblePoint (y, 0) ->
  ConstructiblePoint (x + y, 0).
Proof.
  intros x y Hx Hy.
  destruct (Req_EM_T x y) as [Heq | Hneq].
  - subst. replace (y + y) with (2 * y) by ring.
    apply double_xaxis_constructible. exact Hy.
  - apply add_xaxis_constructible_neq; assumption.
Qed.

(** (x,0),(y,0) constructible → (x-y,0) constructible *)
Lemma sub_xaxis_constructible : forall x y,
  ConstructiblePoint (x, 0) ->
  ConstructiblePoint (y, 0) ->
  ConstructiblePoint (x - y, 0).
Proof.
  intros x y Hx Hy.
  replace (x - y) with (x + (- y)) by ring.
  apply add_xaxis_constructible.
  - exact Hx.
  - apply neg_xaxis_constructible. exact Hy.
Qed.

(** reflect((x,y), y=x) = (y,x) *)
Lemma reflect_across_diagonal : forall x y,
  reflect_point (x, y) (line_through (0, 0) (1, 1)) = (y, x).
Proof.
  intros x y.
  unfold reflect_point, line_through. simpl.
  destruct (Req_EM_T 0 1); [lra|]. simpl.
  f_equal; field.
Qed.

(** y = x ∈ ConstructibleLine *)
Lemma diagonal_line_constructible : ConstructibleLine (line_through (0, 0) (1, 1)).
Proof.
  rewrite <- fold_line_O1. apply CL_fold. apply CF_O1; [constructor | apply construct_point_1_1].
Qed.

(** (x,y) constructible → (y,x) constructible *)
Lemma swap_coords_constructible : forall x y,
  ConstructiblePoint (x, y) -> ConstructiblePoint (y, x).
Proof.
  intros x y H.
  replace (y, x) with (map_point (fold_O1 (0, 0) (1, 1)) (x, y)).
  - apply CP_map; [apply CF_O1; [constructor | apply construct_point_1_1] | exact H].
  - unfold map_point, fold_O1, fold_line. apply reflect_across_diagonal.
Qed.

(** (y,0) constructible → (0,y) constructible *)
Lemma yaxis_from_xaxis : forall y,
  ConstructiblePoint (y, 0) -> ConstructiblePoint (0, y).
Proof.
  intros y H. apply swap_coords_constructible. exact H.
Qed.

(** (0,-1) ∈ ConstructiblePoint *)
Lemma construct_point_0_neg1 : ConstructiblePoint (0, -1).
Proof.
  apply swap_coords_constructible.
  apply neg_xaxis_constructible. constructor.
Qed.

(** (x,0) constructible → line x=x₀ constructible *)
Lemma vertical_at_constructible : forall x,
  ConstructiblePoint (x, 0) -> ConstructibleLine (perp_through (x, 0) line_xaxis).
Proof.
  intros x Hx. rewrite <- fold_line_O4. apply CL_fold. apply CF_O4; [exact Hx | apply CL_x].
Qed.

(** (0,y) constructible → line y=y₀ constructible *)
Lemma horizontal_at_constructible : forall y,
  ConstructiblePoint (0, y) -> ConstructibleLine (perp_through (0, y) line_yaxis).
Proof.
  intros y Hy. rewrite <- fold_line_O4. apply CL_fold. apply CF_O4; [exact Hy | apply CL_y].
Qed.

(** perp_through((1,0), x-axis) = {A:=1, B:=0, C:=-1} *)
Lemma vertical_at_1 : perp_through (1, 0) line_xaxis = {| A := 1; B := 0; C := -1 |}.
Proof.
  unfold perp_through, line_xaxis. simpl. f_equal; ring.
Qed.

(** perp_through((0,y), y-axis) = {A:=0, B:=-1, C:=y} *)
Lemma horizontal_at_y : forall y, perp_through (0, y) line_yaxis = {| A := 0; B := -1; C := y |}.
Proof.
  intro y. unfold perp_through, line_yaxis. simpl. f_equal; ring.
Qed.

(** (x=1) ∩ (y=c) = (1,c) *)
Lemma intersection_vert_horiz : forall y,
  line_intersection (perp_through (1, 0) line_xaxis) (perp_through (0, y) line_yaxis) = (1, y).
Proof.
  intro y. unfold line_intersection, perp_through, line_xaxis, line_yaxis. simpl.
  match goal with |- context [Req_EM_T ?e 0] => destruct (Req_EM_T e 0) as [H|Hne] end.
  - exfalso. lra.
  - unfold Rdiv. f_equal; field; lra.
Qed.

(** (y,0) constructible → (1,y) constructible *)
Lemma point_1_y_constructible : forall y,
  ConstructiblePoint (y, 0) -> ConstructiblePoint (1, y).
Proof.
  intros y Hy.
  rewrite <- intersection_vert_horiz.
  apply CP_inter.
  - apply vertical_at_constructible. constructor.
  - apply horizontal_at_constructible. apply yaxis_from_xaxis. exact Hy.
Qed.

(** (y,0) constructible → line through (0,0) and (1,y) constructible *)
Lemma line_through_origin_1y : forall y,
  ConstructiblePoint (y, 0) -> ConstructibleLine (line_through (0, 0) (1, y)).
Proof.
  intros y Hy.
  rewrite <- fold_line_O1. apply CL_fold. apply CF_O1.
  - constructor.
  - apply point_1_y_constructible. exact Hy.
Qed.

(** y ≠ 0 → line(origin, (1,y)) ∩ (x=x₀) = (x₀, x₀·y) *)
Lemma intersection_slope_vertical : forall x y,
  y <> 0 ->
  line_intersection (line_through (0, 0) (1, y)) (perp_through (x, 0) line_xaxis) = (x, x * y).
Proof.
  intros x y Hyne.
  unfold line_intersection, line_through, perp_through, line_xaxis. simpl.
  destruct (Req_EM_T 0 1) as [H01|_]; [lra|]. simpl.
  match goal with |- context [Req_EM_T ?e 0] => destruct (Req_EM_T e 0) as [H|Hne] end.
  - exfalso. lra.
  - unfold Rdiv. f_equal; field; lra.
Qed.

(** y ≠ 0 ∧ (x,0),(y,0) constructible → (x, x·y) constructible *)
Lemma point_x_xy_constructible : forall x y,
  y <> 0 ->
  ConstructiblePoint (x, 0) ->
  ConstructiblePoint (y, 0) ->
  ConstructiblePoint (x, x * y).
Proof.
  intros x y Hyne Hx Hy.
  rewrite <- intersection_slope_vertical by assumption.
  apply CP_inter.
  - apply line_through_origin_1y. exact Hy.
  - apply vertical_at_constructible. exact Hx.
Qed.

(** (y=b) ∩ (y-axis) = (0,b) *)
Lemma horizontal_yaxis_intersection : forall a b,
  line_intersection (perp_through (a, b) line_yaxis) line_yaxis = (0, b).
Proof.
  intros a b. unfold line_intersection, perp_through, line_yaxis. simpl.
  match goal with |- context [Req_EM_T ?e 0] => destruct (Req_EM_T e 0) as [H|Hne] end.
  - exfalso. lra.
  - apply injective_projections; unfold fst, snd; field; lra.
Qed.

(** (a,b) constructible → (0,b) constructible *)
Lemma project_to_yaxis : forall a b,
  ConstructiblePoint (a, b) -> ConstructiblePoint (0, b).
Proof.
  intros a b Hab.
  rewrite <- (horizontal_yaxis_intersection a b).
  apply CP_inter.
  - rewrite <- fold_line_O4. apply CL_fold. apply CF_O4; [exact Hab | apply CL_y].
  - apply CL_y.
Qed.

(** y ≠ 0 ∧ (x,0),(y,0) constructible → (x·y,0) constructible *)
Lemma mul_xaxis_constructible_neq : forall x y,
  y <> 0 ->
  ConstructiblePoint (x, 0) ->
  ConstructiblePoint (y, 0) ->
  ConstructiblePoint (x * y, 0).
Proof.
  intros x y Hyne Hx Hy.
  apply swap_coords_constructible.
  apply (project_to_yaxis x (x * y)).
  apply point_x_xy_constructible; assumption.
Qed.

(** (x,0),(y,0) constructible → (x·y,0) constructible *)
Lemma mul_xaxis_constructible : forall x y,
  ConstructiblePoint (x, 0) ->
  ConstructiblePoint (y, 0) ->
  ConstructiblePoint (x * y, 0).
Proof.
  intros x y Hx Hy.
  destruct (Req_EM_T y 0) as [Hy0 | Hyne].
  - subst. replace (x * 0) with 0 by ring. constructor.
  - apply mul_xaxis_constructible_neq; assumption.
Qed.

(** x ≠ 0 → line(origin, (1,x)) ∩ (y=1) = (1/x, 1) *)
Lemma intersection_origin_slope_horizontal : forall x,
  x <> 0 ->
  line_intersection (line_through (0, 0) (1, x)) (perp_through (0, 1) line_yaxis) = (1/x, 1).
Proof.
  intros x Hxne.
  unfold line_intersection, line_through, perp_through, line_yaxis. simpl.
  destruct (Req_EM_T 0 1) as [H|_]; [lra|]. simpl.
  match goal with |- context [Req_EM_T ?e 0] => destruct (Req_EM_T e 0) as [H|Hne] end.
  - exfalso. lra.
  - apply injective_projections; unfold fst, snd; field; lra.
Qed.

(** (a,b) constructible → (a,0) constructible *)
Lemma project_to_xaxis : forall a b,
  ConstructiblePoint (a, b) -> ConstructiblePoint (a, 0).
Proof.
  intros a b Hab.
  apply swap_coords_constructible.
  apply (project_to_yaxis b a).
  apply swap_coords_constructible. exact Hab.
Qed.

(** y ≠ 0 ∧ (x,0),(y,0) constructible → (x/y,0) constructible *)
Lemma div_xaxis_constructible : forall x y,
  y <> 0 ->
  ConstructiblePoint (x, 0) ->
  ConstructiblePoint (y, 0) ->
  ConstructiblePoint (x / y, 0).
Proof.
  intros x y Hyne Hx Hy.
  replace (x / y) with (x * (1/y)) by (field; lra).
  apply mul_xaxis_constructible; [exact Hx|].
  apply (project_to_xaxis (1/y) 1).
  rewrite <- (intersection_origin_slope_horizontal y Hyne).
  apply CP_inter.
  - apply line_through_origin_1y. exact Hy.
  - apply horizontal_at_constructible. apply construct_point_0_1.
Qed.

(** (x=x₀) ∩ (y=y₀) = (x₀,y₀) *)
Lemma intersection_vert_at_horiz_at : forall x y,
  line_intersection (perp_through (x, 0) line_xaxis) (perp_through (0, y) line_yaxis) = (x, y).
Proof.
  intros x y.
  unfold line_intersection, perp_through, line_xaxis, line_yaxis. simpl.
  match goal with |- context [Req_EM_T ?e 0] => destruct (Req_EM_T e 0) as [H|Hne] end.
  - exfalso. lra.
  - unfold Rdiv. f_equal; field; lra.
Qed.

(** (x,0),(0,y) constructible → (x,y) constructible *)
Lemma point_xy_constructible : forall x y,
  ConstructiblePoint (x, 0) -> ConstructiblePoint (0, y) ->
  ConstructiblePoint (x, y).
Proof.
  intros x y Hx Hy.
  rewrite <- intersection_vert_at_horiz_at.
  apply CP_inter.
  - apply vertical_at_constructible. exact Hx.
  - apply horizontal_at_constructible. exact Hy.
Qed.

(** (p,0),(q,0) constructible → beloch_P2(p,q) = (q,p) constructible *)
Lemma beloch_P2_constructible : forall p q,
  ConstructiblePoint (p, 0) -> ConstructiblePoint (q, 0) ->
  ConstructiblePoint (beloch_P2 p q).
Proof.
  intros p q Hp Hq.
  unfold beloch_P2.
  apply point_xy_constructible.
  - exact Hq.
  - apply yaxis_from_xaxis. exact Hp.
Qed.

(** beloch_L2(q) = x = -q *)
Lemma beloch_L2_eq_perp : forall q,
  beloch_L2 q = perp_through (-q, 0) line_xaxis.
Proof.
  intro q. unfold beloch_L2, perp_through, line_xaxis. simpl. f_equal; ring.
Qed.

(** (q,0) constructible → beloch_L2(q) constructible *)
Lemma beloch_L2_constructible : forall q,
  ConstructiblePoint (q, 0) -> ConstructibleLine (beloch_L2 q).
Proof.
  intros q Hq.
  rewrite beloch_L2_eq_perp.
  apply vertical_at_constructible.
  apply neg_xaxis_constructible. exact Hq.
Qed.

(** k ≠ 0 → p ∈ {A,B,C} ⟺ p ∈ {kA,kB,kC} *)
Lemma on_line_scale : forall p a b c k,
  k <> 0 ->
  on_line p {| A := a; B := b; C := c |} <->
  on_line p {| A := k * a; B := k * b; C := k * c |}.
Proof.
  intros [x y] a b c k Hk. unfold on_line. simpl. split; intro H; nra.
Qed.

(** p ∈ beloch_L1 ⟺ p ∈ perp_through((0,-1), y-axis) *)
Lemma beloch_L1_equiv_perp : forall p,
  on_line p beloch_L1 <-> on_line p (perp_through (0, -1) line_yaxis).
Proof.
  intros [x y].
  assert (Hperp: perp_through (0, -1) line_yaxis = {| A := 0; B := -1; C := -1 |}).
  { unfold perp_through, line_yaxis. simpl. f_equal; ring. }
  rewrite Hperp.
  unfold beloch_L1, on_line. simpl. split; intro H; lra.
Qed.

(** t³+pt+q=0 → Beloch config constructible and fold satisfies O6 *)
Theorem O6_beloch_geometric_justification : forall p q t,
  ConstructiblePoint (p, 0) ->
  ConstructiblePoint (q, 0) ->
  t * t * t + p * t + q = 0 ->
  ConstructiblePoint beloch_P1 /\
  ConstructiblePoint (beloch_P2 p q) /\
  ConstructibleLine (beloch_L2 q) /\
  satisfies_O6_constraint (fold_O6_beloch p q t) beloch_P1 beloch_L1 (beloch_P2 p q) (beloch_L2 q).
Proof.
  intros p q t Hp Hq Hcubic.
  split; [apply beloch_P1_constructible|].
  split; [apply beloch_P2_constructible; assumption|].
  split; [apply beloch_L2_constructible; exact Hq|].
  apply beloch_fold_satisfies_O6. exact Hcubic.
Qed.

(** (x,0) constructible → (1+x,0) constructible *)
Lemma construct_1_plus_x : forall x,
  ConstructiblePoint (x, 0) -> ConstructiblePoint (1 + x, 0).
Proof.
  intros x Hx.
  replace (1 + x) with (x + 1) by ring.
  apply add_xaxis_constructible; [exact Hx | constructor].
Qed.

(** (2,0) ∈ ConstructiblePoint *)
Lemma construct_2_0 : ConstructiblePoint (2, 0).
Proof.
  replace 2 with (1 + 1) by ring.
  apply construct_1_plus_x. constructor.
Qed.

(** x = 2 *)
Definition line_vert_2 : Line := perp_through (2, 0) line_xaxis.

Lemma line_vert_2_wf : line_wf line_vert_2.
Proof.
  unfold line_vert_2. apply perp_through_wf. exact line_xaxis_wf.
Qed.

Lemma line_vert_2_constructible : ConstructibleLine line_vert_2.
Proof.
  unfold line_vert_2.
  rewrite <- fold_line_O4.
  apply CL_fold. apply CF_O4.
  - exact construct_2_0.
  - apply CL_x.
Qed.

(** O5 constraint: q ∈ crease ∧ reflect(p, crease) ∈ l *)
Definition satisfies_O5_constraint (f : Fold) (p : Point) (l : Line) (q : Point) : Prop :=
  on_line q (fold_line f) /\ on_line (reflect_point p (fold_line f)) l.

(** (1, √x) ∈ line_through((1+x,0), (1,√x)) *)
Lemma geometric_mean_fold_line : forall x,
  0 < x ->
  let fold_ln := line_through (1 + x, 0) (1, sqrt x) in
  on_line (1, sqrt x) fold_ln.
Proof.
  intros x Hpos fold_ln.
  unfold fold_ln.
  apply line_through_on_line_snd.
Qed.

(** x > 0 → (1, √x) ≠ (1+x, 0) *)
Lemma geometric_mean_line_wf : forall x,
  0 < x -> line_wf (line_through (1 + x, 0) (1, sqrt x)).
Proof.
  intros x Hpos.
  apply line_through_wf.
Qed.

(** Explicit form of geometric mean construction line *)
Lemma geometric_mean_line_form : forall x,
  0 < x ->
  line_through (1 + x, 0) (1, sqrt x) =
  {| A := - sqrt x; B := - x; C := (1 + x) * sqrt x |}.
Proof.
  intros x Hpos.
  unfold line_through. simpl.
  destruct (Req_EM_T (1 + x) 1) as [Heq|Hneq].
  - exfalso. lra.
  - f_equal; ring.
Qed.

(** x > 0 → reflect(origin, geometric_mean_line) = (2, 2√x) *)
Lemma reflect_origin_geometric_mean : forall x,
  0 < x ->
  reflect_point (0, 0) (line_through (1 + x, 0) (1, sqrt x)) = (2, 2 * sqrt x).
Proof.
  intros x Hpos.
  rewrite geometric_mean_line_form by lra.
  unfold reflect_point. simpl.
  assert (Hsqrt_sq: sqrt x * sqrt x = x) by (apply sqrt_sqrt; lra).
  assert (Hdenom: (- sqrt x) * (- sqrt x) + (- x) * (- x) = x + x * x).
  { replace ((- sqrt x) * (- sqrt x)) with (sqrt x * sqrt x) by ring.
    rewrite Hsqrt_sq. ring. }
  assert (Hdenom_pos: x + x * x > 0) by nra.
  assert (Hdenom_nz: x + x * x <> 0) by lra.
  assert (Hx_nz: x <> 0) by lra.
  assert (Hfactor: ((- sqrt x) * 0 + (- x) * 0 + (1 + x) * sqrt x) / (x + x * x) = sqrt x / x).
  { replace ((- sqrt x) * 0 + (- x) * 0 + (1 + x) * sqrt x) with ((1 + x) * sqrt x) by ring.
    replace (x + x * x) with (x * (1 + x)) by ring.
    field. lra. }
  rewrite Hdenom. rewrite Hfactor.
  assert (Hgoal_x: 0 - 2 * (- sqrt x) * (sqrt x / x) = 2).
  { replace (0 - 2 * (- sqrt x) * (sqrt x / x)) with (2 * (sqrt x * sqrt x) / x) by (field; lra).
    rewrite Hsqrt_sq. field. lra. }
  assert (Hgoal_y: 0 - 2 * (- x) * (sqrt x / x) = 2 * sqrt x).
  { replace (0 - 2 * (- x) * (sqrt x / x)) with (2 * sqrt x) by (field; lra).
    reflexivity. }
  f_equal; lra.
Qed.

(** (x,0) constructible → (1+x,0) constructible *)
Lemma construct_1_plus_x_point : forall x,
  ConstructiblePoint (x, 0) -> ConstructiblePoint (1 + x, 0).
Proof.
  intros x Hx.
  apply add_xaxis_constructible.
  - constructor.
  - exact Hx.
Qed.

(** (-1,0) ∈ ConstructiblePoint *)
Lemma construct_neg1_0 : ConstructiblePoint (-1, 0).
Proof.
  apply neg_xaxis_constructible. constructor.
Qed.

(** (0,1) ∈ ConstructiblePoint *)
Lemma construct_0_1 : ConstructiblePoint (0, 1).
Proof.
  exact construct_point_0_1.
Qed.

(** x ≠ 0 → line_through((0,1), (x,0)) = {A:=1, B:=x, C:=-x} *)
Lemma line_through_0_1_x_0 : forall x,
  x <> 0 ->
  line_through (0, 1) (x, 0) = {| A := 1; B := x; C := -x |}.
Proof.
  intros x Hxnz.
  unfold line_through. simpl.
  destruct (Req_EM_T 0 x) as [H|_]; [exfalso; lra|].
  f_equal; ring.
Qed.

(** (x,0) constructible → line((0,1),(x,0)) constructible *)
Lemma line_0_1_to_x_0_constructible : forall x,
  ConstructiblePoint (x, 0) ->
  ConstructibleLine (line_through (0, 1) (x, 0)).
Proof.
  intros x Hx.
  rewrite <- fold_line_O1. apply CL_fold. apply CF_O1.
  - exact construct_0_1.
  - exact Hx.
Qed.

(** (x,0) constructible → perp_through((1,0), line((0,1),(x,0))) constructible *)
Lemma perp_at_1_0_to_line_constructible : forall x,
  ConstructiblePoint (x, 0) ->
  ConstructibleLine (perp_through (1, 0) (line_through (0, 1) (x, 0))).
Proof.
  intros x Hx.
  rewrite <- fold_line_O4. apply CL_fold. apply CF_O4.
  - exact construct_point_1_0.
  - apply line_0_1_to_x_0_constructible. exact Hx.
Qed.

(** x ≠ 0 → perp_through((1,0), line((0,1),(x,0))) explicit form *)
Lemma perp_through_1_0_line_form : forall x,
  x <> 0 ->
  perp_through (1, 0) (line_through (0, 1) (x, 0)) = {| A := x; B := -1; C := -x |}.
Proof.
  intros x Hxnz.
  rewrite line_through_0_1_x_0 by assumption.
  unfold perp_through. simpl.
  destruct (Req_EM_T 1 0) as [H|_]; [lra|].
  f_equal; ring.
Qed.

(** x ≠ 0 → intersection of line and its perpendicular through (1,0) *)
Lemma intersection_two_lines_formula : forall x,
  x <> 0 ->
  line_intersection (line_through (0, 1) (x, 0)) (perp_through (1, 0) (line_through (0, 1) (x, 0)))
  = (x * (1 + x) / (1 + x * x), x * (x - 1) / (1 + x * x)).
Proof.
  intros x Hxnz.
  rewrite perp_through_1_0_line_form by assumption.
  rewrite line_through_0_1_x_0 by assumption.
  unfold line_intersection. simpl.
  assert (Hdenom: 1 * (-1) - x * x <> 0).
  { assert (H: 1 + x * x > 0) by (apply Rplus_lt_le_0_compat; [lra | apply Rle_0_sqr]).
    lra. }
  destruct (Req_EM_T (1 * -1 - x * x) 0) as [H|_]; [contradiction|].
  assert (Hdenompos: 1 + x * x > 0) by (apply Rplus_lt_le_0_compat; [lra | apply Rle_0_sqr]).
  f_equal.
  - unfold Rdiv. field. lra.
  - unfold Rdiv. field. lra.
Qed.

(** y-coord of O5 image: qy + √(dist(p,q)² - (lx-qx)²) *)
Definition O5_image_y (px py qx qy lx : R) : R :=
  let d := sqrt ((px - qx)^2 + (py - qy)^2) in
  let dx := lx - qx in
  qy + sqrt (d^2 - dx^2).

(** O5 fold for vertical line x = l_vertical_x *)
Definition fold_O5_correct (p : Point) (l_vertical_x : R) (q : Point) : Line :=
  let qx := fst q in
  let qy := snd q in
  let px := fst p in
  let py := snd p in
  let d := sqrt ((px - qx)^2 + (py - qy)^2) in
  let dx := l_vertical_x - qx in
  let p'y := qy + sqrt (d^2 - dx^2) in
  let p' := (l_vertical_x, p'y) in
  perp_bisector p p'.

(** √4 = 2 *)
Lemma sqrt_O5_image_point : forall x,
  0 < x ->
  O5_image_y 0 0 (1 + x) 0 2 = 2 * sqrt x.
Proof.
  intros x Hpos.
  unfold O5_image_y.
  replace ((0 - (1 + x)) ^ 2 + (0 - 0) ^ 2) with ((1 + x) ^ 2) by ring.
  rewrite sqrt_pow2 by lra.
  replace (2 - (1 + x)) with (1 - x) by ring.
  replace ((1 + x) ^ 2 - (1 - x) ^ 2) with (4 * x) by ring.
  rewrite sqrt_mult by lra.
  rewrite sqrt_4_eq.
  ring.
Qed.

(** x > 0 → O5 fold image y-coordinate = 2√x *)
Definition O5_sqrt_fold_line (x : R) : Line :=
  perp_bisector (0, 0) (2, 2 * sqrt x).

(** x > 0 → (1+x, 0) ∈ O5_sqrt_fold_line(x) *)
Lemma O5_sqrt_fold_passes_through_1px : forall x,
  0 < x ->
  on_line (1 + x, 0) (O5_sqrt_fold_line x).
Proof.
  intros x Hpos.
  unfold O5_sqrt_fold_line, on_line, perp_bisector. simpl.
  destruct (Req_EM_T 0 2) as [H|_]; [lra|].
  assert (Hsqrt_pos: 0 < sqrt x) by (apply sqrt_lt_R0; lra).
  destruct (Req_EM_T 0 (2 * sqrt x)) as [H|_]; [lra|].
  simpl.
  replace (2 * (2 - 0)) with 4 by ring.
  replace (2 * (2 * sqrt x - 0)) with (4 * sqrt x) by ring.
  replace (0 * 0 + 0 * 0 - 2 * 2 - 2 * sqrt x * (2 * sqrt x)) with (- 4 - 4 * (sqrt x * sqrt x)) by ring.
  rewrite sqrt_sqrt by lra.
  ring.
Qed.

(** x > 0 → reflect(origin, O5_sqrt_fold_line(x)) = (2, 2√x) *)
Lemma O5_sqrt_fold_reflects_origin : forall x,
  0 < x ->
  reflect_point (0, 0) (O5_sqrt_fold_line x) = (2, 2 * sqrt x).
Proof.
  intros x Hpos.
  unfold O5_sqrt_fold_line.
  apply perp_bisector_reflects_to_other.
  assert (Hsqrt_pos: 0 < sqrt x) by (apply sqrt_lt_R0; lra).
  intro H. injection H as H1 H2. lra.
Qed.

(** x > 0 → O5 validity condition for sqrt construction *)
Lemma O5_sqrt_validity : forall x,
  0 < x -> O5_vert_valid (0, 0) (1 + x, 0) 2.
Proof.
  intros x Hpos.
  unfold O5_vert_valid. simpl.
  unfold pow. simpl.
  assert (H: (2 - (1 + x)) * ((2 - (1 + x)) * 1) <=
             (0 - (1 + x)) * ((0 - (1 + x)) * 1) + (0 - 0) * ((0 - 0) * 1)).
  { nra. }
  exact H.
Qed.

(** x > 0 → O5_vert_image(origin, (1+x,0), 2) = (2, 2√x) *)
Lemma O5_vert_image_eq_sqrt : forall x,
  0 < x ->
  O5_vert_image (0, 0) (1 + x, 0) 2 = (2, 2 * sqrt x).
Proof.
  intros x Hpos.
  unfold O5_vert_image, O5_vert_image_y. simpl.
  f_equal.
  replace ((0 - (1 + x)) * ((0 - (1 + x)) * 1) + (0 - 0) * ((0 - 0) * 1))
    with ((1 + x)^2) by ring.
  replace ((2 - (1 + x)) * ((2 - (1 + x)) * 1)) with ((1 - x)^2) by ring.
  replace ((1 + x) ^ 2 - (1 - x) ^ 2) with (4 * x) by ring.
  rewrite sqrt_4x_eq by lra.
  ring.
Qed.

(** x > 0 → fold_O5_vert = O5_sqrt_fold_line *)
Lemma fold_O5_vert_eq_sqrt : forall x,
  0 < x ->
  fold_line (fold_O5_vert (0, 0) (1 + x, 0) 2) = O5_sqrt_fold_line x.
Proof.
  intros x Hpos.
  unfold fold_O5_vert, O5_sqrt_fold_line, fold_line.
  f_equal.
  apply O5_vert_image_eq_sqrt. lra.
Qed.

(** x > 0 ∧ (x,0) constructible → (2, 2√x) constructible *)
Lemma O5_image_constructible : forall x,
  0 < x ->
  ConstructiblePoint (x, 0) ->
  ConstructiblePoint (2, 2 * sqrt x).
Proof.
  intros x Hpos Hx.
  assert (Hq: ConstructiblePoint (1 + x, 0)).
  { apply construct_1_plus_x. exact Hx. }
  assert (Hc: ConstructiblePoint (2, 0)) by exact construct_2_0.
  assert (Hvalid: O5_vert_valid (0, 0) (1 + x, 0) 2) by (apply O5_sqrt_validity; lra).
  assert (Hfold: ConstructibleFold (fold_O5_vert (0, 0) (1 + x, 0) 2)).
  { apply CF_O5_vert; [constructor | exact Hq | exact Hc | exact Hvalid]. }
  assert (Himg_eq: map_point (fold_O5_vert (0, 0) (1 + x, 0) 2) (0, 0) = (2, 2 * sqrt x)).
  { unfold map_point. rewrite fold_O5_vert_eq_sqrt by lra.
    apply O5_sqrt_fold_reflects_origin. lra. }
  rewrite <- Himg_eq.
  apply CP_map.
  - exact Hfold.
  - constructor.
Qed.

(** x > 0 ∧ (x,0) constructible → (√x,0) constructible *)
Lemma sqrt_xaxis_constructible_pos : forall x,
  0 < x ->
  ConstructiblePoint (x, 0) ->
  ConstructiblePoint (sqrt x, 0).
Proof.
  intros x Hpos Hx.
  assert (H2sqrtx_0: ConstructiblePoint (2 * sqrt x, 0)).
  { apply swap_coords_constructible.
    apply project_to_yaxis with (a := 2).
    apply O5_image_constructible; assumption. }
  replace (sqrt x) with ((2 * sqrt x) / 2) by (field; lra).
  apply div_xaxis_constructible; [lra | exact H2sqrtx_0 | exact construct_2_0].
Qed.

(** x ≥ 0 ∧ (x,0) constructible → (√x,0) constructible *)
Lemma sqrt_xaxis_constructible : forall x,
  0 <= x ->
  ConstructiblePoint (x, 0) ->
  ConstructiblePoint (sqrt x, 0).
Proof.
  intros x Hpos Hx.
  destruct (Req_dec x 0) as [Hx0 | Hxpos].
  - subst. replace (sqrt 0) with 0 by (symmetry; apply sqrt_0). constructor.
  - apply sqrt_xaxis_constructible_pos; [lra | exact Hx].
Qed.

(** t ≠ 0 → beloch_fold_line(t) ∩ x-axis = (t,0) *)
Lemma beloch_fold_xaxis_intersection : forall t,
  t <> 0 ->
  line_intersection (beloch_fold_line t) line_xaxis = (t, 0).
Proof.
  intros t Ht.
  unfold line_intersection, beloch_fold_line, line_xaxis; simpl.
  assert (Hsimp: t * 1 - -1 * 0 = t) by ring.
  destruct (Req_EM_T (t * 1 - -1 * 0) 0) as [Heq|_].
  - rewrite Hsimp in Heq. contradiction.
  - assert (Hsimp2: t * 1 - 0 * -1 = t) by ring.
    destruct (Req_dec_T (t * 1 - 0 * -1) 0) as [Heq2|_].
    + rewrite Hsimp2 in Heq2. contradiction.
    + apply injective_projections; simpl; unfold Rdiv.
      * replace (- - (t * t) * 1 - - 0 * -1) with (t * t) by ring.
        rewrite Hsimp2. field. lra.
      * replace (t * - 0 - 0 * - - (t * t)) with 0 by ring.
        ring.
Qed.

(** Cubic roots are constructible via O6 (Beloch fold) *)
Lemma cubic_root_xaxis_constructible : forall p q t,
  t <> 0 ->
  ConstructiblePoint (p, 0) ->
  ConstructiblePoint (q, 0) ->
  t * t * t + p * t + q = 0 ->
  ConstructiblePoint (t, 0).
Proof.
  intros p q t Ht Hp Hq Hcubic.
  assert (Hfold_line_eq: fold_line (fold_O6_beloch p q t) = beloch_fold_line t).
  { unfold fold_O6_beloch, fold_line. reflexivity. }
  assert (Hintersect: line_intersection (fold_line (fold_O6_beloch p q t)) line_xaxis = (t, 0)).
  { rewrite Hfold_line_eq. apply beloch_fold_xaxis_intersection. exact Ht. }
  rewrite <- Hintersect.
  apply CP_inter.
  - apply CL_fold. apply CF_O6_beloch; assumption.
  - apply CL_x.
Qed.

(** EuclidNum x → ConstructibleR x *)
Theorem EuclidNum_implies_ConstructibleR : forall x,
  EuclidNum x -> ConstructibleR x.
Proof.
  intros x H. induction H.
  - exists 0. constructor.
  - exists 0. constructor.
  - destruct IHEuclidNum1 as [y1 H1]. destruct IHEuclidNum2 as [y2 H2].
    exists 0. apply add_xaxis_constructible.
    + apply (project_to_xaxis x y1). exact H1.
    + apply (project_to_xaxis y y2). exact H2.
  - destruct IHEuclidNum1 as [y1 H1]. destruct IHEuclidNum2 as [y2 H2].
    exists 0. apply sub_xaxis_constructible.
    + apply (project_to_xaxis x y1). exact H1.
    + apply (project_to_xaxis y y2). exact H2.
  - destruct IHEuclidNum1 as [y1 H1]. destruct IHEuclidNum2 as [y2 H2].
    exists 0. apply mul_xaxis_constructible.
    + apply (project_to_xaxis x y1). exact H1.
    + apply (project_to_xaxis y y2). exact H2.
  - destruct IHEuclidNum as [y1 H1].
    exists 0. replace (/ x) with (1 / x) by (field; assumption).
    apply div_xaxis_constructible; try assumption.
    + constructor.
    + apply (project_to_xaxis x y1). exact H1.
  - destruct IHEuclidNum as [y1 H1].
    exists 0. apply sqrt_xaxis_constructible; try assumption.
    apply (project_to_xaxis x y1). exact H1.
Qed.

(** OrigamiNum x → ConstructibleR x *)
Theorem OrigamiNum_implies_ConstructibleR : forall x,
  OrigamiNum x -> ConstructibleR x.
Proof.
  intros x H. induction H.
  - exists 0. constructor.
  - exists 0. constructor.
  - destruct IHOrigamiNum1 as [y1 H1]. destruct IHOrigamiNum2 as [y2 H2].
    exists 0. apply add_xaxis_constructible.
    + apply (project_to_xaxis x y1). exact H1.
    + apply (project_to_xaxis y y2). exact H2.
  - destruct IHOrigamiNum1 as [y1 H1]. destruct IHOrigamiNum2 as [y2 H2].
    exists 0. apply sub_xaxis_constructible.
    + apply (project_to_xaxis x y1). exact H1.
    + apply (project_to_xaxis y y2). exact H2.
  - destruct IHOrigamiNum1 as [y1 H1]. destruct IHOrigamiNum2 as [y2 H2].
    exists 0. apply mul_xaxis_constructible.
    + apply (project_to_xaxis x y1). exact H1.
    + apply (project_to_xaxis y y2). exact H2.
  - destruct IHOrigamiNum as [y1 H1].
    exists 0. replace (/ x) with (1 / x) by (field; assumption).
    apply div_xaxis_constructible; try assumption.
    + constructor.
    + apply (project_to_xaxis x y1). exact H1.
  - destruct IHOrigamiNum as [y1 H1].
    exists 0. apply sqrt_xaxis_constructible; try assumption.
    apply (project_to_xaxis x y1). exact H1.
  - destruct IHOrigamiNum1 as [ya Ha]. destruct IHOrigamiNum2 as [yb Hb].
    destruct (Req_dec r 0) as [Hr0|Hrn0].
    + subst r. exists 0. constructor.
    + exists 0. apply cubic_root_xaxis_constructible with a b; try assumption.
      * apply (project_to_xaxis a ya). exact Ha.
      * apply (project_to_xaxis b yb). exact Hb.
Qed.



(** (1,0) ∈ ConstructiblePoint *)
Example point_X_constructible : ConstructiblePoint point_X.
Proof.
  constructor.
Qed.

(** line(O,X) ∈ ConstructibleLine *)
Example line_OX_constructible : ConstructibleLine (line_through point_O point_X).
Proof.
  rewrite <- fold_line_O1.
  apply CL_fold.
  apply CF_O1; constructor.
Qed.

(** 1 ∈ ConstructibleR *)
Example one_constructible : ConstructibleR 1.
Proof.
  exists 0.
  constructor.
Qed.

(** √2 ∈ OrigamiNum *)
Definition sqrt_2_point : Point :=
  line_intersection (fold_line (fold_O4 point_X line_xaxis))
                    (fold_line (fold_O4 point_X line_yaxis)).

(** sqrt_2_point ∈ ConstructiblePoint *)
Example sqrt_2_point_constructible : ConstructiblePoint sqrt_2_point.
Proof.
  unfold sqrt_2_point.
  apply CP_inter.
  - apply CL_fold.
    apply CF_O4.
    + constructor.
    + apply CL_x.
  - apply CL_fold.
    apply CF_O4.
    + constructor.
    + apply CL_y.
Qed.
(** perp_through(X, x-axis) = (A=1, B=0, C=-1) *)
Lemma perp_x_at_X :
  A (perp_through point_X line_xaxis) = 1 /\
  B (perp_through point_X line_xaxis) = 0 /\
  C (perp_through point_X line_xaxis) = -1.
Proof.
  unfold perp_through, point_X, line_xaxis.
  simpl.
  destruct (Req_EM_T 0 0).
  - simpl. repeat split; ring.
  - exfalso. auto.
Qed.

(** perp_through(X, y-axis) = (A=0, B=-1, C=0) *)
Lemma perp_y_at_X :
  A (perp_through point_X line_yaxis) = 0 /\
  B (perp_through point_X line_yaxis) = -1 /\
  C (perp_through point_X line_yaxis) = 0.
Proof.
  unfold perp_through, point_X, line_yaxis.
  simpl.
  destruct (Req_EM_T 1 0).
  - exfalso. lra.
  - simpl. repeat split; ring.
Qed.

(** /(-1) = -1 *)
Lemma line_inter_fst_1 : forall l1 l2,
  A l1 = 1 -> B l1 = 0 -> C l1 = -1 ->
  A l2 = 0 -> B l2 = -1 -> C l2 = 0 ->
  fst (line_intersection l1 l2) = 1.
Proof.
  intros l1 l2 Ha1 Hb1 Hc1 Ha2 Hb2 Hc2.
  unfold line_intersection.
  rewrite Ha1, Hb1, Hc1, Ha2, Hb2, Hc2. simpl.
  destruct (Req_dec_T (-1) 0); [exfalso; lra|].
  destruct (Req_dec_T (1 * -1 - 0 * 0) 0); [exfalso; lra|].
  simpl. apply inter_x_coord.
Qed.

(** (1 · -0 - 0 · -(-1)) · /(1 · -1 - 0 · 0) = 0 *)
Lemma line_inter_snd_0 : forall l1 l2,
  A l1 = 1 -> B l1 = 0 -> C l1 = -1 ->
  A l2 = 0 -> B l2 = -1 -> C l2 = 0 ->
  snd (line_intersection l1 l2) = 0.
Proof.
  intros l1 l2 Ha1 Hb1 Hc1 Ha2 Hb2 Hc2.
  unfold line_intersection.
  rewrite Ha1, Hb1, Hc1, Ha2, Hb2, Hc2. simpl.
  destruct (Req_dec_T (-1) 0); [exfalso; lra|].
  destruct (Req_dec_T (1 * -1 - 0 * 0) 0); [exfalso; lra|].
  simpl. apply inter_y_coord.
Qed.


(** fst(sqrt_2_point), snd(sqrt_2_point) ∈ OrigamiNum *)
Lemma sqrt_2_point_good : GoodPoint sqrt_2_point.
Proof.
  unfold sqrt_2_point.
  apply GoodPoint_intersection.
  - apply GoodLine_fold_O4.
    + apply GoodPoint_X.
    + apply GoodLine_xaxis.
  - apply GoodLine_fold_O4.
    + apply GoodPoint_X.
    + apply GoodLine_yaxis.
Qed.


(** perp_bisector(O,X) ∩ x-axis *)
Definition point_half : Point :=
  line_intersection (perp_bisector point_O point_X) line_xaxis.

(** point_half ∈ ConstructiblePoint *)
Example point_half_constructible : ConstructiblePoint point_half.
Proof.
  unfold point_half.
  rewrite <- fold_line_O2.
  apply CP_inter.
  - apply CL_fold.
    apply CF_O2; constructor.
  - apply CL_x.
Qed.

(** fst(point_half), snd(point_half) ∈ OrigamiNum *)
Lemma point_half_good : GoodPoint point_half.
Proof.
  unfold point_half.
  apply GoodPoint_intersection.
  - apply GoodLine_perp_bisector; [apply GoodPoint_O | apply GoodPoint_X].
  - apply GoodLine_xaxis.
Qed.

(** 1/2 ∈ OrigamiNum *)
Definition compute_midpoint (p1 p2 : Point) : Point :=
  midpoint p1 p2.

(** midpoint(O,X) = (1/2, 0) *)
Example compute_half_point : compute_midpoint point_O point_X = (1/2, 0).
Proof.
  unfold compute_midpoint, midpoint, point_O, point_X.
  simpl.
  f_equal; field.
Qed.

(** Alias for perp_bisector *)
Definition compute_perpbis (p1 p2 : Point) : Line :=
  perp_bisector p1 p2.

(** sqrt_2_point ∈ ConstructiblePoint *)
Lemma compute_sqrt2_approx : ConstructiblePoint sqrt_2_point.
Proof.
  apply sqrt_2_point_constructible.
Qed.


(** Continuity of origami operations *)

(** x = y → √x = √y *)
Lemma dist_via_dist2 : forall p q : Point,
  dist p q = sqrt (dist2 p q).
Proof.
  intros [x1 y1] [x2 y2].
  unfold dist, dist2, sqr.
  simpl.
  reflexivity.
Qed.

(** reflect_point(·,l) is uniformly continuous (isometry: δ = ε) *)
Lemma reflect_point_continuous_in_point : forall (l : Line) (p0 : Point) (eps : R),
  line_wf l ->
  eps > 0 ->
  exists delta : R, delta > 0 /\
    forall p : Point,
      dist p p0 < delta ->
      dist (reflect_point p l) (reflect_point p0 l) < eps.
Proof.
  intros l p0 eps Hwf Heps.
  exists eps. split; [exact Heps|].
  intros p Hdist.
  rewrite dist_via_dist2 in *.
  pose proof (reflection_is_isometry p p0 l Hwf) as Hiso.
  apply sqrt_equal in Hiso.
  rewrite <- Hiso.
  exact Hdist.
Qed.

(** map_point(f,·) is uniformly continuous *)
Corollary map_point_continuous : forall (f : Fold) (p0 : Point) (eps : R),
  line_wf (fold_line f) ->
  eps > 0 ->
  exists delta : R, delta > 0 /\
    forall p : Point,
      dist p p0 < delta ->
      dist (map_point f p) (map_point f p0) < eps.
Proof.
  intros [l] p0 eps Hwf Heps.
  unfold map_point; simpl.
  apply (reflect_point_continuous_in_point l p0 eps Hwf Heps).
Qed.


(** Origami numbers ⟺ field extensions of degree 2^a · 3^b over ℚ (Alperin-Lang 2000) *)

(** Euclidean field extension degrees: 2ⁿ *)
Definition in_quadratic_field (x : R) (r : R) : Prop :=
  exists p q : R, is_rational p /\ is_rational q /\ x = p + q * sqrt r.

(** ℚ ⊂ ℚ(√r) *)
Lemma in_quadratic_field_rational : forall x r,
  is_rational x -> in_quadratic_field x r.
Proof.
  intros x r Hx.
  exists x, 0. repeat split.
  - exact Hx.
  - exists 0%Z, 1%Z. split; [lia | simpl; field].
  - ring.
Qed.

(** r ≥ 0 ∧ √r ≠ 0 → r > 0 *)
Lemma cbrt2_not_in_rational_quadratic_field : forall r,
  r >= 0 -> is_rational r -> ~ in_quadratic_field cbrt2 r.
Proof.
  intros r Hr Hr_rat [p [q [Hp [Hq Heq]]]].
  assert (Hcbrt2_pos : cbrt2 > 0) by (apply cbrt_pos_positive; lra).
  assert (Hcube : cbrt2 * cbrt2 * cbrt2 = 2) by (unfold cbrt2; apply cbrt_spec).
  destruct (Req_dec q 0) as [Hq0 | Hqne0].
  - rewrite Hq0 in Heq. rewrite Rmult_0_l, Rplus_0_r in Heq.
    apply cbrt2_not_rational. rewrite Heq. exact Hp.
  - destruct (Req_dec (sqrt r) 0) as [Hsqrt0 | Hsqrtne0].
    + rewrite Hsqrt0 in Heq. rewrite Rmult_0_r, Rplus_0_r in Heq.
      apply cbrt2_not_rational. rewrite Heq. exact Hp.
    + assert (Hr_pos : r > 0) by (apply sqrt_pos_from_ne0; assumption).
      assert (Hcube_expand : (p + q * sqrt r) * (p + q * sqrt r) * (p + q * sqrt r) = 2).
      { rewrite <- Heq. exact Hcube. }
      rewrite cube_in_quadratic_field in Hcube_expand by exact Hr_pos.
      set (A := p*p*p + 3*p*q*q*r) in Hcube_expand.
      set (B := 3*p*p*q + q*q*q*r) in Hcube_expand.
      assert (Hirrational_coeff : B = 0).
      { destruct (Req_dec B 0) as [Hz | Hnz]; [exact Hz|].
        exfalso.
        assert (Hsqrt_expr : sqrt r = (2 - A) / B).
        { unfold Rdiv. apply Rmult_eq_reg_r with B; [|exact Hnz].
          rewrite Rmult_assoc. rewrite Rinv_l by exact Hnz.
          rewrite Rmult_1_r. lra. }
        assert (Hppp : is_rational (p*p*p)) by (apply rational_mul; [apply rational_mul|]; assumption).
        assert (H3 : is_rational 3) by (exists 3%Z, 1%Z; split; [lia|simpl;field]).
        assert (H3pqqr : is_rational (3*p*q*q*r)).
        { apply rational_mul. apply rational_mul. apply rational_mul. apply rational_mul.
          exact H3. exact Hp. exact Hq. exact Hq. exact Hr_rat. }
        assert (HA : is_rational A) by (unfold A; apply rational_add; assumption).
        assert (H3ppq : is_rational (3*p*p*q)).
        { apply rational_mul. apply rational_mul. apply rational_mul.
          exact H3. exact Hp. exact Hp. exact Hq. }
        assert (Hqqqr : is_rational (q*q*q*r)).
        { apply rational_mul. apply rational_mul. apply rational_mul.
          exact Hq. exact Hq. exact Hq. exact Hr_rat. }
        assert (HB : is_rational B) by (unfold B; apply rational_add; assumption).
        assert (Hsqrt_rat : is_rational (sqrt r)).
        { rewrite Hsqrt_expr.
          apply rational_mul.
          - apply rational_sub. exists 2%Z, 1%Z; split; [lia|simpl;field]. exact HA.
          - apply rational_inv; assumption. }
        apply cbrt2_not_rational.
        rewrite Heq. apply rational_add; [exact Hp|apply rational_mul; [exact Hq|exact Hsqrt_rat]]. }
      unfold B in Hirrational_coeff.
      assert (Hr_neg : r <= 0) by (apply irrational_coeff_zero_implies_r_neg with p q; assumption).
      lra.
Qed.

(** ∛2 ≠ √r for any rational r ≥ 0 *)
Lemma quadratic_field_add : forall x y r,
  in_quadratic_field x r -> in_quadratic_field y r -> in_quadratic_field (x + y) r.
Proof.
  intros x y r [px [qx [Hpx [Hqx Hx]]]] [py [qy [Hpy [Hqy Hy]]]].
  exists (px + py), (qx + qy). repeat split.
  - apply rational_add; assumption.
  - apply rational_add; assumption.
  - rewrite Hx, Hy. ring.
Qed.

(** ℚ(√r) closed under - *)
Lemma quadratic_field_sub : forall x y r,
  in_quadratic_field x r -> in_quadratic_field y r -> in_quadratic_field (x - y) r.
Proof.
  intros x y r [px [qx [Hpx [Hqx Hx]]]] [py [qy [Hpy [Hqy Hy]]]].
  exists (px - py), (qx - qy). repeat split.
  - apply rational_sub; assumption.
  - apply rational_sub; assumption.
  - rewrite Hx, Hy. ring.
Qed.

(** ℚ(√r) closed under × *)
Lemma quadratic_field_mul : forall x y r,
  r >= 0 -> is_rational r ->
  in_quadratic_field x r -> in_quadratic_field y r -> in_quadratic_field (x * y) r.
Proof.
  intros x y r Hr Hr_rat [px [qx [Hpx [Hqx Hx]]]] [py [qy [Hpy [Hqy Hy]]]].
  exists (px * py + qx * qy * r), (px * qy + qx * py). repeat split.
  - apply rational_add. apply rational_mul; assumption.
    apply rational_mul. apply rational_mul; assumption. assumption.
  - apply rational_add; apply rational_mul; assumption.
  - rewrite Hx, Hy.
    destruct (Rle_or_lt r 0) as [Hrle | Hrgt].
    + assert (Hr0 : r = 0) by lra. rewrite Hr0. rewrite sqrt_0. ring.
    + set (s := sqrt r).
      assert (Hsq : s * s = r) by (unfold s; apply sqrt_sqrt; lra).
      replace ((px + qx * s) * (py + qy * s)) with
        (px * py + qx * qy * (s * s) + (px * qy + qx * py) * s) by ring.
      rewrite Hsq. ring.
Qed.

(** (p + q√r)(p - q√r) = p² - q²r *)
Lemma O5_general_image_on_line : forall p l q,
  line_wf l -> on_line (O5_general_image p l q) l.
Proof.
  intros p l q Hwf.
  unfold O5_general_image, on_line. simpl.
  assert (Hnorm_pos : A l * A l + B l * B l > 0) by (apply line_norm_pos; exact Hwf).
  assert (Hnorm_nz : A l * A l + B l * B l <> 0) by lra.
  assert (Hsqrt_nz : sqrt (A l * A l + B l * B l) <> 0).
  { apply Rgt_not_eq. apply sqrt_lt_R0. exact Hnorm_pos. }
  field. split; assumption.
Qed.

(** |x|² = x² *)
Lemma O5_general_valid_h2_nonneg : forall p l q,
  line_wf l -> O5_general_valid p l q ->
  let a := A l in let b := B l in let c := C l in
  let qx := fst q in let qy := snd q in
  let px := fst p in let py := snd p in
  let norm2 := a * a + b * b in
  let d := (a * qx + b * qy + c) / norm2 in
  let r2 := (px - qx)^2 + (py - qy)^2 in
  0 <= r2 - d^2 * norm2.
Proof.
  intros p l q Hwf Hvalid.
  simpl.
  unfold O5_general_valid in Hvalid. simpl in Hvalid.
  assert (Hnorm_pos : A l * A l + B l * B l > 0) by (apply line_norm_pos; exact Hwf).
  assert (Hsqrt_sq : sqrt (A l * A l + B l * B l) * sqrt (A l * A l + B l * B l) = A l * A l + B l * B l).
  { apply sqrt_sqrt. lra. }
  replace (A l * (A l * 1) + B l * (B l * 1)) with (A l * A l + B l * B l) in Hvalid by ring.
  replace ((fst p - fst q) * ((fst p - fst q) * 1) + (snd p - snd q) * ((snd p - snd q) * 1))
    with ((fst p - fst q)^2 + (snd p - snd q)^2) in Hvalid by ring.
  set (dist_line := Rabs (A l * fst q + B l * snd q + C l) / sqrt (A l * A l + B l * B l)) in Hvalid.
  assert (Hdist_sq : dist_line * dist_line = (A l * fst q + B l * snd q + C l)^2 / (A l * A l + B l * B l)).
  { unfold dist_line, Rdiv.
    replace (Rabs (A l * fst q + B l * snd q + C l) * / sqrt (A l * A l + B l * B l) *
             (Rabs (A l * fst q + B l * snd q + C l) * / sqrt (A l * A l + B l * B l)))
      with ((Rabs (A l * fst q + B l * snd q + C l) * Rabs (A l * fst q + B l * snd q + C l)) *
            (/ sqrt (A l * A l + B l * B l) * / sqrt (A l * A l + B l * B l))) by ring.
    rewrite Rabs_sqr_eq.
    rewrite <- Rinv_mult.
    rewrite Hsqrt_sq. ring. }
  replace (dist_line * (dist_line * 1)) with (dist_line * dist_line) in Hvalid by ring.
  rewrite Hdist_sq in Hvalid.
  assert (Hineq: (A l * fst q + B l * snd q + C l) ^ 2 <=
                 ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2) * (A l * A l + B l * B l)).
  { apply Rmult_le_reg_r with (/ (A l * A l + B l * B l)).
    - apply Rinv_0_lt_compat. lra.
    - rewrite Rmult_assoc. rewrite Rinv_r by lra. rewrite Rmult_1_r.
      unfold Rdiv in Hvalid. exact Hvalid. }
  replace (((A l * fst q + B l * snd q + C l) / (A l * A l + B l * B l)) ^ 2 *
           (A l * A l + B l * B l))
    with ((A l * fst q + B l * snd q + C l) ^ 2 / (A l * A l + B l * B l)) by (field; lra).
  assert (H1: (A l * fst q + B l * snd q + C l) ^ 2 / (A l * A l + B l * B l) <=
              (fst p - fst q) ^ 2 + (snd p - snd q) ^ 2).
  { apply Rmult_le_reg_r with (A l * A l + B l * B l).
    - lra.
    - unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by lra. rewrite Rmult_1_r.
      replace ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2) with
              (((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2)) by ring.
      replace ((A l * fst q + B l * snd q + C l) ^ 2) with
              ((fst q * A l + B l * snd q + C l) ^ 2) by ring.
      rewrite Rmult_comm. exact Hineq. }
  replace ((fst p - fst q) * ((fst p - fst q) * 1) + (snd p - snd q) * ((snd p - snd q) * 1))
    with ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2) by ring.
  set (expr := (A l * fst q + B l * snd q + C l) / (A l * A l + B l * B l)).
  replace (expr * (expr * 1)) with (expr ^ 2) by ring.
  unfold expr.
  replace (((A l * fst q + B l * snd q + C l) / (A l * A l + B l * B l)) ^ 2)
    with ((A l * fst q + B l * snd q + C l) ^ 2 / (A l * A l + B l * B l) ^ 2).
  2: { unfold Rdiv. rewrite Rpow_mult_distr. rewrite pow_inv by lra. reflexivity. }
  replace ((A l * A l + B l * B l) ^ 2) with ((A l * A l + B l * B l) * (A l * A l + B l * B l)) by ring.
  unfold Rdiv.
  rewrite Rinv_mult.
  replace ((A l * fst q + B l * snd q + C l) ^ 2 * (/ (A l * A l + B l * B l) * / (A l * A l + B l * B l)) *
           (A l * A l + B l * B l))
    with ((A l * fst q + B l * snd q + C l) ^ 2 * / (A l * A l + B l * B l)).
  2: { field. lra. }
  lra.
Qed.

(** (√x/√y)² = x/y *)
Lemma O5_h2_from_valid : forall px py qx qy l,
  line_wf l ->
  O5_general_valid (px, py) l (qx, qy) ->
  0 <= (px - qx) * (px - qx) + (py - qy) * (py - qy) -
       ((A l * qx + B l * qy + C l) / (A l * A l + B l * B l)) *
       ((A l * qx + B l * qy + C l) / (A l * A l + B l * B l)) *
       (A l * A l + B l * B l).
Proof.
  intros px py qx qy l Hwf Hvalid.
  pose proof (O5_general_valid_h2_nonneg (px, py) l (qx, qy) Hwf Hvalid) as H.
  simpl in H.
  replace (A l ^ 2 + B l ^ 2) with (A l * A l + B l * B l) in H by ring.
  replace ((px - qx) ^ 2 + (py - qy) ^ 2)
    with ((px - qx) * (px - qx) + (py - qy) * (py - qy)) in H by ring.
  replace (((A l * qx + B l * qy + C l) / (A l * A l + B l * B l)) ^ 2)
    with (((A l * qx + B l * qy + C l) / (A l * A l + B l * B l)) *
          ((A l * qx + B l * qy + C l) / (A l * A l + B l * B l))) in H by ring.
  replace ((A l * qx + B l * qy + C l) / (A l * A l + B l * B l) *
           ((A l * qx + B l * qy + C l) / (A l * A l + B l * B l) * 1))
    with (((A l * qx + B l * qy + C l) / (A l * A l + B l * B l)) *
          ((A l * qx + B l * qy + C l) / (A l * A l + B l * B l))) in H by ring.
  replace ((px - qx) * ((px - qx) * 1) + (py - qy) * ((py - qy) * 1))
    with ((px - qx) * (px - qx) + (py - qy) * (py - qy)) in H by ring.
  exact H.
Qed.

(** O5 displacement squared equals r² *)
Lemma O5_dist2_eq : forall px py qx qy l,
  line_wf l -> O5_general_valid (px, py) l (qx, qy) ->
  let a := A l in let b := B l in let cc := C l in
  let norm2 := a * a + b * b in
  let d := (a * qx + b * qy + cc) / norm2 in
  let r2 := (px - qx) * (px - qx) + (py - qy) * (py - qy) in
  let h2 := r2 - d * d * norm2 in
  let t := sqrt h2 / sqrt norm2 in
  (- a * d + b * t) * (- a * d + b * t) + (- b * d - a * t) * (- b * d - a * t) = r2.
Proof.
  intros px py qx qy l Hwf Hvalid. simpl.
  set (a := A l). set (b := B l). set (cc := C l).
  set (norm2 := a * a + b * b).
  assert (Hnorm_pos : norm2 > 0) by (unfold norm2, a, b; apply line_norm_pos; exact Hwf).
  set (d := (a * qx + b * qy + cc) / norm2).
  set (r2 := (px - qx) * (px - qx) + (py - qy) * (py - qy)).
  set (h2 := r2 - d * d * norm2).
  assert (Hh2_pos : 0 <= h2).
  { unfold h2, r2, d, norm2, a, b, cc.
    apply (O5_h2_from_valid px py qx qy l Hwf Hvalid). }
  set (t := sqrt h2 / sqrt norm2).
  assert (Ht2 : t * t = h2 / norm2) by (unfold t; apply sqrt_div_sq; lra).
  rewrite (O5_algebraic_identity a b d t norm2 h2 eq_refl Hnorm_pos Ht2).
  unfold h2, r2. ring.
Qed.

(** dist(q, O5_general_image(p,l,q)) = dist(q,p) *)
Lemma O5_general_image_equidistant : forall p l q,
  line_wf l -> O5_general_valid p l q ->
  dist q (O5_general_image p l q) = dist q p.
Proof.
  intros [px py] l [qx qy] Hwf Hvalid.
  unfold dist, O5_general_image, dist2, sqr. simpl.
  f_equal.
  pose proof (O5_dist2_eq px py qx qy l Hwf Hvalid) as H. simpl in H.
  replace (A l * (A l * 1) + B l * (B l * 1)) with (A l * A l + B l * B l) by ring.
  replace ((px - qx) * ((px - qx) * 1) + (py - qy) * ((py - qy) * 1))
    with ((px - qx) * (px - qx) + (py - qy) * (py - qy)) by ring.
  replace ((A l * qx + B l * qy + C l) / (A l * A l + B l * B l) *
           ((A l * qx + B l * qy + C l) / (A l * A l + B l * B l) * 1))
    with ((A l * qx + B l * qy + C l) / (A l * A l + B l * B l) *
          ((A l * qx + B l * qy + C l) / (A l * A l + B l * B l))) by ring.
  set (a := A l). set (b := B l). set (cc := C l).
  set (norm2 := a * a + b * b).
  set (d := (a * qx + b * qy + cc) / norm2).
  set (r2 := (px - qx) * (px - qx) + (py - qy) * (py - qy)).
  set (h2 := r2 - d * d * norm2).
  set (t := sqrt h2 / sqrt norm2).
  replace ((qx - (qx - a * d + b * t)) * (qx - (qx - a * d + b * t)) +
           (qy - (qy - b * d - a * t)) * (qy - (qy - b * d - a * t)))
    with ((- a * d + b * t) * (- a * d + b * t) + (- b * d - a * t) * (- b * d - a * t)) by ring.
  replace ((qx - px) * (qx - px) + (qy - py) * (qy - py))
    with ((px - qx) * (px - qx) + (py - qy) * (py - qy)) by ring.
  unfold a, b, cc, norm2, d, r2, h2, t.
  exact H.
Qed.

(** p₁ ≠ p₂ ∧ dist(q,p₁) = dist(q,p₂) → q ∈ perp_bisector(p₁,p₂) *)
Lemma equidistant_on_perp_bisector : forall p1 p2 q,
  p1 <> p2 ->
  dist q p1 = dist q p2 ->
  on_line q (perp_bisector p1 p2).
Proof.
  intros [x1 y1] [x2 y2] [qx qy] Hneq Hdist.
  unfold on_line, perp_bisector, dist, dist2, sqr in *. simpl in *.
  destruct (Req_EM_T x1 x2) as [Hx|Hx].
  - subst x2.
    destruct (Req_EM_T y1 y2) as [Hy|Hy].
    + exfalso. apply Hneq. subst. reflexivity.
    + simpl.
      assert (Hsqrt_eq : sqrt ((qx - x1) * (qx - x1) + (qy - y1) * (qy - y1)) =
                         sqrt ((qx - x1) * (qx - x1) + (qy - y2) * (qy - y2))) by exact Hdist.
      assert (Hpos1 : 0 <= (qx - x1) * (qx - x1) + (qy - y1) * (qy - y1)).
      { apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
      assert (Hpos2 : 0 <= (qx - x1) * (qx - x1) + (qy - y2) * (qy - y2)).
      { apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
      apply (sqrt_inj _ _ Hpos1 Hpos2) in Hsqrt_eq.
      assert (Hy_eq : (qy - y1) * (qy - y1) = (qy - y2) * (qy - y2)) by lra.
      assert (Hqy : qy = (y1 + y2) / 2).
      { assert (H1 : (qy - y1 + (qy - y2)) * (qy - y1 - (qy - y2)) = 0).
        { replace ((qy - y1 + (qy - y2)) * (qy - y1 - (qy - y2)))
            with ((qy - y1) * (qy - y1) - (qy - y2) * (qy - y2)) by ring.
          lra. }
        apply Rmult_integral in H1. destruct H1 as [H1|H1]; lra. }
      rewrite Hqy. field; lra.
  - simpl.
    assert (Hsqrt_eq : sqrt ((qx - x1) * (qx - x1) + (qy - y1) * (qy - y1)) =
                       sqrt ((qx - x2) * (qx - x2) + (qy - y2) * (qy - y2))) by exact Hdist.
    assert (Hpos1 : 0 <= (qx - x1) * (qx - x1) + (qy - y1) * (qy - y1)).
    { apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
    assert (Hpos2 : 0 <= (qx - x2) * (qx - x2) + (qy - y2) * (qy - y2)).
    { apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
    apply (sqrt_inj _ _ Hpos1 Hpos2) in Hsqrt_eq.
    nra.
Qed.

(** O5 fold passes through pivot q *)
Lemma O5_fold_through_pivot : forall p l q,
  line_wf l -> O5_general_valid p l q -> p <> O5_general_image p l q ->
  on_line q (fold_line (fold_O5_general p l q)).
Proof.
  intros p l q Hwf Hvalid Hneq.
  unfold fold_O5_general, fold_line. simpl.
  apply equidistant_on_perp_bisector.
  - exact Hneq.
  - symmetry. apply O5_general_image_equidistant; assumption.
Qed.

(** reflect(p, O5_fold) = O5_general_image(p,l,q) *)
Lemma O5_fold_reflects_onto_line : forall p l q,
  line_wf l -> O5_general_valid p l q -> p <> O5_general_image p l q ->
  reflect_point p (fold_line (fold_O5_general p l q)) = O5_general_image p l q.
Proof.
  intros p l q Hwf Hvalid Hneq.
  unfold fold_O5_general, fold_line. simpl.
  apply perp_bisector_reflects_to_other. exact Hneq.
Qed.

(** q ∈ O5_fold ∧ reflect(p, O5_fold) ∈ l *)
Theorem O5_general_spec : forall p l q,
  line_wf l -> O5_general_valid p l q -> p <> O5_general_image p l q ->
  on_line q (fold_line (fold_O5_general p l q)) /\
  on_line (reflect_point p (fold_line (fold_O5_general p l q))) l.
Proof.
  intros p l q Hwf Hvalid Hneq.
  split.
  - apply O5_fold_through_pivot; assumption.
  - rewrite O5_fold_reflects_onto_line by assumption.
    apply O5_general_image_on_line. exact Hwf.
Qed.

(** fold_O5_general satisfies O5 constraint *)
Lemma O5_fold_satisfies_constraint : forall p l q,
  line_wf l -> O5_general_valid p l q -> p <> O5_general_image p l q ->
  satisfies_O5_constraint (fold_O5_general p l q) p l q.
Proof.
  intros p l q Hwf Hvalid Hneq.
  unfold satisfies_O5_constraint.
  apply O5_general_spec; assumption.
Qed.








(** x + y = y + x *)
Definition point_line_dist (p : Point) (l : Line) : R :=
  Rabs (A l * fst p + B l * snd p + C l) / sqrt (A l * A l + B l * B l).

(** point_line_dist ≥ 0 *)
Lemma point_line_dist_nonneg : forall p l,
  line_wf l -> 0 <= point_line_dist p l.
Proof.
  intros p l Hwf. unfold point_line_dist.
  apply Rmult_le_pos.
  - apply Rabs_pos.
  - apply Rlt_le. apply Rinv_0_lt_compat. apply sqrt_lt_R0.
    apply line_norm_pos. exact Hwf.
Qed.

(** (point_line_dist p l)² = (Ax+By+C)² / (A²+B²) *)
Lemma point_line_dist_sq : forall p l,
  line_wf l ->
  point_line_dist p l * point_line_dist p l =
  (A l * fst p + B l * snd p + C l)^2 / (A l * A l + B l * B l).
Proof.
  intros [px py] l Hwf. unfold point_line_dist. simpl.
  assert (Hnorm_pos : A l * A l + B l * B l > 0) by (apply line_norm_pos; exact Hwf).
  assert (Hsqrt_pos : sqrt (A l * A l + B l * B l) > 0) by (apply sqrt_lt_R0; lra).
  assert (Hsqrt_nz : sqrt (A l * A l + B l * B l) <> 0) by lra.
  assert (Hsqrt_sq : sqrt (A l * A l + B l * B l) * sqrt (A l * A l + B l * B l)
                     = A l * A l + B l * B l) by (apply sqrt_sqrt; lra).
  set (v := A l * px + B l * py + C l).
  set (s := sqrt (A l * A l + B l * B l)).
  assert (Hs_nz : s <> 0) by (unfold s; lra).
  assert (Habs_sq : Rabs v * Rabs v = v * v) by apply Rabs_sqr_eq.
  unfold Rdiv.
  replace (Rabs v * / s * (Rabs v * / s)) with (Rabs v * Rabs v * / (s * s)).
  2: { field. exact Hs_nz. }
  rewrite Habs_sq.
  fold s in Hsqrt_sq.
  rewrite Hsqrt_sq.
  replace (v * (v * 1)) with (v * v) by ring.
  reflexivity.
Qed.

(** dist²((px,py),(qx,qy)) = (px-qx)² + (py-qy)² *)
Lemma dist2_formula : forall px py qx qy,
  dist2 (px, py) (qx, qy) = (px - qx)^2 + (py - qy)^2.
Proof.
  intros. unfold dist2, sqr. simpl. ring.
Qed.

(** dist² ≥ 0 *)
Lemma dist2_nonneg : forall p q, 0 <= dist2 p q.
Proof.
  intros [px py] [qx qy]. unfold dist2, sqr. simpl.
  apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.


(** O5_general_valid ⟺ (point_line_dist q l)² ≤ dist²(p,q) *)
Lemma O5_valid_unfold : forall p l q,
  O5_general_valid p l q <-> (point_line_dist q l)^2 <= dist2 p q.
Proof.
  intros [px py] l [qx qy]. unfold O5_general_valid, point_line_dist, dist2, sqr. simpl.
  replace (A l * (A l * 1) + B l * (B l * 1)) with (A l * A l + B l * B l) by ring.
  replace ((px - qx) * ((px - qx) * 1) + (py - qy) * ((py - qy) * 1))
    with ((px - qx) * (px - qx) + (py - qy) * (py - qy)) by ring.
  reflexivity.
Qed.

(** x,y ≥ 0 → (x² ≤ y² ⟺ x ≤ y) *)
Theorem O5_valid_iff_dist : forall p l q,
  line_wf l ->
  O5_general_valid p l q <-> point_line_dist q l <= dist p q.
Proof.
  intros p l q Hwf.
  rewrite O5_valid_unfold.
  rewrite dist_via_dist2.
  assert (Hpld_nn : 0 <= point_line_dist q l) by (apply point_line_dist_nonneg; exact Hwf).
  assert (Hd2_nn : 0 <= dist2 p q) by apply dist2_nonneg.
  assert (Hsqrt_nn : 0 <= sqrt (dist2 p q)) by apply sqrt_pos.
  assert (Hsqrt_sq : sqrt (dist2 p q) * sqrt (dist2 p q) = dist2 p q).
  { apply sqrt_def. exact Hd2_nn. }
  split; intro H.
  - apply sq_le_iff; try assumption.
    replace ((sqrt (dist2 p q))^2) with (dist2 p q) by (simpl; lra).
    exact H.
  - apply sq_le_iff in H; try assumption.
    replace (dist2 p q) with ((sqrt (dist2 p q))^2) by (simpl; lra).
    exact H.
Qed.

(** O5: d > r → no solution; d = r → tangent; d < r → 2 solutions *)
Lemma O5_solution_count : forall p l q,
  line_wf l ->
  let d := point_line_dist q l in
  let r := dist p q in
  (d > r -> ~ O5_general_valid p l q) /\
  (d = r -> O5_general_valid p l q) /\
  (d < r -> O5_general_valid p l q).
Proof.
  intros p l q Hwf d r.
  repeat split; intro H.
  - intro Hvalid.
    apply O5_valid_iff_dist in Hvalid; [|exact Hwf].
    unfold d, r in *. lra.
  - apply O5_valid_iff_dist; [exact Hwf|].
    unfold d, r in *. lra.
  - apply O5_valid_iff_dist; [exact Hwf|].
    unfold d, r in *. lra.
Qed.


(** O5 fold multiplicity. The creases that place p onto l through the pivot q
    correspond to points of l at distance |pq| from q (the circle-line
    intersection): two distinct creases strictly inside the radius, exactly one
    landing point at the tangent distance, none beyond it. *)

(** A point of l obtained by sliding the parameter s along the line direction
    (B l, -A l) from the foot of q. *)
Definition o5land (l : Line) (q : Point) (s : R) : Point :=
  (fst (foot_on_line q l) + s * B l, snd (foot_on_line q l) - s * A l).

Lemma dist2_sym2 : forall p q, dist2 p q = dist2 q p.
Proof. intros [px py] [qx qy]; unfold dist2, sqr; ring. Qed.

Lemma o5land_on_line : forall l q s, line_wf l -> on_line (o5land l q s) l.
Proof.
  intros l q s Hwf.
  pose proof (foot_on_line_incident q l Hwf) as Hf.
  unfold o5land, on_line in *.
  destruct (foot_on_line q l) as [Fx Fy]. cbn [fst snd] in *. nra.
Qed.

Lemma o5land_dist2 : forall l q s, line_wf l ->
  dist2 (o5land l q s) q
   = (A l * fst q + B l * snd q + C l)^2 / (A l * A l + B l * B l)
     + (A l * A l + B l * B l) * (s * s).
Proof.
  intros l [qx qy] s Hwf.
  assert (Hn : A l * A l + B l * B l <> 0)
    by (apply Rgt_not_eq; apply line_norm_pos; exact Hwf).
  unfold o5land, dist2, foot_on_line, sqr. cbn [fst snd]. field. exact Hn.
Qed.

Lemma o5land_hits : forall l p q s, line_wf l ->
  (A l * A l + B l * B l) * (s * s)
    = dist2 p q - (A l * fst q + B l * snd q + C l)^2 / (A l * A l + B l * B l) ->
  dist2 (o5land l q s) q = dist2 p q.
Proof.
  intros l p q s Hwf Hs. rewrite (o5land_dist2 l q s Hwf). lra.
Qed.

(** A landing point at radius |pq| gives a genuine O5 crease through q. *)
Lemma o5land_crease : forall l p q s, line_wf l -> ~ on_line p l ->
  dist2 (o5land l q s) q = dist2 p q ->
  satisfies_O5_constraint (fold_line_ctor (perp_bisector p (o5land l q s))) p l q.
Proof.
  intros l p q s Hwf Hpnl Hd.
  assert (Hpne : p <> o5land l q s).
  { intro Heq. apply Hpnl. rewrite Heq. apply o5land_on_line; exact Hwf. }
  unfold satisfies_O5_constraint. cbn [fold_line]. split.
  - apply equidistant_on_perp_bisector; [exact Hpne|].
    rewrite (dist_via_dist2 q p), (dist_via_dist2 q (o5land l q s)).
    f_equal. rewrite (dist2_sym2 q p), (dist2_sym2 q (o5land l q s)).
    symmetry; exact Hd.
  - rewrite perp_bisector_reflects_to_other by exact Hpne. apply o5land_on_line; exact Hwf.
Qed.

(** d < r: two distinct creases solve the O5 incidence. *)
Lemma O5_two_distinct_creases : forall l p q, line_wf l -> ~ on_line p l ->
  point_line_dist q l < dist p q ->
  exists f1 f2, f1 <> f2 /\
    satisfies_O5_constraint f1 p l q /\ satisfies_O5_constraint f2 p l q.
Proof.
  intros l p q Hwf Hpnl Hlt.
  assert (Hn : A l * A l + B l * B l > 0) by (apply line_norm_pos; exact Hwf).
  assert (Hpld2 : (A l * fst q + B l * snd q + C l)^2 / (A l * A l + B l * B l)
                  = point_line_dist q l * point_line_dist q l)
    by (symmetry; apply point_line_dist_sq; exact Hwf).
  assert (Hpos : 0 <= point_line_dist q l) by (apply point_line_dist_nonneg; exact Hwf).
  assert (Hdd : dist p q * dist p q = dist2 p q)
    by (rewrite (dist_via_dist2 p q) at 1 2; apply sqrt_sqrt; apply dist2_nonneg).
  assert (Hh2 : 0 < dist2 p q - (A l * fst q + B l * snd q + C l)^2 / (A l * A l + B l * B l)).
  { rewrite Hpld2. nra. }
  assert (Harg : 0 <= (dist2 p q - (A l * fst q + B l * snd q + C l)^2 / (A l * A l + B l * B l))
                      / (A l * A l + B l * B l))
    by (apply Rlt_le; apply Rdiv_lt_0_compat; lra).
  remember (sqrt ((dist2 p q - (A l * fst q + B l * snd q + C l)^2 / (A l * A l + B l * B l))
                  / (A l * A l + B l * B l))) as t eqn:Edt.
  assert (Ht2 : t * t = (dist2 p q - (A l * fst q + B l * snd q + C l)^2 / (A l * A l + B l * B l))
                        / (A l * A l + B l * B l))
    by (rewrite Edt; apply sqrt_sqrt; exact Harg).
  assert (Htpos : 0 < t)
    by (rewrite Edt; apply sqrt_lt_R0; apply Rdiv_lt_0_compat; lra).
  assert (Hhitst : (A l * A l + B l * B l) * (t * t)
                   = dist2 p q - (A l * fst q + B l * snd q + C l)^2 / (A l * A l + B l * B l))
    by (rewrite Ht2; field; lra).
  assert (Hhitsmt : (A l * A l + B l * B l) * ((-t) * (-t))
                    = dist2 p q - (A l * fst q + B l * snd q + C l)^2 / (A l * A l + B l * B l))
    by (replace ((-t) * (-t)) with (t * t) by ring; exact Hhitst).
  assert (Hpne1 : p <> o5land l q t)
    by (intro H; apply Hpnl; rewrite H; apply o5land_on_line; exact Hwf).
  assert (Hpne2 : p <> o5land l q (-t))
    by (intro H; apply Hpnl; rewrite H; apply o5land_on_line; exact Hwf).
  assert (Hlandne : o5land l q t <> o5land l q (-t)).
  { unfold o5land. intro Heq. injection Heq as H1 H2.
    assert (HB : t * B l = 0) by nra. assert (HA : t * A l = 0) by nra.
    apply Rmult_integral in HB; apply Rmult_integral in HA.
    destruct Hwf as [Ha|Hb];
      [destruct HA as [|HA0]; [lra | exact (Ha HA0)] | destruct HB as [|HB0]; [lra | exact (Hb HB0)]]. }
  exists (fold_line_ctor (perp_bisector p (o5land l q t))),
         (fold_line_ctor (perp_bisector p (o5land l q (-t)))).
  split; [|split].
  - intro Hfeq. injection Hfeq as Hpb. apply Hlandne.
    transitivity (reflect_point p (perp_bisector p (o5land l q t))).
    + symmetry. apply perp_bisector_reflects_to_other. exact Hpne1.
    + rewrite Hpb. apply perp_bisector_reflects_to_other. exact Hpne2.
  - apply o5land_crease; [exact Hwf | exact Hpnl | apply (o5land_hits l p q t Hwf Hhitst)].
  - apply o5land_crease; [exact Hwf | exact Hpnl | apply (o5land_hits l p q (-t) Hwf Hhitsmt)].
Qed.

(** Every point of l is an o5land offset from the foot of q. *)
Lemma o5land_surj : forall l q y, line_wf l -> on_line y l -> exists s, y = o5land l q s.
Proof.
  intros l [qx qy] [y1 y2] Hwf Hy.
  assert (Hn : A l * A l + B l * B l <> 0)
    by (apply Rgt_not_eq; apply line_norm_pos; exact Hwf).
  unfold on_line in Hy.
  assert (HC : C l = -(A l * y1 + B l * y2)) by lra.
  exists ((B l * (y1 - qx) - A l * (y2 - qy)) / (A l * A l + B l * B l)).
  unfold o5land, foot_on_line. cbn [fst snd]. rewrite HC. f_equal; field; exact Hn.
Qed.

(** The foot of q is the closest point of l to q. *)
Lemma o5_min_dist : forall l q y, line_wf l -> on_line y l ->
  (A l * fst q + B l * snd q + C l)^2 / (A l * A l + B l * B l) <= dist2 q y.
Proof.
  intros l q y Hwf Hy.
  destruct (o5land_surj l q y Hwf Hy) as [s Hs].
  assert (Hn : A l * A l + B l * B l > 0) by (apply line_norm_pos; exact Hwf).
  rewrite Hs, (dist2_sym2 q (o5land l q s)), (o5land_dist2 l q s Hwf). nra.
Qed.

(** d > r: no well-formed crease solves the O5 incidence. *)
Lemma O5_no_crease : forall l p q, line_wf l ->
  dist p q < point_line_dist q l ->
  forall f, line_wf (fold_line f) -> ~ satisfies_O5_constraint f p l q.
Proof.
  intros l p q Hwf Hlt f Hwff [Hq Hr].
  assert (Hqfix : reflect_point q (fold_line f) = q)
    by (apply reflect_point_on_line; exact Hq).
  assert (Hiso : dist2 (reflect_point p (fold_line f)) (reflect_point q (fold_line f)) = dist2 p q)
    by (apply reflect_point_isometry_dist2; exact Hwff).
  rewrite Hqfix in Hiso.
  assert (Hmin : (A l * fst q + B l * snd q + C l)^2 / (A l * A l + B l * B l)
                 <= dist2 q (reflect_point p (fold_line f)))
    by (apply o5_min_dist; [exact Hwf | exact Hr]).
  assert (Hpld2 : (A l * fst q + B l * snd q + C l)^2 / (A l * A l + B l * B l)
                  = point_line_dist q l * point_line_dist q l)
    by (symmetry; apply point_line_dist_sq; exact Hwf).
  assert (Hpos : 0 <= point_line_dist q l) by (apply point_line_dist_nonneg; exact Hwf).
  assert (Hdp : 0 <= dist p q) by (rewrite dist_via_dist2; apply sqrt_pos).
  assert (Hdd : dist p q * dist p q = dist2 p q)
    by (rewrite (dist_via_dist2 p q) at 1 2; apply sqrt_sqrt; apply dist2_nonneg).
  rewrite (dist2_sym2 q (reflect_point p (fold_line f))), Hiso, Hpld2 in Hmin.
  nra.
Qed.

(** d < r: the valid landing points are exactly two distinct points. *)
Lemma O5_landings_exactly_two : forall l p q, line_wf l ->
  point_line_dist q l < dist p q ->
  exists y1 y2, y1 <> y2 /\
    (forall y, (on_line y l /\ dist2 q y = dist2 p q) <-> (y = y1 \/ y = y2)).
Proof.
  intros l p q Hwf Hlt.
  assert (Hn : A l*A l+B l*B l > 0) by (apply line_norm_pos; exact Hwf).
  assert (Hpld2 : (A l*fst q+B l*snd q+C l)^2/(A l*A l+B l*B l) = point_line_dist q l * point_line_dist q l)
    by (symmetry; apply point_line_dist_sq; exact Hwf).
  assert (Hpos : 0 <= point_line_dist q l) by (apply point_line_dist_nonneg; exact Hwf).
  assert (Hdd : dist p q * dist p q = dist2 p q)
    by (rewrite (dist_via_dist2 p q) at 1 2; apply sqrt_sqrt; apply dist2_nonneg).
  assert (Hh2 : 0 < dist2 p q - (A l*fst q+B l*snd q+C l)^2/(A l*A l+B l*B l)) by (rewrite Hpld2; nra).
  assert (Harg : 0 <= (dist2 p q - (A l*fst q+B l*snd q+C l)^2/(A l*A l+B l*B l))/(A l*A l+B l*B l))
    by (apply Rlt_le; apply Rdiv_lt_0_compat; lra).
  remember (sqrt ((dist2 p q - (A l*fst q+B l*snd q+C l)^2/(A l*A l+B l*B l))/(A l*A l+B l*B l))) as t eqn:Edt.
  assert (Ht2 : t*t = (dist2 p q - (A l*fst q+B l*snd q+C l)^2/(A l*A l+B l*B l))/(A l*A l+B l*B l))
    by (rewrite Edt; apply sqrt_sqrt; exact Harg).
  assert (Htpos : 0 < t) by (rewrite Edt; apply sqrt_lt_R0; apply Rdiv_lt_0_compat; lra).
  assert (Hnt2 : (A l*A l+B l*B l)*(t*t) = dist2 p q - (A l*fst q+B l*snd q+C l)^2/(A l*A l+B l*B l))
    by (rewrite Ht2; field; lra).
  exists (o5land l q t), (o5land l q (-t)). split.
  - unfold o5land. intro Heq. injection Heq as H1 H2.
    assert (HB : t*B l = 0) by nra. assert (HA : t*A l = 0) by nra.
    apply Rmult_integral in HB; apply Rmult_integral in HA.
    destruct Hwf as [Ha|Hb];
      [destruct HA as [|HA0]; [lra | exact (Ha HA0)] | destruct HB as [|HB0]; [lra | exact (Hb HB0)]].
  - intro y. split.
    + intros [Hyl Hyd]. destruct (o5land_surj l q y Hwf Hyl) as [s Hs].
      assert (Hns2 : (A l*A l+B l*B l)*(s*s) = dist2 p q - (A l*fst q+B l*snd q+C l)^2/(A l*A l+B l*B l)).
      { assert (dist2 q (o5land l q s) = dist2 p q) by (rewrite <- Hs; exact Hyd).
        rewrite (dist2_sym2 q (o5land l q s)), (o5land_dist2 l q s Hwf) in H. lra. }
      assert (Hsst : s*s = t*t)
        by (apply (Rmult_eq_reg_l (A l*A l+B l*B l)); [rewrite Hns2, Hnt2; reflexivity | lra]).
      assert (Hfac : (s - t)*(s + t) = 0) by nra.
      apply Rmult_integral in Hfac. destruct Hfac as [He|He].
      * left. rewrite Hs. replace s with t by lra. reflexivity.
      * right. rewrite Hs. replace s with (-t) by lra. reflexivity.
    + intros [Hy|Hy]; subst y.
      * split; [apply o5land_on_line; exact Hwf|].
        rewrite (dist2_sym2 q (o5land l q t)), (o5land_dist2 l q t Hwf). lra.
      * split; [apply o5land_on_line; exact Hwf|].
        rewrite (dist2_sym2 q (o5land l q (-t))), (o5land_dist2 l q (-t) Hwf).
        replace ((-t)*(-t)) with (t*t) by ring. lra.
Qed.

(** d = r (tangent): exactly one valid landing point, the foot of q. *)
Lemma O5_landing_unique : forall l p q, line_wf l ->
  point_line_dist q l = dist p q ->
  exists y, forall y', (on_line y' l /\ dist2 q y' = dist2 p q) <-> y' = y.
Proof.
  intros l p q Hwf Heq.
  assert (Hn : A l*A l+B l*B l > 0) by (apply line_norm_pos; exact Hwf).
  assert (Hpld2 : (A l*fst q+B l*snd q+C l)^2/(A l*A l+B l*B l) = point_line_dist q l * point_line_dist q l)
    by (symmetry; apply point_line_dist_sq; exact Hwf).
  assert (Hdd : dist p q * dist p q = dist2 p q)
    by (rewrite (dist_via_dist2 p q) at 1 2; apply sqrt_sqrt; apply dist2_nonneg).
  assert (Hh0 : dist2 p q - (A l*fst q+B l*snd q+C l)^2/(A l*A l+B l*B l) = 0)
    by (rewrite Hpld2, Heq; lra).
  exists (o5land l q 0). intro y'. split.
  - intros [Hyl Hyd]. destruct (o5land_surj l q y' Hwf Hyl) as [s Hs].
    assert (Hns2 : (A l*A l+B l*B l)*(s*s) = 0).
    { assert (dist2 q (o5land l q s) = dist2 p q) by (rewrite <- Hs; exact Hyd).
      rewrite (dist2_sym2 q (o5land l q s)), (o5land_dist2 l q s Hwf) in H. lra. }
    assert (Hs0 : s = 0).
    { assert (Hss : s*s = 0)
        by (apply (Rmult_eq_reg_l (A l*A l+B l*B l)); [rewrite Hns2; ring | lra]).
      apply Rmult_integral in Hss. destruct Hss; assumption. }
    rewrite Hs, Hs0. reflexivity.
  - intros ->. split; [apply o5land_on_line; exact Hwf|].
    rewrite (dist2_sym2 q (o5land l q 0)), (o5land_dist2 l q 0 Hwf). lra.
Qed.


(** Root structure of depressed cubic t³ + pt + q *)

(** t³ + pt + q *)
Definition O6_fold_from_root (p q t : R) : Fold := fold_O6_beloch p q t.

(** ∃! t with t³ + pt + q = 0 *)
Definition point_continuous (f : Point -> Point) : Prop :=
  forall p eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall p', dist p p' < delta -> dist (f p') (f p) < eps.

Lemma reflect_linear_in_point : forall l px py px' py',
  line_wf l ->
  let k := 2 / (A l * A l + B l * B l) in
  fst (reflect_point (px', py') l) - fst (reflect_point (px, py) l) =
    (1 - k * A l * A l) * (px' - px) - k * A l * B l * (py' - py).
Proof.
  intros l px py px' py' Hwf k.
  unfold reflect_point, k. simpl.
  assert (Hn : A l * A l + B l * B l > 0) by (apply line_norm_pos; exact Hwf).
  field. lra.
Qed.



(** * Multi-Fold Origami Extensions

    Single-fold origami (Huzita-Hatori) solves cubics and constructs numbers
    in towers of degree 2 and 3 extensions. Simultaneous k-fold operations
    extend constructibility to higher algebraic degrees. *)

(** A 2-fold operation produces two crease lines simultaneously. *)
Definition two_fold_lines (l1 l2 : Line) : Prop :=
  line_wf l1 /\ line_wf l2.

(** Quintisection: dividing an angle into five equal parts.
    Requires solving a degree-5 Chebyshev polynomial. *)
Definition heptagon_vertex_1 : Point := (cos_2pi_7, sin_2pi_7).

(** Both coordinates of (cos(2π/7), sin(2π/7)) are in OrigamiNum *)
Theorem heptagon_vertex_1_constructible :
  OrigamiNum (fst heptagon_vertex_1) /\ OrigamiNum (snd heptagon_vertex_1).
Proof.
  unfold heptagon_vertex_1. simpl.
  split.
  - exact cos_2pi_7_is_origami_constructible.
  - exact sin_2pi_7_is_origami_constructible.
Qed.

(** Concrete O6 fold extraction.
    Tschirnhaus substitution: 8c³+4c²-4c-1=0 becomes t³+pt+q=0
    with c = t - 1/6, p = -7/12, q = -7/216. *)
Definition heptagon_c_from_t (t : R) : R := t - tschirnhaus_shift.

(** t = c + 1/6 *)
Definition heptagon_t_from_c (c : R) : R := c + tschirnhaus_shift.

(** Depressed cubic: t³ + pt + q *)
Lemma tschirnhaus_transformation : forall t,
  heptagon_poly (heptagon_c_from_t t) = 8 * heptagon_depressed t.
Proof.
  intros t.
  unfold heptagon_poly, heptagon_c_from_t, heptagon_depressed.
  unfold tschirnhaus_shift, heptagon_cubic_a, heptagon_cubic_b.
  field.
Qed.

(** t₀ = cos(2π/7) + 1/6 is a root of the depressed cubic *)
Definition heptagon_t0 : R := heptagon_t_from_c cos_2pi_7.

(** Auxiliary: heptagon_depressed in expanded form *)
Theorem heptagon_t0_is_depressed_root : heptagon_depressed heptagon_t0 = 0.
Proof.
  unfold heptagon_t0, heptagon_t_from_c, tschirnhaus_shift.
  pose proof cos_2pi_7_satisfies_heptagon_poly as Hpoly.
  unfold heptagon_poly in Hpoly.
  rewrite heptagon_depressed_expanded.
  set (c := cos_2pi_7) in *.
  replace ((c + 1/6)^3 - 7/12 * (c + 1/6) - 7/216)
    with ((8 * c^3 + 4 * c^2 - 4 * c - 1) / 8) by field.
  rewrite Hpoly. field.
Qed.

(** heptagon_depressed matches depressed_cubic *)
Theorem heptagon_t0_is_cubic_root :
  is_cubic_root heptagon_cubic_a heptagon_cubic_b heptagon_t0.
Proof.
  unfold is_cubic_root.
  rewrite <- heptagon_depressed_eq_depressed_cubic.
  exact heptagon_t0_is_depressed_root.
Qed.

(** The concrete O6 Beloch fold for the heptagon *)
Definition heptagon_O6_fold : Fold :=
  fold_O6_beloch heptagon_cubic_a heptagon_cubic_b heptagon_t0.

(** cos(2π/7) = t₀ - 1/6 *)
Theorem cos_2pi_7_from_t0 : cos_2pi_7 = heptagon_t0 - tschirnhaus_shift.
Proof.
  unfold heptagon_t0, heptagon_t_from_c, tschirnhaus_shift. ring.
Qed.

(** Summary: concrete O6 parameters for heptagon construction *)
Theorem heptagon_O6_parameters :
  heptagon_cubic_a = -7/12 /\
  heptagon_cubic_b = -7/216 /\
  is_cubic_root heptagon_cubic_a heptagon_cubic_b heptagon_t0 /\
  cos_2pi_7 = heptagon_t0 - 1/6.
Proof.
  split. { reflexivity. }
  split. { reflexivity. }
  split. { exact heptagon_t0_is_cubic_root. }
  exact cos_2pi_7_from_t0.
Qed.


(** Vertices of a regular polygon with an origami base angle are constructible.
    Each coordinate cos(k.theta), sin(k.theta) is a real-polynomial combination of
    cos(theta) and sin(theta) via the angle-addition formulas, hence origami, hence
    the vertex is a constructible point. *)

(** OrigamiNum x -> (x, 0) is a constructible point *)
Lemma origami_xaxis_point : forall x, OrigamiNum x -> ConstructiblePoint (x, 0).
Proof.
  intros x Hx. destruct (OrigamiNum_implies_ConstructibleR x Hx) as [y Hy].
  exact (project_to_xaxis x y Hy).
Qed.

(** cos(theta), sin(theta) origami -> cos(k.theta), sin(k.theta) origami *)
Lemma vertex_constructible : forall theta,
  OrigamiNum (cos theta) -> OrigamiNum (sin theta) ->
  forall k : nat, ConstructiblePoint (cos (INR k * theta), sin (INR k * theta)).
Proof.
  intros theta Hc Hs k.
  destruct (vertex_coords_origami theta Hc Hs k) as [Hck Hsk].
  apply point_xy_constructible.
  - apply origami_xaxis_point; exact Hck.
  - apply yaxis_from_xaxis. apply origami_xaxis_point; exact Hsk.
Qed.

(** Regular n-gon: the k-th vertex (cos(2.pi.k/n), sin(2.pi.k/n)) is constructible
    whenever the base vertex angle has origami cosine and sine. *)
Lemma regular_ngon_vertex_constructible : forall (n k : nat),
  (n <> 0)%nat ->
  OrigamiNum (cos (2 * PI / INR n)) -> OrigamiNum (sin (2 * PI / INR n)) ->
  ConstructiblePoint (cos (2 * PI * INR k / INR n), sin (2 * PI * INR k / INR n)).
Proof.
  intros n k Hn Hc Hs.
  assert (HnR : INR n <> 0) by (apply not_0_INR; exact Hn).
  replace (2 * PI * INR k / INR n) with (INR k * (2 * PI / INR n)) by (field; exact HnR).
  apply vertex_constructible; assumption.
Qed.

(** Every vertex of the regular heptagon is a constructible point. *)
Lemma heptagon_vertex_constructible_all : forall k,
  ConstructiblePoint (heptagon_vertex k).
Proof.
  intro k.
  assert (Heq : heptagon_vertex k
              = (cos (INR k * (2 * PI / 7)), sin (INR k * (2 * PI / 7)))).
  { unfold heptagon_vertex, rotate_point. cbn [fst snd]. f_equal.
    - replace (1 * cos (2 * PI * INR k / 7) - 0 * sin (2 * PI * INR k / 7))
        with (cos (2 * PI * INR k / 7)) by ring. f_equal. field.
    - replace (1 * sin (2 * PI * INR k / 7) + 0 * cos (2 * PI * INR k / 7))
        with (sin (2 * PI * INR k / 7)) by ring. f_equal. field. }
  rewrite Heq. apply vertex_constructible.
  - exact cos_2pi_7_is_origami_constructible.
  - exact sin_2pi_7_is_origami_constructible.
Qed.

(** Each heptagon edge fold produces a constructible crease line. *)
Lemma heptagon_edge_fold_constructible : forall k,
  ConstructibleLine (execute_fold_step (heptagon_edge_fold k)).
Proof.
  intro k. unfold heptagon_edge_fold. cbn [execute_fold_step]. rewrite fold_line_O1.
  apply line_through_constructible; apply heptagon_vertex_constructible_all.
Qed.

(** Each edge crease passes through the two consecutive heptagon vertices. *)
Lemma heptagon_edge_contains_vertices : forall k,
  on_line (heptagon_vertex k) (execute_fold_step (heptagon_edge_fold k)) /\
  on_line (heptagon_vertex (S k mod 7)) (execute_fold_step (heptagon_edge_fold k)).
Proof.
  intro k. unfold heptagon_edge_fold. cbn [execute_fold_step]. rewrite fold_line_O1.
  split; [apply line_through_on_line_fst | apply line_through_on_line_snd].
Qed.

(** Executing a fold sequence whose steps are all O1 joins of constructible points
    keeps every accumulated crease a constructible line. *)
Lemma execute_O1_seq_constructible :
  forall seq st,
    Forall (fun step => exists p1 p2,
              step = FS_O1 p1 p2 /\ ConstructiblePoint p1 /\ ConstructiblePoint p2) seq ->
    Forall ConstructibleLine (state_lines st) ->
    Forall ConstructibleLine (state_lines (execute_sequence st seq)).
Proof.
  induction seq as [|step rest IH]; intros st Hseq Hst; [exact Hst|].
  inversion Hseq as [|s l Hstep Hrest]; subst.
  destruct Hstep as [p1 [p2 [Heq [Hp1 Hp2]]]]. subst step.
  apply IH; [exact Hrest|].
  unfold add_fold_to_state. cbn [state_lines execute_fold_step]. rewrite fold_line_O1.
  constructor; [apply line_through_constructible; assumption | exact Hst].
Qed.

(** The seven heptagon edge folds form such a sequence. *)
Lemma heptagon_edges_seq_O1 :
  Forall (fun step => exists p1 p2,
            step = FS_O1 p1 p2 /\ ConstructiblePoint p1 /\ ConstructiblePoint p2)
         (map heptagon_edge_fold (seq 0 7)).
Proof.
  apply Forall_forall. intros step Hin.
  apply in_map_iff in Hin. destruct Hin as [k [Hk _]]. subst step.
  unfold heptagon_edge_fold. exists (heptagon_vertex k), (heptagon_vertex (S k mod 7)).
  split; [reflexivity | split; apply heptagon_vertex_constructible_all].
Qed.


(** ∛2 satisfies t³ - 2 = 0, i.e., depressed_cubic(0, -2, ∛2) = 0.
    Restatement of cbrt2_is_origami with explicit O6 parameters. *)
Definition delian_O6_fold : Fold :=
  fold_O6_beloch delian_p delian_q cbrt2.

(** p = 0 ∧ q = -2 ∧ is_cubic_root(p, q, ∛2) ∧ (∛2)³ = 2 *)
Open Scope R_scope.
Open Scope R_scope.
Open Scope R_scope.
Theorem fold_O5_general_satisfies_O5 : forall p l q,
  line_wf l -> O5_general_valid p l q -> p <> O5_general_image p l q ->
  satisfies_O5_constraint (fold_O5_general p l q) p l q.
Proof.
  intros p l q Hwf Hvalid Hneq.
  unfold satisfies_O5_constraint.
  apply O5_general_spec; assumption.
Qed.

(** The Beloch (O6) fold solves an arbitrary depressed cubic: for any p, q a real
    root exists and the corresponding fold satisfies the O6 constraint. *)
Theorem O6_beloch_solves_any_cubic : forall p q,
  exists t, t*t*t + p*t + q = 0 /\
    satisfies_O6_constraint (fold_O6_beloch p q t)
      beloch_P1 beloch_L1 (beloch_P2 p q) (beloch_L2 q).
Proof.
  intros p q.
  destruct (depressed_cubic_root_exists p q) as [t Ht].
  unfold is_cubic_root, depressed_cubic in Ht.
  assert (Ht' : t*t*t + p*t + q = 0) by (rewrite <- Ht; ring).
  exists t. split; [exact Ht'|].
  apply beloch_fold_satisfies_O6. exact Ht'.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════
   Single-fold decision procedure: soundness and completeness of the depth
   enumeration extended to the O5, O6, O7 creases and the special folds.
   ═══════════════════════════════════════════════════════════════════════════ *)

(* -- Beloch-crease root list: soundness and completeness -- *)
Lemma some_cubic_root_is_root : forall p q,
  (some_cubic_root p q) ^ 3 + p * (some_cubic_root p q) + q = 0.
Proof.
  intros p q. unfold some_cubic_root.
  pose proof (proj2_sig (depressed_cubic_root_sig p q)) as Hr.
  unfold is_cubic_root, depressed_cubic in Hr. exact Hr.
Qed.
Close Scope R_scope.
Open Scope R_scope.
Lemma cubic_root_list_sound : forall p q t,
  In t (cubic_root_list p q) -> t ^ 3 + p * t + q = 0.
Proof.
  intros p q t Hin. unfold cubic_root_list in Hin. cbv zeta in Hin.
  set (r0 := some_cubic_root p q) in *.
  pose proof (some_cubic_root_is_root p q) as Hr0. change (r0 ^ 3 + p * r0 + q = 0) in Hr0.
  destruct (Rle_dec 0 (-3 * r0 * r0 - 4 * p)) as [Hd | Hd].
  - assert (Hs : sqrt (-3 * r0 * r0 - 4 * p) * sqrt (-3 * r0 * r0 - 4 * p)
                 = -3 * r0 * r0 - 4 * p) by (apply sqrt_sqrt; exact Hd).
    simpl in Hin. destruct Hin as [Ht | [Ht | [Ht | []]]]; subst t.
    + rewrite (cubic_factor_id p q r0 r0), Hr0. replace (r0 - r0) with 0 by ring. ring.
    + rewrite (cubic_factor_id p q r0 _), Hr0.
      assert (Hquad : (- r0 + sqrt (-3 * r0 * r0 - 4 * p)) / 2
                      * ((- r0 + sqrt (-3 * r0 * r0 - 4 * p)) / 2)
                      + r0 * ((- r0 + sqrt (-3 * r0 * r0 - 4 * p)) / 2)
                      + (r0 * r0 + p) = 0) by nra.
      rewrite Hquad. ring.
    + rewrite (cubic_factor_id p q r0 _), Hr0.
      assert (Hquad : (- r0 - sqrt (-3 * r0 * r0 - 4 * p)) / 2
                      * ((- r0 - sqrt (-3 * r0 * r0 - 4 * p)) / 2)
                      + r0 * ((- r0 - sqrt (-3 * r0 * r0 - 4 * p)) / 2)
                      + (r0 * r0 + p) = 0) by nra.
      rewrite Hquad. ring.
  - simpl in Hin. destruct Hin as [Ht | []]; subst t.
    rewrite (cubic_factor_id p q r0 r0), Hr0. replace (r0 - r0) with 0 by ring. ring.
Qed.

Lemma cubic_root_list_complete : forall p q t,
  t ^ 3 + p * t + q = 0 -> In t (cubic_root_list p q).
Proof.
  intros p q t Ht. unfold cubic_root_list. cbv zeta.
  set (r0 := some_cubic_root p q) in *.
  pose proof (some_cubic_root_is_root p q) as Hr0. change (r0 ^ 3 + p * r0 + q = 0) in Hr0.
  assert (Hprod : (t - r0) * (t * t + r0 * t + (r0 * r0 + p)) = 0).
  { replace ((t - r0) * (t * t + r0 * t + (r0 * r0 + p)))
      with ((t ^ 3 + p * t + q) - (r0 ^ 3 + p * r0 + q)) by ring.
    rewrite Ht, Hr0. ring. }
  apply Rmult_integral in Hprod. destruct Hprod as [Hroot | Hquad].
  - assert (t = r0) by lra. subst t. destruct (Rle_dec 0 (-3*r0*r0-4*p)); simpl; left; reflexivity.
  - assert (Hsq2 : (2 * t + r0) * (2 * t + r0) = -3 * r0 * r0 - 4 * p).
    { replace ((2 * t + r0) * (2 * t + r0))
        with (4 * (t * t + r0 * t + (r0 * r0 + p)) + (-3 * r0 * r0 - 4 * p)) by ring.
      rewrite Hquad. ring. }
    assert (Hd : 0 <= -3 * r0 * r0 - 4 * p).
    { pose proof (Rle_0_sqr (2 * t + r0)) as Hsqr. unfold Rsqr in Hsqr. lra. }
    assert (Hs : sqrt (-3 * r0 * r0 - 4 * p) * sqrt (-3 * r0 * r0 - 4 * p)
                 = -3 * r0 * r0 - 4 * p) by (apply sqrt_sqrt; exact Hd).
    assert (Hfac : (2 * t + r0 - sqrt (-3*r0*r0-4*p))
                 * (2 * t + r0 + sqrt (-3*r0*r0-4*p)) = 0).
    { replace ((2 * t + r0 - sqrt (-3*r0*r0-4*p)) * (2 * t + r0 + sqrt (-3*r0*r0-4*p)))
        with ((2 * t + r0) * (2 * t + r0)
              - sqrt (-3*r0*r0-4*p) * sqrt (-3*r0*r0-4*p)) by ring.
      rewrite Hsq2, Hs. ring. }
    destruct (Rle_dec 0 (-3*r0*r0-4*p)) as [_ | Hcontra]; [| lra].
    apply Rmult_integral in Hfac. simpl. destruct Hfac as [H1 | H2].
    + right; left. lra.
    + right; right; left. lra.
Qed.

Lemma cubic_real_roots_line_sound : forall p q x,
  In x (cubic_real_roots p q) -> exists t, x = beloch_fold_line t /\ t ^ 3 + p * t + q = 0.
Proof.
  intros p q x Hin. unfold cubic_real_roots in Hin.
  apply in_map_iff in Hin. destruct Hin as [t [Hx Ht]].
  exists t. split; [symmetry; exact Hx | apply cubic_root_list_sound; exact Ht].
Qed.

Lemma cubic_real_roots_line_complete : forall p q t,
  t ^ 3 + p * t + q = 0 -> In (beloch_fold_line t) (cubic_real_roots p q).
Proof.
  intros p q t Ht. unfold cubic_real_roots. apply in_map.
  apply cubic_root_list_complete. exact Ht.
Qed.

(* -- x-axis projection of a constructible point is constructible -- *)
Lemma foot_on_line_xaxis : forall p, foot_on_line p line_xaxis = (fst p, 0).
Proof. intros [x y]. unfold foot_on_line, line_xaxis; simpl. f_equal; field. Qed.

Lemma line_wf_xaxis : line_wf line_xaxis.
Proof. unfold line_wf, line_xaxis; simpl; right; lra. Qed.

Lemma CP_proj_x : forall p, ConstructiblePoint p -> ConstructiblePoint (fst p, 0).
Proof.
  intros p Hp. rewrite <- foot_on_line_xaxis.
  apply foot_constructible; [apply line_wf_xaxis | exact Hp | apply CL_x].
Qed.

(* -- crease-line constructibility from the fold constructors -- *)
Lemma CL_of_O5 : forall p1 l p2, ConstructiblePoint p1 -> ConstructibleLine l ->
  ConstructiblePoint p2 -> ConstructibleLine (fold_line (fold_O5 p1 l p2)).
Proof. intros; apply ConstructibleLine_of_fold, CF_O5; assumption. Qed.

Lemma CL_of_O6 : forall p1 l1 p2 l2, ConstructiblePoint p1 -> ConstructibleLine l1 ->
  ConstructiblePoint p2 -> ConstructibleLine l2 ->
  ConstructibleLine (fold_line (fold_O6 p1 l1 p2 l2)).
Proof. intros; apply ConstructibleLine_of_fold, CF_O6; assumption. Qed.

Lemma CL_of_O7 : forall p1 l1 l2, ConstructiblePoint p1 -> ConstructibleLine l1 ->
  ConstructibleLine l2 -> ConstructibleLine (fold_line (fold_O7 p1 l1 l2)).
Proof. intros; apply ConstructibleLine_of_fold, CF_O7; assumption. Qed.

Lemma CL_of_O5_vert : forall p q c, ConstructiblePoint p -> ConstructiblePoint q ->
  ConstructiblePoint (c, 0) -> O5_vert_valid p q c ->
  ConstructibleLine (fold_line (fold_O5_vert p q c)).
Proof. intros; apply ConstructibleLine_of_fold, CF_O5_vert; assumption. Qed.

Lemma CL_of_beloch : forall p q t, ConstructiblePoint (p, 0) -> ConstructiblePoint (q, 0) ->
  t * t * t + p * t + q = 0 -> ConstructibleLine (beloch_fold_line t).
Proof. intros; apply ConstructibleLine_of_fold with (f := fold_O6_beloch p q t), CF_O6_beloch; assumption. Qed.

Lemma CL_of_O5_general : forall p l q, ConstructiblePoint p -> ConstructibleLine l ->
  ConstructiblePoint q -> line_wf l -> O5_general_valid p l q ->
  p <> O5_general_image p l q ->
  ConstructibleLine (fold_line (fold_O5_general p l q)).
Proof. intros; apply ConstructibleLine_of_fold, CF_O5_general; assumption. Qed.

(* -- enumeration soundness (extended to all fold generators) -- *)
Lemma enum_sound_both : forall d,
  (forall p, In p (enum_points d) -> ConstructiblePoint p) /\
  (forall l, In l (enum_lines d) -> ConstructibleLine l).
Proof.
  induction d.
  - split; [apply In_enum_points_base | apply In_enum_lines_base].
  - destruct IHd as [IHp IHl]. split.
    + intros p H. simpl in H.
      apply in_app_or in H. destruct H as [H|H]. { apply IHp; exact H. }
      apply in_app_or in H. destruct H as [H|H].
      { apply in_flat_map in H. destruct H as [l1 [Hl1 H]].
        apply in_flat_map in H. destruct H as [l2 [Hl2 H]].
        simpl in H. destruct H as [H|H]; [|contradiction].
        subst. apply line_intersection_constructible; apply IHl; assumption. }
      apply in_flat_map in H. destruct H as [p0 [Hp0 H]].
      apply in_flat_map in H. destruct H as [l0 [Hl0 H]].
      simpl in H. destruct H as [H|H]; [|contradiction].
      subst. apply reflect_point_constructible; [apply IHp|apply IHl]; assumption.
    + intros l H. simpl in H.
      apply in_app_or in H. destruct H as [H|H]. { apply IHl; exact H. }
      apply in_app_or in H. destruct H as [H|H].
      { (* O1/O2: line_through, perp_bisector *)
        apply in_flat_map in H. destruct H as [p1 [Hp1 H]].
        apply in_flat_map in H. destruct H as [p2 [Hp2 H]].
        simpl in H. destruct H as [H|[H|H]]; try contradiction.
        - subst. apply line_through_constructible; apply IHp; assumption.
        - subst. apply perp_bisector_constructible; apply IHp; assumption. }
      apply in_app_or in H. destruct H as [H|H].
      { (* O3: bisector *)
        apply in_flat_map in H. destruct H as [l1 [Hl1 H]].
        apply in_flat_map in H. destruct H as [l2 [Hl2 H]].
        simpl in H. destruct H as [H|H]; [|contradiction].
        subst. apply bisector_constructible; apply IHl; assumption. }
      apply in_app_or in H. destruct H as [H|H].
      { (* O4: perp_through *)
        apply in_flat_map in H. destruct H as [p0 [Hp0 H]].
        apply in_flat_map in H. destruct H as [l0 [Hl0 H]].
        simpl in H. destruct H as [H|H]; [|contradiction].
        subst. apply perp_through_constructible; [apply IHp|apply IHl]; assumption. }
      apply in_app_or in H. destruct H as [H|H].
      { (* O5 *)
        apply in_flat_map in H. destruct H as [p1 [Hp1 H]].
        apply in_flat_map in H. destruct H as [l0 [Hl0 H]].
        apply in_flat_map in H. destruct H as [p2 [Hp2 H]].
        simpl in H. destruct H as [H|H]; [|contradiction].
        subst. apply CL_of_O5; [apply IHp; exact Hp1 | apply IHl; exact Hl0 | apply IHp; exact Hp2]. }
      apply in_app_or in H. destruct H as [H|H].
      { (* O6 *)
        apply in_flat_map in H. destruct H as [p1 [Hp1 H]].
        apply in_flat_map in H. destruct H as [l1 [Hl1 H]].
        apply in_flat_map in H. destruct H as [p2 [Hp2 H]].
        apply in_flat_map in H. destruct H as [l2 [Hl2 H]].
        simpl in H. destruct H as [H|H]; [|contradiction].
        subst. apply CL_of_O6;
          [apply IHp; exact Hp1 | apply IHl; exact Hl1 | apply IHp; exact Hp2 | apply IHl; exact Hl2]. }
      apply in_app_or in H. destruct H as [H|H].
      { (* O7 *)
        apply in_flat_map in H. destruct H as [p1 [Hp1 H]].
        apply in_flat_map in H. destruct H as [l1 [Hl1 H]].
        apply in_flat_map in H. destruct H as [l2 [Hl2 H]].
        simpl in H. destruct H as [H|H]; [|contradiction].
        subst. apply CL_of_O7;
          [apply IHp; exact Hp1 | apply IHl; exact Hl1 | apply IHl; exact Hl2]. }
      apply in_app_or in H. destruct H as [H|H].
      { (* O5_vert (guarded) *)
        apply in_flat_map in H. destruct H as [p0 [Hp0 H]].
        apply in_flat_map in H. destruct H as [q0 [Hq0 H]].
        apply in_flat_map in H. destruct H as [pc [Hpc H]].
        destruct (O5_vert_valid_dec p0 q0 (fst pc)) as [Hv|Hv].
        - simpl in H. destruct H as [H|H]; [|contradiction]. subst.
          apply CL_of_O5_vert;
            [apply IHp; exact Hp0 | apply IHp; exact Hq0
             | apply CP_proj_x; apply IHp; exact Hpc | exact Hv].
        - simpl in H. contradiction. }
      apply in_app_or in H. destruct H as [H|H].
      { (* O6 Beloch *)
        apply in_flat_map in H. destruct H as [pp [Hpp H]].
        apply in_flat_map in H. destruct H as [pq [Hpq H]].
        apply cubic_real_roots_line_sound in H. destruct H as [t [Hx Hroot]]. subst l.
        apply CL_of_beloch with (p := fst pp) (q := fst pq);
          [apply CP_proj_x; apply IHp; exact Hpp | apply CP_proj_x; apply IHp; exact Hpq |].
        replace (t * t * t) with (t ^ 3) by ring. exact Hroot. }
      { (* O5_general (guarded) *)
        apply in_flat_map in H. destruct H as [p0 [Hp0 H]].
        apply in_flat_map in H. destruct H as [l0 [Hl0 H]].
        apply in_flat_map in H. destruct H as [q0 [Hq0 H]].
        destruct (O5_general_guard p0 l0 q0) as [Hg|Hg].
        - destruct Hg as [Hwf [Hval Hne]].
          simpl in H. destruct H as [H|H]; [|contradiction]. subst.
          apply CL_of_O5_general;
            [apply IHp; exact Hp0 | apply IHl; exact Hl0 | apply IHp; exact Hq0
             | exact Hwf | exact Hval | exact Hne].
        - simpl in H. contradiction. }
Qed.

Theorem In_enum_points_constructible : forall d p,
  In p (enum_points d) -> ConstructiblePoint p.
Proof. intros d; apply (enum_sound_both d). Qed.

Theorem In_enum_lines_constructible : forall d l,
  In l (enum_lines d) -> ConstructibleLine l.
Proof. intros d; apply (enum_sound_both d). Qed.

(** The depth-bounded decision procedure is sound: every point it accepts at
    some depth is genuinely constructible. The enumeration now ranges over all
    of O1-O7 plus the special folds (vertical O5, the Beloch O6 cubic solver,
    and the general O5), so this is full single-fold constructibility, not only
    the compass-equivalent fragment. *)
Theorem point_constructible_depth_sound : forall p d,
  point_constructible_depth p d = true -> ConstructiblePoint p.
Proof.
  intros p d H. unfold point_constructible_depth in H.
  apply existsb_exists in H. destruct H as [q [Hin Heq]].
  destruct (point_eq_dec p q) as [Hpq|Hpq]; [|discriminate].
  subst q. apply (In_enum_points_constructible d). exact Hin.
Qed.

(* ===== membership of the new fold creases in the extended enum_lines ===== *)

Lemma O6_line_in_enum_S : forall d1 d2 d3 d4 p1 l1 p2 l2,
  In p1 (enum_points d1) -> In l1 (enum_lines d2) ->
  In p2 (enum_points d3) -> In l2 (enum_lines d4) ->
  In (fold_line (fold_O6 p1 l1 p2 l2))
     (enum_lines (S (Nat.max d1 (Nat.max d2 (Nat.max d3 d4))))).
Proof.
  intros d1 d2 d3 d4 p1 l1 p2 l2 H1 H2 H3 H4. simpl.
  set (D := Nat.max d1 (Nat.max d2 (Nat.max d3 d4))).
  apply incl_appr. apply incl_appr. apply incl_appr. apply incl_appr.
  apply incl_appr. apply incl_appl.
  apply in_flat_map_intro with (x := p1).
  { apply (enum_points_monotone_le d1 D); [unfold D; lia | exact H1]. }
  apply in_flat_map_intro with (x := l1).
  { apply (enum_lines_monotone_le d2 D); [unfold D; lia | exact H2]. }
  apply in_flat_map_intro with (x := p2).
  { apply (enum_points_monotone_le d3 D); [unfold D; lia | exact H3]. }
  apply in_flat_map_intro with (x := l2).
  { apply (enum_lines_monotone_le d4 D); [unfold D; lia | exact H4]. }
  simpl. left. reflexivity.
Qed.

Lemma O7_line_in_enum_S : forall d1 d2 d3 p1 l1 l2,
  In p1 (enum_points d1) -> In l1 (enum_lines d2) -> In l2 (enum_lines d3) ->
  In (fold_line (fold_O7 p1 l1 l2)) (enum_lines (S (Nat.max d1 (Nat.max d2 d3)))).
Proof.
  intros d1 d2 d3 p1 l1 l2 H1 H2 H3. simpl.
  set (D := Nat.max d1 (Nat.max d2 d3)).
  apply incl_appr. apply incl_appr. apply incl_appr. apply incl_appr.
  apply incl_appr. apply incl_appr. apply incl_appl.
  apply in_flat_map_intro with (x := p1).
  { apply (enum_points_monotone_le d1 D); [unfold D; lia | exact H1]. }
  apply in_flat_map_intro with (x := l1).
  { apply (enum_lines_monotone_le d2 D); [unfold D; lia | exact H2]. }
  apply in_flat_map_intro with (x := l2).
  { apply (enum_lines_monotone_le d3 D); [unfold D; lia | exact H3]. }
  simpl. left. reflexivity.
Qed.

Lemma O5vert_line_in_enum_S : forall d1 d2 d3 p q pc,
  In p (enum_points d1) -> In q (enum_points d2) -> In pc (enum_points d3) ->
  O5_vert_valid p q (fst pc) ->
  In (fold_line (fold_O5_vert p q (fst pc)))
     (enum_lines (S (Nat.max d1 (Nat.max d2 d3)))).
Proof.
  intros d1 d2 d3 p q pc H1 H2 H3 Hvalid. simpl.
  set (D := Nat.max d1 (Nat.max d2 d3)).
  apply incl_appr. apply incl_appr. apply incl_appr. apply incl_appr.
  apply incl_appr. apply incl_appr. apply incl_appr. apply incl_appl.
  apply in_flat_map_intro with (x := p).
  { apply (enum_points_monotone_le d1 D); [unfold D; lia | exact H1]. }
  apply in_flat_map_intro with (x := q).
  { apply (enum_points_monotone_le d2 D); [unfold D; lia | exact H2]. }
  apply in_flat_map_intro with (x := pc).
  { apply (enum_points_monotone_le d3 D); [unfold D; lia | exact H3]. }
  destruct (O5_vert_valid_dec p q (fst pc)) as [Hv | Hv].
  - simpl. left. reflexivity.
  - exfalso. apply Hv. exact Hvalid.
Qed.

Lemma beloch_line_in_enum_S : forall d1 d2 pp pq t,
  In pp (enum_points d1) -> In pq (enum_points d2) ->
  t ^ 3 + (fst pp) * t + (fst pq) = 0 ->
  In (beloch_fold_line t) (enum_lines (S (Nat.max d1 d2))).
Proof.
  intros d1 d2 pp pq t H1 H2 Hroot. simpl.
  set (D := Nat.max d1 d2).
  apply incl_appr. apply incl_appr. apply incl_appr. apply incl_appr.
  apply incl_appr. apply incl_appr. apply incl_appr. apply incl_appr. apply incl_appl.
  apply in_flat_map_intro with (x := pp).
  { apply (enum_points_monotone_le d1 D); [unfold D; lia | exact H1]. }
  apply in_flat_map_intro with (x := pq).
  { apply (enum_points_monotone_le d2 D); [unfold D; lia | exact H2]. }
  apply cubic_real_roots_line_complete. exact Hroot.
Qed.

Lemma O5general_line_in_enum_S : forall d1 d2 d3 p l q,
  In p (enum_points d1) -> In l (enum_lines d2) -> In q (enum_points d3) ->
  line_wf l -> O5_general_valid p l q -> p <> O5_general_image p l q ->
  In (fold_line (fold_O5_general p l q))
     (enum_lines (S (Nat.max d1 (Nat.max d2 d3)))).
Proof.
  intros d1 d2 d3 p l q H1 H2 H3 Hwf Hval Hne. simpl.
  set (D := Nat.max d1 (Nat.max d2 d3)).
  apply incl_appr. apply incl_appr. apply incl_appr. apply incl_appr.
  apply incl_appr. apply incl_appr. apply incl_appr. apply incl_appr. apply incl_appr.
  apply in_flat_map_intro with (x := p).
  { apply (enum_points_monotone_le d1 D); [unfold D; lia | exact H1]. }
  apply in_flat_map_intro with (x := l).
  { apply (enum_lines_monotone_le d2 D); [unfold D; lia | exact H2]. }
  apply in_flat_map_intro with (x := q).
  { apply (enum_points_monotone_le d3 D); [unfold D; lia | exact H3]. }
  destruct (O5_general_guard p l q) as [Hg | Hg].
  - simpl. left. reflexivity.
  - exfalso. apply Hg. split; [exact Hwf | split; [exact Hval | exact Hne]].
Qed.

(* ===== wrappers: eventually-in-enum for each new fold ===== *)

Lemma CF_O6_in_enum : forall p1 l1 p2 l2,
  (exists d, In p1 (enum_points d)) -> (exists d, In l1 (enum_lines d)) ->
  (exists d, In p2 (enum_points d)) -> (exists d, In l2 (enum_lines d)) ->
  exists d, In (fold_line (fold_O6 p1 l1 p2 l2)) (enum_lines d).
Proof.
  intros p1 l1 p2 l2 [d1 H1] [d2 H2] [d3 H3] [d4 H4].
  eexists. apply O6_line_in_enum_S; eassumption.
Qed.

Lemma CF_O7_in_enum : forall p1 l1 l2,
  (exists d, In p1 (enum_points d)) -> (exists d, In l1 (enum_lines d)) ->
  (exists d, In l2 (enum_lines d)) ->
  exists d, In (fold_line (fold_O7 p1 l1 l2)) (enum_lines d).
Proof.
  intros p1 l1 l2 [d1 H1] [d2 H2] [d3 H3].
  eexists. apply O7_line_in_enum_S; eassumption.
Qed.

Lemma CF_O5_vert_in_enum : forall p q c,
  (exists d, In p (enum_points d)) -> (exists d, In q (enum_points d)) ->
  (exists d, In (c, 0) (enum_points d)) -> O5_vert_valid p q c ->
  exists d, In (fold_line (fold_O5_vert p q c)) (enum_lines d).
Proof.
  intros p q c [d1 H1] [d2 H2] [d3 H3] Hvalid.
  eexists. apply (O5vert_line_in_enum_S d1 d2 d3 p q (c, 0) H1 H2 H3). exact Hvalid.
Qed.

Lemma CF_O6_beloch_in_enum : forall p q t,
  (exists d, In (p, 0) (enum_points d)) -> (exists d, In (q, 0) (enum_points d)) ->
  t * t * t + p * t + q = 0 ->
  exists d, In (fold_line (fold_O6_beloch p q t)) (enum_lines d).
Proof.
  intros p q t [d1 H1] [d2 H2] Hroot.
  eexists. apply (beloch_line_in_enum_S d1 d2 (p, 0) (q, 0) t H1 H2).
  cbn [fst]. replace (t ^ 3) with (t * t * t) by ring. exact Hroot.
Qed.

Lemma CF_O5_general_in_enum : forall p l q,
  (exists d, In p (enum_points d)) -> (exists d, In l (enum_lines d)) ->
  (exists d, In q (enum_points d)) ->
  line_wf l -> O5_general_valid p l q -> p <> O5_general_image p l q ->
  exists d, In (fold_line (fold_O5_general p l q)) (enum_lines d).
Proof.
  intros p l q [d1 H1] [d2 H2] [d3 H3] Hwf Hval Hne.
  eexists. apply O5general_line_in_enum_S; eassumption.
Qed.

(* ===== completeness: every constructible point/line/fold is enumerated ===== *)

Combined Scheme constructible_combined_ind from
  Constructible_mut, ConstructibleLine_mut, ConstructibleFold_mut.

Theorem constructible_enum_complete :
  (forall p, ConstructiblePoint p -> exists d, In p (enum_points d)) /\
  (forall l, ConstructibleLine l -> exists d, In l (enum_lines d)) /\
  (forall f, ConstructibleFold f -> exists d, In (fold_line f) (enum_lines d)).
Proof.
  apply constructible_combined_ind.
  - exists 0%nat. apply point_O_in_enum_0.
  - exists 0%nat. apply point_X_in_enum_0.
  - intros l1 l2 _ IH1 _ IH2. apply CP_inter_in_enum; assumption.
  - intros f p _ IHf _ IHp. apply CP_map_in_enum; assumption.
  - exists 0%nat. apply line_xaxis_in_enum_0.
  - exists 0%nat. apply line_yaxis_in_enum_0.
  - intros f _ IHf. exact IHf.
  - intros p1 p2 _ IH1 _ IH2. apply CF_O1_in_enum; assumption.
  - intros p1 p2 _ IH1 _ IH2. apply CF_O2_in_enum; assumption.
  - intros l1 l2 _ IH1 _ IH2. apply CF_O3_in_enum; assumption.
  - intros p l _ IHp _ IHl. apply CF_O4_in_enum; assumption.
  - intros p1 l p2 _ IH1 Hl IHl _ IH2.
    apply CF_O5_in_enum; try assumption. apply ConstructibleLine_wf; exact Hl.
  - intros p1 l1 p2 l2 _ IH1 _ IHl1 _ IH2 _ IHl2. apply CF_O6_in_enum; assumption.
  - intros p1 l1 l2 _ IH1 _ IHl1 _ IHl2. apply CF_O7_in_enum; assumption.
  - intros p q c _ IHp _ IHq _ IHc Hvalid. apply CF_O5_vert_in_enum; assumption.
  - intros p q t _ IHp _ IHq Hroot. apply CF_O6_beloch_in_enum; assumption.
  - intros p l q _ IHp _ IHl _ IHq Hwf Hval Hne. apply CF_O5_general_in_enum; assumption.
Qed.

(* ===== the full single-fold constructibility characterization ===== *)

Theorem constructible_point_iff_enum : forall p,
  ConstructiblePoint p <-> exists d, In p (enum_points d).
Proof.
  intro p. split.
  - apply constructible_enum_complete.
  - intros [d Hd]. apply (In_enum_points_constructible d). exact Hd.
Qed.

Theorem constructible_line_iff_enum : forall l,
  ConstructibleLine l <-> exists d, In l (enum_lines d).
Proof.
  intro l. split.
  - apply constructible_enum_complete.
  - intros [d Hd]. apply (In_enum_lines_constructible d). exact Hd.
Qed.

Theorem point_constructible_depth_complete : forall p,
  ConstructiblePoint p -> exists d, point_constructible_depth p d = true.
Proof.
  intros p Hp. destruct (proj1 constructible_enum_complete p Hp) as [d Hd].
  exists d. unfold point_constructible_depth. apply existsb_exists.
  exists p. split; [exact Hd | destruct (point_eq_dec p p); [reflexivity | contradiction]].
Qed.


(** ═══════════════════════════════════════════════════════════════════════════
    OCAML EXTRACTION
    ═══════════════════════════════════════════════════════════════════════════ *)
Close Scope R_scope.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope R_scope.
Theorem O6_general_solvable : forall (a b A2 B2 C2 : R), A2 <> 0 ->
  exists s, satisfies_O6_line_constraint (beloch_fold_line s)
              beloch_P1 beloch_L1 (a, b) {| A := A2; B := B2; C := C2 |}.
Proof.
  intros a b A2 B2 C2 HA2.
  assert (Hc3 : 2*A2 <> 0) by (apply Rmult_integral_contrapositive_currified; [lra|exact HA2]).
  destruct (general_cubic_root_exists (2*A2)
              (A2*a+B2*b+C2 - 2*a*A2 - 2*B2)
              (2*(a*B2+b*A2))
              (A2*a+B2*b+C2 - 2*b*B2) Hc3) as [s Hs].
  exists s. unfold satisfies_O6_line_constraint. split.
  - apply beloch_P1_reflects_to_L1.
  - unfold reflect_point, beloch_fold_line, on_line; simpl.
    assert (Hd : s*s + 1 <> 0) by nra.
    apply (Rmult_eq_reg_r (s*s + 1)); [| exact Hd].
    rewrite Rmult_0_l.
    transitivity (2*A2*s^3 + (A2*a+B2*b+C2 - 2*a*A2 - 2*B2)*s^2
                  + 2*(a*B2+b*A2)*s + (A2*a+B2*b+C2 - 2*b*B2)).
    + field. exact Hd.
    + exact Hs.
Qed.

(* a general cubic with nonzero leading coefficient and negative depressed
   discriminant has a unique real root: the single-solution O6 case *)
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
Theorem O6_scaled_solvable : forall (d1 a b A2 B2 C2 : R), d1 <> 0 -> A2 <> 0 ->
  exists s, satisfies_O6_line_constraint
              {| A := s; B := -1; C := -(d1*s*s) |}
              (0, d1) {| A := 0; B := 1; C := d1 |}
              (a, b) {| A := A2; B := B2; C := C2 |}.
Proof.
  intros d1 a b A2 B2 C2 Hd1 HA2.
  assert (Hc3 : 2*d1*A2 <> 0).
  { apply Rmult_integral_contrapositive_currified;
      [apply Rmult_integral_contrapositive_currified; [lra|exact Hd1] | exact HA2]. }
  destruct (general_cubic_root_exists (2*d1*A2)
              (A2*a+B2*b+C2 - 2*a*A2 - 2*d1*B2)
              (2*(a*B2+b*A2))
              (A2*a+B2*b+C2 - 2*b*B2) Hc3) as [s Hs].
  exists s. unfold satisfies_O6_line_constraint. split.
  - unfold reflect_point, on_line; simpl.
    assert (Hd : s*s + 1 <> 0) by nra.
    apply (Rmult_eq_reg_r (s*s + 1)); [| exact Hd].
    rewrite Rmult_0_l. field. exact Hd.
  - unfold reflect_point, on_line; simpl.
    assert (Hd : s*s + 1 <> 0) by nra.
    apply (Rmult_eq_reg_r (s*s + 1)); [| exact Hd].
    rewrite Rmult_0_l.
    transitivity (2*d1*A2*(s^3) + (A2*a+B2*b+C2 - 2*a*A2 - 2*d1*B2)*(s^2)
                  + 2*(a*B2+b*A2)*s + (A2*a+B2*b+C2 - 2*b*B2)).
    + field. exact Hd.
    + exact Hs.
Qed.

(* Rigid motions preserve reflection and incidence, so an arbitrary O6
   configuration reduces to the horizontal-directrix form O6_scaled_solvable
   handles.  These are the commutation lemmas for that reduction. *)
Definition translate_point (p v : Point) : Point := (fst p + fst v, snd p + snd v).
Definition translate_line (l : Line) (v : Point) : Line :=
  {| A := A l; B := B l; C := C l - A l * fst v - B l * snd v |}.
Definition rotate_line (l : Line) (th : R) : Line :=
  {| A := A l * cos th - B l * sin th; B := A l * sin th + B l * cos th; C := C l |}.

Lemma on_line_translate : forall p l v,
  on_line (translate_point p v) (translate_line l v) <-> on_line p l.
Proof.
  intros [x y] l [vx vy]. unfold on_line, translate_point, translate_line; simpl.
  split; intro H; lra.
Qed.

Lemma reflect_translate : forall p l v, line_wf l ->
  reflect_point (translate_point p v) (translate_line l v) = translate_point (reflect_point p l) v.
Proof.
  intros [x y] l [vx vy] Hwf.
  assert (Hd : A l * A l + B l * B l <> 0) by (destruct Hwf as [H|H]; nra).
  unfold reflect_point, translate_point, translate_line; simpl.
  f_equal; field; exact Hd.
Qed.

Lemma on_line_rotate : forall p l th,
  on_line (rotate_point p th) (rotate_line l th) <-> on_line p l.
Proof.
  intros [x y] l th. unfold on_line, rotate_point, rotate_line; simpl.
  assert (Hcs : cos th * cos th + sin th * sin th = 1)
    by (pose proof (sin2_cos2 th) as H; unfold Rsqr in H; lra).
  assert (Hrot : (A l * cos th - B l * sin th) * (x * cos th - y * sin th) +
                 (A l * sin th + B l * cos th) * (x * sin th + y * cos th) + C l
                 = A l * x + B l * y + C l)
    by (transitivity ((A l * x + B l * y) * (cos th * cos th + sin th * sin th) + C l);
        [ring | rewrite Hcs; ring]).
  rewrite Hrot. reflexivity.
Qed.

Lemma reflect_rotate : forall p l th, line_wf l ->
  reflect_point (rotate_point p th) (rotate_line l th) = rotate_point (reflect_point p l) th.
Proof.
  intros [x y] l th Hwf.
  assert (Hcs : cos th * cos th + sin th * sin th = 1)
    by (pose proof (sin2_cos2 th) as H; unfold Rsqr in H; lra).
  assert (Hd : A l * A l + B l * B l <> 0) by (destruct Hwf as [H|H]; nra).
  assert (Hden : (A l * cos th - B l * sin th) * (A l * cos th - B l * sin th) +
                 (A l * sin th + B l * cos th) * (A l * sin th + B l * cos th)
                 = A l * A l + B l * B l)
    by (transitivity ((A l * A l + B l * B l) * (cos th * cos th + sin th * sin th));
        [ring | rewrite Hcs; ring]).
  assert (Hnum : (A l * cos th - B l * sin th) * (x * cos th - y * sin th) +
                 (A l * sin th + B l * cos th) * (x * sin th + y * cos th) + C l
                 = A l * x + B l * y + C l)
    by (transitivity ((A l * x + B l * y) * (cos th * cos th + sin th * sin th) + C l);
        [ring | rewrite Hcs; ring]).
  unfold reflect_point, rotate_point, rotate_line; simpl.
  rewrite Hden, Hnum. f_equal; field; exact Hd.
Qed.

(* An O6 constraint transfers along a rotation and a translation: if a crease
   solves O6 for a configuration, the moved crease solves O6 for the moved
   configuration.  With O6_scaled_solvable, this reduces any O6 problem to the
   horizontal-directrix reference form (modulo the explicit normalizing motion). *)
Lemma satisfies_O6_rotate : forall th p1 l1 p2 l2 crease,
  line_wf crease ->
  satisfies_O6_line_constraint crease p1 l1 p2 l2 ->
  satisfies_O6_line_constraint (rotate_line crease th)
     (rotate_point p1 th) (rotate_line l1 th) (rotate_point p2 th) (rotate_line l2 th).
Proof.
  intros th p1 l1 p2 l2 crease Hwf [H1 H2].
  unfold satisfies_O6_line_constraint in *. split.
  - rewrite (reflect_rotate p1 crease th Hwf), on_line_rotate. exact H1.
  - rewrite (reflect_rotate p2 crease th Hwf), on_line_rotate. exact H2.
Qed.

Lemma satisfies_O6_translate : forall v p1 l1 p2 l2 crease,
  line_wf crease ->
  satisfies_O6_line_constraint crease p1 l1 p2 l2 ->
  satisfies_O6_line_constraint (translate_line crease v)
     (translate_point p1 v) (translate_line l1 v) (translate_point p2 v) (translate_line l2 v).
Proof.
  intros v p1 l1 p2 l2 crease Hwf [H1 H2].
  unfold satisfies_O6_line_constraint in *. split.
  - rewrite (reflect_translate p1 crease v Hwf), on_line_translate. exact H1.
  - rewrite (reflect_translate p2 crease v Hwf), on_line_translate. exact H2.
Qed.

(* unit-circle parametrization: any (c,s) on the unit circle is (cos th, sin th)
   for some angle th - the rotation that aligns an arbitrary directrix to
   horizontal in the O6 normalization. *)
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
Lemma rotate_point_zero : forall p, rotate_point p 0 = p.
Proof. intros [x y]. unfold rotate_point; simpl. rewrite cos_0, sin_0. f_equal; ring. Qed.

Lemma rotate_point_compose : forall p a b,
  rotate_point (rotate_point p a) b = rotate_point p (a + b).
Proof.
  intros [x y] a b. unfold rotate_point; simpl. rewrite cos_plus, sin_plus. f_equal; ring.
Qed.

Lemma reflect_scale : forall p l k, k <> 0 -> line_wf l ->
  reflect_point p {| A := k * A l; B := k * B l; C := k * C l |} = reflect_point p l.
Proof.
  intros [x y] l k Hk Hwf.
  assert (Hd : A l * A l + B l * B l <> 0) by (destruct Hwf as [H|H]; nra).
  assert (Hd2 : k * A l * (k * A l) + k * B l * (k * B l) <> 0).
  { replace (k * A l * (k * A l) + k * B l * (k * B l)) with (k * k * (A l * A l + B l * B l)) by ring.
    apply Rmult_integral_contrapositive_currified;
      [apply Rmult_integral_contrapositive_currified; exact Hk | exact Hd]. }
  unfold reflect_point; simpl. f_equal; field; split; assumption.
Qed.

(* Record eta for Line, rotation composition on lines, and the O6 normalization
   machinery: a crease solving the reference O6 configuration transports, under
   the rigid motion aligning (p1,l1) to (focus (0,d1), directrix y=-d1), to a
   crease solving an arbitrary configuration. *)
Lemma line_eta : forall l, {| A := A l; B := B l; C := C l |} = l.
Proof. intros [a b c]; reflexivity. Qed.

Lemma rotate_line_zero : forall l, rotate_line l 0 = l.
Proof.
  intros l. destruct l as [a b c]. unfold rotate_line; simpl.
  rewrite cos_0, sin_0. f_equal; ring.
Qed.

Lemma rotate_line_compose : forall l a b,
  rotate_line (rotate_line l a) b = rotate_line l (a + b).
Proof.
  intros l a b. destruct l as [u v w]. unfold rotate_line; simpl.
  rewrite cos_plus, sin_plus. f_equal; ring.
Qed.

Lemma satisfies_O6_scale_l1 : forall crease p1 l1 p2 l2 k, k <> 0 ->
  satisfies_O6_line_constraint crease p1 {| A := k * A l1; B := k * B l1; C := k * C l1 |} p2 l2 <->
  satisfies_O6_line_constraint crease p1 l1 p2 l2.
Proof.
  intros crease p1 l1 p2 l2 k Hk. unfold satisfies_O6_line_constraint.
  pose proof (on_line_scale (reflect_point p1 crease) (A l1) (B l1) (C l1) k Hk) as Hsc.
  destruct l1 as [a1 b1 c1]. simpl in Hsc. rewrite <- Hsc. tauto.
Qed.

Lemma motion_inv_point : forall x th v,
  translate_point (rotate_point (rotate_point (translate_point x (- fst v, - snd v)) (- th)) th) v = x.
Proof.
  intros [x y] th [vx vy]. rewrite rotate_point_compose. replace (- th + th) with 0 by ring.
  rewrite rotate_point_zero. unfold translate_point; simpl. f_equal; ring.
Qed.

Lemma motion_inv_line : forall l th v,
  translate_line (rotate_line (rotate_line (translate_line l (- fst v, - snd v)) (- th)) th) v = l.
Proof.
  intros l th [vx vy]. rewrite rotate_line_compose. replace (- th + th) with 0 by ring.
  rewrite rotate_line_zero. destruct l as [a b c]. unfold translate_line; simpl. f_equal; ring.
Qed.

Lemma line_wf_rotate : forall l th, line_wf l -> line_wf (rotate_line l th).
Proof.
  intros l th Hwf.
  assert (Hd : A l * A l + B l * B l <> 0) by (destruct Hwf as [H|H]; nra).
  unfold line_wf, rotate_line; simpl.
  destruct (Req_dec (A l * cos th - B l * sin th) 0) as [HA|HA]; [right | left; exact HA].
  intro HB.
  assert (Hcs : cos th * cos th + sin th * sin th = 1)
    by (pose proof (sin2_cos2 th) as H; unfold Rsqr in H; lra).
  apply Hd. nra.
Qed.

Lemma line_wf_rotate_translate : forall l th v, line_wf l ->
  line_wf (translate_line (rotate_line l th) v).
Proof.
  intros l th v Hwf.
  assert (Hd : A l * A l + B l * B l <> 0) by (destruct Hwf as [H|H]; nra).
  unfold line_wf, translate_line, rotate_line; simpl.
  destruct (Req_dec (A l * cos th - B l * sin th) 0) as [HA|HA]; [right | left; exact HA].
  intro HB.
  assert (Hcs : cos th * cos th + sin th * sin th = 1)
    by (pose proof (sin2_cos2 th) as H; unfold Rsqr in H; lra).
  apply Hd. nra.
Qed.

(* General exact O6 solvability for arbitrary constructible foci and directrices:
   reduce to the reference parabola by the rigid motion aligning l1 to horizontal
   (exists_angle), solve there (O6_scaled_solvable), and transport the crease back. *)
Theorem O6_fully_general : forall p1 l1 p2 l2,
  line_wf l1 -> line_wf l2 -> ~ on_line p1 l1 ->
  A l1 * B l2 <> A l2 * B l1 ->
  exists crease, line_wf crease /\ satisfies_O6_line_constraint crease p1 l1 p2 l2.
Proof.
  intros p1 l1 p2 l2 Hwf1 Hwf2 Hp1 Hpar. destruct p1 as [px py].
  set (N := R_sqrt.sqrt (A l1 * A l1 + B l1 * B l1)).
  assert (HA2B2 : 0 < A l1 * A l1 + B l1 * B l1) by (destruct Hwf1 as [H|H]; nra).
  assert (HN : 0 < N) by (unfold N; apply sqrt_lt_R0; exact HA2B2).
  assert (HN2 : N * N = A l1 * A l1 + B l1 * B l1) by (unfold N; apply sqrt_sqrt; lra).
  assert (HN2p : N ^ 2 = A l1 * A l1 + B l1 * B l1) by (simpl; rewrite Rmult_1_r; exact HN2).
  set (d1 := (A l1 * px + B l1 * py + C l1) / (2 * N)).
  assert (Hp1ne : A l1 * px + B l1 * py + C l1 <> 0)
    by (intro Hc; apply Hp1; unfold on_line; simpl; lra).
  assert (Hd1 : d1 <> 0).
  { unfold d1. intro Hc. apply Hp1ne.
    apply (Rmult_eq_reg_r (/ (2 * N))); [| apply Rinv_neq_0_compat; lra].
    rewrite Rmult_0_l. exact Hc. }
  destruct (exists_angle (B l1 / N) (- A l1 / N)) as [th [Hcos Hsin]].
  { replace (B l1 / N * (B l1 / N) + - A l1 / N * (- A l1 / N))
      with ((A l1 * A l1 + B l1 * B l1) / (N * N)) by (field; lra).
    rewrite HN2. field; lra. }
  set (v := (px - d1 * A l1 / N, py - d1 * B l1 / N)).
  assert (Hfocus : translate_point (rotate_point (0, d1) th) v = (px, py)).
  { unfold rotate_point, translate_point, v; simpl. rewrite Hcos, Hsin. f_equal; field; lra. }
  assert (Hdir : translate_line (rotate_line {| A := 0; B := 1; C := d1 |} th) v
                 = {| A := / N * A l1; B := / N * B l1; C := / N * C l1 |}).
  { unfold rotate_line, translate_line, v; simpl. f_equal.
    - rewrite ?Hcos, ?Hsin; field; lra.
    - rewrite ?Hcos, ?Hsin; field; lra.
    - rewrite ?Hcos, ?Hsin.
      replace (d1 - (0 * (B l1 / N) - 1 * (- A l1 / N)) * (px - d1 * A l1 / N)
                  - (0 * (- A l1 / N) + 1 * (B l1 / N)) * (py - d1 * B l1 / N))
        with (d1 + d1 * (A l1 * A l1 + B l1 * B l1) / (N * N)
              - (A l1 * px + B l1 * py) / N) by (field; lra).
      rewrite HN2. unfold d1. field. split; lra. }
  assert (HNne : N <> 0) by lra.
  assert (HA2 : A (rotate_line (translate_line l2 (- fst v, - snd v)) (- th)) <> 0).
  { unfold rotate_line, translate_line; simpl. rewrite cos_neg, sin_neg, Hcos, Hsin.
    intro Hc. apply Hpar.
    apply (Rmult_eq_reg_r (/ N)); [| apply Rinv_neq_0_compat; exact HNne].
    field_simplify; try exact HNne. nra. }
  destruct (O6_scaled_solvable d1
              (fst (rotate_point (translate_point p2 (- fst v, - snd v)) (- th)))
              (snd (rotate_point (translate_point p2 (- fst v, - snd v)) (- th)))
              (A (rotate_line (translate_line l2 (- fst v, - snd v)) (- th)))
              (B (rotate_line (translate_line l2 (- fst v, - snd v)) (- th)))
              (C (rotate_line (translate_line l2 (- fst v, - snd v)) (- th)))
              Hd1 HA2) as [s Hs].
  exists (translate_line (rotate_line {| A := s; B := -1; C := - (d1 * s * s) |} th) v).
  assert (Hwfc : line_wf {| A := s; B := -1; C := - (d1 * s * s) |}) by (right; simpl; lra).
  split.
  - apply line_wf_rotate_translate. exact Hwfc.
  - pose proof (satisfies_O6_rotate th _ _ _ _ _ Hwfc Hs) as Hr.
    pose proof (satisfies_O6_translate v _ _ _ _ _ (line_wf_rotate _ th Hwfc) Hr) as Ht.
    rewrite <- surjective_pairing in Ht.
    rewrite (line_eta (rotate_line (translate_line l2 (- fst v, - snd v)) (- th))) in Ht.
    rewrite Hfocus, Hdir, (motion_inv_point p2 th v), (motion_inv_line l2 th v) in Ht.
    apply (proj1 (satisfies_O6_scale_l1 _ (px, py) l1 p2 l2 (/ N) (Rinv_neq_0_compat N HNne))).
    exact Ht.
Qed.

(* ============================================================================
   General O6 as a constructible operation.  The general-position O6 crease has
   origami coordinates -- it is a rigid-motion image of a crease whose slope is an
   origami root of an origami-coefficient cubic -- and it equals, up to scale, the
   perpendicular bisector of p1 and its reflection, hence the O2 fold of two
   constructible points.
   ============================================================================ *)

(** Origami numbers are closed under roots of a general cubic with origami
    coefficients: depress the cubic, then apply the depressed-root constructor. *)
Lemma OrigamiNum_general_cubic_root : forall c3 c2 c1 c0,
  OrigamiNum c3 -> OrigamiNum c2 -> OrigamiNum c1 -> OrigamiNum c0 -> c3 <> 0 ->
  exists s, OrigamiNum s /\ c3 * (s ^ 3) + c2 * (s ^ 2) + c1 * s + c0 = 0.
Proof.
  intros c3 c2 c1 c0 H3 H2 H1 H0 Hc3.
  assert (O3 : OrigamiNum 3) by apply Origami_three.
  assert (O2 : OrigamiNum 2) by (replace 2 with (1 + 1) by ring; apply ON_add; apply ON_1).
  assert (O27 : OrigamiNum 27) by
    (replace 27 with (3 * 3 * 3) by ring; apply ON_mul; [apply ON_mul; exact O3 | exact O3]).
  assert (H3c3 : 3 * c3 <> 0) by (apply Rmult_integral_contrapositive_currified; [lra | exact Hc3]).
  assert (H3c3c3 : 3 * c3 * c3 <> 0)
    by (apply Rmult_integral_contrapositive_currified; [exact H3c3 | exact Hc3]).
  assert (H27c3 : 27 * c3 * c3 * c3 <> 0).
  { apply Rmult_integral_contrapositive_currified; [| exact Hc3].
    apply Rmult_integral_contrapositive_currified; [| exact Hc3].
    apply Rmult_integral_contrapositive_currified; [lra | exact Hc3]. }
  assert (ON3c3 : OrigamiNum (3 * c3)) by (apply ON_mul; [exact O3 | exact H3]).
  assert (ON3c3c3 : OrigamiNum (3 * c3 * c3)) by (apply ON_mul; [exact ON3c3 | exact H3]).
  assert (ON27c3 : OrigamiNum (27 * c3 * c3 * c3))
    by (apply ON_mul; [apply ON_mul; [apply ON_mul; [exact O27 | exact H3] | exact H3] | exact H3]).
  set (sh := c2 / (3 * c3)).
  set (P := c1 / c3 - c2 * c2 / (3 * c3 * c3)).
  set (Q := c0 / c3 - c1 * c2 / (3 * c3 * c3) + 2 * (c2 * c2 * c2) / (27 * c3 * c3 * c3)).
  assert (HshON : OrigamiNum sh) by (unfold sh; apply Origami_div; [exact H2 | exact ON3c3 | exact H3c3]).
  assert (HPON : OrigamiNum P).
  { unfold P. apply ON_sub.
    - apply Origami_div; [exact H1 | exact H3 | exact Hc3].
    - apply Origami_div; [apply ON_mul; [exact H2 | exact H2] | exact ON3c3c3 | exact H3c3c3]. }
  assert (HQON : OrigamiNum Q).
  { unfold Q. apply ON_add.
    - apply ON_sub.
      + apply Origami_div; [exact H0 | exact H3 | exact Hc3].
      + apply Origami_div; [apply ON_mul; [exact H1 | exact H2] | exact ON3c3c3 | exact H3c3c3].
    - apply Origami_div;
        [apply ON_mul; [exact O2 | apply ON_mul; [apply ON_mul; [exact H2 | exact H2] | exact H2]]
        | exact ON27c3 | exact H27c3]. }
  destruct (depressed_cubic_root_exists P Q) as [u Hu].
  unfold is_cubic_root, depressed_cubic in Hu.
  assert (HuON : OrigamiNum u).
  { apply (ON_cubic_root P Q u HPON HQON). replace (u * u * u) with (u ^ 3) by ring. exact Hu. }
  exists (u - sh). split.
  - apply ON_sub; assumption.
  - assert (Hdep : c3 * ((u - sh) ^ 3) + c2 * ((u - sh) ^ 2) + c1 * (u - sh) + c0
                   = c3 * (u ^ 3 + P * u + Q)) by (unfold sh, P, Q; field; exact Hc3).
    rewrite Hdep, Hu. ring.
Qed.

(** rotate_point preserves origami coordinates. *)
Lemma GoodPoint_rotate : forall p th,
  GoodPoint p -> OrigamiNum (cos th) -> OrigamiNum (sin th) ->
  GoodPoint (rotate_point p th).
Proof.
  intros [x y] th [Hx Hy] Hc Hs. unfold rotate_point, GoodPoint; simpl in *.
  split.
  - apply ON_sub; apply ON_mul; assumption.
  - apply ON_add; apply ON_mul; assumption.
Qed.

(** translate_point preserves origami coordinates. *)
Lemma GoodPoint_translate : forall p v,
  GoodPoint p -> GoodPoint v -> GoodPoint (translate_point p v).
Proof.
  intros [x y] [vx vy] [Hx Hy] [Hvx Hvy]. unfold translate_point, GoodPoint; simpl in *.
  split; apply ON_add; assumption.
Qed.

(** rotate_line preserves origami coefficients. *)
Lemma GoodLine_rotate : forall l th,
  GoodLine l -> OrigamiNum (cos th) -> OrigamiNum (sin th) ->
  GoodLine (rotate_line l th).
Proof.
  intros l th [HA [HB HC]] Hc Hs. unfold rotate_line, GoodLine; simpl.
  split; [| split].
  - apply ON_sub; apply ON_mul; assumption.
  - apply ON_add; apply ON_mul; assumption.
  - exact HC.
Qed.

(** translate_line preserves origami coefficients. *)
Lemma GoodLine_translate : forall l v,
  GoodLine l -> GoodPoint v -> GoodLine (translate_line l v).
Proof.
  intros l [vx vy] [HA [HB HC]] [Hvx Hvy]. unfold translate_line, GoodLine; simpl in *.
  split; [exact HA | split; [exact HB |]].
  apply ON_sub; [apply ON_sub; [exact HC | apply ON_mul; [exact HA | exact Hvx]]
                | apply ON_mul; [exact HB | exact Hvy]].
Qed.

(** Reflection across a line is invariant under scaling its coefficients. *)
Lemma reflect_point_scale_eq : forall p k l,
  k <> 0 -> A l * A l + B l * B l <> 0 ->
  reflect_point p {| A := k * A l; B := k * B l; C := k * C l |} = reflect_point p l.
Proof.
  intros [x y] k l Hk Hnz. unfold reflect_point; simpl.
  assert (Hknz : k * A l * (k * A l) + k * B l * (k * B l) <> 0).
  { replace (k * A l * (k * A l) + k * B l * (k * B l))
      with (k * k * (A l * A l + B l * B l)) by ring.
    apply Rmult_integral_contrapositive_currified;
      [apply Rmult_integral_contrapositive_currified; exact Hk | exact Hnz]. }
  f_equal; field; split; assumption.
Qed.

(** A point with origami coordinates is constructible. *)
Lemma good_constructible_point : forall p, GoodPoint p -> ConstructiblePoint p.
Proof.
  intros [x y] [Hx Hy]. simpl in Hx, Hy.
  apply point_xy_constructible.
  - apply origami_xaxis_point; exact Hx.
  - apply yaxis_from_xaxis. apply origami_xaxis_point; exact Hy.
Qed.

(** The reference-parabola O6 solve with an origami crease slope, for origami
    inputs (the same cubic as O6_scaled_solvable, solved inside OrigamiNum). *)
Lemma O6_scaled_solvable_good : forall d1 a b A2 B2 C2,
  OrigamiNum d1 -> OrigamiNum a -> OrigamiNum b ->
  OrigamiNum A2 -> OrigamiNum B2 -> OrigamiNum C2 ->
  d1 <> 0 -> A2 <> 0 ->
  exists s, OrigamiNum s /\
    satisfies_O6_line_constraint
      {| A := s; B := -1; C := -(d1 * s * s) |}
      (0, d1) {| A := 0; B := 1; C := d1 |}
      (a, b) {| A := A2; B := B2; C := C2 |}.
Proof.
  intros d1 a b A2 B2 C2 Hd1 Ha Hb HA2 HB2 HC2 Hd1n HA2n.
  assert (O2 : OrigamiNum 2) by (replace 2 with (1 + 1) by ring; apply ON_add; apply ON_1).
  assert (Hc3 : 2 * d1 * A2 <> 0).
  { apply Rmult_integral_contrapositive_currified;
      [apply Rmult_integral_contrapositive_currified; [lra | exact Hd1n] | exact HA2n]. }
  assert (ONc3 : OrigamiNum (2 * d1 * A2))
    by (apply ON_mul; [apply ON_mul; [exact O2 | exact Hd1] | exact HA2]).
  assert (ONc2 : OrigamiNum (A2 * a + B2 * b + C2 - 2 * a * A2 - 2 * d1 * B2)).
  { apply ON_sub; [apply ON_sub;
      [apply ON_add; [apply ON_add; [apply ON_mul; [exact HA2 | exact Ha]
                                    | apply ON_mul; [exact HB2 | exact Hb]] | exact HC2]
      | apply ON_mul; [apply ON_mul; [exact O2 | exact Ha] | exact HA2]]
    | apply ON_mul; [apply ON_mul; [exact O2 | exact Hd1] | exact HB2]]. }
  assert (ONc1 : OrigamiNum (2 * (a * B2 + b * A2)))
    by (apply ON_mul; [exact O2 | apply ON_add; [apply ON_mul; [exact Ha | exact HB2]
                                                | apply ON_mul; [exact Hb | exact HA2]]]).
  assert (ONc0 : OrigamiNum (A2 * a + B2 * b + C2 - 2 * b * B2)).
  { apply ON_sub; [apply ON_add; [apply ON_add; [apply ON_mul; [exact HA2 | exact Ha]
                                                | apply ON_mul; [exact HB2 | exact Hb]] | exact HC2]
    | apply ON_mul; [apply ON_mul; [exact O2 | exact Hb] | exact HB2]]. }
  destruct (OrigamiNum_general_cubic_root _ _ _ _ ONc3 ONc2 ONc1 ONc0 Hc3) as [s [Hson Hs]].
  exists s. split; [exact Hson |].
  unfold satisfies_O6_line_constraint. split.
  - unfold reflect_point, on_line; simpl.
    assert (Hd : s * s + 1 <> 0) by nra.
    apply (Rmult_eq_reg_r (s * s + 1)); [| exact Hd]. rewrite Rmult_0_l. field. exact Hd.
  - unfold reflect_point, on_line; simpl.
    assert (Hd : s * s + 1 <> 0) by nra.
    apply (Rmult_eq_reg_r (s * s + 1)); [| exact Hd]. rewrite Rmult_0_l.
    transitivity (2 * d1 * A2 * (s ^ 3)
                  + (A2 * a + B2 * b + C2 - 2 * a * A2 - 2 * d1 * B2) * (s ^ 2)
                  + 2 * (a * B2 + b * A2) * s + (A2 * a + B2 * b + C2 - 2 * b * B2)).
    + field. exact Hd.
    + exact Hs.
Qed.

(** General-position O6 has an origami-coordinate crease for origami inputs: the
    same construction as O6_fully_general, with OrigamiNum threaded through the
    rigid-motion reduction and the origami cubic root. *)
Theorem O6_general_good : forall p1 l1 p2 l2,
  GoodPoint p1 -> GoodLine l1 -> GoodPoint p2 -> GoodLine l2 ->
  line_wf l1 -> line_wf l2 -> ~ on_line p1 l1 ->
  A l1 * B l2 <> A l2 * B l1 ->
  exists crease, GoodLine crease /\ line_wf crease /\
    satisfies_O6_line_constraint crease p1 l1 p2 l2.
Proof.
  intros p1 l1 p2 l2 HGp1 HGl1 HGp2 HGl2 Hwf1 Hwf2 Hp1 Hpar.
  destruct HGl1 as [HoA1 [HoB1 HoC1]]. destruct HGl2 as [HoA2 [HoB2 HoC2]].
  destruct p1 as [px py]. destruct HGp1 as [Hopx Hopy]. simpl in Hopx, Hopy.
  assert (Ho2 : OrigamiNum 2) by (replace 2 with (1 + 1) by ring; apply ON_add; apply ON_1).
  set (N := R_sqrt.sqrt (A l1 * A l1 + B l1 * B l1)).
  assert (HA2B2 : 0 < A l1 * A l1 + B l1 * B l1) by (destruct Hwf1 as [H|H]; nra).
  assert (HN : 0 < N) by (unfold N; apply sqrt_lt_R0; exact HA2B2).
  assert (HN2 : N * N = A l1 * A l1 + B l1 * B l1) by (unfold N; apply sqrt_sqrt; lra).
  assert (HN2p : N ^ 2 = A l1 * A l1 + B l1 * B l1) by (simpl; rewrite Rmult_1_r; exact HN2).
  assert (HNne : N <> 0) by lra.
  assert (HoN : OrigamiNum N)
    by (unfold N; apply ON_sqrt; [apply ON_add; apply ON_mul; assumption | lra]).
  set (d1 := (A l1 * px + B l1 * py + C l1) / (2 * N)).
  assert (Hp1ne : A l1 * px + B l1 * py + C l1 <> 0)
    by (intro Hc; apply Hp1; unfold on_line; simpl; lra).
  assert (Hd1 : d1 <> 0).
  { unfold d1. intro Hc. apply Hp1ne.
    apply (Rmult_eq_reg_r (/ (2 * N))); [| apply Rinv_neq_0_compat; lra].
    rewrite Rmult_0_l. exact Hc. }
  assert (H2Nne : 2 * N <> 0) by lra.
  assert (Hod1 : OrigamiNum d1).
  { unfold d1. apply Origami_div.
    - apply ON_add; [apply ON_add; apply ON_mul; assumption | exact HoC1].
    - apply ON_mul; [exact Ho2 | exact HoN].
    - exact H2Nne. }
  destruct (exists_angle (B l1 / N) (- A l1 / N)) as [th [Hcos Hsin]].
  { replace (B l1 / N * (B l1 / N) + - A l1 / N * (- A l1 / N))
      with ((A l1 * A l1 + B l1 * B l1) / (N * N)) by (field; lra).
    rewrite HN2. field; lra. }
  assert (Hocos : OrigamiNum (cos th))
    by (rewrite Hcos; apply Origami_div; [exact HoB1 | exact HoN | exact HNne]).
  assert (Hosin : OrigamiNum (sin th)).
  { rewrite Hsin. replace (- A l1 / N) with (- (A l1 / N)) by (field; exact HNne).
    apply Origami_neg. apply Origami_div; [exact HoA1 | exact HoN | exact HNne]. }
  set (v := (px - d1 * A l1 / N, py - d1 * B l1 / N)).
  assert (HGv : GoodPoint v).
  { unfold v, GoodPoint; simpl. split.
    - apply ON_sub; [exact Hopx |
        apply Origami_div; [apply ON_mul; [exact Hod1 | exact HoA1] | exact HoN | exact HNne]].
    - apply ON_sub; [exact Hopy |
        apply Origami_div; [apply ON_mul; [exact Hod1 | exact HoB1] | exact HoN | exact HNne]]. }
  assert (Hfocus : translate_point (rotate_point (0, d1) th) v = (px, py)).
  { unfold rotate_point, translate_point, v; simpl. rewrite Hcos, Hsin. f_equal; field; lra. }
  assert (Hdir : translate_line (rotate_line {| A := 0; B := 1; C := d1 |} th) v
                 = {| A := / N * A l1; B := / N * B l1; C := / N * C l1 |}).
  { unfold rotate_line, translate_line, v; simpl. f_equal.
    - rewrite ?Hcos, ?Hsin; field; lra.
    - rewrite ?Hcos, ?Hsin; field; lra.
    - rewrite ?Hcos, ?Hsin.
      replace (d1 - (0 * (B l1 / N) - 1 * (- A l1 / N)) * (px - d1 * A l1 / N)
                  - (0 * (- A l1 / N) + 1 * (B l1 / N)) * (py - d1 * B l1 / N))
        with (d1 + d1 * (A l1 * A l1 + B l1 * B l1) / (N * N)
              - (A l1 * px + B l1 * py) / N) by (field; lra).
      rewrite HN2. unfold d1. field. split; lra. }
  assert (HA2 : A (rotate_line (translate_line l2 (- fst v, - snd v)) (- th)) <> 0).
  { unfold rotate_line, translate_line; simpl. rewrite cos_neg, sin_neg, Hcos, Hsin.
    intro Hc. apply Hpar.
    apply (Rmult_eq_reg_r (/ N)); [| apply Rinv_neq_0_compat; exact HNne].
    field_simplify; try exact HNne. nra. }
  assert (Hocosn : OrigamiNum (cos (- th))) by (rewrite cos_neg; exact Hocos).
  assert (Hosinn : OrigamiNum (sin (- th))) by (rewrite sin_neg; apply Origami_neg; exact Hosin).
  assert (HGmv : GoodPoint (- fst v, - snd v)).
  { destruct HGv as [Hvx Hvy]. unfold GoodPoint; simpl.
    split; apply Origami_neg; [exact Hvx | exact Hvy]. }
  assert (HGp2m : GoodPoint (rotate_point (translate_point p2 (- fst v, - snd v)) (- th)))
    by (apply GoodPoint_rotate;
        [apply GoodPoint_translate; [exact HGp2 | exact HGmv] | exact Hocosn | exact Hosinn]).
  assert (HGl2m : GoodLine (rotate_line (translate_line l2 (- fst v, - snd v)) (- th)))
    by (apply GoodLine_rotate;
        [apply GoodLine_translate;
           [split; [exact HoA2 | split; [exact HoB2 | exact HoC2]] | exact HGmv]
        | exact Hocosn | exact Hosinn]).
  destruct HGp2m as [Hoa Hob]. destruct HGl2m as [HoA2' [HoB2' HoC2']].
  destruct (O6_scaled_solvable_good d1
              (fst (rotate_point (translate_point p2 (- fst v, - snd v)) (- th)))
              (snd (rotate_point (translate_point p2 (- fst v, - snd v)) (- th)))
              (A (rotate_line (translate_line l2 (- fst v, - snd v)) (- th)))
              (B (rotate_line (translate_line l2 (- fst v, - snd v)) (- th)))
              (C (rotate_line (translate_line l2 (- fst v, - snd v)) (- th)))
              Hod1 Hoa Hob HoA2' HoB2' HoC2' Hd1 HA2) as [s [Hson Hs]].
  exists (translate_line (rotate_line {| A := s; B := -1; C := - (d1 * s * s) |} th) v).
  assert (Hwfc : line_wf {| A := s; B := -1; C := - (d1 * s * s) |}) by (right; simpl; lra).
  assert (HGref : GoodLine {| A := s; B := -1; C := - (d1 * s * s) |}).
  { unfold GoodLine; cbn [A B C]. split; [exact Hson | split].
    - replace (-1) with (0 - 1) by ring. apply ON_sub; [apply ON_0 | apply ON_1].
    - apply Origami_neg. apply ON_mul; [apply ON_mul; [exact Hod1 | exact Hson] | exact Hson]. }
  split; [| split].
  - apply GoodLine_translate;
      [apply GoodLine_rotate; [exact HGref | exact Hocos | exact Hosin] | exact HGv].
  - apply line_wf_rotate_translate. exact Hwfc.
  - pose proof (satisfies_O6_rotate th _ _ _ _ _ Hwfc Hs) as Hr.
    pose proof (satisfies_O6_translate v _ _ _ _ _ (line_wf_rotate _ th Hwfc) Hr) as Ht.
    rewrite <- surjective_pairing in Ht.
    rewrite (line_eta (rotate_line (translate_line l2 (- fst v, - snd v)) (- th))) in Ht.
    rewrite Hfocus, Hdir, (motion_inv_point p2 th v), (motion_inv_line l2 th v) in Ht.
    apply (proj1 (satisfies_O6_scale_l1 _ (px, py) l1 p2 l2 (/ N) (Rinv_neq_0_compat N HNne))).
    exact Ht.
Qed.

(** Reflecting any point across the perpendicular bisector of p and its mirror
    image in c equals reflecting across c -- the two lines coincide -- so the
    perpendicular bisector carries the O6 incidence of c. *)
Lemma reflect_via_perp_bisector : forall q p c,
  line_wf c -> ~ on_line p c ->
  reflect_point q (perp_bisector p (reflect_point p c)) = reflect_point q c.
Proof.
  intros q p c Hwf Hnp.
  assert (HD : A c * A c + B c * B c <> 0) by (pose proof (line_norm_pos c Hwf); lra).
  destruct p as [px py].
  assert (Hnum : A c * px + B c * py + C c <> 0)
    by (intro Hc0; apply Hnp; unfold on_line; simpl; exact Hc0).
  set (lam := (A c * px + B c * py + C c) / (A c * A c + B c * B c)).
  assert (Hlam : lam <> 0).
  { unfold lam, Rdiv. intro Hc0. apply Rmult_integral in Hc0.
    destruct Hc0 as [Hc0 | Hc0]; [apply Hnum; exact Hc0 | exact (Rinv_neq_0_compat _ HD Hc0)]. }
  set (k := -4 * lam).
  assert (Hk : k <> 0)
    by (unfold k; apply Rmult_integral_contrapositive_currified; [lra | exact Hlam]).
  assert (Hpb : perp_bisector (px, py) (reflect_point (px, py) c)
                = {| A := k * A c; B := k * B c; C := k * C c |}).
  { unfold reflect_point, perp_bisector. cbn [fst snd].
    match goal with
    | |- context[Req_EM_T px ?t] => destruct (Req_EM_T px t) as [Hx | Hx]
    end.
    - assert (HAc0 : A c = 0).
      { assert (H0 : A c * lam = 0) by (unfold lam; nra).
        apply Rmult_integral in H0. destruct H0 as [H0 | H0];
          [exact H0 | exfalso; apply Hlam; exact H0]. }
      match goal with
      | |- context[Req_EM_T py ?t] => destruct (Req_EM_T py t) as [Hy | Hy]
      end.
      + exfalso. assert (HBc0 : B c = 0).
        { assert (H0 : B c * lam = 0) by (unfold lam; nra).
          apply Rmult_integral in H0. destruct H0 as [H0 | H0];
            [exact H0 | exfalso; apply Hlam; exact H0]. }
        destruct Hwf as [Hw | Hw]; [apply Hw; exact HAc0 | apply Hw; exact HBc0].
      + assert (HBcn : B c <> 0)
          by (destruct Hwf as [Hw | Hw]; [exfalso; apply Hw; exact HAc0 | exact Hw]).
        f_equal; unfold k, lam; rewrite HAc0; field; nra.
    - f_equal; unfold k, lam; field; exact HD. }
  rewrite Hpb. apply reflect_point_scale_eq; [exact Hk | exact HD].
Qed.

(** General O6 is a constructible single fold: for constructible foci and
    directrices in general position there is a constructible crease meeting the
    O6 incidence constraint -- built as the O2 fold of p1 and its reflection,
    which carries the O6 incidence of the origami-coordinate crease. *)
Theorem O6_general_constructible : forall p1 l1 p2 l2,
  ConstructiblePoint p1 -> ConstructibleLine l1 ->
  ConstructiblePoint p2 -> ConstructibleLine l2 ->
  ~ on_line p1 l1 -> A l1 * B l2 <> A l2 * B l1 ->
  exists crease, ConstructibleLine crease /\
    satisfies_O6_line_constraint crease p1 l1 p2 l2.
Proof.
  intros p1 l1 p2 l2 Cp1 Cl1 Cp2 Cl2 Hp1 Hpar.
  destruct (O6_general_good p1 l1 p2 l2
              (constructible_implies_origami p1 Cp1) (ConstructibleLine_good l1 Cl1)
              (constructible_implies_origami p2 Cp2) (ConstructibleLine_good l2 Cl2)
              (ConstructibleLine_wf l1 Cl1) (ConstructibleLine_wf l2 Cl2) Hp1 Hpar)
    as [c [Gc [Hwfc [Ho1 Ho2]]]].
  assert (HD : A c * A c + B c * B c <> 0) by (pose proof (line_norm_pos c Hwfc); lra).
  assert (Hpc : ~ on_line p1 c).
  { intro Hon. apply Hp1.
    assert (Heq : reflect_point p1 c = p1) by (apply reflect_point_on_line; exact Hon).
    rewrite Heq in Ho1. exact Ho1. }
  exists (perp_bisector p1 (reflect_point p1 c)). split.
  - rewrite <- fold_line_O2. apply CL_fold. apply CF_O2.
    + exact Cp1.
    + apply good_constructible_point. apply GoodPoint_reflect;
        [exact Hwfc | exact (constructible_implies_origami p1 Cp1) | exact Gc].
  - unfold satisfies_O6_line_constraint. split.
    + rewrite (reflect_via_perp_bisector p1 p1 c Hwfc Hpc). exact Ho1.
    + rewrite (reflect_via_perp_bisector p2 p1 c Hwfc Hpc). exact Ho2.
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
(* ===== Complex Cardano (item 10): C as a field, complex square and cube
   roots via polar form, and the radical formula returning all three roots of
   z^3 + p z + q over C with no discriminant-sign restriction.  Wrapped in a
   module so the complex type C does not collide with the Line field C. ===== *)
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
Theorem cos_2pi_n_origami_deg3 : forall n, (3 <= n)%nat -> euler_phi n = 6%nat ->
  OrigamiNum (cos (2 * PI / INR n)).
Proof.
  intros n Hn Hphi.
  destruct (cos_recip_annih n 3 Hn ltac:(lia)) as [R [HRlen [HRlead HRroot]]].
  set (y := 2 * cos (2 * PI / INR n)) in *.
  destruct R as [|r0 [|r1 [|r2 [|r3 [|? ?]]]]]; cbn [length] in HRlen; try (exfalso; lia).
  cbn [peval] in HRroot. cbn [nth] in HRlead.
  assert (Hr3 : IZR r3 <> 0) by (apply not_0_IZR; exact HRlead).
  assert (Hmonic : y*y*y + (IZR r2/IZR r3)*(y*y) + (IZR r1/IZR r3)*y + (IZR r0/IZR r3) = 0).
  { apply (Rmult_eq_reg_l (IZR r3)); [|exact Hr3]. rewrite Rmult_0_r.
    transitivity (IZR r0 + y * (IZR r1 + y * (IZR r2 + y * (IZR r3 + y * 0)))).
    - field. exact Hr3.
    - exact HRroot. }
  assert (Hy : OrigamiNum y).
  { apply (origami_general_cubic (IZR r2/IZR r3) (IZR r1/IZR r3) (IZR r0/IZR r3) y);
      [ apply Origami_div; [apply Origami_Z | apply Origami_Z | exact Hr3]
      | apply Origami_div; [apply Origami_Z | apply Origami_Z | exact Hr3]
      | apply Origami_div; [apply Origami_Z | apply Origami_Z | exact Hr3]
      | exact Hmonic ]. }
  replace (cos (2 * PI / INR n)) with (y / 2) by (unfold y; field).
  apply Origami_div; [exact Hy | apply Origami_two | lra].
Qed.

(* a later import shadowed the bare name sqrt with the primitive int sqrt; restore
   the real square root for the constructions below *)

(* a real root of any monic quadratic with origami coefficients is origami *)
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
Theorem cos_2pi_n_origami_deg2 : forall n, (3 <= n)%nat -> euler_phi n = 4%nat ->
  OrigamiNum (cos (2 * PI / INR n)).
Proof.
  intros n Hn Hphi.
  destruct (cos_recip_annih n 2 Hn ltac:(lia)) as [R [HRlen [HRlead HRroot]]].
  set (y := 2 * cos (2 * PI / INR n)) in *.
  destruct R as [|r0 [|r1 [|r2 [|? ?]]]]; cbn [length] in HRlen; try (exfalso; lia).
  cbn [peval] in HRroot. cbn [nth] in HRlead.
  assert (Hr2 : IZR r2 <> 0) by (apply not_0_IZR; exact HRlead).
  assert (Hmonic : y*y + (IZR r1/IZR r2)*y + (IZR r0/IZR r2) = 0).
  { apply (Rmult_eq_reg_l (IZR r2)); [|exact Hr2]. rewrite Rmult_0_r.
    transitivity (IZR r0 + y * (IZR r1 + y * (IZR r2 + y * 0))).
    - field. exact Hr2.
    - exact HRroot. }
  assert (Hy : OrigamiNum y).
  { apply (origami_general_quadratic (IZR r1/IZR r2) (IZR r0/IZR r2) y);
      [ apply Origami_div; [apply Origami_Z | apply Origami_Z | exact Hr2]
      | apply Origami_div; [apply Origami_Z | apply Origami_Z | exact Hr2]
      | exact Hmonic ]. }
  replace (cos (2 * PI / INR n)) with (y / 2) by (unfold y; field).
  apply Origami_div; [exact Hy | apply Origami_two | lra].
Qed.

(* ===== The 2-3-smooth-n polygons: cos(2pi/n) is origami for n = 2^a * 3^b ===== *)
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
Lemma cos_third_origami : forall m, (1 <= m)%nat ->
  OrigamiNum (cos (2 * PI / INR m)) -> OrigamiNum (cos (2 * PI / INR (3*m))).
Proof.
  intros m Hm Hc.
  assert (HmR : INR m <> 0) by (apply not_0_INR; lia).
  assert (H4 : OrigamiNum 4) by (replace 4 with (2+2) by lra; apply ON_add; apply Origami_two).
  set (u := cos (2 * PI / INR (3*m))).
  assert (Hangle : 3 * (2 * PI / INR (3*m)) = 2 * PI / INR m).
  { rewrite mult_INR. replace (INR 3) with 3 by (simpl; ring). field. exact HmR. }
  assert (Ht : cos (2 * PI / INR m) = 4 * u^3 - 3 * u).
  { unfold u. rewrite <- Hangle. apply cos_triple. }
  apply (cubic_root_closure (-3/4) (- cos (2 * PI / INR m) / 4) u).
  - replace (-3/4) with (IZR (-3) / IZR 4) by (simpl; lra). apply Origami_Q; lia.
  - apply Origami_div; [apply Origami_neg; exact Hc | exact H4 | lra].
  - unfold u in *. rewrite Ht. field.
Qed.

(* origami bisection: from cos(2pi/m) build cos(2pi/(2m)) via the half-angle sqrt *)
Lemma cos_half_origami : forall m, (1 <= m)%nat ->
  OrigamiNum (cos (2 * PI / INR m)) -> OrigamiNum (cos (2 * PI / INR (2*m))).
Proof.
  intros m Hm Hc.
  assert (HmR : INR m <> 0) by (apply not_0_INR; lia).
  set (v := cos (2 * PI / INR (2*m))).
  assert (Hangle2 : 2 * (2 * PI / INR (2*m)) = 2 * PI / INR m).
  { rewrite mult_INR. replace (INR 2) with 2 by (simpl; ring). field. exact HmR. }
  assert (Hcd : cos (2 * PI / INR m) = 2*v*v - 1).
  { rewrite <- Hangle2. unfold v. apply cos_double. }
  assert (Hnn : 0 <= (1 + cos (2 * PI / INR m))/2) by (rewrite Hcd; nra).
  assert (Hson : OrigamiNum (sqrt ((1 + cos (2 * PI / INR m))/2))).
  { apply ON_sqrt; [|exact Hnn].
    apply Origami_div; [apply ON_add; [apply ON_1 | exact Hc] | apply Origami_two | lra]. }
  destruct (Rle_dec 0 v) as [Hvnn | Hvneg].
  - replace v with (sqrt ((1 + cos (2 * PI / INR m))/2)); [exact Hson|].
    rewrite Hcd. replace ((1 + (2*v*v-1))/2) with (v*v) by field.
    rewrite sqrt_square by exact Hvnn. reflexivity.
  - replace v with (- sqrt ((1 + cos (2 * PI / INR m))/2)); [apply Origami_neg; exact Hson|].
    rewrite Hcd. replace ((1 + (2*v*v-1))/2) with ((-v)*(-v)) by field.
    rewrite sqrt_square by lra. ring.
Qed.

(* the 3^b-gons are origami (repeated trisection) *)
Lemma cos_2pi_3pow : forall b, OrigamiNum (cos (2 * PI / INR (3^b))).
Proof.
  induction b as [|b IH].
  - simpl (3^0)%nat. replace (2 * PI / INR 1) with (2*PI) by (simpl; field).
    rewrite cos_2PI. apply ON_1.
  - replace (3 ^ S b)%nat with (3 * 3^b)%nat by (simpl; lia).
    apply cos_third_origami; [assert (3^b <> 0)%nat by (apply Nat.pow_nonzero; lia); lia | exact IH].
Qed.

(* THE 2-3-SMOOTH POLYGONS: for n = 2^a * 3^b, cos(2pi/n) is origami-constructible
   (repeated origami bisection and trisection of the full angle). *)
Theorem cos_2pi_2a3b_origami : forall a b, OrigamiNum (cos (2 * PI / INR (2^a * 3^b))).
Proof.
  induction a as [|a IH]; intro b.
  - simpl (2^0)%nat. rewrite Nat.mul_1_l. apply cos_2pi_3pow.
  - replace (2 ^ S a * 3^b)%nat with (2 * (2^a * 3^b))%nat by (simpl; lia).
    apply cos_half_origami; [|exact (IH b)].
    assert (2^a <> 0)%nat by (apply Nat.pow_nonzero; lia).
    assert (3^b <> 0)%nat by (apply Nat.pow_nonzero; lia). nia.
Qed.

(* ===== Compass-straightedge (Gauss-Wantzel) impossibility ===== *)
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
Lemma cos_half_euclid : forall m, (1 <= m)%nat ->
  EuclidNum (cos (2 * PI / INR m)) -> EuclidNum (cos (2 * PI / INR (2*m))).
Proof.
  intros m Hm Hc.
  assert (HmR : INR m <> 0) by (apply not_0_INR; lia).
  assert (E2 : EuclidNum 2) by (replace 2 with (1+1) by lra; apply EN_add; apply EN_1).
  set (v := cos (2 * PI / INR (2*m))).
  assert (Hangle2 : 2 * (2 * PI / INR (2*m)) = 2 * PI / INR m).
  { rewrite mult_INR. replace (INR 2) with 2 by (simpl; ring). field. exact HmR. }
  assert (Hcd : cos (2 * PI / INR m) = 2*v*v - 1).
  { rewrite <- Hangle2. unfold v. set (x := 2 * PI / INR (2*m)).
    replace (2*x) with (x+x) by ring. rewrite cos_plus.
    pose proof (sin2_cos2 x) as Hsc. unfold Rsqr in Hsc. nra. }
  assert (Hnn : 0 <= (1 + cos (2 * PI / INR m))/2) by (rewrite Hcd; nra).
  assert (Hson : EuclidNum (sqrt ((1 + cos (2 * PI / INR m))/2))).
  { apply EN_sqrt; [|exact Hnn].
    replace ((1 + cos (2 * PI / INR m))/2)
      with ((1 + cos (2 * PI / INR m)) * / 2) by (unfold Rdiv; ring).
    apply EN_mul; [apply EN_add; [apply EN_1 | exact Hc] | apply EN_inv; [exact E2 | lra]]. }
  destruct (Rle_dec 0 v) as [Hvnn | Hvneg].
  - replace v with (sqrt ((1 + cos (2 * PI / INR m))/2)); [exact Hson|].
    rewrite Hcd. replace ((1 + (2*v*v-1))/2) with (v*v) by field.
    rewrite sqrt_square by exact Hvnn. reflexivity.
  - replace v with (- sqrt ((1 + cos (2 * PI / INR m))/2)).
    + replace (- sqrt ((1 + cos (2 * PI / INR m))/2))
        with (0 - sqrt ((1 + cos (2 * PI / INR m))/2)) by ring.
      apply EN_sub; [apply EN_0 | exact Hson].
    + rewrite Hcd. replace ((1 + (2*v*v-1))/2) with ((-v)*(-v)) by field.
      rewrite sqrt_square by lra. ring.
Qed.

Theorem cos_2pi_pow2_euclid : forall a, EuclidNum (cos (2 * PI / INR (2^a))).
Proof.
  induction a as [|a IH].
  - simpl (2^0)%nat. replace (2 * PI / INR 1) with (2*PI) by (simpl; field).
    rewrite cos_2PI. apply EN_1.
  - replace (2 ^ S a)%nat with (2 * 2^a)%nat by (simpl; lia).
    apply cos_half_euclid; [assert (2^a <> 0)%nat by (apply Nat.pow_nonzero; lia); lia | exact IH].
Qed.

(* ===== Degree-based impossibility, factored generally ===== *)

(* a real number whose degree over Q is not 2-3-smooth is not origami-constructible *)
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
Open Scope nat_scope.
Open Scope Z_scope.
Open Scope R_scope.
Section PrimeCase.

Variable P : nat.
Variable g : Z.
Hypothesis HP : Znumtheory.prime (Z.of_nat P).
Hypothesis HP5 : (5 <= P)%nat.
Hypothesis Hg : per P g (P - 1).
Hypothesis Hgord : forall k, (1 <= k < P - 1)%nat -> ~ cg (Z.of_nat P) (zpn g k) 1.

Local Notation p := (Z.of_nat P).
Local Notation n := (P - 1)%nat.

Lemma Hp0 : (p <> 0)%Z. Proof. lia. Qed.
Lemma HpZ : (0 < p)%Z. Proof. lia. Qed.

(* the period of the coset  v * <g^D>  (D | n), as a real cosine sum *)
Definition PerV (v : Z) (D : nat) : R :=
  csum p (map (fun t => (v * zpn g (D * t))%Z) (seq 0 (n / D))).

(* csum over a mapped list depends only on the residues of the entries *)
Lemma csum_map_ext : forall (f f' : nat -> Z) l,
  (forall t, ca p (f t) = ca p (f' t)) -> csum p (map f l) = csum p (map f' l).
Proof.
  intros f f' l Hff. induction l as [|x l IH]; [reflexivity|].
  cbn [map]. rewrite !csum_cons, IH, (Hff x). reflexivity.
Qed.

(* the period depends only on the residue class of v *)
Lemma PerV_cong : forall v v' D, cg p v v' -> PerV v D = PerV v' D.
Proof.
  intros v v' D Hvv. unfold PerV. apply csum_map_ext. intro t.
  apply ca_cong; [exact Hp0|].
  replace (v * zpn g (D * t) - v' * zpn g (D * t))%Z
    with ((v - v') * zpn g (D * t))%Z by ring.
  apply Z.divide_mul_l. exact Hvv.
Qed.

(* IZR of the prime is INR of the nat prime; the angle bridge *)
Lemma IZR_p : IZR p = INR P.
Proof. rewrite INR_IZR_INZ. reflexivity. Qed.

Lemma INR_P_neq : INR P <> 0.
Proof. rewrite <- IZR_p. apply not_0_IZR. exact Hp0. Qed.

Lemma ca_one : ca p 1 = cos (2 * PI / INR P).
Proof.
  unfold ca. rewrite IZR_p. replace (IZR 1) with 1 by (cbn; reflexivity).
  replace (2 * PI * 1 / INR P) with (2 * PI / INR P) by (field; apply INR_P_neq).
  reflexivity.
Qed.

(* ===== generic real sums over nat-index lists, and a stride reindex ===== *)

Definition rsum (l : list nat) (phi : nat -> R) : R :=
  fold_right (fun x a => phi x + a) 0 l.

Lemma rsum_nil : forall phi, rsum [] phi = 0. Proof. reflexivity. Qed.
Lemma rsum_cons : forall x l phi, rsum (x :: l) phi = phi x + rsum l phi.
Proof. reflexivity. Qed.

Lemma rsum_app : forall l1 l2 phi, rsum (l1 ++ l2) phi = rsum l1 phi + rsum l2 phi.
Proof.
  intros l1 l2 phi. induction l1 as [|x l1 IH].
  - rewrite app_nil_l, rsum_nil. ring.
  - rewrite <- app_comm_cons, !rsum_cons, IH. ring.
Qed.

Lemma rsum_plus : forall l f h, rsum l (fun x => f x + h x) = rsum l f + rsum l h.
Proof.
  intros l f h. induction l as [|x l IH].
  - rewrite !rsum_nil. ring.
  - rewrite !rsum_cons, IH. ring.
Qed.

Lemma rsum_zero : forall l, rsum l (fun _ => 0) = 0.
Proof. intro l. induction l as [|x l IH]; [reflexivity|]. rewrite rsum_cons, IH. ring. Qed.

Lemma rsum_ext : forall l f h, (forall x, f x = h x) -> rsum l f = rsum l h.
Proof.
  intros l f h H. induction l as [|x l IH]; [reflexivity|].
  rewrite !rsum_cons, IH, (H x). reflexivity.
Qed.

Lemma rsum_single : forall a phi, rsum [a] phi = phi a.
Proof. intros a phi. rewrite rsum_cons, rsum_nil. ring. Qed.

Lemma rsum_seq_shift : forall len m phi,
  rsum (seq m len) phi = rsum (seq 0 len) (fun l => phi ((m + l)%nat)).
Proof.
  induction len as [|len IH]; intros m phi.
  - reflexivity.
  - cbn [seq]. rewrite !rsum_cons, (IH (S m) phi), (IH 1%nat (fun l => phi ((m + l)%nat))).
    cbn beta.
    replace (m + 0)%nat with m by lia.
    f_equal. apply rsum_ext. intro x. f_equal. lia.
Qed.

(* the stride decomposition  sum_{t<s*F'} = sum_{l<s} sum_{t'<F'} phi(l + s*t') *)
Lemma double_seq_sum : forall s F' phi,
  rsum (seq 0 (s * F')) phi
  = rsum (seq 0 s) (fun l => rsum (seq 0 F') (fun t' => phi ((l + s * t')%nat))).
Proof.
  intros s F'. induction F' as [|F' IH]; intro phi.
  - rewrite Nat.mul_0_r. cbn [seq]. rewrite rsum_nil. symmetry.
    transitivity (rsum (seq 0 s) (fun _ => 0)).
    + apply rsum_ext. intro l. apply rsum_nil.
    + apply rsum_zero.
  - replace (s * S F')%nat with (s * F' + s)%nat by lia.
    rewrite seq_app, Nat.add_0_l, rsum_app, (IH phi).
    rewrite (rsum_seq_shift s (s * F')%nat phi).
    rewrite <- rsum_plus.
    apply rsum_ext. intro l.
    rewrite seq_S, rsum_app, rsum_single.
    f_equal. f_equal. lia.
Qed.

Lemma csum_map_rsum : forall h l, csum p (map h l) = rsum l (fun t => ca p (h t)).
Proof.
  intros h l. induction l as [|x l IH]; [reflexivity|].
  cbn [map]. rewrite csum_cons, IH. reflexivity.
Qed.

(* n / D = s * (n / (D*s))  when  D*s | n *)
Lemma div_stride : forall D s, (D <> 0)%nat -> (s <> 0)%nat -> Nat.divide (D * s) n ->
  (n / D = s * (n / (D * s)))%nat.
Proof.
  intros D s HD Hs [q Hq].
  assert (HnD : (n / D = s * q)%nat).
  { rewrite Hq. replace (q * (D * s))%nat with (s * q * D)%nat by lia.
    rewrite Nat.div_mul by exact HD. reflexivity. }
  assert (HnDs : (n / (D * s) = q)%nat).
  { rewrite Hq. rewrite Nat.div_mul by lia. reflexivity. }
  rewrite HnD, HnDs. reflexivity.
Qed.

(* PARTITION / TELESCOPING: a level-D period is the sum of its s level-(Ds) sub-periods *)
Lemma PerV_partition : forall w D s, (D <> 0)%nat -> (s <> 0)%nat -> Nat.divide (D * s) n ->
  PerV w D = rsum (seq 0 s) (fun l => PerV (w * zpn g (D * l)) (D * s)).
Proof.
  intros w D s HD Hs Hdiv.
  unfold PerV.
  rewrite csum_map_rsum.
  rewrite (div_stride D s HD Hs Hdiv).
  rewrite double_seq_sum.
  apply rsum_ext. intro l.
  rewrite csum_map_rsum.
  apply rsum_ext. intro t'.
  f_equal.
  rewrite <- Z.mul_assoc, <- zpn_add.
  f_equal. f_equal. lia.
Qed.

(* ===== more rsum algebra: scaling, Fubini, map, periodic shift ===== *)

Lemma rsum_scale_l : forall c l f, c * rsum l f = rsum l (fun x => c * f x).
Proof.
  intros c l f. induction l as [|x l IH].
  - rewrite !rsum_nil. ring.
  - rewrite !rsum_cons. rewrite <- IH. ring.
Qed.

Lemma rsum_scale_r : forall c l f, rsum l f * c = rsum l (fun x => f x * c).
Proof.
  intros c l f. induction l as [|x l IH].
  - rewrite !rsum_nil. ring.
  - rewrite !rsum_cons. rewrite <- IH. ring.
Qed.

Lemma rsum_map_nat : forall (h : nat -> nat) l f,
  rsum (map h l) f = rsum l (fun x => f (h x)).
Proof.
  intros h l f. induction l as [|x l IH]; [reflexivity|].
  cbn [map]. rewrite !rsum_cons, IH. reflexivity.
Qed.

Lemma rsum_swap : forall l1 l2 F,
  rsum l1 (fun i => rsum l2 (fun j => F i j))
  = rsum l2 (fun j => rsum l1 (fun i => F i j)).
Proof.
  intros l1 l2 F. induction l1 as [|x l1 IH].
  - rewrite rsum_nil. symmetry. rewrite <- (rsum_zero l2).
    apply rsum_ext. intro j. apply rsum_nil.
  - rewrite rsum_cons, IH.
    rewrite <- (rsum_plus l2 (fun j => F x j) (fun j => rsum l1 (fun i => F i j))).
    apply rsum_ext. intro j. rewrite rsum_cons. reflexivity.
Qed.

(* a function periodic with period F, summed over one period, is shift-invariant *)
Lemma rsum_shift1_periodic : forall len dh,
  dh (0 + len)%nat = dh 0%nat ->
  rsum (seq 0 len) (fun k => dh (S k)) = rsum (seq 0 len) dh.
Proof.
  intros len dh Hper.
  assert (H1 : rsum (seq 0 len) (fun k => dh (S k)) = rsum (seq 1 len) dh).
  { rewrite <- seq_shift, rsum_map_nat. reflexivity. }
  assert (Ha : rsum (seq 0 (S len)) dh = dh 0%nat + rsum (seq 1 len) dh).
  { cbn [seq]. rewrite rsum_cons. reflexivity. }
  assert (Hb : rsum (seq 0 (S len)) dh = rsum (seq 0 len) dh + dh (0 + len)%nat).
  { rewrite seq_S, rsum_app, rsum_single. reflexivity. }
  rewrite H1. rewrite Hper in Hb. lra.
Qed.

Lemma rsum_shift_periodic : forall len i dh,
  (forall j, dh (j + len)%nat = dh j) ->
  rsum (seq 0 len) dh = rsum (seq 0 len) (fun k => dh (i + k)%nat).
Proof.
  intros len i dh Hper. induction i as [|i IH].
  - apply rsum_ext. intro k. f_equal; lia.
  - rewrite IH.
    assert (Hd : (fun k => dh (i + k)%nat) (0 + len)%nat = (fun k => dh (i + k)%nat) 0%nat).
    { cbn beta. replace (i + (0 + len))%nat with ((i + 0)%nat + len)%nat by lia.
      rewrite Hper. f_equal; lia. }
    rewrite <- (rsum_shift1_periodic len (fun k => dh (i + k)%nat) Hd).
    apply rsum_ext. intro k. f_equal; lia.
Qed.

(* ===== Period multiplication (Gaussian) =====
   The Galois identity  PerV a D * PerV b D = (1/2) sum_s (PerV(a g^{Ds}+b) D + PerV(a g^{Ds}-b) D),
   reindexed via Fubini (rsum_swap) and the F-periodicity of g^{Ds} (period F = n/D). *)

Lemma gn1 : cg p (zpn g n) 1.
Proof. exact (proj2 Hg). Qed.

Lemma PerV_rsum : forall v D,
  PerV v D = rsum (seq 0 (n / D)) (fun t => ca p (v * zpn g (D * t))%Z).
Proof. intros v D. unfold PerV. apply csum_map_rsum. Qed.

Lemma rsum_ON : forall (l : list nat) (f : nat -> R),
  (forall x, OrigamiNum (f x)) -> OrigamiNum (rsum l f).
Proof.
  intros l f Hf. induction l as [|x l IH].
  - rewrite rsum_nil. apply ON_0.
  - rewrite rsum_cons. apply ON_add; [apply Hf | exact IH].
Qed.

Lemma ca_mul : forall x y, ca p x * ca p y = (ca p (x + y)%Z + ca p (x - y)%Z) / 2.
Proof.
  intros x y. unfold ca. rewrite plus_IZR, minus_IZR.
  set (A := 2 * PI * IZR x / IZR p). set (B := 2 * PI * IZR y / IZR p).
  assert (Hpr : IZR p <> 0) by (apply not_0_IZR; exact Hp0).
  replace (2 * PI * (IZR x + IZR y) / IZR p) with (A + B) by (unfold A, B; field; exact Hpr).
  replace (2 * PI * (IZR x - IZR y) / IZR p) with (A - B) by (unfold A, B; field; exact Hpr).
  pose proof (cos_plus A B) as Hcp. pose proof (cos_minus A B) as Hcm. lra.
Qed.

(* g^{D(i+n/D)} ≡ g^{Di} mod p : the period-F shift in the a-exponent *)
Lemma gshift : forall a (i D : nat), (1 <= D)%nat -> Nat.divide D n ->
  (p | a * zpn g (D * (i + n / D)) - a * zpn g (D * i))%Z.
Proof.
  intros a i D HD Hdiv.
  assert (HDFn : (D * (n / D) = n)%nat).
  { pose proof (Nat.div_mod n D ltac:(lia)) as Hdm.
    assert (Hmod0 : (n mod D = 0)%nat)
      by (apply (proj2 (Nat.mod_divide n D ltac:(lia))); exact Hdiv).
    lia. }
  assert (Hexp : (D * (i + n / D) = D * i + n)%nat)
    by (rewrite Nat.mul_add_distr_l, HDFn; reflexivity).
  rewrite Hexp, zpn_add.
  replace (a * (zpn g (D * i) * zpn g n) - a * zpn g (D * i))%Z
    with (a * zpn g (D * i) * (zpn g n - 1))%Z by ring.
  apply Z.divide_mul_r. exact gn1.
Qed.

(* double-sum reindex: sum_s sum_t Phi s t = sum_s sum_u Phi (s+u) u, Phi F-periodic in arg 1 *)
Lemma double_reindex : forall (Fl : nat) (Phi : nat -> nat -> R),
  (forall i t, Phi (i + Fl)%nat t = Phi i t) ->
  rsum (seq 0 Fl) (fun s => rsum (seq 0 Fl) (fun t => Phi s t))
  = rsum (seq 0 Fl) (fun s => rsum (seq 0 Fl) (fun u => Phi (s + u)%nat u)).
Proof.
  intros Fl Phi Hper.
  transitivity (rsum (seq 0 Fl) (fun u => rsum (seq 0 Fl) (fun i => Phi i u))).
  - apply rsum_swap.
  - symmetry.
    transitivity (rsum (seq 0 Fl) (fun u => rsum (seq 0 Fl) (fun s => Phi (s + u)%nat u))).
    + apply rsum_swap.
    + apply rsum_ext. intro u.
      rewrite (rsum_shift_periodic Fl u (fun i => Phi i u) (fun j => Hper j u)).
      apply rsum_ext. intro k. replace (k + u)%nat with (u + k)%nat by lia. reflexivity.
Qed.

Lemma PerV_mul : forall a b (D : nat), (1 <= D)%nat -> Nat.divide D n ->
  2 * (PerV a D * PerV b D)
  = rsum (seq 0 (n / D))
      (fun s => PerV (a * zpn g (D * s) + b)%Z D + PerV (a * zpn g (D * s) - b)%Z D).
Proof.
  intros a b D HD Hdiv.
  assert (HA : 2 * (PerV a D * PerV b D)
    = rsum (seq 0 (n / D)) (fun s => rsum (seq 0 (n / D)) (fun t =>
        ca p (a * zpn g (D * s) + b * zpn g (D * t))%Z
        + ca p (a * zpn g (D * s) - b * zpn g (D * t))%Z))).
  { rewrite (PerV_rsum a D), (PerV_rsum b D).
    rewrite rsum_scale_r, rsum_scale_l.
    apply rsum_ext. intro s.
    rewrite rsum_scale_l, rsum_scale_l.
    apply rsum_ext. intro t.
    rewrite (ca_mul (a * zpn g (D * s))%Z (b * zpn g (D * t))%Z). field. }
  assert (HB : rsum (seq 0 (n / D))
        (fun s => PerV (a * zpn g (D * s) + b)%Z D + PerV (a * zpn g (D * s) - b)%Z D)
    = rsum (seq 0 (n / D)) (fun s => rsum (seq 0 (n / D)) (fun u =>
        ca p (a * zpn g (D * (s + u)) + b * zpn g (D * u))%Z
        + ca p (a * zpn g (D * (s + u)) - b * zpn g (D * u))%Z))).
  { apply rsum_ext. intro s.
    rewrite (PerV_rsum (a * zpn g (D * s) + b)%Z D),
            (PerV_rsum (a * zpn g (D * s) - b)%Z D).
    rewrite <- rsum_plus.
    apply rsum_ext. intro u.
    assert (He1 : ((a * zpn g (D * s) + b) * zpn g (D * u))%Z
                = (a * zpn g (D * (s + u)) + b * zpn g (D * u))%Z).
    { rewrite Nat.mul_add_distr_l, (zpn_add g (D * s) (D * u)). ring. }
    assert (He2 : ((a * zpn g (D * s) - b) * zpn g (D * u))%Z
                = (a * zpn g (D * (s + u)) - b * zpn g (D * u))%Z).
    { rewrite Nat.mul_add_distr_l, (zpn_add g (D * s) (D * u)). ring. }
    rewrite He1, He2. reflexivity. }
  rewrite HA, HB.
  apply (double_reindex (n / D)
    (fun i t => ca p (a * zpn g (D * i) + b * zpn g (D * t))%Z
              + ca p (a * zpn g (D * i) - b * zpn g (D * t))%Z)).
  intros i t.
  assert (E1 : ca p (a * zpn g (D * (i + n / D)) + b * zpn g (D * t))%Z
             = ca p (a * zpn g (D * i) + b * zpn g (D * t))%Z).
  { apply ca_cong; [exact Hp0|].
    replace (a * zpn g (D * (i + n / D)) + b * zpn g (D * t)
             - (a * zpn g (D * i) + b * zpn g (D * t)))%Z
      with (a * zpn g (D * (i + n / D)) - a * zpn g (D * i))%Z by ring.
    apply gshift; assumption. }
  assert (E2 : ca p (a * zpn g (D * (i + n / D)) - b * zpn g (D * t))%Z
             = ca p (a * zpn g (D * i) - b * zpn g (D * t))%Z).
  { apply ca_cong; [exact Hp0|].
    replace (a * zpn g (D * (i + n / D)) - b * zpn g (D * t)
             - (a * zpn g (D * i) - b * zpn g (D * t)))%Z
      with (a * zpn g (D * (i + n / D)) - a * zpn g (D * i))%Z by ring.
    apply gshift; assumption. }
  rewrite E1, E2. reflexivity.
Qed.

(* ===== Tower step: sub-period power sums collapse to the coarse level ===== *)

(* Sum of the s sub-periods of a g^D-coset, with g^{Dl} factored out, is the
   coarse period (this is PerV_partition, reindexed). *)
Lemma collapse : forall (D s : nat) M, (D <> 0)%nat -> (s <> 0)%nat -> Nat.divide (D * s) n ->
  rsum (seq 0 s) (fun l => PerV (zpn g (D * l) * M)%Z (D * s)) = PerV M D.
Proof.
  intros D s M HD Hs Hdiv.
  rewrite (PerV_partition M D s HD Hs Hdiv).
  apply rsum_ext. intro l. replace (zpn g (D * l) * M)%Z with (M * zpn g (D * l))%Z by ring.
  reflexivity.
Qed.

(* Q2 collapse:  2 * sum_l (sub_l)^2  =  sum_{s'} (coarse periods). *)
Lemma sub_sq_eq : forall (D s : nat) w, (1 <= D)%nat -> (1 <= s)%nat -> Nat.divide (D * s) n ->
  2 * rsum (seq 0 s) (fun l =>
        PerV (w * zpn g (D * l))%Z (D * s) * PerV (w * zpn g (D * l))%Z (D * s))
  = rsum (seq 0 (n / (D * s))) (fun s' =>
      PerV (w * zpn g (D * s * s') + w)%Z D + PerV (w * zpn g (D * s * s') - w)%Z D).
Proof.
  intros D s w HD Hs Hdiv.
  assert (HE : (1 <= D * s)%nat) by nia.
  rewrite rsum_scale_l.
  transitivity (rsum (seq 0 s) (fun l => rsum (seq 0 (n / (D * s))) (fun s' =>
      PerV (w * zpn g (D * l) * zpn g (D * s * s') + w * zpn g (D * l))%Z (D * s)
      + PerV (w * zpn g (D * l) * zpn g (D * s * s') - w * zpn g (D * l))%Z (D * s)))).
  { apply rsum_ext. intro l.
    exact (PerV_mul (w * zpn g (D * l))%Z (w * zpn g (D * l))%Z (D * s) HE Hdiv). }
  rewrite rsum_swap.
  apply rsum_ext. intro s'.
  rewrite rsum_plus.
  assert (HAp : rsum (seq 0 s) (fun l =>
            PerV (w * zpn g (D * l) * zpn g (D * s * s') + w * zpn g (D * l))%Z (D * s))
          = PerV (w * zpn g (D * s * s') + w)%Z D).
  { transitivity (rsum (seq 0 s) (fun l =>
        PerV (zpn g (D * l) * (w * zpn g (D * s * s') + w))%Z (D * s))).
    - apply rsum_ext. intro l.
      replace (zpn g (D * l) * (w * zpn g (D * s * s') + w))%Z
        with (w * zpn g (D * l) * zpn g (D * s * s') + w * zpn g (D * l))%Z by ring.
      reflexivity.
    - apply collapse; [lia | lia | exact Hdiv]. }
  assert (HBm : rsum (seq 0 s) (fun l =>
            PerV (w * zpn g (D * l) * zpn g (D * s * s') - w * zpn g (D * l))%Z (D * s))
          = PerV (w * zpn g (D * s * s') - w)%Z D).
  { transitivity (rsum (seq 0 s) (fun l =>
        PerV (zpn g (D * l) * (w * zpn g (D * s * s') - w))%Z (D * s))).
    - apply rsum_ext. intro l.
      replace (zpn g (D * l) * (w * zpn g (D * s * s') - w))%Z
        with (w * zpn g (D * l) * zpn g (D * s * s') - w * zpn g (D * l))%Z by ring.
      reflexivity.
    - apply collapse; [lia | lia | exact Hdiv]. }
  rewrite HAp, HBm. reflexivity.
Qed.

Lemma sub_sq_ON : forall (D s : nat) w, (1 <= D)%nat -> (1 <= s)%nat -> Nat.divide (D * s) n ->
  (forall v, OrigamiNum (PerV v D)) ->
  OrigamiNum (rsum (seq 0 s) (fun l =>
     PerV (w * zpn g (D * l))%Z (D * s) * PerV (w * zpn g (D * l))%Z (D * s))).
Proof.
  intros D s w HD Hs Hdiv IH.
  assert (Hhalf : rsum (seq 0 s) (fun l =>
            PerV (w * zpn g (D * l))%Z (D * s) * PerV (w * zpn g (D * l))%Z (D * s))
        = (rsum (seq 0 (n / (D * s))) (fun s' =>
            PerV (w * zpn g (D * s * s') + w)%Z D + PerV (w * zpn g (D * s * s') - w)%Z D)) / 2).
  { pose proof (sub_sq_eq D s w HD Hs Hdiv) as Heq. lra. }
  rewrite Hhalf.
  apply Origami_div; [| apply Origami_two | lra].
  apply rsum_ON. intro s'. apply ON_add; apply IH.
Qed.

End PrimeCase.
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
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope Z_scope.
Open Scope R_scope.
(* ---- multiplicative CRT reduction (former dev.v) ---- *)
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
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope Z_scope.
Open Scope R_scope.
Open Scope R_scope.
(* sin(2pi/n) is origami whenever cos(2pi/n) is (n >= 2): sin = sqrt(1 - cos^2), >= 0 *)
Lemma sin_origami_of_cos : forall n, (2 <= n)%nat ->
  OrigamiNum (cos (2 * PI / INR n)) -> OrigamiNum (sin (2 * PI / INR n)).
Proof.
  intros n Hn Hc.
  pose proof PI_RGT_0 as HPI.
  assert (HnR : INR n <> 0) by (apply not_0_INR; lia).
  assert (HnPos : 0 < INR n) by (apply lt_0_INR; lia).
  assert (Hn2 : 2 <= INR n) by (replace 2 with (INR 2) by (simpl; ring); apply le_INR; lia).
  set (t := 2 * PI / INR n) in *.
  assert (Ht0 : 0 <= t).
  { unfold t, Rdiv. apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; exact HnPos]. }
  assert (Htpi : t <= PI).
  { unfold t. apply Rmult_le_reg_r with (INR n); [exact HnPos |].
    unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by exact HnR. rewrite Rmult_1_r. nra. }
  assert (Hsnn : 0 <= sin t) by (apply sin_ge_0; [exact Ht0 | exact Htpi]).
  assert (Hsq : sin t = sqrt (1 - cos t * cos t)).
  { rewrite <- (sqrt_Rsqr (sin t) Hsnn). f_equal. unfold Rsqr.
    pose proof (sin2_cos2 t) as H. unfold Rsqr in H. lra. }
  rewrite Hsq. apply ON_sqrt.
  - apply ON_sub; [apply ON_1 | apply ON_mul; exact Hc].
  - pose proof (COS_bound t) as [Hlo Hhi]. nra.
Qed.

(* CRT / angle-addition: cos,sin origami for coprime m,k give them for the product *)
Lemma cos_sin_origami_mul : forall m k,
  (1 <= m)%nat -> (1 <= k)%nat -> Nat.gcd m k = 1%nat ->
  OrigamiNum (cos (2 * PI / INR m)) -> OrigamiNum (sin (2 * PI / INR m)) ->
  OrigamiNum (cos (2 * PI / INR k)) -> OrigamiNum (sin (2 * PI / INR k)) ->
  OrigamiNum (cos (2 * PI / INR (m * k))) /\ OrigamiNum (sin (2 * PI / INR (m * k))).
Proof.
  intros m k Hm Hk Hgcd Hcm Hsm Hck Hsk.
  destruct (bezout_coprime m k ltac:(lia) Hgcd) as [u [v Huv]].
  assert (HmR : INR m <> 0) by (apply not_0_INR; lia).
  assert (HkR : INR k <> 0) by (apply not_0_INR; lia).
  assert (HuvR : INR u * INR m = 1 + INR v * INR k).
  { rewrite <- !mult_INR. replace (1:R) with (INR 1) by (simpl; ring).
    rewrite <- plus_INR. apply f_equal. exact Huv. }
  assert (Hone : INR u * INR m - INR v * INR k = 1) by lra.
  assert (Hangle : 2 * PI / INR (m * k) = INR u * (2 * PI / INR k) - INR v * (2 * PI / INR m)).
  { rewrite mult_INR.
    transitivity (2 * PI * (INR u * INR m - INR v * INR k) / (INR m * INR k)).
    - rewrite Hone. field. repeat split; assumption.
    - field. repeat split; assumption. }
  destruct (vertex_coords_origami (2 * PI / INR k) Hck Hsk u) as [Hcuk Hsuk].
  destruct (vertex_coords_origami (2 * PI / INR m) Hcm Hsm v) as [Hcvm Hsvm].
  rewrite Hangle. split.
  - rewrite cos_minus. apply ON_add; apply ON_mul; assumption.
  - rewrite sin_minus. apply ON_sub; apply ON_mul; assumption.
Qed.
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
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope Z_scope.
Open Scope R_scope.
Open Scope R_scope.
Section Reduction.
(* For prime p with 2-3-smooth phi(p), cos(2pi/p) is origami (Gaussian periods
   over the cyclic unit group mod p). *)
Variable Hcore : forall p, Znumtheory.prime (Z.of_nat p) ->
  two_three_smooth (euler_phi p) -> OrigamiNum (cos (2 * PI / INR p)).
Variable Hppart : forall p n, (2 <= p)%nat -> (1 <= n)%nat ->
  exists e k, n = (p ^ e * k)%nat /\ ~ Nat.divide p k.
Variable Hcop_pp : forall p e k, Znumtheory.prime (Z.of_nat p) ->
  ~ Nat.divide p k -> Nat.gcd (p ^ e) k = 1%nat.
Variable Hphi_pp : forall p e, Znumtheory.prime (Z.of_nat p) -> (2 <= e)%nat ->
  Nat.divide p (euler_phi (p ^ e)).
Variable Hpdiv23 : forall p a b, Znumtheory.prime (Z.of_nat p) ->
  Nat.divide p (2 ^ a * 3 ^ b)%nat -> (p = 2 \/ p = 3)%nat.

Theorem cos_sin_smooth : forall n, (1 <= n)%nat -> two_three_smooth (euler_phi n) ->
  OrigamiNum (cos (2 * PI / INR n)) /\ OrigamiNum (sin (2 * PI / INR n)).
Proof.
  intro n. induction n as [n IH] using (well_founded_induction lt_wf). intros Hn Hsm.
  destruct (le_lt_dec n 2) as [Hle | Hgt].
  - assert (E : n = 1%nat \/ n = 2%nat) by lia. destruct E as [E|E]; subst n.
    + replace (2 * PI / INR 1) with (2 * PI) by (simpl; field).
      rewrite cos_2PI, sin_2PI. split; [apply ON_1 | apply ON_0].
    + replace (2 * PI / INR 2) with PI by (simpl; field).
      rewrite cos_PI, sin_PI. split; [apply Origami_neg; apply ON_1 | apply ON_0].
  - assert (Hn2 : (2 <= n)%nat) by lia.
    destruct (prime_factor_nat n ltac:(lia)) as [p [Hp Hpn]].
    assert (Hp2 : (2 <= p)%nat) by (destruct Hp; lia).
    destruct (Hppart p n Hp2 ltac:(lia)) as [e [k [Hnk Hpk]]].
    assert (He1 : (1 <= e)%nat).
    { destruct e as [|e']; [|lia]. exfalso. rewrite Nat.pow_0_r, Nat.mul_1_l in Hnk.
      subst k. apply Hpk; exact Hpn. }
    set (q := (p ^ e)%nat) in *.
    assert (Hple : (p <= q)%nat).
    { unfold q. rewrite <- (Nat.pow_1_r p) at 1. apply Nat.pow_le_mono_r; lia. }
    assert (Hq2 : (2 <= q)%nat) by lia.
    assert (Hgcd : Nat.gcd q k = 1%nat) by (unfold q; apply Hcop_pp; assumption).
    assert (Hk1 : (1 <= k)%nat).
    { destruct k as [|k']; [|lia]. rewrite Nat.mul_0_r in Hnk. lia. }
    destruct (le_lt_dec k 1) as [Hkle | Hkgt].
    + assert (Ek : k = 1%nat) by lia. subst k. rewrite Nat.mul_1_r in Hnk.
      assert (Hcosn : OrigamiNum (cos (2 * PI / INR n))).
      { destruct (le_lt_dec p 3) as [Hple3 | Hpgt].
        - assert (Ep : p = 2%nat \/ p = 3%nat) by lia. destruct Ep as [Ep|Ep]; subst p.
          + assert (Heq : n = (2 ^ e * 3 ^ 0)%nat).
            { rewrite Hnk. unfold q. rewrite Nat.pow_0_r, Nat.mul_1_r. reflexivity. }
            rewrite Heq. apply (cos_2pi_2a3b_origami e 0).
          + assert (Heq : n = (2 ^ 0 * 3 ^ e)%nat).
            { rewrite Hnk. unfold q. rewrite Nat.pow_0_r, Nat.mul_1_l. reflexivity. }
            rewrite Heq. apply (cos_2pi_2a3b_origami 0 e).
        - assert (He1' : e = 1%nat).
          { destruct (le_lt_dec e 1) as [Hele|Hege]; [lia | exfalso].
            assert (Hpphi : Nat.divide p (euler_phi (p ^ e))) by (apply Hphi_pp; [exact Hp | lia]).
            assert (Hphin : euler_phi n = euler_phi (p ^ e)) by (rewrite Hnk; reflexivity).
            destruct Hsm as [a [b Hab]].
            assert (Hpdvd : Nat.divide p (2 ^ a * 3 ^ b)%nat).
            { rewrite <- Hab, Hphin. exact Hpphi. }
            destruct (Hpdiv23 p a b Hp Hpdvd) as [E2|E3]; lia. }
          subst e. unfold q in Hnk. rewrite Nat.pow_1_r in Hnk.
          assert (En : n = p) by lia. rewrite En.
          apply Hcore; [exact Hp | rewrite <- En; exact Hsm]. }
      split; [exact Hcosn | apply sin_origami_of_cos; [exact Hn2 | exact Hcosn]].
    + assert (Hk2 : (2 <= k)%nat) by lia.
      assert (Hqlt : (q < n)%nat) by (rewrite Hnk; nia).
      assert (Hklt : (k < n)%nat) by (rewrite Hnk; nia).
      assert (Hphi_eq : euler_phi n = (euler_phi q * euler_phi k)%nat).
      { rewrite Hnk. apply euler_phi_mult; [lia | lia | exact Hgcd]. }
      destruct Hsm as [a [b Hab]].
      assert (Hsmq : two_three_smooth (euler_phi q)).
      { apply (divisor_smooth a b). rewrite <- Hab, Hphi_eq. exists (euler_phi k). ring. }
      assert (Hsmk : two_three_smooth (euler_phi k)).
      { apply (divisor_smooth a b). rewrite <- Hab, Hphi_eq. exists (euler_phi q). ring. }
      destruct (IH q Hqlt ltac:(lia) Hsmq) as [Hcq Hsq].
      destruct (IH k Hklt ltac:(lia) Hsmk) as [Hck Hsk].
      rewrite Hnk.
      apply cos_sin_origami_mul; [lia | lia | exact Hgcd | exact Hcq | exact Hsq | exact Hck | exact Hsk].
Qed.

(* 2-3-smooth phi(n) gives origami cos(2pi/n). *)
Theorem cos_2pi_n_origami_smooth : forall n, (1 <= n)%nat ->
  two_three_smooth (euler_phi n) -> OrigamiNum (cos (2 * PI / INR n)).
Proof. intros n Hn Hsm. apply (cos_sin_smooth n Hn Hsm). Qed.

(* cos(2pi/n) is origami iff phi(n) is 2-3-smooth. *)
Theorem ngon_origami_iff : forall n, (3 <= n)%nat ->
  (OrigamiNum (cos (2 * PI / INR n)) <-> two_three_smooth (euler_phi n)).
Proof.
  intros n Hn. split.
  - intro HO. destruct (Classical_Prop.classic (two_three_smooth (euler_phi n))) as [Hs|Hns].
    + exact Hs.
    + exfalso. exact (cos_2pi_n_not_origami_clean n Hn Hns HO).
  - intro Hs. apply cos_2pi_n_origami_smooth; [lia | exact Hs].
Qed.

End Reduction.
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
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope Z_scope.
Open Scope R_scope.
Open Scope R_scope.
(* ---- base level of the period tower (former gauss.v) ---- *)
(******************************************************************************)
(*  gauss.v — completes todo item #1: the Galois sufficiency backbone.          *)
(*                                                                            *)
(*  Discharges Hcore (the last hypothesis of dev.v's Section Reduction) via    *)
(*  the real Gaussian-period tower over the cyclic unit group mod p, then      *)
(*  assembles the full constructibility iff: for n >= 3, cos(2*PI/n) is         *)
(*  origami iff phi(n) is 2-3-smooth.                                          *)
(******************************************************************************)
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
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope Z_scope.
Open Scope R_scope.
Open Scope R_scope.
Open Scope R_scope.
(* ===== generic rsum helpers (rsum : list nat -> (nat -> R) -> R) ===== *)

Lemma rsum_nilL : forall phi, rsum [] phi = 0.
Proof. reflexivity. Qed.

Lemma rsum_consL : forall x l phi, rsum (x :: l) phi = phi x + rsum l phi.
Proof. reflexivity. Qed.

Lemma rsum_appL : forall l1 l2 phi, rsum (l1 ++ l2) phi = rsum l1 phi + rsum l2 phi.
Proof.
  intros l1 l2 phi. induction l1 as [|x l1 IH].
  - rewrite app_nil_l, rsum_nilL. ring.
  - rewrite <- app_comm_cons, !rsum_consL, IH. ring.
Qed.

Lemma rsum_singleL : forall a phi, rsum [a] phi = phi a.
Proof. intros a phi. rewrite rsum_consL, rsum_nilL. ring. Qed.

Lemma rsum_const1 : forall m, rsum (seq 0 m) (fun _ => 1) = INR m.
Proof.
  induction m as [|m IH].
  - reflexivity.
  - rewrite seq_S, rsum_appL, rsum_singleL, IH, S_INR. ring.
Qed.

Lemma rsum_2 : forall phi, rsum (seq 0 2) phi = phi 0%nat + phi 1%nat.
Proof. intro phi. change (seq 0 2) with [0%nat; 1%nat]. rewrite !rsum_consL, rsum_nilL. ring. Qed.

Lemma rsum_3 : forall phi, rsum (seq 0 3) phi = phi 0%nat + phi 1%nat + phi 2%nat.
Proof. intro phi. change (seq 0 3) with [0%nat; 1%nat; 2%nat]. rewrite !rsum_consL, rsum_nilL. ring. Qed.

(* cossum as an rsum over an index range *)
Lemma cossum_rsum : forall m a, cossum m a = rsum (seq 0 m) (fun k => cos (INR k * a)).
Proof.
  intros m a. induction m as [|m IH].
  - reflexivity.
  - cbn [cossum]. rewrite seq_S, rsum_appL, rsum_singleL, IH. reflexivity.
Qed.

(* rsum of cos-of-residue equals csum over the mapped integer list *)
Lemma rsum_ca_map : forall (p : Z) (h : nat -> Z) (l : list nat),
  rsum l (fun t => ca p (h t)) = csum p (map h l).
Proof.
  intros p h l. induction l as [|x l IH].
  - reflexivity.
  - cbn [map]. rewrite rsum_consL, csum_cons, IH. reflexivity.
Qed.
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
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope Z_scope.
Open Scope R_scope.
Open Scope R_scope.
Open Scope R_scope.
Section W.

Variable P : nat.
Variable g : Z.
Hypothesis HP : Znumtheory.prime (Z.of_nat P).
Hypothesis HP5 : (5 <= P)%nat.
Hypothesis Hg : per P g (P - 1).
Hypothesis Hgord : forall k, (1 <= k < P - 1)%nat -> ~ cg (Z.of_nat P) (zpn g k) 1%Z.
Hypothesis Hgr : (1 <= g < Z.of_nat P)%Z.
Hypothesis Hsmooth : two_three_smooth (P - 1).

(* ===== p does not divide g, its powers, or v*g^t (for p-coprime v) ===== *)

Lemma pndg : ~ Z.divide (Z.of_nat P) g.
Proof.
  intro Hd.
  pose proof (Znumtheory.Zdivide_le (Z.of_nat P) g ltac:(lia) ltac:(lia) Hd). lia.
Qed.

Lemma pndzpn : forall i, ~ Z.divide (Z.of_nat P) (zpn g i).
Proof.
  induction i as [|i IH].
  - cbn [zpn]. intro Hd.
    pose proof (Znumtheory.Zdivide_le (Z.of_nat P) 1 ltac:(lia) ltac:(lia) Hd). lia.
  - cbn [zpn]. intro Hd.
    destruct (Znumtheory.prime_mult (Z.of_nat P) HP g (zpn g i) Hd) as [H|H].
    + apply pndg; exact H.
    + apply IH; exact H.
Qed.

Lemma pndvg : forall v, ~ Z.divide (Z.of_nat P) v ->
  forall t, ~ Z.divide (Z.of_nat P) (v * zpn g t)%Z.
Proof.
  intros v Hv t Hd.
  destruct (Znumtheory.prime_mult (Z.of_nat P) HP v (zpn g t) Hd) as [H|H].
  - apply Hv; exact H.
  - apply (pndzpn t); exact H.
Qed.

(* ===== distinct powers: g^i = g^j mod p (i,j < p-1) forces i = j ===== *)

Lemma zpn_lt_neq : forall i j, (i < j)%nat -> (j < P - 1)%nat ->
  ~ Z.divide (Z.of_nat P) (zpn g i - zpn g j)%Z.
Proof.
  intros i j Hij Hj Hd.
  assert (Hjj : zpn g j = (zpn g i * zpn g (j - i))%Z).
  { rewrite <- zpn_add. f_equal. lia. }
  assert (Hfac : (zpn g i - zpn g j)%Z = (zpn g i * (1 - zpn g (j - i)))%Z)
    by (rewrite Hjj; ring).
  rewrite Hfac in Hd.
  assert (Hd2 : Z.divide (Z.of_nat P) (1 - zpn g (j - i))%Z).
  { destruct (Znumtheory.prime_mult (Z.of_nat P) HP (zpn g i) (1 - zpn g (j - i)) Hd)
      as [Hbad|Hgood]; [exfalso; apply (pndzpn i); exact Hbad | exact Hgood]. }
  assert (Hd3 : Z.divide (Z.of_nat P) (zpn g (j - i) - 1)%Z).
  { replace (zpn g (j - i) - 1)%Z with (-(1 - zpn g (j - i)))%Z by ring.
    apply Z.divide_opp_r; exact Hd2. }
  apply (Hgord (j - i)); [split; lia | exact Hd3].
Qed.

Lemma zpn_mod_inj : forall i j, (i < P - 1)%nat -> (j < P - 1)%nat ->
  Z.divide (Z.of_nat P) (zpn g i - zpn g j)%Z -> i = j.
Proof.
  intros i j Hi Hj Hd.
  destruct (Nat.lt_trichotomy i j) as [Hlt|[Heq|Hgt]].
  - exfalso. apply (zpn_lt_neq i j Hlt Hj Hd).
  - exact Heq.
  - exfalso. apply (zpn_lt_neq j i Hgt Hi).
    replace (zpn g j - zpn g i)%Z with (-(zpn g i - zpn g j))%Z by ring.
    apply Z.divide_opp_r; exact Hd.
Qed.

(* ===== Base level: the full period PerV v 1 is rational (= INR(p-1) if p|v,
   else -1 by the geometric sum over the units), hence origami. ===== *)

Lemma base : forall v, OrigamiNum (PerV P g v 1).
Proof.
  intro v.
  assert (Hpne : (Z.of_nat P <> 0)%Z) by lia.
  assert (HPV : PerV P g v 1 = rsum (seq 0 (P - 1)) (fun t => ca (Z.of_nat P) (v * zpn g t)%Z)).
  { rewrite (PerV_rsum P g v 1), Nat.div_1_r. apply rsum_ext. intro t.
    rewrite Nat.mul_1_l. reflexivity. }
  rewrite HPV.
  destruct (Znumtheory.Zdivide_dec (Z.of_nat P) v) as [Hdv | Hndv].
  - assert (Hall : rsum (seq 0 (P - 1)) (fun t => ca (Z.of_nat P) (v * zpn g t)%Z)
                 = rsum (seq 0 (P - 1)) (fun _ => 1)).
    { apply rsum_ext. intro t.
      transitivity (ca (Z.of_nat P) 0%Z).
      - apply ca_cong; [exact Hpne |].
        replace (v * zpn g t - 0)%Z with (v * zpn g t)%Z by ring.
        apply Z.divide_mul_l; exact Hdv.
      - apply ca_0. }
    rewrite Hall, rsum_const1. apply Origami_nat.
  - set (q := Z.of_nat P) in *.
    set (L1 := map (fun t => (v * zpn g t) mod q)%Z (seq 0 (P - 1))).
    set (L2 := map Z.of_nat (seq 1 (P - 1))).
    assert (HinclF : incl L1 L2).
    { intros x Hx. unfold L1 in Hx. apply in_map_iff in Hx.
      destruct Hx as [t [Hxt Ht]]. cbn beta in Hxt.
      assert (Hbound : (0 <= x < q)%Z) by (rewrite <- Hxt; apply Z.mod_pos_bound; lia).
      assert (Hnz : (x <> 0)%Z).
      { rewrite <- Hxt. intro H0. apply (pndvg v Hndv t).
        apply (proj1 (Z.mod_divide (v * zpn g t) q Hpne)); exact H0. }
      unfold L2. apply in_map_iff. exists (Z.to_nat x). split.
      - rewrite Z2Nat.id by lia. reflexivity.
      - apply in_seq.
        assert (Hxk : x = Z.of_nat (Z.to_nat x)) by (rewrite Z2Nat.id by lia; reflexivity).
        rewrite Hxk in Hbound, Hnz. lia. }
    assert (Hlen1 : length L1 = (P - 1)%nat)
      by (unfold L1; rewrite length_map, length_seq; reflexivity).
    assert (Hlen2 : length L2 = (P - 1)%nat)
      by (unfold L2; rewrite length_map, length_seq; reflexivity).
    assert (HndL1 : NoDup L1).
    { unfold L1. apply pm_NoDup_map_inj_in; [| apply seq_NoDup].
      intros i j Hi Hj Heq. cbn beta in Heq. apply in_seq in Hi. apply in_seq in Hj.
      apply (zpn_mod_inj i j); [lia | lia |].
      assert (Hvij : Z.divide q (v * zpn g i - v * zpn g j)%Z).
      { apply (proj1 (Z.mod_divide (v * zpn g i - v * zpn g j) q Hpne)).
        rewrite Zminus_mod, Heq, Z.sub_diag. apply Zmod_0_l. }
      replace (v * zpn g i - v * zpn g j)%Z with (v * (zpn g i - zpn g j))%Z in Hvij by ring.
      destruct (Znumtheory.prime_mult q HP v (zpn g i - zpn g j) Hvij) as [Hbad|Hgood].
      - exfalso. apply Hndv; exact Hbad.
      - exact Hgood. }
    assert (HndL2 : NoDup L2).
    { unfold L2. apply pm_NoDup_map_inj_in; [| apply seq_NoDup].
      intros i j _ _ Heq. apply Nat2Z.inj; exact Heq. }
    assert (HinclB : incl L2 L1).
    { apply (NoDup_length_incl HndL1); [rewrite Hlen1, Hlen2; lia | exact HinclF]. }
    assert (Hperm : Permutation L1 L2).
    { apply NoDup_Permutation; [exact HndL1 | exact HndL2 |].
      intro x. split; [apply HinclF | apply HinclB]. }
    assert (Hmod : rsum (seq 0 (P - 1)) (fun t => ca q (v * zpn g t)%Z) = csum q L1).
    { unfold L1. rewrite <- (rsum_ca_map q (fun t => (v * zpn g t) mod q)%Z (seq 0 (P - 1))).
      apply rsum_ext. intro t. apply ca_cong; [exact Hpne |].
      replace (v * zpn g t - (v * zpn g t) mod q)%Z with (((v * zpn g t) / q) * q)%Z
        by (rewrite Z.mod_eq by lia; ring).
      apply Z.divide_factor_r. }
    assert (Hunits : csum q L2 = rsum (seq 1 (P - 1)) (fun k => ca q (Z.of_nat k))).
    { unfold L2. symmetry. apply (rsum_ca_map q Z.of_nat (seq 1 (P - 1))). }
    assert (Hfull : rsum (seq 0 P) (fun k => ca q (Z.of_nat k)) = 0).
    { assert (Hb : forall k, cos (INR k * (2 * PI / INR P)) = ca q (Z.of_nat k)).
      { intro k. unfold ca, q. rewrite <- !INR_IZR_INZ. f_equal. field. apply not_0_INR; lia. }
      rewrite <- (rsum_ext (seq 0 P) (fun k => cos (INR k * (2 * PI / INR P)))
                   (fun k => ca q (Z.of_nat k)) Hb).
      rewrite <- cossum_rsum. apply cossum_full_zero. lia. }
    assert (HseqP : seq 0 P = 0%nat :: seq 1 (P - 1)).
    { replace P with (S (P - 1)) at 1 by lia. reflexivity. }
    assert (Hm1 : rsum (seq 1 (P - 1)) (fun k => ca q (Z.of_nat k)) = -1).
    { assert (Hca0 : ca q (Z.of_nat 0) = 1) by (change (Z.of_nat 0) with 0%Z; apply ca_0).
      rewrite HseqP, rsum_consL, Hca0 in Hfull. lra. }
    rewrite Hmod, (csum_perm q L1 L2 Hperm), Hunits, Hm1.
    replace (-1) with (- (1)) by ring. apply Origami_neg, ON_1.
Qed.

End W.
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
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope Z_scope.
Open Scope R_scope.
Open Scope R_scope.
Open Scope R_scope.
(* ---- the period tower + Hcore + the full iff (former tower.v) ---- *)
(******************************************************************************)
(*  tower.v — completes todo item #1: the Galois sufficiency backbone.          *)
(*                                                                            *)
(*  The Gaussian-period tower: for prime p with 2-3-smooth phi(p) = p-1, every  *)
(*  period PerV P g v D is origami, by induction up the divisor chain of p-1    *)
(*  (each step a degree-2 sqrt or degree-3 cube root, both origami).  This       *)
(*  discharges Hcore, the sole remaining hypothesis of dev.v's Reduction, and    *)
(*  closes the constructible half of the n-gon theorem for all n.               *)
(******************************************************************************)
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
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope Z_scope.
Open Scope R_scope.
Open Scope R_scope.
Open Scope R_scope.
Open Scope R_scope.
(* ===== Pure algebra: a root from the power sums of the conjugate periods ===== *)

(* degree-2: a is a root of t^2 - e1 t + e2, with e1,e2 the symmetric functions
   read off from the power sums p1 = e1 = a+b, p2 = a^2+b^2. *)
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
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope Z_scope.
Open Scope R_scope.
Open Scope R_scope.
Open Scope R_scope.
Open Scope R_scope.
Section Tower.

Variable P : nat.
Variable g : Z.
Hypothesis HP : Znumtheory.prime (Z.of_nat P).
Hypothesis HP5 : (5 <= P)%nat.
Hypothesis Hg : per P g (P - 1).
Hypothesis Hgord : forall k, (1 <= k < P - 1)%nat -> ~ cg (Z.of_nat P) (zpn g k) 1%Z.
Hypothesis Hgr : (1 <= g < Z.of_nat P)%Z.
Hypothesis Hsmooth : two_three_smooth (P - 1).

Local Notation n := (P - 1)%nat.

(* ===== general two-coset same-index product collapse (generalizes sub_sq) ===== *)
Lemma par_prod_eq : forall (D s : nat) (u u' : Z),
  (1 <= D)%nat -> (1 <= s)%nat -> Nat.divide (D * s) n ->
  2 * rsum (seq 0 s)
        (fun l => PerV P g (u * zpn g (D * l)) (D * s)
                * PerV P g (u' * zpn g (D * l)) (D * s))
  = rsum (seq 0 (n / (D * s)))
      (fun s'' => PerV P g (u * zpn g (D * s * s'') + u') D
                + PerV P g (u * zpn g (D * s * s'') - u') D).
Proof.
  intros D s u u' HD Hs Hdiv.
  assert (HE : (1 <= D * s)%nat) by nia.
  assert (HDne : D <> 0%nat) by lia.
  assert (Hsne : s <> 0%nat) by lia.
  rewrite rsum_scale_l.
  transitivity (rsum (seq 0 s) (fun l =>
      rsum (seq 0 (n / (D * s))) (fun s'' =>
          PerV P g (u * zpn g (D * l) * zpn g (D * s * s'') + u' * zpn g (D * l)) (D * s)
        + PerV P g (u * zpn g (D * l) * zpn g (D * s * s'') - u' * zpn g (D * l)) (D * s)))).
  { apply rsum_ext. intro l.
    exact (PerV_mul P g HP5 Hg (u * zpn g (D * l))%Z (u' * zpn g (D * l))%Z (D * s) HE Hdiv). }
  rewrite rsum_swap.
  apply rsum_ext. intro s''.
  rewrite rsum_plus.
  assert (HAp : rsum (seq 0 s) (fun l =>
            PerV P g (u * zpn g (D * l) * zpn g (D * s * s'') + u' * zpn g (D * l)) (D * s))
          = PerV P g (u * zpn g (D * s * s'') + u') D).
  { transitivity (rsum (seq 0 s) (fun l =>
        PerV P g (zpn g (D * l) * (u * zpn g (D * s * s'') + u')) (D * s))).
    - apply rsum_ext. intro l.
      replace (zpn g (D * l) * (u * zpn g (D * s * s'') + u'))%Z
        with (u * zpn g (D * l) * zpn g (D * s * s'') + u' * zpn g (D * l))%Z by ring.
      reflexivity.
    - exact (collapse P g HP5 D s (u * zpn g (D * s * s'') + u')%Z HDne Hsne Hdiv). }
  assert (HBm : rsum (seq 0 s) (fun l =>
            PerV P g (u * zpn g (D * l) * zpn g (D * s * s'') - u' * zpn g (D * l)) (D * s))
          = PerV P g (u * zpn g (D * s * s'') - u') D).
  { transitivity (rsum (seq 0 s) (fun l =>
        PerV P g (zpn g (D * l) * (u * zpn g (D * s * s'') - u')) (D * s))).
    - apply rsum_ext. intro l.
      replace (zpn g (D * l) * (u * zpn g (D * s * s'') - u'))%Z
        with (u * zpn g (D * l) * zpn g (D * s * s'') - u' * zpn g (D * l))%Z by ring.
      reflexivity.
    - exact (collapse P g HP5 D s (u * zpn g (D * s * s'') - u')%Z HDne Hsne Hdiv). }
  rewrite HAp, HBm. reflexivity.
Qed.

(* origami-ness of the parallel product, given the coarse level is origami *)
Lemma par_prod_ON : forall (D s : nat) (u u' : Z),
  (1 <= D)%nat -> (1 <= s)%nat -> Nat.divide (D * s) n ->
  (forall v, OrigamiNum (PerV P g v D)) ->
  OrigamiNum (rsum (seq 0 s)
     (fun l => PerV P g (u * zpn g (D * l)) (D * s)
             * PerV P g (u' * zpn g (D * l)) (D * s))).
Proof.
  intros D s u u' HD Hs Hdiv IH.
  assert (Hhalf : rsum (seq 0 s)
        (fun l => PerV P g (u * zpn g (D * l)) (D * s)
                * PerV P g (u' * zpn g (D * l)) (D * s))
      = (rsum (seq 0 (n / (D * s)))
          (fun s'' => PerV P g (u * zpn g (D * s * s'') + u') D
                    + PerV P g (u * zpn g (D * s * s'') - u') D)) / 2).
  { pose proof (par_prod_eq D s u u' HD Hs Hdiv) as Heq. lra. }
  rewrite Hhalf.
  apply Origami_div; [| apply Origami_two | lra].
  apply rsum_ON. intro s''. apply ON_add; apply IH.
Qed.

(* ===== the cubic power sum: sum of the s conjugate sub-periods cubed ===== *)
Lemma sub_cube_ON : forall (D s : nat) (w : Z),
  (1 <= D)%nat -> (1 <= s)%nat -> Nat.divide (D * s) n ->
  (forall v, OrigamiNum (PerV P g v D)) ->
  OrigamiNum (rsum (seq 0 s)
     (fun l => PerV P g (w * zpn g (D * l)) (D * s)
             * PerV P g (w * zpn g (D * l)) (D * s)
             * PerV P g (w * zpn g (D * l)) (D * s))).
Proof.
  intros D s w HD Hs Hdiv IH.
  assert (HE : (1 <= D * s)%nat) by nia.
  set (RHS := rsum (seq 0 (n / (D * s)))
     (fun s' =>
        rsum (seq 0 s) (fun l =>
           PerV P g (w * zpn g (D * l)) (D * s)
         * PerV P g ((w * zpn g (D * s * s') + w) * zpn g (D * l)) (D * s))
      + rsum (seq 0 s) (fun l =>
           PerV P g (w * zpn g (D * l)) (D * s)
         * PerV P g ((w * zpn g (D * s * s') - w) * zpn g (D * l)) (D * s)))).
  assert (Hstep : 2 * rsum (seq 0 s)
        (fun l => PerV P g (w * zpn g (D * l)) (D * s)
                * PerV P g (w * zpn g (D * l)) (D * s)
                * PerV P g (w * zpn g (D * l)) (D * s))
      = RHS).
  { rewrite rsum_scale_l. unfold RHS.
    transitivity (rsum (seq 0 s) (fun l =>
        rsum (seq 0 (n / (D * s))) (fun s' =>
            PerV P g (w * zpn g (D * l)) (D * s)
          * PerV P g ((w * zpn g (D * s * s') + w) * zpn g (D * l)) (D * s)
          + PerV P g (w * zpn g (D * l)) (D * s)
          * PerV P g ((w * zpn g (D * s * s') - w) * zpn g (D * l)) (D * s)))).
    - apply rsum_ext. intro l.
      assert (Hsq2 : 2 * (PerV P g (w * zpn g (D * l)) (D * s)
                       * PerV P g (w * zpn g (D * l)) (D * s))
        = rsum (seq 0 (n / (D * s))) (fun s' =>
            PerV P g ((w * zpn g (D * s * s') + w) * zpn g (D * l)) (D * s)
          + PerV P g ((w * zpn g (D * s * s') - w) * zpn g (D * l)) (D * s))).
      { rewrite (PerV_mul P g HP5 Hg (w * zpn g (D * l))%Z (w * zpn g (D * l))%Z (D * s) HE Hdiv).
        apply rsum_ext. intro s'.
        replace (w * zpn g (D * l) * zpn g (D * s * s') + w * zpn g (D * l))%Z
          with ((w * zpn g (D * s * s') + w) * zpn g (D * l))%Z by ring.
        replace (w * zpn g (D * l) * zpn g (D * s * s') - w * zpn g (D * l))%Z
          with ((w * zpn g (D * s * s') - w) * zpn g (D * l))%Z by ring.
        reflexivity. }
      replace (2 * (PerV P g (w * zpn g (D * l)) (D * s)
                  * PerV P g (w * zpn g (D * l)) (D * s)
                  * PerV P g (w * zpn g (D * l)) (D * s)))
        with (PerV P g (w * zpn g (D * l)) (D * s)
            * (2 * (PerV P g (w * zpn g (D * l)) (D * s)
                  * PerV P g (w * zpn g (D * l)) (D * s)))) by ring.
      rewrite Hsq2, rsum_scale_l. apply rsum_ext. intro s'. ring.
    - rewrite rsum_swap. apply rsum_ext. intro s'. apply rsum_plus. }
  assert (HON : OrigamiNum RHS).
  { unfold RHS. apply rsum_ON. intro s'. apply ON_add.
    - exact (par_prod_ON D s w (w * zpn g (D * s * s') + w)%Z HD Hs Hdiv IH).
    - exact (par_prod_ON D s w (w * zpn g (D * s * s') - w)%Z HD Hs Hdiv IH). }
  assert (Hval : rsum (seq 0 s)
        (fun l => PerV P g (w * zpn g (D * l)) (D * s)
                * PerV P g (w * zpn g (D * l)) (D * s)
                * PerV P g (w * zpn g (D * l)) (D * s))
      = RHS / 2) by lra.
  rewrite Hval. apply Origami_div; [exact HON | apply Origami_two | lra].
Qed.

(* ===== tower step: degree-2 (quadratic / square root) ===== *)
Lemma step2 : forall (D : nat) (w : Z), (1 <= D)%nat -> Nat.divide (D * 2) n ->
  (forall v, OrigamiNum (PerV P g v D)) ->
  OrigamiNum (PerV P g w (D * 2)).
Proof.
  intros D w HD Hdiv IH.
  assert (He1 : PerV P g w D
    = PerV P g (w * zpn g (D * 0)) (D * 2) + PerV P g (w * zpn g (D * 1)) (D * 2)).
  { rewrite (PerV_partition P g HP5 w D 2 ltac:(lia) ltac:(lia) Hdiv). apply rsum_2. }
  assert (Hp2 : rsum (seq 0 2) (fun l => PerV P g (w * zpn g (D * l)) (D * 2)
                                       * PerV P g (w * zpn g (D * l)) (D * 2))
    = PerV P g (w * zpn g (D * 0)) (D * 2) * PerV P g (w * zpn g (D * 0)) (D * 2)
    + PerV P g (w * zpn g (D * 1)) (D * 2) * PerV P g (w * zpn g (D * 1)) (D * 2))
    by apply rsum_2.
  assert (Hp2ON : OrigamiNum (rsum (seq 0 2) (fun l => PerV P g (w * zpn g (D * l)) (D * 2)
                                       * PerV P g (w * zpn g (D * l)) (D * 2))))
    by exact (sub_sq_ON P g HP5 Hg D 2 w HD ltac:(lia) Hdiv IH).
  set (e1 := PerV P g w D) in *.
  set (p2 := rsum (seq 0 2) (fun l => PerV P g (w * zpn g (D * l)) (D * 2)
                                    * PerV P g (w * zpn g (D * l)) (D * 2))) in *.
  set (x0 := PerV P g (w * zpn g (D * 0)) (D * 2)) in *.
  set (x1 := PerV P g (w * zpn g (D * 1)) (D * 2)) in *.
  assert (He1ON : OrigamiNum e1) by (unfold e1; apply IH).
  assert (He2ON : OrigamiNum ((e1 * e1 - p2) / 2)) by
    (apply Origami_div; [ apply ON_sub; [ apply ON_mul; exact He1ON | exact Hp2ON ]
                        | apply Origami_two | lra ]).
  assert (Hx0 : PerV P g w (D * 2) = x0).
  { unfold x0. f_equal. rewrite Nat.mul_0_r. cbn [zpn]. ring. }
  rewrite Hx0.
  apply (origami_general_quadratic (- e1) ((e1 * e1 - p2) / 2) x0).
  - apply Origami_neg; exact He1ON.
  - exact He2ON.
  - exact (quad_root_from_psums x0 x1 e1 p2 He1 Hp2).
Qed.

(* ===== tower step: degree-3 (cubic / cube root) ===== *)
Lemma step3 : forall (D : nat) (w : Z), (1 <= D)%nat -> Nat.divide (D * 3) n ->
  (forall v, OrigamiNum (PerV P g v D)) ->
  OrigamiNum (PerV P g w (D * 3)).
Proof.
  intros D w HD Hdiv IH.
  assert (He1 : PerV P g w D
    = PerV P g (w * zpn g (D * 0)) (D * 3)
    + PerV P g (w * zpn g (D * 1)) (D * 3)
    + PerV P g (w * zpn g (D * 2)) (D * 3)).
  { rewrite (PerV_partition P g HP5 w D 3 ltac:(lia) ltac:(lia) Hdiv). apply rsum_3. }
  assert (Hp2 : rsum (seq 0 3) (fun l => PerV P g (w * zpn g (D * l)) (D * 3)
                                       * PerV P g (w * zpn g (D * l)) (D * 3))
    = PerV P g (w * zpn g (D * 0)) (D * 3) * PerV P g (w * zpn g (D * 0)) (D * 3)
    + PerV P g (w * zpn g (D * 1)) (D * 3) * PerV P g (w * zpn g (D * 1)) (D * 3)
    + PerV P g (w * zpn g (D * 2)) (D * 3) * PerV P g (w * zpn g (D * 2)) (D * 3))
    by apply rsum_3.
  assert (Hp3 : rsum (seq 0 3) (fun l => PerV P g (w * zpn g (D * l)) (D * 3)
                                       * PerV P g (w * zpn g (D * l)) (D * 3)
                                       * PerV P g (w * zpn g (D * l)) (D * 3))
    = PerV P g (w * zpn g (D * 0)) (D * 3) * PerV P g (w * zpn g (D * 0)) (D * 3) * PerV P g (w * zpn g (D * 0)) (D * 3)
    + PerV P g (w * zpn g (D * 1)) (D * 3) * PerV P g (w * zpn g (D * 1)) (D * 3) * PerV P g (w * zpn g (D * 1)) (D * 3)
    + PerV P g (w * zpn g (D * 2)) (D * 3) * PerV P g (w * zpn g (D * 2)) (D * 3) * PerV P g (w * zpn g (D * 2)) (D * 3))
    by apply rsum_3.
  assert (Hp2ON : OrigamiNum (rsum (seq 0 3) (fun l => PerV P g (w * zpn g (D * l)) (D * 3)
                                       * PerV P g (w * zpn g (D * l)) (D * 3))))
    by exact (sub_sq_ON P g HP5 Hg D 3 w HD ltac:(lia) Hdiv IH).
  assert (Hp3ON : OrigamiNum (rsum (seq 0 3) (fun l => PerV P g (w * zpn g (D * l)) (D * 3)
                                       * PerV P g (w * zpn g (D * l)) (D * 3)
                                       * PerV P g (w * zpn g (D * l)) (D * 3))))
    by exact (sub_cube_ON D 3 w HD ltac:(lia) Hdiv IH).
  set (e1 := PerV P g w D) in *.
  set (p2 := rsum (seq 0 3) (fun l => PerV P g (w * zpn g (D * l)) (D * 3)
                                    * PerV P g (w * zpn g (D * l)) (D * 3))) in *.
  set (p3 := rsum (seq 0 3) (fun l => PerV P g (w * zpn g (D * l)) (D * 3)
                                    * PerV P g (w * zpn g (D * l)) (D * 3)
                                    * PerV P g (w * zpn g (D * l)) (D * 3))) in *.
  set (x0 := PerV P g (w * zpn g (D * 0)) (D * 3)) in *.
  set (x1 := PerV P g (w * zpn g (D * 1)) (D * 3)) in *.
  set (x2 := PerV P g (w * zpn g (D * 2)) (D * 3)) in *.
  assert (He1ON : OrigamiNum e1) by (unfold e1; apply IH).
  assert (He2ON : OrigamiNum ((e1 * e1 - p2) / 2)) by
    (apply Origami_div; [ apply ON_sub; [ apply ON_mul; exact He1ON | exact Hp2ON ]
                        | apply Origami_two | lra ]).
  assert (Hx0 : PerV P g w (D * 3) = x0).
  { unfold x0. f_equal. rewrite Nat.mul_0_r. cbn [zpn]. ring. }
  rewrite Hx0.
  apply (origami_general_cubic (- e1) ((e1 * e1 - p2) / 2)
           (- ((p3 - e1 * p2 + ((e1 * e1 - p2) / 2) * e1) / 3)) x0).
  - apply Origami_neg; exact He1ON.
  - exact He2ON.
  - apply Origami_neg. apply Origami_div.
    + apply ON_add.
      * apply ON_sub; [ exact Hp3ON | apply ON_mul; [ exact He1ON | exact Hp2ON ] ].
      * apply ON_mul; [ exact He2ON | exact He1ON ].
    + apply Origami_three.
    + lra.
  - exact (cubic_root_from_psums x0 x1 x2 e1 p2 p3 He1 Hp2 Hp3).
Qed.

(* ===== the tower: every period at every divisor level of n=p-1 is origami ===== *)
Lemma period_tower : forall D, Nat.divide D n -> forall v, OrigamiNum (PerV P g v D).
Proof.
  intro D. induction D as [D IHD] using (well_founded_induction lt_wf). intros Hdiv v.
  destruct (Nat.eq_dec D 1) as [HD1 | HDne].
  - subst D. apply (base P g HP HP5 Hgord Hgr).
  - assert (HDpos : (1 <= D)%nat).
    { destruct (Nat.eq_dec D 0) as [HD0|HD0].
      - subst D. destruct Hdiv as [z Hz]. rewrite Nat.mul_0_r in Hz. lia.
      - lia. }
    assert (HD2 : (2 <= D)%nat) by lia.
    destruct (prime_factor_nat D HD2) as [q [Hqprime Hqdvd]].
    assert (Hq0 : q <> 0%nat) by (destruct Hqprime as [Hqg _]; lia).
    assert (Hq2nat : (2 <= q)%nat) by (destruct Hqprime as [Hqg _]; lia).
    destruct Hsmooth as [a [b Hab]].
    assert (Hq23 : q = 2%nat \/ q = 3%nat).
    { apply (prime_dvd_2a3b q a b Hqprime). rewrite <- Hab.
      apply (Nat.divide_trans q D (P - 1) Hqdvd Hdiv). }
    assert (HqD : (D / q * q)%nat = D) by (apply divides_div_mul; [exact Hq0 | exact Hqdvd]).
    set (D' := (D / q)%nat) in *.
    assert (HD'pos : (1 <= D')%nat) by nia.
    assert (HD'lt : (D' < D)%nat) by nia.
    assert (HD'div : Nat.divide D' (P - 1)).
    { apply (Nat.divide_trans D' D (P - 1)); [ exists q; lia | exact Hdiv ]. }
    assert (IHD' : forall v0, OrigamiNum (PerV P g v0 D')) by exact (IHD D' HD'lt HD'div).
    destruct Hq23 as [Hq2 | Hq3].
    + subst q.
      assert (Hd2div : Nat.divide (D' * 2) (P - 1)) by (rewrite HqD; exact Hdiv).
      rewrite <- HqD. exact (step2 D' v HD'pos Hd2div IHD').
    + subst q.
      assert (Hd3div : Nat.divide (D' * 3) (P - 1)) by (rewrite HqD; exact Hdiv).
      rewrite <- HqD. exact (step3 D' v HD'pos Hd3div IHD').
Qed.

(* ===== the target: cos(2*PI/P) is the finest period, hence origami ===== *)
Lemma cos_origami_section : OrigamiNum (cos (2 * PI / INR P)).
Proof.
  assert (Hnn : Nat.divide n n) by apply Nat.divide_refl.
  pose proof (period_tower n Hnn 1%Z) as HPer.
  assert (Hval : PerV P g 1 n = cos (2 * PI / INR P)).
  { rewrite (PerV_rsum P g 1 n).
    assert (Hnn1 : (n / n = 1)%nat) by (apply Nat.div_same; lia).
    rewrite Hnn1.
    assert (Hseq : seq 0 1 = [0%nat]) by reflexivity.
    rewrite Hseq, rsum_single. cbn beta.
    rewrite Nat.mul_0_r. cbn [zpn].
    replace (1 * 1)%Z with 1%Z by ring.
    exact (ca_one P HP5). }
  rewrite <- Hval. exact HPer.
Qed.

End Tower.
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
Open Scope R_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope Z_scope.
Open Scope R_scope.
Open Scope R_scope.
Open Scope R_scope.
Open Scope R_scope.
(* ===== Hcore for primes p >= 5: pick a primitive root, run the tower ===== *)
Lemma Hcore_ge5 : forall p, Znumtheory.prime (Z.of_nat p) ->
  two_three_smooth (euler_phi p) -> (5 <= p)%nat ->
  OrigamiNum (cos (2 * PI / INR p)).
Proof.
  intros p Hp Hsm Hp5.
  destruct (primitive_root p Hp Hsm Hp5) as [g [Hgr [Hper Hgord]]].
  assert (Hsm' : two_three_smooth (p - 1)) by (rewrite <- (euler_phi_prime p Hp); exact Hsm).
  exact (cos_origami_section p g Hp Hp5 Hper Hgord Hgr Hsm').
Qed.

(* ===== Hcore: the prime case, all primes (small primes 2,3 directly) ===== *)
Theorem Hcore : forall p, Znumtheory.prime (Z.of_nat p) ->
  two_three_smooth (euler_phi p) -> OrigamiNum (cos (2 * PI / INR p)).
Proof.
  intros p Hp Hsm.
  destruct (le_lt_dec 5 p) as [Hge | Hlt].
  - exact (Hcore_ge5 p Hp Hsm Hge).
  - assert (Hp2 : (2 <= p)%nat) by (destruct Hp as [Hgt _]; lia).
    destruct (Nat.eq_dec p 2) as [E2|N2]; [ subst p; exact (cos_2pi_2a3b_origami 1 0) |].
    destruct (Nat.eq_dec p 3) as [E3|N3]; [ subst p; exact (cos_2pi_2a3b_origami 0 1) |].
    exfalso. assert (E4 : p = 4%nat) by lia.
    pose proof (is_prime_of_Z p Hp) as Hisp. rewrite E4 in Hisp. destruct Hisp as [_ Hd].
    destruct (Hd 2%nat ltac:(lia) ltac:(exists 2%nat; reflexivity)) as [H|H]; lia.
Qed.

(* ===== TODO #1 COMPLETE: the constructive direction and the full iff ===== *)

(* constructive backbone: 2-3-smooth phi(n) => cos(2*PI/n) is origami, for all n *)
Theorem cos_2pi_n_origami_smooth_complete : forall m, (1 <= m)%nat ->
  two_three_smooth (euler_phi m) -> OrigamiNum (cos (2 * PI / INR m)).
Proof.
  exact (cos_2pi_n_origami_smooth Hcore ppart_exists coprime_pp p_dvd_phi_pp prime_dvd_2a3b).
Qed.

(* the full single-fold n-gon characterization, both directions, all n >= 3 *)
Theorem ngon_origami_iff_complete : forall m, (3 <= m)%nat ->
  (OrigamiNum (cos (2 * PI / INR m)) <-> two_three_smooth (euler_phi m)).
Proof.
  exact (ngon_origami_iff Hcore ppart_exists coprime_pp p_dvd_phi_pp prime_dvd_2a3b).
Qed.

(* The regular n-gon as a geometric object: all n vertices
   (cos(2.pi.k/n), sin(2.pi.k/n)) on the unit circle are constructible points
   exactly when phi(n) is 2-3-smooth, lifting the angle-level
   ngon_origami_iff_complete from cos(2pi/n) to the polygon itself. *)
Definition regular_ngon_constructible (n : nat) : Prop :=
  forall k : nat,
    ConstructiblePoint (cos (2 * PI * INR k / INR n), sin (2 * PI * INR k / INR n)).

Theorem regular_ngon_constructible_iff : forall n, (3 <= n)%nat ->
  (regular_ngon_constructible n <-> two_three_smooth (euler_phi n)).
Proof.
  intros n Hn. split.
  - intro Hverts.
    assert (HnR : INR n <> 0) by (apply not_0_INR; lia).
    specialize (Hverts 1%nat).
    replace (2 * PI * INR 1 / INR n) with (2 * PI / INR n) in Hverts
      by (rewrite INR_1; field; exact HnR).
    apply constructible_implies_origami in Hverts.
    destruct Hverts as [Hcos _]. simpl in Hcos.
    exact (proj1 (ngon_origami_iff_complete n Hn) Hcos).
  - intros Hsm k.
    assert (Hcos : OrigamiNum (cos (2 * PI / INR n)))
      by exact (proj2 (ngon_origami_iff_complete n Hn) Hsm).
    assert (Hsin : OrigamiNum (sin (2 * PI / INR n)))
      by (apply sin_origami_of_cos; [lia | exact Hcos]).
    apply regular_ngon_vertex_constructible; [lia | exact Hcos | exact Hsin].
Qed.
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
Import Cardano_C.
Open Scope R_scope.

(* ============================================================================
   Casus irreducibilis for real square+cube-root towers.

   The classical theorem: a cubic that is irreducible over Q with three real
   roots has no root expressible by real radicals.  The obstruction is not
   degree (the degree is 3, which is 2-3-smooth, so origami solves it); it is
   that Cardano's real root genuinely requires *complex* cube roots.

   Core obstruction: a real cube-root extension F(beta), beta^3 = a, of a real
   field F contains no new root of an F-irreducible cubic with three real roots.
   ============================================================================ *)

(** A monic cubic evaluated at a complex point (real coefficients). *)
Definition fC (B1 B2 B3 : R) (z : C) : C :=
  Cadd (Cadd (Ccube z) (Cmul (RtoC B1) (Cmul z z))) (Cadd (Cmul (RtoC B2) z) (RtoC B3)).

(** Cube-root obstruction.  If rho = c0 + c1*beta + c2*beta^2 (ci in F, beta a
    real cube root of a in F, with 1,beta,beta^2 independent over F) is a root of
    a monic cubic with coefficients in F all of whose complex roots are real,
    then c1 = c2 = 0 -- i.e. rho already lies in F. *)
Lemma casus_cube_heart :
  forall (F : R -> Prop) (a c0 c1 c2 B1 B2 B3 beta : R),
  is_subfield F -> F a -> F c0 -> F c1 -> F c2 -> F B1 -> F B2 -> F B3 ->
  beta ^ 3 = a ->
  lin_indep F (powers beta 3) ->
  (forall z : C, fC B1 B2 B3 z = C0 -> Cim z = 0) ->
  (c0 + c1 * beta + c2 * beta ^ 2) ^ 3
    + B1 * (c0 + c1 * beta + c2 * beta ^ 2) ^ 2
    + B2 * (c0 + c1 * beta + c2 * beta ^ 2) + B3 = 0 ->
  c1 = 0 /\ c2 = 0.
Proof.
  intros F a c0 c1 c2 B1 B2 B3 beta HF Fa Fc0 Fc1 Fc2 FB1 FB2 FB3 Hbeta Hindep Hreal Hroot.
  set (A0 := c0*c0*c0 + 6*c0*c1*c2*a + a*(c1*c1*c1) + a*a*(c2*c2*c2)
             + B1*(c0*c0 + 2*c1*c2*a) + B2*c0 + B3).
  set (A1 := 3*c0*c0*c1 + 3*a*c0*c2*c2 + 3*a*c1*c1*c2 + B1*(2*c0*c1 + c2*c2*a) + B2*c1).
  set (A2 := 3*c0*c0*c2 + 3*c0*c1*c1 + 3*a*c1*c2*c2 + B1*(2*c0*c2 + c1*c1) + B2*c2).
  assert (E4 : beta^4 = a*beta)
    by (replace (beta^4) with (beta^3*beta) by ring; rewrite Hbeta; ring).
  set (P0 := c0*c0 + 2*c1*c2*a). set (P1 := 2*c0*c1 + c2*c2*a). set (P2 := 2*c0*c2 + c1*c1).
  assert (Hrho2 : (c0 + c1*beta + c2*beta^2)^2 = P0 + P1*beta + P2*beta^2).
  { unfold P0, P1, P2.
    assert (Hr : (c0 + c1*beta + c2*beta^2)^2
                 = c0*c0 + 2*c0*c1*beta + (2*c0*c2+c1*c1)*beta^2 + 2*c1*c2*beta^3 + c2*c2*beta^4)
      by ring.
    rewrite Hr, Hbeta, E4. ring. }
  assert (Hrho3 : (c0 + c1*beta + c2*beta^2)^3
                  = (c0*P0 + a*(c1*P2 + c2*P1)) + (c0*P1 + c1*P0 + a*c2*P2)*beta
                    + (c0*P2 + c1*P1 + c2*P0)*beta^2).
  { assert (Hr : (c0 + c1*beta + c2*beta^2)^3
                 = (c0 + c1*beta + c2*beta^2) * (c0 + c1*beta + c2*beta^2)^2) by ring.
    rewrite Hr, Hrho2.
    assert (Hr2 : (c0 + c1*beta + c2*beta^2) * (P0 + P1*beta + P2*beta^2)
                  = c0*P0 + (c0*P1 + c1*P0)*beta + (c0*P2 + c1*P1 + c2*P0)*beta^2
                    + (c1*P2 + c2*P1)*beta^3 + c2*P2*beta^4) by ring.
    rewrite Hr2, Hbeta, E4. ring. }
  assert (HRstar : (c0 + c1*beta + c2*beta^2)^3 + B1*(c0+c1*beta+c2*beta^2)^2
                   + B2*(c0+c1*beta+c2*beta^2) + B3 = A0 + A1*beta + A2*beta^2).
  { rewrite Hrho3, Hrho2. unfold A0, A1, A2, P0, P1, P2. ring. }
  assert (Heq0 : A0 + A1*beta + A2*beta^2 = 0) by (rewrite <- HRstar; exact Hroot).
  assert (F1 : F 1) by (apply subfield_1; exact HF).
  assert (F2 : F 2) by (replace 2 with (1+1) by ring; apply subfield_add; assumption).
  assert (F3 : F 3) by (replace 3 with (2+1) by ring; apply subfield_add; assumption).
  assert (F6 : F 6) by (replace 6 with (2*3) by ring; apply subfield_mul; assumption).
  assert (FA0 : F A0) by (unfold A0; sfclose).
  assert (FA1 : F A1) by (unfold A1; sfclose).
  assert (FA2 : F A2) by (unfold A2; sfclose).
  assert (HFA : Forall F (A0 :: A1 :: A2 :: nil))
    by (constructor; [exact FA0 | constructor; [exact FA1 | constructor; [exact FA2 | constructor]]]).
  assert (Hlen3 : length (A0 :: A1 :: A2 :: nil) = length (powers beta 3))
    by (rewrite powers_length; reflexivity).
  assert (HAcomb : Fcomb (A0 :: A1 :: A2 :: nil) (powers beta 3) = 0).
  { transitivity (A0 + A1*beta + A2*beta^2); [simpl; ring | exact Heq0]. }
  pose proof (Hindep (A0::A1::A2::nil) Hlen3 HFA HAcomb) as HA.
  pose proof (Forall_inv HA) as HA0.
  pose proof (Forall_inv (Forall_inv_tail HA)) as HA1.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HA))) as HA2.
  (* the complex conjugate root rho' = c0 + c1*(beta*omega) + c2*(beta*omega)^2 *)
  set (gamma := Cmul (RtoC beta) Comega).
  assert (Hg3 : Ccube gamma = RtoC a).
  { unfold gamma.
    replace (Ccube (Cmul (RtoC beta) Comega))
      with (Cmul (Ccube (RtoC beta)) (Ccube Comega)) by (unfold Ccube; ring).
    rewrite Comega_cube.
    replace (Ccube (RtoC beta)) with (RtoC (beta^3))
      by (unfold Ccube, RtoC, Cmul; simpl; f_equal; ring).
    rewrite Hbeta. ring. }
  assert (Hgre : fst gamma = - beta / 2)
    by (unfold gamma, Cmul, RtoC, Comega; simpl; field).
  assert (Hgim : snd gamma = beta * sqrt 3 / 2)
    by (unfold gamma, Cmul, RtoC, Comega; simpl; field).
  clearbody gamma.
  set (rhoC := Cadd (RtoC c0) (Cadd (Cmul (RtoC c1) gamma) (Cmul (RtoC c2) (Cmul gamma gamma)))).
  assert (HfC0 : fC B1 B2 B3 rhoC = C0).
  { assert (Hred : fC B1 B2 B3 rhoC
        = Cadd (RtoC A0) (Cadd (Cmul (RtoC A1) gamma) (Cmul (RtoC A2) (Cmul gamma gamma)))).
    { assert (Hb3C : Cmul gamma (Cmul gamma gamma) = RtoC a)
        by (rewrite <- Hg3; unfold Ccube; ring).
      unfold fC, rhoC, A0, A1, A2, Ccube.
      rewrite ?RtoC_add, ?RtoC_mul, ?RtoC_add, ?RtoC_mul, ?RtoC_add, ?RtoC_mul.
      replace (RtoC a) with (Cmul gamma (Cmul gamma gamma)) by (exact Hb3C).
      replace (RtoC 2) with (Cadd C1 C1)
        by (unfold RtoC, C1, Cadd; simpl; f_equal; ring).
      replace (RtoC 3) with (Cadd C1 (Cadd C1 C1))
        by (unfold RtoC, C1, Cadd; simpl; f_equal; ring).
      replace (RtoC 6) with (Cadd (Cadd C1 (Cadd C1 C1)) (Cadd C1 (Cadd C1 C1)))
        by (unfold RtoC, C1, Cadd; simpl; f_equal; ring).
      ring. }
    rewrite Hred, HA0, HA1, HA2.
    apply injective_projections; simpl; ring. }
  pose proof (Hreal rhoC HfC0) as HImg.
  assert (HCim : Cim rhoC = sqrt 3 / 2 * (c1*beta - c2*beta^2)).
  { unfold rhoC, Cim, Cadd, Cmul, RtoC; simpl; rewrite Hgre, Hgim; field. }
  rewrite HCim in HImg.
  assert (Hdiff : c1*beta - c2*beta^2 = 0).
  { assert (Hs3 : sqrt 3 <> 0) by (apply Rgt_not_eq; apply sqrt_lt_R0; lra).
    apply Rmult_integral in HImg. destruct HImg as [Hc | Hc]; [| exact Hc].
    exfalso. apply Hs3. lra. }
  assert (HFc : Forall F (0 :: c1 :: (- c2) :: nil)) by (repeat constructor; sfclose).
  assert (Hlen3' : length (0 :: c1 :: (- c2) :: nil) = length (powers beta 3))
    by (rewrite powers_length; reflexivity).
  assert (HFcomb2 : Fcomb (0 :: c1 :: (- c2) :: nil) (powers beta 3) = 0).
  { transitivity (0*1 + c1*beta + (- c2)*beta^2); [simpl; ring |].
    replace (0*1 + c1*beta + (- c2)*beta^2) with (c1*beta - c2*beta^2) by ring. exact Hdiff. }
  pose proof (Hindep (0::c1::(-c2)::nil) Hlen3' HFc HFcomb2) as Hzero.
  pose proof (Forall_inv (Forall_inv_tail Hzero)) as Hc1z.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail Hzero))) as Hnc2.
  split; [exact Hc1z | lra].
Qed.

(** Square-root obstruction.  A real square-root extension F(beta), beta^2 = d,
    cannot contain a root of an F-irreducible cubic: the candidate root and its
    square already lie in the 2-dimensional space spanned by 1 and beta, so
    1, rho, rho^2 are F-dependent -- contradicting degree 3. *)
Lemma casus_sqrt_obstruction :
  forall (F : R -> Prop) (d c0 c1 beta : R),
  is_subfield F -> F d -> F c0 -> F c1 ->
  beta ^ 2 = d ->
  lin_indep F (powers (c0 + c1 * beta) 3) ->
  False.
Proof.
  intros F d c0 c1 beta HF Fd Fc0 Fc1 Hbeta2 Hindep.
  set (rho := c0 + c1 * beta).
  assert (F2 : F 2) by (replace 2 with (1+1) by ring; apply subfield_add;
    [exact HF | apply subfield_1; exact HF | apply subfield_1; exact HF]).
  assert (Hrel : (c0*c0 - c1*c1*d) * 1 + (- (2*c0)) * rho + 1 * rho^2 = 0).
  { unfold rho. replace d with (beta*beta) by (rewrite <- Hbeta2; ring). ring. }
  assert (HF3 : Forall F ((c0*c0 - c1*c1*d) :: (- (2*c0)) :: 1 :: nil)).
  { repeat (apply Forall_cons; [ sfclose | ]). apply Forall_nil. }
  assert (Hlen : length ((c0*c0 - c1*c1*d) :: (- (2*c0)) :: 1 :: nil) = length (powers rho 3))
    by (rewrite powers_length; reflexivity).
  assert (Hcomb : Fcomb ((c0*c0 - c1*c1*d) :: (- (2*c0)) :: 1 :: nil) (powers rho 3) = 0).
  { transitivity ((c0*c0 - c1*c1*d) * 1 + (- (2*c0)) * rho + 1 * rho^2);
      [simpl; ring | exact Hrel]. }
  pose proof (Hindep _ Hlen HF3 Hcomb) as Hzero.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail Hzero))) as H1.
  lra.
Qed.

(** Real cube roots are unique: x^3 = y^3 forces x = y over R. *)
Lemma cube_inj : forall x y : R, x ^ 3 = y ^ 3 -> x = y.
Proof.
  intros x y H.
  destruct (Req_dec x y) as [He|Hne]; [exact He | exfalso].
  assert (Hfac : (x - y) * (x^2 + x*y + y^2) = 0).
  { replace ((x - y) * (x^2 + x*y + y^2)) with (x^3 - y^3) by ring.
    rewrite H. ring. }
  apply Rmult_integral in Hfac. destruct Hfac as [Hxy|Hq].
  - apply Hne. lra.
  - assert (Hsos : (x + y/2)^2 + 3/4*y^2 = 0)
      by (replace ((x + y/2)^2 + 3/4*y^2) with (x^2 + x*y + y^2) by field; exact Hq).
    assert (H1 : 0 <= (x + y/2)^2) by nra.
    assert (H2 : 0 <= y^2) by nra.
    assert (Hy2 : y ^ 2 = 0) by nra.
    assert (Hy0 : y = 0) by nra.
    assert (Hx0 : x = 0) by nra.
    apply Hne; lra.
Qed.

(** Independence of 1, beta, beta^2 over F for a real cube root beta not in F.
    The cube analog of lin_indep_sqrt: a nontrivial F-relation among 1, beta,
    beta^2 would place beta itself in F. *)
Lemma lin_indep_cube : forall (F : R -> Prop) (a beta : R),
  is_subfield F -> F a -> beta ^ 3 = a -> ~ F beta ->
  lin_indep F (powers beta 3).
Proof.
  intros F a beta HF Fa Hbeta Hnotin ks Hlen HFks Hcomb.
  rewrite powers_length in Hlen.
  destruct ks as [|k0 [|k1 [|k2 [|k3 ks']]]]; try discriminate Hlen.
  pose proof (Forall_inv HFks) as Fk0.
  pose proof (Forall_inv (Forall_inv_tail HFks)) as Fk1.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HFks))) as Fk2.
  assert (Hrel : k0 + k1 * beta + k2 * beta ^ 2 = 0)
    by (transitivity (Fcomb (k0::k1::k2::nil) (powers beta 3));
        [simpl; ring | exact Hcomb]).
  assert (Hrel' : k0 * beta + k1 * beta ^ 2 + k2 * a = 0).
  { transitivity (beta * (k0 + k1 * beta + k2 * beta ^ 2));
      [ rewrite <- Hbeta; ring | rewrite Hrel; ring ]. }
  assert (Hk2 : k2 = 0).
  { destruct (Req_dec k2 0) as [H0|Hk2ne]; [exact H0 | exfalso].
    set (N := k1 * k1 - k0 * k2).
    assert (HNbeta : N * beta = a * k2 ^ 2 - k1 * k0).
    { unfold N.
      transitivity (k1 * (k0 + k1*beta + k2*beta^2)
                    - k2 * (k0*beta + k1*beta^2 + k2*a) - k1*k0 + k2^2*a);
        [ ring | rewrite Hrel, Hrel'; ring ]. }
    destruct (Req_dec N 0) as [HN0|HNne].
    - apply Hnotin.
      assert (Hkk : k1 * k1 = k0 * k2) by (unfold N in HN0; lra).
      assert (Hac : a * k2 ^ 2 = k1 * k0) by (rewrite HN0 in HNbeta; lra).
      assert (Hak : a * k2 ^ 3 = k1 ^ 3).
      { replace (a * k2 ^ 3) with (a * k2 ^ 2 * k2) by ring.
        rewrite Hac. replace (k1 * k0 * k2) with (k1 * (k0 * k2)) by ring.
        rewrite <- Hkk. ring. }
      assert (Hcube : beta ^ 3 = (k1 / k2) ^ 3).
      { rewrite Hbeta. apply (Rmult_eq_reg_r (k2 ^ 3));
          [| apply pow_nonzero; exact Hk2ne].
        rewrite Hak. field. exact Hk2ne. }
      apply cube_inj in Hcube. rewrite Hcube.
      apply subfield_div; auto.
    - apply Hnotin.
      assert (Hbe : beta = (a * k2 ^ 2 - k1 * k0) / N).
      { apply (Rmult_eq_reg_l N); [| exact HNne].
        rewrite HNbeta. field. exact HNne. }
      rewrite Hbe. apply subfield_div; [exact HF | | unfold N; sfclose | exact HNne].
      replace (k2 ^ 2) with (k2 * k2) by ring. sfclose. }
  subst k2.
  assert (Hrel2 : k0 + k1 * beta = 0)
    by (replace (k0 + k1*beta) with (k0 + k1*beta + 0*beta^2) by ring; exact Hrel).
  assert (Hk1 : k1 = 0).
  { destruct (Req_dec k1 0) as [H0|Hk1ne]; [exact H0 | exfalso].
    apply Hnotin.
    assert (Hbe : beta = (- k0) / k1).
    { apply (Rmult_eq_reg_r k1); [| exact Hk1ne].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by exact Hk1ne.
      rewrite Rmult_1_r. rewrite Rmult_comm. lra. }
    rewrite Hbe. apply subfield_div; [exact HF | apply subfield_opp; auto | auto | auto]. }
  subst k1.
  assert (Hk0 : k0 = 0) by lra.
  subst k0.
  repeat constructor.
Qed.

(** The cube extension F(beta), beta^3 = a in F: the F-span of 1, beta, beta^2. *)
Definition CF (F : R -> Prop) (beta : R) (x : R) : Prop :=
  exists c0 c1 c2, F c0 /\ F c1 /\ F c2 /\ x = c0 + c1 * beta + c2 * beta ^ 2.

Lemma CF_contains : forall F beta x, is_subfield F -> F x -> CF F beta x.
Proof.
  intros F beta x HF Hx. exists x, 0, 0.
  repeat split; [exact Hx | apply subfield_0; auto | apply subfield_0; auto | ring].
Qed.

Lemma CF_self : forall F beta, is_subfield F -> CF F beta beta.
Proof.
  intros F beta HF. exists 0, 1, 0.
  repeat split; [apply subfield_0; auto | apply subfield_1; auto | apply subfield_0; auto | ring].
Qed.

(** F(beta) is a subfield when beta is a real cube root not already in F.
    Sum/difference/product are span-closed (product reduced via beta^3 = a);
    the inverse uses the norm N = c0^3 + a c1^3 + a^2 c2^3 - 3 a c0 c1 c2, whose
    nonvanishing for a nonzero element follows from independence of 1, beta,
    beta^2 (a vanishing norm-cofactor would make a a cube in F, i.e. beta in F). *)
Lemma CF_subfield : forall F beta a,
  is_subfield F -> F a -> beta ^ 3 = a -> ~ F beta -> is_subfield (CF F beta).
Proof.
  intros F beta a HF Fa Hbeta Hnotin.
  pose proof (lin_indep_cube F a beta HF Fa Hbeta Hnotin) as Hindep.
  assert (F3 : F 3) by (apply subfield_3; auto).
  repeat split.
  - apply CF_contains; [exact HF | apply subfield_0; auto].
  - apply CF_contains; [exact HF | apply subfield_1; auto].
  - intros x y [a0[a1[a2[Ha0[Ha1[Ha2 Hx]]]]]] [b0[b1[b2[Hb0[Hb1[Hb2 Hy]]]]]].
    exists (a0+b0), (a1+b1), (a2+b2).
    repeat split; [sfclose | sfclose | sfclose | subst; ring].
  - intros x y [a0[a1[a2[Ha0[Ha1[Ha2 Hx]]]]]] [b0[b1[b2[Hb0[Hb1[Hb2 Hy]]]]]].
    exists (a0-b0), (a1-b1), (a2-b2).
    repeat split; [sfclose | sfclose | sfclose | subst; ring].
  - intros x y [a0[a1[a2[Ha0[Ha1[Ha2 Hx]]]]]] [b0[b1[b2[Hb0[Hb1[Hb2 Hy]]]]]].
    exists (a0*b0 + a*(a1*b2 + a2*b1)),
           (a0*b1 + a1*b0 + a*(a2*b2)),
           (a0*b2 + a1*b1 + a2*b0).
    repeat split; [sfclose | sfclose | sfclose |].
    subst x y. replace a with (beta^3) by (exact Hbeta). ring.
  - intros x [c0[c1[c2[Fc0[Fc1[Fc2 Hx]]]]]] Hxne.
    set (N := c0*c0*c0 + a*(c1*c1*c1) + a*a*(c2*c2*c2) - 3*(a*c0*c1*c2)).
    set (m0 := c0*c0 - a*c1*c2).
    set (m1 := a*(c2*c2) - c0*c1).
    set (m2 := c1*c1 - c0*c2).
    assert (FN : F N) by (unfold N; sfclose).
    assert (Fm0 : F m0) by (unfold m0; sfclose).
    assert (Fm1 : F m1) by (unfold m1; sfclose).
    assert (Fm2 : F m2) by (unfold m2; sfclose).
    assert (Hgm : x * (m0 + m1*beta + m2*beta^2) = N).
    { rewrite Hx. unfold N, m0, m1, m2.
      replace a with (beta^3) by (exact Hbeta). ring. }
    assert (HNne : N <> 0).
    { intro HN0. rewrite HN0 in Hgm.
      apply Rmult_integral in Hgm. destruct Hgm as [Hc|HM].
      - apply Hxne; exact Hc.
      - assert (Hlen : length (m0::m1::m2::nil) = length (powers beta 3))
          by (rewrite powers_length; reflexivity).
        assert (HFm : Forall F (m0::m1::m2::nil))
          by (constructor; [exact Fm0 | constructor; [exact Fm1 | constructor; [exact Fm2 | constructor]]]).
        assert (Hcomb : Fcomb (m0::m1::m2::nil) (powers beta 3) = 0)
          by (transitivity (m0 + m1*beta + m2*beta^2); [simpl; ring | exact HM]).
        pose proof (Hindep _ Hlen HFm Hcomb) as HZ.
        assert (Hm0z : m0 = 0) by exact (Forall_inv HZ).
        assert (Hm1z : m1 = 0) by exact (Forall_inv (Forall_inv_tail HZ)).
        assert (Hm2z : m2 = 0) by exact (Forall_inv (Forall_inv_tail (Forall_inv_tail HZ))).
        destruct (Req_dec c2 0) as [Hc2z|Hc2ne].
        + subst c2.
          assert (Hc1z : c1 = 0) by (unfold m2 in Hm2z; nra).
          assert (Hc0z : c0 = 0) by (unfold m0 in Hm0z; nra).
          apply Hxne. rewrite Hx. subst c0 c1. ring.
        + apply Hnotin.
          assert (Hm1' : a*(c2*c2) = c0*c1) by (unfold m1 in Hm1z; lra).
          assert (Hm2' : c0*c2 = c1*c1) by (unfold m2 in Hm2z; lra).
          assert (Hac : a * c2^3 = c1^3).
          { replace (a*c2^3) with (a*(c2*c2)*c2) by ring.
            rewrite Hm1'. replace (c0*c1*c2) with (c1*(c0*c2)) by ring.
            rewrite Hm2'. ring. }
          assert (Hcube : beta^3 = (c1/c2)^3).
          { rewrite Hbeta. apply (Rmult_eq_reg_r (c2^3));
              [| apply pow_nonzero; exact Hc2ne].
            rewrite Hac. field. exact Hc2ne. }
          apply cube_inj in Hcube. rewrite Hcube.
          apply subfield_div; auto. }
    exists (m0/N), (m1/N), (m2/N).
    repeat split.
    + apply subfield_div; auto.
    + apply subfield_div; auto.
    + apply subfield_div; auto.
    + apply (Rmult_eq_reg_l x); [| exact Hxne].
      rewrite Rinv_r by exact Hxne.
      replace (x * (m0/N + m1/N*beta + m2/N*beta^2))
        with ((x * (m0 + m1*beta + m2*beta^2)) / N) by (field; exact HNne).
      rewrite Hgm. field. exact HNne.
Qed.

(** Cube-step descent.  If a root of a monic cubic with three real roots and
    coefficients in F lies in the cube extension F(beta) (beta a real cube root
    not in F), then a root already lies in F.  This is the casus-irreducibilis
    obstruction in descent form: casus_cube_heart forces the beta- and
    beta^2-components of the root to vanish, so the root is its own F-part. *)
Lemma cube_conj_vieta_step : forall (F : R -> Prop) (B1 B2 B3 beta a p q r : R),
  is_subfield F -> F a -> F B1 -> F B2 -> F B3 -> F p -> F q -> F r ->
  beta ^ 3 = a -> ~ F beta ->
  (forall z : C, fC B1 B2 B3 z = C0 -> Cim z = 0) ->
  (p + q*beta + r*beta^2) ^ 3 + B1 * (p + q*beta + r*beta^2) ^ 2
    + B2 * (p + q*beta + r*beta^2) + B3 = 0 ->
  exists w, F w /\ w ^ 3 + B1 * w ^ 2 + B2 * w + B3 = 0.
Proof.
  intros F B1 B2 B3 beta a p q r HF Fa FB1 FB2 FB3 Fp Fq Fr Hbeta Hnotin Hreal Hroot.
  pose proof (lin_indep_cube F a beta HF Fa Hbeta Hnotin) as Hindep.
  pose proof (casus_cube_heart F a p q r B1 B2 B3 beta
                HF Fa Fp Fq Fr FB1 FB2 FB3 Hbeta Hindep Hreal Hroot) as [Hq0 Hr0].
  exists p. split; [exact Fp|].
  rewrite <- Hroot. rewrite Hq0, Hr0. ring.
Qed.

(** A real square+cube-root tower over Q: subfields reachable from the rationals
    by adjoining real square roots (QF, quadratic extension) and real cube roots
    (CF, cubic extension), each a genuine extension (the radicand's root not
    already present). *)
Inductive RRTower : (R -> Prop) -> Prop :=
| RRT_base : RRTower is_rational
| RRT_sqrt : forall (F : R -> Prop) (s : R),
    RRTower F -> F (s * s) -> ~ F s -> RRTower (QF F s)
| RRT_cube : forall (F : R -> Prop) (beta a : R),
    RRTower F -> F a -> beta ^ 3 = a -> ~ F beta -> RRTower (CF F beta).

Lemma RRTower_subfield : forall F, RRTower F -> is_subfield F.
Proof.
  intros F HT. induction HT.
  - apply is_rational_subfield.
  - apply QF_subfield; [exact IHHT | exact H].
  - apply (CF_subfield F beta a); [exact IHHT | exact H | exact H0 | exact H1].
Qed.

(** Casus irreducibilis for real square+cube-root towers.  A monic cubic with
    rational coefficients, three real roots (every complex root is real), and no
    rational root -- i.e. irreducible over Q -- has no root in ANY real
    square+cube-root tower over Q.  Cardano's formula solves it over C with
    complex cube roots; this is the impossibility of doing so with real radicals,
    the exact counterpart to origami solving every cubic. *)
Theorem casus_irreducibilis_tower :
  forall (B1 B2 B3 : R),
  is_rational B1 -> is_rational B2 -> is_rational B3 ->
  (forall z : C, fC B1 B2 B3 z = C0 -> Cim z = 0) ->
  (forall x, is_rational x -> x ^ 3 + B1 * x ^ 2 + B2 * x + B3 <> 0) ->
  forall (F : R -> Prop), RRTower F ->
  forall w, F w -> w ^ 3 + B1 * w ^ 2 + B2 * w + B3 <> 0.
Proof.
  intros B1 B2 B3 QB1 QB2 QB3 Hreal Hnorat F HT.
  assert (Hmain : is_subfield F /\
                  (forall w, F w -> w ^ 3 + B1 * w ^ 2 + B2 * w + B3 <> 0)).
  { induction HT.
    - split; [apply is_rational_subfield | exact Hnorat].
    - destruct IHHT as [HFsub IHroot]. split.
      + apply QF_subfield; [exact HFsub | exact H].
      + intros w [p [q [Fp [Fq Hw]]]] Hroot.
        assert (FB1 : F B1) by (apply subfield_contains_rational; [exact HFsub | exact QB1]).
        assert (FB2 : F B2) by (apply subfield_contains_rational; [exact HFsub | exact QB2]).
        assert (FB3 : F B3) by (apply subfield_contains_rational; [exact HFsub | exact QB3]).
        destruct (Req_dec q 0) as [Hq0|Hqne].
        * assert (Hwp : w = p) by (rewrite Hw, Hq0; ring).
          apply (IHroot p Fp). rewrite <- Hwp. exact Hroot.
        * assert (Hcub : (p+q*s)*(p+q*s)*(p+q*s) + B1*((p+q*s)*(p+q*s))
                         + B2*(p+q*s) + B3 = 0).
          { rewrite Hw in Hroot. rewrite <- Hroot. ring. }
          destruct (cubic_conj_vieta_step F B3 B2 B1 s p q
                      HFsub H FB3 FB2 FB1 Fp Fq H0 Hqne Hcub) as [w' [Fw' Hw'root]].
          apply (IHroot w' Fw'). rewrite <- Hw'root. ring.
    - destruct IHHT as [HFsub IHroot]. split.
      + apply (CF_subfield F beta a); [exact HFsub | exact H | exact H0 | exact H1].
      + intros w [p [q [r [Fp [Fq [Fr Hw]]]]]] Hroot.
        assert (FB1 : F B1) by (apply subfield_contains_rational; [exact HFsub | exact QB1]).
        assert (FB2 : F B2) by (apply subfield_contains_rational; [exact HFsub | exact QB2]).
        assert (FB3 : F B3) by (apply subfield_contains_rational; [exact HFsub | exact QB3]).
        assert (Hcub : (p+q*beta+r*beta^2) ^ 3 + B1*(p+q*beta+r*beta^2) ^ 2
                       + B2*(p+q*beta+r*beta^2) + B3 = 0)
          by (rewrite Hw in Hroot; exact Hroot).
        destruct (cube_conj_vieta_step F B1 B2 B3 beta a p q r
                    HFsub H FB1 FB2 FB3 Fp Fq Fr H0 H1 Hreal Hcub) as [w' [Fw' Hw'root]].
        exact (IHroot w' Fw' Hw'root). }
  destruct Hmain as [_ Hroot]. exact Hroot.
Qed.

Lemma RtoC_opp : forall x, RtoC (- x) = Copp (RtoC x).
Proof. intros x. unfold RtoC, Copp. simpl. f_equal. ring. Qed.

(** A real cubic that splits into three real linear factors has only real
    complex roots.  This discharges the three-real-roots hypothesis of
    casus_irreducibilis_tower whenever the cubic is presented by its real roots
    r1, r2, r3 (its coefficients being the elementary symmetric functions). *)
Lemma all_roots_real_of_split : forall (r1 r2 r3 : R) (z : C),
  fC (-(r1+r2+r3)) (r1*r2 + r1*r3 + r2*r3) (-(r1*r2*r3)) z = C0 ->
  Cim z = 0.
Proof.
  intros r1 r2 r3 z Hz.
  assert (Hfac : fC (-(r1+r2+r3)) (r1*r2 + r1*r3 + r2*r3) (-(r1*r2*r3)) z
    = Cmul (Cmul (Csub z (RtoC r1)) (Csub z (RtoC r2))) (Csub z (RtoC r3))).
  { unfold fC, Ccube.
    rewrite ?RtoC_opp, ?RtoC_add, ?RtoC_mul, ?RtoC_add, ?RtoC_mul.
    ring. }
  rewrite Hfac in Hz.
  apply Cmul_integral in Hz. destruct Hz as [Hz12 | Hz3].
  - apply Cmul_integral in Hz12. destruct Hz12 as [Hz1 | Hz2].
    + assert (Hze : z = RtoC r1)
        by (transitivity (Cadd (Csub z (RtoC r1)) (RtoC r1)); [ring | rewrite Hz1; ring]).
      rewrite Hze; reflexivity.
    + assert (Hze : z = RtoC r2)
        by (transitivity (Cadd (Csub z (RtoC r2)) (RtoC r2)); [ring | rewrite Hz2; ring]).
      rewrite Hze; reflexivity.
  - assert (Hze : z = RtoC r3)
      by (transitivity (Cadd (Csub z (RtoC r3)) (RtoC r3)); [ring | rewrite Hz3; ring]).
    rewrite Hze; reflexivity.
Qed.

(** Casus irreducibilis presented by the three real roots.  If three reals have
    rational elementary symmetric functions and none of them (nor any rational)
    is a root -- the cubic is irreducible over Q -- then no root lies in any real
    square+cube-root tower over Q. *)
Corollary casus_irreducibilis_split :
  forall (r1 r2 r3 : R),
  is_rational (-(r1+r2+r3)) ->
  is_rational (r1*r2 + r1*r3 + r2*r3) ->
  is_rational (-(r1*r2*r3)) ->
  (forall x, is_rational x ->
     x ^ 3 + (-(r1+r2+r3)) * x ^ 2 + (r1*r2 + r1*r3 + r2*r3) * x + (-(r1*r2*r3)) <> 0) ->
  forall F, RRTower F ->
  forall w, F w ->
    w ^ 3 + (-(r1+r2+r3)) * w ^ 2 + (r1*r2 + r1*r3 + r2*r3) * w + (-(r1*r2*r3)) <> 0.
Proof.
  intros r1 r2 r3 Q1 Q2 Q3 Hnorat F HT w Hw.
  apply (casus_irreducibilis_tower _ _ _ Q1 Q2 Q3
           (all_roots_real_of_split r1 r2 r3) Hnorat F HT w Hw).
Qed.

(** A concrete witness: x^3 - 3x + 1 (the nonagon cubic, with roots 2cos(2 pi k/9))
    has three real roots and no rational root, so none of its roots lies in any
    real square+cube-root tower over Q.  Two roots come from the intermediate
    value theorem; Vieta pins the third, giving the three-real-roots hypothesis
    via all_roots_real_of_split, and the dev's rational-root theorem
    (cubic_no_rat_root_of_int, nonagon_check) supplies irreducibility over Q. *)
Theorem nonagon_cubic_not_in_real_radical_tower :
  forall F, RRTower F -> forall w, F w -> w ^ 3 + 0 * w ^ 2 + (-3) * w + 1 <> 0.
Proof.
  destruct (IVT_root_exists (-3) 1 (-2) (-1) ltac:(lra)
              ltac:(unfold depressed_cubic_alt, cube_func; nra)
              ltac:(unfold depressed_cubic_alt, cube_func; nra))
    as [r1 [Hr1b Hr1eq]].
  destruct (IVT_root_exists (-3) 1 1 2 ltac:(lra)
              ltac:(unfold depressed_cubic_alt, cube_func; nra)
              ltac:(unfold depressed_cubic_alt, cube_func; nra))
    as [r3 [Hr3b Hr3eq]].
  assert (Hr1 : r1 ^ 3 - 3*r1 + 1 = 0) by (unfold depressed_cubic in Hr1eq; lra).
  assert (Hr3 : r3 ^ 3 - 3*r3 + 1 = 0) by (unfold depressed_cubic in Hr3eq; lra).
  assert (Hne : r1 <> r3) by lra.
  assert (HV2 : r1 ^ 2 + r1*r3 + r3 ^ 2 = 3).
  { assert (H : (r1 - r3) * (r1 ^ 2 + r1*r3 + r3 ^ 2 - 3) = 0).
    { replace ((r1 - r3) * (r1 ^ 2 + r1*r3 + r3 ^ 2 - 3))
        with ((r1 ^ 3 - 3*r1 + 1) - (r3 ^ 3 - 3*r3 + 1)) by ring.
      rewrite Hr1, Hr3. ring. }
    apply Rmult_integral in H. destruct H as [Hc|Hc]; [exfalso; apply Hne; lra | lra]. }
  assert (HS3 : r1*r3*(r1 + r3) = 1) by nra.
  assert (Hallreal : forall z : C, fC 0 (-3) 1 z = C0 -> Cim z = 0).
  { assert (Hc1 : -(r1 + r3 + -(r1+r3)) = 0) by ring.
    assert (Hc2 : r1*r3 + r1*(-(r1+r3)) + r3*(-(r1+r3)) = -3) by nra.
    assert (Hc3 : -(r1*r3*(-(r1+r3))) = 1) by nra.
    pose proof (all_roots_real_of_split r1 r3 (-(r1+r3))) as Hars.
    rewrite Hc1, Hc2, Hc3 in Hars. exact Hars. }
  assert (Hnorat : forall x, is_rational x -> x ^ 3 + 0*x ^ 2 + (-3)*x + 1 <> 0).
  { intros x Hx Heq.
    assert (Heq' : x*x*x + IZR 0*(x*x) + IZR (-3)*x + IZR 1 = 0).
    { replace (IZR 0) with 0 by (simpl; ring).
      replace (IZR (-3)) with (-3) by (simpl; ring).
      replace (IZR 1) with 1 by (simpl; ring).
      replace (x*x*x + 0*(x*x) + (-3)*x + 1) with (x ^ 3 + 0*x ^ 2 + (-3)*x + 1) by ring.
      exact Heq. }
    exact (cubic_no_rat_root_of_int 1 (-3) 0 nonagon_check x Hx Heq'). }
  assert (Q0 : is_rational 0) by (replace 0 with (IZR 0) by (simpl; ring); apply is_rational_IZR).
  assert (Q2 : is_rational (-3)) by (replace (-3) with (IZR (-3)) by (simpl; ring); apply is_rational_IZR).
  assert (Q3 : is_rational 1) by apply is_rational_1.
  exact (casus_irreducibilis_tower 0 (-3) 1 Q0 Q2 Q3 Hallreal Hnorat).
Qed.
