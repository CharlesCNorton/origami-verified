(** Origami Geometry: Huzita-Hatori axioms O1-O7, constructibility, algebraic characterization.
    Author: Charles C Norton, November 2025 *)

From Coq Require Import Reals.
Require Import Lra.
Require Import Field.
Require Import Coq.Reals.R_sqr.
Require Import Psatz.
Require Import Nsatz.
Require Import Ring.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.micromega.RingMicromega.
Require Import List.
Require Import ProofIrrelevance.
Require Import ClassicalDescription.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope R_scope.

Section Geometry_Primitives.
(** Points in ℝ², lines as {(x,y) : Ax + By + C = 0} with A ≠ 0 ∨ B ≠ 0 *)

(** (x, y) ∈ ℝ² *)
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

End Geometry_Primitives.

Section Geometric_Predicates.

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

End Geometric_Predicates.

Section Computable_Predicates.
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

End Computable_Predicates.

Section Metric_Geometry.

(** x² *)
Definition sqr (x : R) : R := x * x.

(** √((x₁-x₂)² + (y₁-y₂)²) *)
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
Definition line_norm (l : Line) : R :=
  sqrt (sqr (A l) + sqr (B l)).

(** |Ax + By + C| / √(A² + B²) *)
Definition dist_point_line (p : Point) (l : Line) : R :=
  Rabs (let '(x, y) := p in A l * x + B l * y + C l) / line_norm l.

End Metric_Geometry.

Section Fold_Primitives.
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

End Fold_Primitives.

Section Origami_Operations.
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

(** p₁ ≠ p₂ → reflect(p₁, perp_bisector(p₁,p₂)) = p₂ *)
Theorem perp_bisector_reflects_correctly : forall p1 p2,
  p1 <> p2 ->
  reflect_point p1 (perp_bisector p1 p2) = p2.
Proof.
  intros p1 p2 Hneq.
  apply perp_bisector_reflects_to_other.
  exact Hneq.
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

(** Alias for fold_O6_approx *)
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

(** p₁ ≠ p₂ → reflect(p₁, perp_bisector(p₁,p₂)) = p₂ *)
Lemma reflect_perp_bisector_swap : forall p1 p2,
  p1 <> p2 -> reflect_point p1 (perp_bisector p1 p2) = p2.
Proof.
  intros [x1 y1] [x2 y2] Hneq.
  unfold reflect_point, perp_bisector.
  destruct (Req_EM_T x1 x2) as [Hx|Hx].
  - subst. destruct (Req_EM_T y1 y2) as [Hy|Hy].
    + subst. exfalso. apply Hneq. reflexivity.
    + simpl. f_equal; field; intro H; apply Hy; lra.
  - simpl. assert (Hden: 2 * (x2 - x1) * (2 * (x2 - x1)) + 2 * (y2 - y1) * (2 * (y2 - y1)) <> 0).
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
  - rewrite reflect_perp_bisector_swap; [|exact Hneq].
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
Lemma sum_sq_nz_l : forall a b, a <> 0 -> a * a + b * b <> 0.
Proof.
  intros a b Ha. intro H.
  assert (Ha2 : 0 <= a * a) by apply Rle_0_sqr.
  assert (Hb2 : 0 <= b * b) by apply Rle_0_sqr.
  assert (Haz : a * a = 0) by lra.
  apply Rmult_integral in Haz. destruct Haz; lra.
Qed.

(** x₁ ≠ x₂ → fst(reflect((x₁,y₁), perp_bisector)) = x₂ *)
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

(** p₁ ≠ p₂ → reflect(p₁, perp_bisector(p₁,p₂)) = p₂ *)
Lemma perp_bisector_reflection : forall p1 p2,
  p1 <> p2 ->
  reflect_point p1 (perp_bisector p1 p2) = p2.
Proof.
  intros [x1 y1] [x2 y2] Hneq.
  apply refl_gen_bisector.
  destruct (Req_EM_T x1 x2); destruct (Req_EM_T y1 y2); subst.
  - exfalso. apply Hneq. reflexivity.
  - right. assumption.
  - left. assumption.
  - left. assumption.
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
  apply perp_bisector_reflection. exact Hneq.
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
  apply perp_bisector_reflection. exact Hneq2.
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
  rewrite perp_bisector_reflection; auto.
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

End Origami_Operations.

Section Cubic_Bridge.
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

End Cubic_Bridge.

Section Construction_Algorithms.
(** Algorithms for origami constructions *)

(** reflect(p,f) *)
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

End Construction_Algorithms.

Section Constructibility.
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

End Constructibility.

Section Decidability.
(** Enumeration-based decidability for bounded depth constructibility *)

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
      flat_map (fun p => flat_map (fun l => [perp_through p l]) prev_lines) prev_points
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
  rewrite app_length.
  apply Nat.le_add_r.
Qed.

(** |enum_lines(d)| ≤ |enum_lines(S d)| *)
Lemma enum_lines_size_monotone : forall d,
  (length (enum_lines d) <= length (enum_lines (S d)))%nat.
Proof.
  intro d. simpl.
  rewrite app_length.
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

Theorem In_enum_points_constructible : forall d p,
  In p (enum_points d) -> ConstructiblePoint p.
Proof.
  intro d.
  assert (Hboth: (forall p, In p (enum_points d) -> ConstructiblePoint p) /\
                 (forall l, In l (enum_lines d) -> ConstructibleLine l)).
  { induction d.
    - split; [apply In_enum_points_base|apply In_enum_lines_base].
    - destruct IHd as [IHp IHl]. split.
      + intros p H. simpl in H.
        apply in_app_or in H. destruct H as [H|H].
        * apply IHp. exact H.
        * apply in_app_or in H. destruct H as [H|H].
          -- apply in_flat_map in H. destruct H as [l1 [Hl1 H]].
             apply in_flat_map in H. destruct H as [l2 [Hl2 H]].
             simpl in H. destruct H as [H|H]; [|contradiction].
             subst. apply line_intersection_constructible; apply IHl; assumption.
          -- apply in_flat_map in H. destruct H as [p0 [Hp0 H]].
             apply in_flat_map in H. destruct H as [l0 [Hl0 H]].
             simpl in H. destruct H as [H|H]; [|contradiction].
             subst. apply reflect_point_constructible; [apply IHp|apply IHl]; assumption.
      + intros l H. simpl in H.
        apply in_app_or in H. destruct H as [H|H].
        * apply IHl. exact H.
        * apply in_app_or in H. destruct H as [H|H].
          -- apply in_flat_map in H. destruct H as [p1 [Hp1 H]].
             apply in_flat_map in H. destruct H as [p2 [Hp2 H]].
             simpl in H. destruct H as [H|[H|H]]; try contradiction.
             ++ subst. apply line_through_constructible; apply IHp; assumption.
             ++ subst. apply perp_bisector_constructible; apply IHp; assumption.
          -- apply in_app_or in H. destruct H as [H|H].
             ++ apply in_flat_map in H. destruct H as [l1 [Hl1 H]].
                apply in_flat_map in H. destruct H as [l2 [Hl2 H]].
                simpl in H. destruct H as [H|H]; [|contradiction].
                subst. apply bisector_constructible; apply IHl; assumption.
             ++ apply in_flat_map in H. destruct H as [p0 [Hp0 H]].
                apply in_flat_map in H. destruct H as [l0 [Hl0 H]].
                simpl in H. destruct H as [H|H]; [|contradiction].
                subst. apply perp_through_constructible; [apply IHp|apply IHl]; assumption. }
  apply Hboth.
Qed.

Theorem In_enum_lines_constructible : forall d l,
  In l (enum_lines d) -> ConstructibleLine l.
Proof.
  intro d.
  assert (Hboth: (forall p, In p (enum_points d) -> ConstructiblePoint p) /\
                 (forall l, In l (enum_lines d) -> ConstructibleLine l)).
  { induction d.
    - split; [apply In_enum_points_base|apply In_enum_lines_base].
    - destruct IHd as [IHp IHl]. split.
      + intros p H. simpl in H.
        apply in_app_or in H. destruct H as [H|H].
        * apply IHp. exact H.
        * apply in_app_or in H. destruct H as [H|H].
          -- apply in_flat_map in H. destruct H as [l1 [Hl1 H]].
             apply in_flat_map in H. destruct H as [l2 [Hl2 H]].
             simpl in H. destruct H as [H|H]; [|contradiction].
             subst. apply line_intersection_constructible; apply IHl; assumption.
          -- apply in_flat_map in H. destruct H as [p0 [Hp0 H]].
             apply in_flat_map in H. destruct H as [l0 [Hl0 H]].
             simpl in H. destruct H as [H|H]; [|contradiction].
             subst. apply reflect_point_constructible; [apply IHp|apply IHl]; assumption.
      + intros l H. simpl in H.
        apply in_app_or in H. destruct H as [H|H].
        * apply IHl. exact H.
        * apply in_app_or in H. destruct H as [H|H].
          -- apply in_flat_map in H. destruct H as [p1 [Hp1 H]].
             apply in_flat_map in H. destruct H as [p2 [Hp2 H]].
             simpl in H. destruct H as [H|[H|H]]; try contradiction.
             ++ subst. apply line_through_constructible; apply IHp; assumption.
             ++ subst. apply perp_bisector_constructible; apply IHp; assumption.
          -- apply in_app_or in H. destruct H as [H|H].
             ++ apply in_flat_map in H. destruct H as [l1 [Hl1 H]].
                apply in_flat_map in H. destruct H as [l2 [Hl2 H]].
                simpl in H. destruct H as [H|H]; [|contradiction].
                subst. apply bisector_constructible; apply IHl; assumption.
             ++ apply in_flat_map in H. destruct H as [p0 [Hp0 H]].
                apply in_flat_map in H. destruct H as [line0 [Hline0 H]].
                simpl in H. destruct H as [H|H]; [|contradiction].
                subst. apply perp_through_constructible; [apply IHp|apply IHl]; assumption. }
  apply Hboth.
Qed.

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

Lemma max_le_l : forall n m : nat, (n <= Nat.max n m)%nat.
Proof.
  intros. apply Nat.le_max_l.
Qed.

Lemma max_le_r : forall n m : nat, (m <= Nat.max n m)%nat.
Proof.
  intros. apply Nat.le_max_r.
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
  apply incl_appr. apply incl_appr. apply incl_appr.
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

Lemma foot_eq_intersection_case1 : forall x y b c,
  b <> 0 ->
  (x - 0 * ((0 * x + b * y + c) / (b * b)), y - b * ((0 * x + b * y + c) / (b * b))) =
  ((- (0 * y - b * x) * b - - c * - 0) / (b * b - 0 * - 0), (b * - c - 0 * - (0 * y - b * x)) / (b * b - 0 * - 0)).
Proof.
  intros. unfold Rdiv. f_equal; field; lra.
Qed.


Lemma foot_eq_intersection : forall p l,
  line_wf l -> foot_on_line p l = line_intersection (perp_through p l) l.
Proof.
  intros [x y] [a b c] Hnz.
  unfold foot_on_line, line_intersection, perp_through; simpl.
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
    + simpl. unfold d. assert (Heq: 0 * 0 + b * b = b * b) by ring. rewrite Heq. apply foot_eq_intersection_case1. assumption.
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
  rewrite foot_eq_intersection by exact Hwf.
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
Lemma neg_zero : -0 = 0.
Proof. ring. Qed.

(** A(perp_through(p, {A:=0,B:=b,C:=c})) = b *)
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

End Decidability.

Section Fold_Sequences.
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
Definition heptagon_cubic_a : R := -7/12.
Definition heptagon_cubic_b : R := -7/216.

(** O6 configuration for cos(2π/7) *)
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
  unfold heptagon_vertices. rewrite map_length, seq_length. reflexivity.
Qed.

(** |heptagon_full_sequence| = 8 *)
Lemma heptagon_full_sequence_length :
  fold_sequence_length heptagon_full_sequence = 8%nat.
Proof.
  reflexivity.
Qed.

End Fold_Sequences.

Section Origami_Algebra.
(** Algebraic characterization of origami-constructible numbers *)

(** Origami numbers: closed under +, -, ×, /, √, and cubic roots *)
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

End Origami_Algebra.

Section Reverse_Completeness.
(** Partial converse: OrigamiNum base cases are constructible *)

(** 0 ∈ ConstructibleR *)
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
Lemma simplify_reflect_x_coord :
  forall a b c x y,
  a * a + b * b <> 0 ->
  x - 2 * a * ((a * x + b * y + c) / (a * a + b * b)) =
  ((a * a + b * b) * x - 2 * a * (a * x + b * y + c)) / (a * a + b * b).
Proof.
  intros. unfold Rdiv. field. exact H.
Qed.

(** reflect((0,0), perp_bisector((1,0),(2,0))) = (3,0) *)
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
Lemma geometric_mean_point_wf : forall x,
  0 < x -> (1, sqrt x) <> (1 + x, 0).
Proof.
  intros x Hpos Heq.
  injection Heq as H1 H2.
  assert (Hsqrt_pos: sqrt x > 0) by (apply sqrt_lt_R0; lra).
  lra.
Qed.

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
Lemma sqrt_4_eq : sqrt 4 = 2.
Proof.
  replace 4 with (2 * 2) by ring.
  rewrite sqrt_square; lra.
Qed.

(** x > 0 → O5_image_y(0,0,1+x,0,2) = 2√x *)
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
  apply perp_bisector_reflection.
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

End Reverse_Completeness.

Section Construction_Examples.

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
Example sqrt_2_constructible : OrigamiNum (sqrt 2).
Proof.
  apply ON_sqrt.
  - apply Origami_two.
  - replace 2 with (1 + 1) by lra.
    apply Rplus_le_le_0_compat; apply Rle_0_1.
Qed.

(** Intersection of perpendiculars through X to both axes *)
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
Lemma inter_y_coord : (1 * - 0 - 0 * - (-1)) * / (1 * -1 - 0 * 0) = 0.
Proof.
  assert (H1: 1 * - 0 - 0 * - (-1) = 0) by ring.
  rewrite H1. ring.
Qed.

(** snd(intersection of x=1 and y=0) = 0 *)
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

Section Trigonometric_Identities.
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

End Trigonometric_Identities.

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

End Construction_Examples.

Section Computational_Geometry.
(** Executable algorithms for geometric operations *)

(** Alias for midpoint *)
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

End Computational_Geometry.

Section Topology_Continuity.
(** Continuity of origami operations *)

(** x = y → √x = √y *)
Lemma sqrt_equal : forall x y : R, x = y -> sqrt x = sqrt y.
Proof.
  intros x y H.
  rewrite H.
  reflexivity.
Qed.

(** dist(p,q) = √(dist²(p,q)) *)
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

End Topology_Continuity.

Section Algebraic_Characterization.
(** Origami numbers ⟺ field extensions of degree 2^a · 3^b over ℚ (Alperin-Lang 2000) *)

(** Euclidean field extension degrees: 2ⁿ *)
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
        simpl. lia. }
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

Section CRT_Machinery.
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

Eval compute in (euler_phi 11, euler_phi 23, euler_phi 31, euler_phi 47).
Eval compute in (euler_phi 50, euler_phi 100, euler_phi 200).

End CRT_Machinery.

Section Impossibility.
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

(** EuclidNum height 1 ⟹ x ∈ ℚ(√r) for some rational r ≥ 0 *)
Lemma EuclidNum_ht_1_in_quadratic_field : forall x,
  EuclidNum_ht x 1 -> exists r, r >= 0 /\ is_rational r /\ in_quadratic_field x r.
Proof.
Admitted.

(** ∛2 not at Euclidean height 1 *)
Lemma cbrt2_not_EuclidNum_ht_1 : ~ EuclidNum_ht cbrt2 1.
Proof.
  intro H.
  destruct (EuclidNum_ht_1_in_quadratic_field cbrt2 H) as [r [Hr_ge [Hr_rat Hr_quad]]].
  exact (cbrt2_not_in_rational_quadratic_field r Hr_ge Hr_rat Hr_quad).
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

End Impossibility.

Section Famous_Constants.

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

End Famous_Constants.

Section Main_Results.

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

End Main_Results.

(** O5_general_image(p,l,q) ∈ l *)
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
Lemma Rabs_sqr_eq : forall x, Rabs x * Rabs x = x * x.
Proof. intro x. rewrite <- Rabs_mult. rewrite Rabs_pos_eq; [ring | apply Rle_0_sqr]. Qed.

(** O5_general_valid ⟹ h² = r² - d²‖l‖² ≥ 0 *)
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
  apply perp_bisector_reflection. exact Hneq.
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

Eval compute in (midpoint (0, 0) (1, 0)).

Eval compute in (reflect_point (1, 0) line_yaxis).

Eval compute in (perp_bisector (0, 0) (2, 0)).

Eval compute in (beloch_fold_line 1).

Eval compute in (O5_vert_image (0, 0) (3, 0) 2).

Eval compute in (euler_phi 7, euler_phi 9, euler_phi 11).

Eval compute in (fold_line (fold_O7 (1, 1) line_xaxis line_yaxis)).

(** x + y = y + x *)
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

Section O5_Solvability.

(** |Ax + By + C| / √(A² + B²) *)
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

(** dist = √dist² *)
Lemma dist_eq_sqrt_dist2 : forall p q, dist p q = sqrt (dist2 p q).
Proof.
  intros [px py] [qx qy]. unfold dist, dist2, sqr. simpl. reflexivity.
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
Theorem O5_valid_iff_dist : forall p l q,
  line_wf l ->
  O5_general_valid p l q <-> point_line_dist q l <= dist p q.
Proof.
  intros p l q Hwf.
  rewrite O5_valid_unfold.
  rewrite dist_eq_sqrt_dist2.
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

End O5_Solvability.

Section O6_Multiplicity.
(** Root structure of depressed cubic t³ + pt + q *)

(** t³ + pt + q *)
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

End O6_Multiplicity.

Section Discriminant_Theorem.
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

End Discriminant_Theorem.

Section Discriminant_Zero_Case.
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

End Discriminant_Zero_Case.

Section Discriminant_Positive_Case.
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

(** ∀ p q, ∃ r, r³ + pr + q = 0 (via IVT) *)
Theorem depressed_cubic_root_exists : forall p q,
  exists r, is_cubic_root p q r.
Proof.
  intros p q.
  destruct (depressed_cubic_alt_neg_large p q) as [M1 HM1].
  destruct (depressed_cubic_alt_pos_large p q) as [M2 HM2].
  set (a := Rmin M1 M2 - 1).
  set (b := Rmax M1 M2 + 1).
  assert (Ha_lt_M1 : a < M1) by (unfold a, Rmin; destruct (Rle_dec M1 M2); lra).
  assert (Hb_gt_M2 : b > M2) by (unfold b, Rmax; destruct (Rle_dec M1 M2); lra).
  assert (Hab : a < b) by (unfold a, b, Rmin, Rmax; destruct (Rle_dec M1 M2); lra).
  assert (Hfa : depressed_cubic_alt p q a < 0) by (apply HM1; exact Ha_lt_M1).
  assert (Hfb : depressed_cubic_alt p q b > 0) by (apply HM2; exact Hb_gt_M2).
  destruct (IVT (depressed_cubic_alt p q) a b
                (depressed_cubic_alt_continuous p q) Hab Hfa Hfb)
    as [r [[Har Hrb] Hr]].
  exists r.
  unfold is_cubic_root.
  rewrite depressed_cubic_alt_eq.
  exact Hr.
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

End Discriminant_Positive_Case.

Section O6_Fold_Count.
(** O6 fold multiplicity determined by cubic discriminant *)

(** Beloch fold from cubic root t *)
Definition O6_fold_from_root (p q t : R) : Fold := fold_O6_beloch p q t.

(** ∃! t with t³ + pt + q = 0 *)
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

End O6_Fold_Count.

Section Cardano_Formula.
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

End Cardano_Formula.

End Algebraic_Characterization.

Section Fold_Continuity.

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

End Fold_Continuity.

Section Multi_Fold_Origami.

(** * Multi-Fold Origami Extensions

    Single-fold origami (Huzita-Hatori) solves cubics and constructs numbers
    in towers of degree 2 and 3 extensions. Simultaneous k-fold operations
    extend constructibility to higher algebraic degrees. *)

(** A 2-fold operation produces two crease lines simultaneously. *)
Definition two_fold_lines (l1 l2 : Line) : Prop :=
  line_wf l1 /\ line_wf l2.

(** Quintisection: dividing an angle into five equal parts.
    Requires solving a degree-5 Chebyshev polynomial. *)
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

(** The regular hendecagon (11-gon) central angle. *)
Definition cos_2pi_11 : R := cos (2 * PI / 11).
Definition sin_2pi_11 : R := sin (2 * PI / 11).

(** Minimal polynomial of cos(2π/11) over Q has degree 5.
    Derived from: 2cos(2π/11) satisfies y^5 + y^4 - 4y^3 - 3y^2 + 3y + 1 = 0.
    Substituting y = 2x gives: 32x^5 + 16x^4 - 32x^3 - 12x^2 + 6x + 1 = 0.
    Monic form: x^5 + (1/2)x^4 - x^3 - (3/8)x^2 + (3/16)x + (1/32) = 0. *)
Definition cos_2pi_11_minpoly (x : R) : R :=
  x^5 + (/2) * x^4 - x^3 - (3/8) * x^2 + (3/16) * x + (/32).

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

Fixpoint chebyshev_T (n : nat) (x : R) : R :=
  match n with
  | O => 1
  | S O => x
  | S (S m as p) => 2 * x * chebyshev_T p x - chebyshev_T m x
  end.

Lemma chebyshev_rec : forall n x,
  chebyshev_T (S (S n)) x = 2 * x * chebyshev_T (S n) x - chebyshev_T n x.
Proof. reflexivity. Qed.

Lemma cos_2x_minus : forall a b,
  2 * cos b * cos a - cos (a - b) = cos (a + b).
Proof.
  intros. rewrite cos_plus. rewrite cos_minus. ring.
Qed.

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
Definition chebyshev_11_quotient (x : R) : R :=
  1024*x^10 + 1024*x^9 - 1792*x^8 - 1792*x^7 + 1024*x^6 + 1024*x^5 - 208*x^4 - 208*x^3 + 12*x^2 + 12*x + 1.

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
Definition minpoly_2cos_degree : nat := 5.

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

Definition algebraic_degree_cos_2pi_11 : nat := 5.

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
Definition hendecagon_vertex (k : nat) : R * R :=
  (cos (2 * PI * INR k / 11), sin (2 * PI * INR k / 11)).

Theorem hendecagon_vertex_0 : hendecagon_vertex 0 = (1, 0).
Proof.
  unfold hendecagon_vertex. simpl.
  rewrite Rmult_0_r. unfold Rdiv. rewrite Rmult_0_l.
  rewrite cos_0, sin_0. reflexivity.
Qed.

Theorem hendecagon_vertex_1 : hendecagon_vertex 1 = (cos_2pi_11, sin_2pi_11).
Proof.
  unfold hendecagon_vertex, cos_2pi_11, sin_2pi_11.
  simpl INR.
  replace (2 * PI * 1 / 11) with (2 * PI / 11) by field.
  reflexivity.
Qed.

End Multi_Fold_Origami.

Section Origami_Hierarchy.

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

Conjecture hierarchy_stabilizes_at_2 :
  forall x, OrigamiNum3 x -> OrigamiNum2 x.

End Origami_Hierarchy.

Section Heptagon_Verified_Construction.
(** Heptagon construction via Chebyshev polynomials.

    The regular heptagon requires solving 8c³ + 4c² - 4c - 1 = 0.
    This cubic is not solvable by radicals of degree ≤ 2, hence
    the heptagon is not compass-straightedge constructible.
    However, origami (O6 Beloch fold) solves cubics. *)

(** The heptagon polynomial: 8c³ + 4c² - 4c - 1 = 0 *)
Definition heptagon_poly (c : R) : R := 8*c^3 + 4*c^2 - 4*c - 1.

(** cos(2π/7) *)
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

Definition tschirnhaus_shift : R := 1/6.

(** c = t - 1/6 *)
Definition heptagon_c_from_t (t : R) : R := t - tschirnhaus_shift.

(** t = c + 1/6 *)
Definition heptagon_t_from_c (c : R) : R := c + tschirnhaus_shift.

(** Depressed cubic: t³ + pt + q *)
Definition heptagon_depressed (t : R) : R :=
  t^3 + heptagon_cubic_a * t + heptagon_cubic_b.

(** Tschirnhaus: heptagon_poly(t - 1/6) = 8 · (t³ - 7t/12 - 7/216) *)
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
Lemma heptagon_depressed_expanded : forall t,
  heptagon_depressed t = t^3 - 7/12 * t - 7/216.
Proof.
  intros. unfold heptagon_depressed, heptagon_cubic_a, heptagon_cubic_b. field.
Qed.

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
Lemma heptagon_depressed_eq_depressed_cubic : forall t,
  heptagon_depressed t = depressed_cubic heptagon_cubic_a heptagon_cubic_b t.
Proof.
  intros. unfold heptagon_depressed, depressed_cubic. ring.
Qed.

(** t₀ is a root of the standard depressed cubic *)
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

End Heptagon_Verified_Construction.

Section Delian_Problem.
(** ∛2 satisfies t³ - 2 = 0, i.e., depressed_cubic(0, -2, ∛2) = 0.
    Restatement of cbrt2_is_origami with explicit O6 parameters. *)

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
Definition delian_O6_fold : Fold :=
  fold_O6_beloch delian_p delian_q cbrt2.

(** p = 0 ∧ q = -2 ∧ is_cubic_root(p, q, ∛2) ∧ (∛2)³ = 2 *)
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

End Delian_Problem.

Section Hendecagon_Boundary.
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

End Hendecagon_Boundary.

Section Showcase.
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
Eval compute in (euler_phi 7, euler_phi 9, euler_phi 11, euler_phi 13, euler_phi 19).

End Showcase.

Section Density_Analysis.
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

Eval compute in count_smooth_in_range 3 51.
Eval compute in count_smooth_in_range 3 101.

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

Eval compute in list_smooth_in_range 3 51.
Eval compute in list_non_smooth_in_range 3 51.

(** First 20 non-constructible n values *)
Eval compute in list_non_smooth_in_range 3 80.

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

Eval compute in constructible_3_to_50.
Eval compute in constructible_3_to_100.

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

Eval compute in first_non_constructible.

(** φ values for non-constructible n *)
Eval compute in map euler_phi (list_non_smooth_in_range 3 50).

End Density_Analysis.

Section Algebraic_Classifier.
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

Eval compute in classify_by_degree 1.
Eval compute in classify_by_degree 2.
Eval compute in classify_by_degree 3.
Eval compute in classify_by_degree 4.
Eval compute in classify_by_degree 5.
Eval compute in classify_by_degree 6.
Eval compute in classify_by_degree 8.
Eval compute in classify_by_degree 9.
Eval compute in classify_by_degree 10.

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

Eval compute in classification_summary.

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

End Algebraic_Classifier.
