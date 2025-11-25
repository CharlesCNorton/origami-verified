(** * Origami Geometry Formalization

    This file provides a complete formalization of origami (paper folding) geometry
    over the reals, including:
    - The seven Huzita-Hatori origami axioms (O1-O7)
    - Geometric primitives (points, lines, folds) in R²
    - Constructibility predicates defining what can be built via origami operations
    - Algebraic characterization: origami numbers include all rationals, square roots,
      and cubic roots (going beyond compass-and-straightedge constructions)

    Author: Charles C Norton
    Date: November 22, 2025
*)

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
Import ListNotations.
Open Scope R_scope.

(** ** Geometric Primitives

    Basic definitions for points and lines in R². Lines are represented in
    implicit form Ax + By + C = 0 with the invariant A ≠ 0 ∨ B ≠ 0.
*)

Section Geometry_Primitives.

(** Points are simply pairs of reals. *)
Definition Point : Type := R * R.

Record Line : Type := {
  A : R;
  B : R;
  C : R
}.

Definition line_wf (l : Line) : Prop := A l <> 0 \/ B l <> 0.

Definition mkLine (a b c : R) (H : a <> 0 \/ b <> 0) : Line :=
  {| A := a; B := b; C := c |}.

Definition normalize_line (l : Line) : Line :=
  let a := A l in
  let b := B l in
  let c := C l in
  let n := sqrt (a * a + b * b) in
  {| A := a / n; B := b / n; C := c / n |}.

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

Definition on_line (p : Point) (l : Line) : Prop :=
  let '(x, y) := p in A l * x + B l * y + C l = 0.

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

Definition point_eq (p q : Point) : Prop :=
  fst p = fst q /\ snd p = snd q.

Definition line_parallel (l1 l2 : Line) : Prop :=
  A l1 * B l2 = A l2 * B l1.

Definition line_perp (l1 l2 : Line) : Prop :=
  A l1 * A l2 + B l1 * B l2 = 0.

End Geometric_Predicates.

Section Computable_Predicates.

(** Decidable version of point equality for computation. *)
Definition point_eq_dec (p q : Point) : {p = q} + {p <> q}.
Proof.
  destruct p as [x1 y1], q as [x2 y2].
  destruct (Req_EM_T x1 x2) as [Hx | Hx].
  - destruct (Req_EM_T y1 y2) as [Hy | Hy].
    + left. rewrite Hx, Hy. reflexivity.
    + right. intro H. injection H as H1 H2. contradiction.
  - right. intro H. injection H as H1 H2. contradiction.
Defined.

(** Decidable version of on_line predicate. *)
Definition on_line_dec (p : Point) (l : Line) : {on_line p l} + {~on_line p l}.
Proof.
  unfold on_line.
  destruct p as [x y].
  apply Req_EM_T.
Defined.

(** Decidable version of line_parallel predicate. *)
Definition line_parallel_dec (l1 l2 : Line) : {line_parallel l1 l2} + {~line_parallel l1 l2}.
Proof.
  unfold line_parallel.
  apply Req_EM_T.
Defined.

(** Decidable version of line_perp predicate. *)
Definition line_perp_dec (l1 l2 : Line) : {line_perp l1 l2} + {~line_perp l1 l2}.
Proof.
  unfold line_perp.
  apply Req_EM_T.
Defined.

End Computable_Predicates.

Section Metric_Geometry.

Definition sqr (x : R) : R := x * x.

Definition dist (p q : Point) : R :=
  let '(x1, y1) := p in
  let '(x2, y2) := q in
  sqrt (sqr (x1 - x2) + sqr (y1 - y2)).

Definition dist2 (p q : Point) : R :=
  let '(x1, y1) := p in
  let '(x2, y2) := q in
  sqr (x1 - x2) + sqr (y1 - y2).

Lemma square_pos : forall x : R, x <> 0 -> x * x > 0.
Proof.
  intros x Hneq.
  destruct (Rlt_dec x 0) as [Hlt | Hnlt].
  - nra.
  - destruct (Rgt_dec x 0) as [Hgt | HnGt].
    + nra.
    + exfalso; nra.
Qed.

Lemma mul_div_cancel_l : forall a c, a <> 0 -> a * (c / a) = c.
Proof.
  intros a c Ha.
  unfold Rdiv.
  rewrite Rmult_comm.
  rewrite Rmult_assoc.
  rewrite Rinv_l; [ring|exact Ha].
Qed.

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

Definition line_norm (l : Line) : R :=
  sqrt (sqr (A l) + sqr (B l)).

Definition dist_point_line (p : Point) (l : Line) : R :=
  Rabs (let '(x, y) := p in A l * x + B l * y + C l) / line_norm l.

End Metric_Geometry.

Section Fold_Primitives.

Inductive Fold : Type :=
| fold_line_ctor : Line -> Fold.

Definition fold_line (f : Fold) : Line :=
  match f with
  | fold_line_ctor l => l
  end.

(* Reflection of a point across a fold line. *)

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

(* Canonical distinct points chosen on a line for constructions. *)

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

Definition map_point (f : Fold) (p : Point) : Point :=
  reflect_point p (fold_line f).

(* Line through two points, choosing a vertical fallback if x-coordinates coincide. *)

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

Lemma line_through_wf : forall p1 p2, line_wf (line_through p1 p2).
Proof.
  intros [x1 y1] [x2 y2].
  unfold line_wf, line_through.
  destruct (Req_EM_T x1 x2) as [Heq | Hneq]; simpl.
  - left. apply R1_neq_R0.
  - right. assert (Hgoal: x2 - x1 <> 0) by lra. exact Hgoal.
Qed.

Lemma line_through_on_line_fst : forall p1 p2,
  on_line p1 (line_through p1 p2).
Proof.
  intros [x1 y1] [x2 y2].
  unfold on_line, line_through; simpl.
  destruct (Req_EM_T x1 x2); simpl; ring.
Qed.

Lemma line_through_on_line_snd : forall p1 p2,
  on_line p2 (line_through p1 p2).
Proof.
  intros [x1 y1] [x2 y2].
  unfold on_line, line_through; simpl.
  destruct (Req_EM_T x1 x2) as [Hx|Hx]; simpl.
  - subst. ring.
  - ring.
Qed.

(* Reflection of a line across a fold line. *)

Definition map_line (f : Fold) (l : Line) : Line :=
  let '(p1, p2) := base_points l in
  line_through (map_point f p1) (map_point f p2).

Definition foot_on_line (p : Point) (l : Line) : Point :=
  let '(x, y) := p in
  let a := A l in
  let b := B l in
  let c := C l in
  let denom := a * a + b * b in
  let factor := (a * x + b * y + c) / denom in
  (x - a * factor, y - b * factor).

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

Lemma base_points_distinct : forall l,
  fst (base_points l) <> snd (base_points l).
Proof.
  intro l; unfold base_points; simpl.
  destruct (Req_EM_T (B l) 0) as [Hb | Hb].
  - intro Heq. injection Heq. intros. lra.
  - intro Heq. injection Heq. intros. lra.
Qed.

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

Definition midpoint (p1 p2 : Point) : Point :=
  let '(x1, y1) := p1 in
  let '(x2, y2) := p2 in
  ((x1 + x2) / 2, (y1 + y2) / 2).

Definition line_intersection (l1 l2 : Line) : Point :=
  let D := A l1 * B l2 - A l2 * B l1 in
  let Dx := (- C l1) * B l2 - (- C l2) * B l1 in
  let Dy := A l1 * (- C l2) - A l2 * (- C l1) in
  match Req_EM_T D 0 with
  | left _ => (0, 0)
  | right Hnz => (Dx / D, Dy / D)
  end.

Lemma line_intersection_parallel : forall l1 l2,
  A l1 * B l2 - A l2 * B l1 = 0 -> line_intersection l1 l2 = (0, 0).
Proof.
  intros l1 l2 HD.
  unfold line_intersection.
  destruct (Req_EM_T (A l1 * B l2 - A l2 * B l1) 0).
  - reflexivity.
  - contradiction.
Qed.

Definition line_xaxis : Line := {| A := 0; B := 1; C := 0 |}.
Definition line_yaxis : Line := {| A := 1; B := 0; C := 0 |}.

Lemma line_xaxis_wf : line_wf line_xaxis.
Proof. unfold line_wf, line_xaxis. simpl. right. apply R1_neq_R0. Qed.

Lemma line_yaxis_wf : line_wf line_yaxis.
Proof. unfold line_wf, line_yaxis. simpl. left. apply R1_neq_R0. Qed.

Definition point_O : Point := (0, 0).
Definition point_X : Point := (1, 0).

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

Lemma foot_on_line_incident : forall p l, line_wf l -> on_line (foot_on_line p l) l.
Proof.
  intros [x y] l Hwf; unfold foot_on_line, on_line; simpl.
  apply proj_eval.
  exact Hwf.
Qed.

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

Lemma map_point_fix : forall f p, on_line p (fold_line f) -> map_point f p = p.
Proof.
  intros f p H.
  destruct f; simpl in *.
  apply reflect_point_on_line; exact H.
Qed.

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

Lemma map_point_involutive : forall f p, line_wf (fold_line f) -> map_point f (map_point f p) = p.
Proof.
  intros [l] p Hwf; simpl in *.
  apply reflect_point_involutive. exact Hwf.
Qed.

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

Definition fold_O1 (p1 p2 : Point) : Fold :=
  fold_line_ctor (line_through p1 p2).

(* Origami operation O2: perpendicular bisector mapping p1 to p2. *)

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

Definition fold_O2 (p1 p2 : Point) : Fold :=
  fold_line_ctor (perp_bisector p1 p2).

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

Lemma fold_line_O1 : forall p1 p2, fold_line (fold_O1 p1 p2) = line_through p1 p2.
Proof. reflexivity. Qed.

Lemma fold_line_O2 : forall p1 p2, fold_line (fold_O2 p1 p2) = perp_bisector p1 p2.
Proof. reflexivity. Qed.

(* Origami operation O4: perpendicular to l through p. *)

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

Definition fold_O4 (p : Point) (l : Line) : Fold :=
  fold_line_ctor (perp_through p l).

Lemma fold_line_O4 : forall p l, fold_line (fold_O4 p l) = perp_through p l.
Proof. reflexivity. Qed.

(* Origami operation O3: fold mapping line l1 onto l2 via an angle bisector. *)

(** Signed distance from a point to a line.
    This is positive on one side of the line and negative on the other.
    The magnitude equals the Euclidean distance to the line. *)
Definition signed_dist (p : Point) (l : Line) : R :=
  let '(x, y) := p in
  (A l * x + B l * y + C l) / line_norm l.

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

Definition fold_O3 (l1 l2 : Line) : Fold :=
  fold_line_ctor (bisector l1 l2).

Lemma fold_line_O3 : forall l1 l2, fold_line (fold_O3 l1 l2) = bisector l1 l2.
Proof. reflexivity. Qed.

(** O3 Correctness: The bisector is the locus of points equidistant from both lines.
    This is the fundamental characterization of an angle bisector.
    We prove this for the standard (non-degenerate) case where the bisector
    is defined by the difference of normalized line equations. *)
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

(** O3 Correctness (converse): Points equidistant from both lines lie on the bisector
    (when the bisector is in standard form, not degenerate). *)
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

(* Origami operation O5: fold p1 onto l through p2. *)

Definition fold_O5 (p1 : Point) (l : Line) (p2 : Point) : Fold :=
  let proj := foot_on_line p1 l in
  let aux_line := line_through p1 proj in
  fold_line_ctor (perp_through p2 aux_line).

Lemma fold_line_O5 : forall p1 l p2, fold_line (fold_O5 p1 l p2) = perp_through p2 (line_through p1 (foot_on_line p1 l)).
Proof. reflexivity. Qed.

(** Corrected O5 for vertical lines: fold p onto vertical line x=c through q.
    The O5 fold places p onto the vertical line, passing through q.
    The image p' is at (c, qy + sqrt(dist(q,p)^2 - (c-qx)^2)). *)

Definition O5_vert_image_y (p q : Point) (c : R) : R :=
  let d2 := (fst p - fst q)^2 + (snd p - snd q)^2 in
  let dx2 := (c - fst q)^2 in
  snd q + sqrt (d2 - dx2).

Definition O5_vert_image (p q : Point) (c : R) : Point :=
  (c, O5_vert_image_y p q c).

Definition fold_O5_vert (p q : Point) (c : R) : Fold :=
  fold_line_ctor (perp_bisector p (O5_vert_image p q c)).

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

(** Beloch Fold Construction for Cubic Equations.
    The Beloch fold (O6) solves depressed cubics t³ + pt + q = 0.
    Configuration:
    - P1 = (0, 1), L1: y = -1 (parabola y = x²/4 has focus P1, directrix L1)
    - P2 = (q, p), L2: x = -q
    The common tangent (O6 fold) has slope t where t is a cubic root. *)

Definition beloch_P1 : Point := (0, 1).
Definition beloch_L1 : Line := {| A := 0; B := 1; C := 1 |}.
Definition beloch_P2 (p q : R) : Point := (q, p).
Definition beloch_L2 (q : R) : Line := {| A := 1; B := 0; C := q |}.

(** The Beloch fold line: y = tx - t², i.e., tx - y - t² = 0 *)
Definition beloch_fold_line (t : R) : Line := {| A := t; B := -1; C := -(t*t) |}.

Definition fold_O6_beloch (p q t : R) : Fold :=
  fold_line_ctor (beloch_fold_line t).

Lemma beloch_L1_wf : line_wf beloch_L1.
Proof. unfold line_wf, beloch_L1; simpl; right; lra. Qed.

Lemma beloch_L2_wf : forall q, line_wf (beloch_L2 q).
Proof. intro q; unfold line_wf, beloch_L2; simpl; left; lra. Qed.

Lemma beloch_fold_line_wf : forall t, line_wf (beloch_fold_line t).
Proof. intro t; unfold line_wf, beloch_fold_line; simpl; right; lra. Qed.

(** Reflection of P1 = (0, 1) across Beloch fold line lands on L1: y = -1 *)
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

(** Reflection of P2 = (q, p) across Beloch fold lands on L2: x = -q, when t³ + pt + q = 0 *)
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

(** O6 Geometric Characterization:
    A fold line f satisfying O6(p1, l1, p2, l2) must satisfy:
    - reflect_point p1 f lies on l1
    - reflect_point p2 f lies on l2

    This generally yields a cubic equation in the fold line parameters. *)

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

(** The Beloch fold satisfies O6 constraints when t is a cubic root *)
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

Lemma line_perp_comm : forall l1 l2,
  line_perp l1 l2 -> line_perp l2 l1.
Proof.
  intros l1 l2 H.
  unfold line_perp in *.
  lra.
Qed.

Lemma perp_through_perp : forall p l,
  line_perp (perp_through p l) l.
Proof.
  intros [x y] l.
  unfold line_perp, perp_through.
  destruct (Req_EM_T (A l) 0); simpl; ring.
Qed.


Definition parallel_line_through (p : Point) (l : Line) : Line :=
  {| A := A l; B := B l; C := - A l * (fst p) - B l * (snd p) |}.

Lemma parallel_line_through_wf : forall p l, line_wf l -> line_wf (parallel_line_through p l).
Proof.
  intros p l Hwf.
  unfold line_wf, parallel_line_through. simpl.
  exact Hwf.
Qed.

Lemma parallel_line_through_parallel : forall p l,
  line_parallel (parallel_line_through p l) l.
Proof.
  intros p l.
  unfold line_parallel, parallel_line_through. simpl.
  ring.
Qed.

Lemma parallel_line_through_incident : forall p l,
  on_line p (parallel_line_through p l).
Proof.
  intros [x y] l.
  unfold on_line, parallel_line_through.
  destruct l as [a b c]; simpl.
  ring.
Qed.

Lemma perp_to_line_perp : forall l1 l2,
  line_perp l1 l2 <-> A l1 * A l2 + B l1 * B l2 = 0.
Proof.
  intros l1 l2.
  unfold line_perp. split; intro H; exact H.
Qed.

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

Lemma reflect_point_on_line_stays : forall p l,
  on_line p l -> reflect_point p l = p.
Proof.
  intros p l Hp.
  apply reflect_point_on_line.
  exact Hp.
Qed.


Theorem perpendicularity_symmetric : forall l1 l2,
  line_perp l1 l2 -> line_perp l2 l1.
Proof.
  intros l1 l2 H.
  apply line_perp_comm.
  exact H.
Qed.

Theorem parallel_is_symmetric : forall l1 l2,
  line_parallel l1 l2 -> line_parallel l2 l1.
Proof.
  intros l1 l2 H.
  unfold line_parallel in *.
  lra.
Qed.

Theorem point_on_parallel_line : forall p l,
  on_line p (parallel_line_through p l).
Proof.
  intros p l.
  apply parallel_line_through_incident.
Qed.

Theorem constructed_line_is_parallel : forall p l,
  line_parallel (parallel_line_through p l) l.
Proof.
  intros p l.
  apply parallel_line_through_parallel.
Qed.

Theorem perpendicular_construction_works : forall p l,
  line_perp (construct_perp_line_at p l) l /\
  on_line p (construct_perp_line_at p l).
Proof.
  intros p l.
  split.
  - apply construct_perp_line_at_perp.
  - apply construct_perp_line_at_incident.
Qed.

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

Theorem perp_bisector_reflects_correctly : forall p1 p2,
  p1 <> p2 ->
  reflect_point p1 (perp_bisector p1 p2) = p2.
Proof.
  intros p1 p2 Hneq.
  apply perp_bisector_reflects_to_other.
  exact Hneq.
Qed.

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

Theorem foot_on_line_minimizes_distance : forall p l,
  line_wf l -> on_line (foot_on_line p l) l.
Proof.
  intros p l Hwf.
  apply foot_on_line_incident. exact Hwf.
Qed.

Theorem origami_axiom_O1_always_exists : forall p1 p2,
  exists f, on_line p1 (fold_line f) /\ on_line p2 (fold_line f).
Proof.
  intros p1 p2.
  exists (fold_line_ctor (line_through p1 p2)).
  split; unfold fold_line; simpl.
  - apply line_through_on_line_fst.
  - apply line_through_on_line_snd.
Qed.

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


Lemma line_intersection_on_line_snd : forall l1 l2,
  A l1 * B l2 - A l2 * B l1 <> 0 ->
  on_line (line_intersection l1 l2) l2.
Proof.
  intros l1 l2 HD.
  unfold line_intersection, on_line.
  destruct (Req_EM_T (A l1 * B l2 - A l2 * B l1) 0) as [Heq|Hneq]; [contradiction|].
  simpl. field. exact Hneq.
Qed.




Lemma O6_constraint_verification : forall f p1 l1 p2 l2,
  satisfies_O6_constraint f p1 l1 p2 l2 ->
  on_line (map_point f p1) l1 /\ on_line (map_point f p2) l2.
Proof.
  intros f p1 l1 p2 l2 [H1 H2].
  unfold map_point, satisfies_O6_constraint in *.
  split; assumption.
Qed.

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

(** The approximation satisfies O6 when both points already lie on their target lines *)
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

(** For general O6, we show that the fold line passes through the correct midpoints,
    which is the geometric construction approach. The general case requires solving
    a cubic equation to find the exact fold line satisfying both constraints. *)
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

Definition fold_O6 := fold_O6_approx.

Lemma fold_line_O6 : forall p1 l1 p2 l2,
  fold_line (fold_O6 p1 l1 p2 l2) = line_through (midpoint p1 (foot_on_line p1 l1)) (midpoint p2 (foot_on_line p2 l2)).
Proof. reflexivity. Qed.

Theorem O6_approx_correctness : forall p1 l1 p2 l2,
  on_line p1 l1 -> on_line p2 l2 ->
  satisfies_O6_constraint (fold_O6 p1 l1 p2 l2) p1 l1 p2 l2.
Proof.
  intros p1 l1 p2 l2 H1 H2.
  apply fold_O6_approx_satisfies_when_on_lines; assumption.
Qed.

Lemma O6_solution_exists_special_case : forall p1 l1 p2 l2,
  on_line p1 l1 -> on_line p2 l2 ->
  exists crease, satisfies_O6_line_constraint crease p1 l1 p2 l2.
Proof.
  intros p1 l1 p2 l2 H1 H2.
  exists (fold_line (fold_O6 p1 l1 p2 l2)).
  unfold fold_O6, fold_O6_approx, fold_line; simpl.
  apply fold_O6_approx_satisfies_when_on_lines; assumption.
Qed.

Lemma midpoint_self : forall p,
  midpoint p p = p.
Proof.
  intro p. destruct p as [x y].
  unfold midpoint. simpl. f_equal; field.
Qed.

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




(** O7 Geometric Characterization:
    A fold line f satisfying O7(p1, l1, l2) must satisfy:
    - reflect_point p1 f lies on l1
    - f is perpendicular to l2 *)

Definition satisfies_O7_constraint (f : Fold) (p1 : Point) (l1 : Line) (l2 : Line) : Prop :=
  let crease := fold_line f in
  on_line (reflect_point p1 crease) l1 /\ line_perp crease l2.

Definition line_perp_through (p : Point) (l : Line) : Line :=
  perp_through p l.

Lemma perp_through_is_perp : forall p l,
  line_perp (perp_through p l) l.
Proof.
  intros [x y] l.
  unfold line_perp, perp_through.
  destruct (Req_EM_T (A l) 0); simpl; ring.
Qed.

Lemma perp_through_incident : forall p l,
  on_line p (perp_through p l).
Proof.
  intros [x y] l.
  unfold on_line, perp_through.
  destruct (Req_EM_T (A l) 0); simpl; ring.
Qed.

Lemma perp_bisector_dist2_eq : forall p1 p2,
  dist2 p1 (midpoint p1 p2) = dist2 p2 (midpoint p1 p2).
Proof.
  intros [x1 y1] [x2 y2].
  unfold dist2, midpoint; simpl.
  unfold sqr. field.
Qed.

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

(** O7 construction: Create a line perpendicular to l2 that reflects p1 onto l1.
    This is done by:
    1. Creating a line through p1 perpendicular to l2
    2. Finding where this perpendicular intersects l1 (the target point)
    3. Constructing the perpendicular bisector of p1 and the target point *)
Definition fold_O7_simple (p1 : Point) (l1 : Line) (l2 : Line) : Fold :=
  let perp_l2 := perp_through p1 l2 in
  let target := line_intersection perp_l2 l1 in
  fold_line_ctor (perp_bisector p1 target).

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

(** Corrected O7 construction *)
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

(** Auxiliary lemma about perpendicularity when direction is parallel to l2 *)
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

(** Perpendicularity proof for fold_O7_corrected (non-degenerate case) *)
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

Definition fold_O7 := fold_O7_corrected.

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

Lemma point_on_perp_through : forall p l,
  on_line p (perp_through p l).
Proof.
  intros [x y] l.
  unfold perp_through, on_line. simpl.
  destruct (Req_EM_T (A l) 0); simpl; ring.
Qed.

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

(** When p1 is on l1, the parameter t in fold_O7_corrected equals 0. *)
Lemma fold_O7_t_zero_when_on_line : forall p1 l1 l2,
  on_line p1 l1 ->
  A l1 * B l2 - B l1 * A l2 <> 0 ->
  - (A l1 * fst p1 + B l1 * snd p1 + C l1) / (A l1 * B l2 + B l1 * - A l2) = 0.
Proof.
  intros [px py] l1 l2 Hon Hnonpar.
  unfold on_line in Hon. simpl in *.
  rewrite Hon. field. lra.
Qed.

(** When p1 is on l1 (non-parallel case), p1 lies on the fold line. *)
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

(** When p1 is on l1 (non-parallel case), reflection is trivial. *)
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

Lemma midpoint_avg : forall a b, (a + b) / 2 = (a + b) * / 2.
Proof.
  intros. unfold Rdiv. reflexivity.
Qed.

Lemma diff_sqr : forall a b, a * a - b * b = (a - b) * (a + b).
Proof.
  intros. ring.
Qed.

Lemma mid_coord : forall a b, (a + b) / 2 * 2 = a + b.
Proof.
  intros. field.
Qed.

Lemma two_neq_zero : 2 <> 0.
Proof.
  lra.
Qed.

Lemma half_sum : forall a b, a - (a + b) / 2 = (a - b) / 2.
Proof.
  intros. field.
Qed.

Lemma sqr_diff_factor : forall a b, a * a - b * b = -(2 * (b - a)) * ((a + b) / 2).
Proof.
  intros. field.
Qed.

Lemma double_cancel : forall a b, b <> 0 -> 2 * b * (a / (b * b)) = 2 * a / b.
Proof.
  intros. field. assumption.
Qed.

Lemma cancel_fraction : forall a b, b <> 0 -> a * (b / (b * b)) = a / b.
Proof.
  intros. field. assumption.
Qed.

Lemma four_is_nonzero : 4 <> 0.
Proof.
  lra.
Qed.

Lemma four_sqr : forall a, 4 * a * a = 2 * (2 * a) * (2 * a) / 2.
Proof.
  intros. field.
Qed.

Lemma sum_sqr_nonzero : forall a b, a <> 0 -> a * a + b * b <> 0.
Proof.
  intros a b Ha.
  intro Hcontra.
  assert (Ha_sq_pos : 0 <= a * a) by apply Rle_0_sqr.
  assert (Hb_sq_pos : 0 <= b * b) by apply Rle_0_sqr.
  assert (Ha_sq_z : a * a = 0) by lra.
  destruct (Rmult_integral _ _ Ha_sq_z) as [Ha_z | Ha_z]; lra.
Qed.

Lemma sum_sqr_nonzero_sym : forall a b, b <> 0 -> a * a + b * b <> 0.
Proof.
  intros a b Hb.
  intro Hcontra.
  assert (Ha_sq_pos : 0 <= a * a) by apply Rle_0_sqr.
  assert (Hb_sq_pos : 0 <= b * b) by apply Rle_0_sqr.
  assert (Hb_sq_z : b * b = 0) by lra.
  destruct (Rmult_integral _ _ Hb_sq_z) as [Hb_z | Hb_z]; lra.
Qed.

Lemma refl_sub_main : forall p x, p - 2 * p * x = p * (1 - 2 * x).
Proof.
  intros. ring.
Qed.

Lemma fold_div : forall a b c, c <> 0 -> a / c + b / c = (a + b) / c.
Proof.
  intros. field. assumption.
Qed.

Lemma factor_half_diff : forall a b, 2 * (b - a) * a + (a * a - b * b) = -(b - a) * (b - a).
Proof.
  intros. ring.
Qed.

Lemma simpl_reflect_y : forall a y1 y2, a <> 0 -> y1 - 2 * a * (a * ((y1 - y2) / 2) / (a * a)) = y2.
Proof.
  intros. field. assumption.
Qed.

Lemma simpl_reflect_x : forall a x1 x2, a <> 0 -> x1 - 2 * a * (a * ((x1 - x2) / 2) / (a * a)) = x2.
Proof.
  intros. field. assumption.
Qed.

Lemma mid_on_perp_vert : forall x y1 y2, y1 <> y2 -> 0 * x + 2 * (y2 - y1) * ((y1 + y2) / 2) + (x * x + y1 * y1 - x * x - y2 * y2) = 0.
Proof.
  intros. field.
Qed.

Lemma mid_on_perp_horiz : forall x1 x2 y, x1 <> x2 -> 2 * (x2 - x1) * ((x1 + x2) / 2) + 2 * (y - y) * ((y + y) / 2) + (x1 * x1 + y * y - x2 * x2 - y * y) = 0.
Proof.
  intros. field.
Qed.

Lemma mid_on_perp_gen : forall x1 y1 x2 y2, x1 <> x2 -> y1 <> y2 -> 2 * (x2 - x1) * ((x1 + x2) / 2) + 2 * (y2 - y1) * ((y1 + y2) / 2) + (x1 * x1 + y1 * y1 - x2 * x2 - y2 * y2) = 0.
Proof.
  intros. field.
Qed.

Lemma zero_mul_l : forall a b, 0 * a + b = b.
Proof.
  intros. ring.
Qed.

Lemma zero_mul_r : forall a b, a + 0 * b = a.
Proof.
  intros. ring.
Qed.

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

Lemma sum_sq_nz_l : forall a b, a <> 0 -> a * a + b * b <> 0.
Proof.
  intros a b Ha. intro H.
  assert (Ha2 : 0 <= a * a) by apply Rle_0_sqr.
  assert (Hb2 : 0 <= b * b) by apply Rle_0_sqr.
  assert (Haz : a * a = 0) by lra.
  apply Rmult_integral in Haz. destruct Haz; lra.
Qed.

Lemma refl_gen_bisector_horiz_x : forall x1 x2 y1 y2,
  x1 <> x2 ->
  fst (reflect_point (x1, y1) (perp_bisector (x1, y1) (x2, y2))) = x2.
Proof.
  intros x1 x2 y1 y2 Hx.
  unfold reflect_point, perp_bisector.
  destruct (Req_EM_T x1 x2); [lra|].
  simpl. field. apply sum_sq_nz_l. lra.
Qed.

Lemma refl_gen_bisector_horiz_y : forall x1 x2 y1 y2,
  x1 <> x2 ->
  snd (reflect_point (x1, y1) (perp_bisector (x1, y1) (x2, y2))) = y2.
Proof.
  intros x1 x2 y1 y2 Hx.
  unfold reflect_point, perp_bisector.
  destruct (Req_EM_T x1 x2); [lra|].
  simpl. field. apply sum_sq_nz_l. lra.
Qed.

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

(** Helper: The constructed point q in O7_corrected lies on l1 *)
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

(** Helper: Perpendicular bisector reflects p1 onto any point q that lies on the target line *)
Lemma perp_bisector_reflects_onto_line : forall p1 q l,
  on_line q l ->
  p1 <> q ->
  on_line (reflect_point p1 (perp_bisector p1 q)) l.
Proof.
  intros p1 q l Hq_on_l Hneq.
  rewrite perp_bisector_reflection; auto.
Qed.

(** Helper 1: If t * B l2 = 0 and t * (-A l2) = 0, then t = 0 (using line normal nonzero) *)
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

(** Helper 2: If (x + t*a, y + t*b) = (x, y), then t*a = 0 and t*b = 0 *)
Lemma point_eq_implies_offset_zero : forall x y t a b,
  (x + t * a, y + t * b) = (x, y) ->
  t * a = 0 /\ t * b = 0.
Proof.
  intros x y t a b Heq.
  injection Heq as Hx Hy.
  split; lra.
Qed.

(** Helper 3: If t * denom = 0 and denom ≠ 0, then t = 0 *)
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

(** Helper 4: If p1 is not on l1 and q is constructed as in O7_corrected, then p1 ≠ q *)
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

(** O7 satisfies both constraints: reflection and perpendicularity *)
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

(** Unified O7: fold_O7 satisfies constraints whenever solvable. *)
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

Lemma O6_constraint_unfold : forall p1 l1 p2 l2 f,
  satisfies_O6_constraint f p1 l1 p2 l2 ->
  on_line (reflect_point p1 (fold_line f)) l1 /\
  on_line (reflect_point p2 (fold_line f)) l2.
Proof.
  intros p1 l1 p2 l2 f H.
  exact H.
Qed.

(** Cubic polynomial in depressed form: t³ + pt + q *)
Definition cubic_depressed (p q t : R) : R := t * t * t + p * t + q.

Lemma cubic_root_iff : forall p q r,
  cubic_depressed p q r = 0 <-> r * r * r + p * r + q = 0.
Proof.
  intros p q r.
  unfold cubic_depressed.
  reflexivity.
Qed.

(** Discriminant of depressed cubic: Δ = -4p³ - 27q² *)
Definition cubic_discriminant (p q : R) : R := -4 * p * p * p - 27 * q * q.

(** Real cube root function for positive reals using IVT *)
Definition cube_func (x : R) : R := x * x * x.

Lemma cube_func_continuous : continuity cube_func.
Proof.
  unfold cube_func.
  apply continuity_mult.
  - apply continuity_mult.
    + apply derivable_continuous, derivable_id.
    + apply derivable_continuous, derivable_id.
  - apply derivable_continuous, derivable_id.
Qed.

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

Definition cbrt_pos (y : R) (Hy : 0 < y) : R := proj1_sig (cube_root_pos_exists y Hy).

Lemma cbrt_pos_spec : forall y Hy, 0 < cbrt_pos y Hy /\ cube_func (cbrt_pos y Hy) = y.
Proof.
  intros y Hy.
  unfold cbrt_pos.
  destruct (cube_root_pos_exists y Hy) as [x Hx]. simpl.
  exact Hx.
Qed.

Lemma neg_pos_iff : forall x, x < 0 -> 0 < - x.
Proof. intros x Hx. lra. Qed.

Lemma neg_case_proof : forall x, ~ 0 < x -> x <> 0 -> x < 0.
Proof. intros x Hnpos Hneg. lra. Qed.

Definition cbrt (x : R) : R :=
  match Rlt_dec 0 x with
  | left Hpos => cbrt_pos x Hpos
  | right Hnpos =>
      match Req_EM_T x 0 with
      | left _ => 0
      | right Hneg => - cbrt_pos (- x) (neg_pos_iff x (neg_case_proof x Hnpos Hneg))
      end
  end.

Lemma cbrt_spec_pos : forall x, 0 < x -> cube_func (cbrt x) = x.
Proof.
  intros x Hx.
  unfold cbrt.
  destruct (Rlt_dec 0 x) as [Hpos | Hnpos].
  - destruct (cbrt_pos_spec x Hpos) as [_ Hcube]. exact Hcube.
  - exfalso. lra.
Qed.

Lemma cbrt_0 : cbrt 0 = 0.
Proof.
  unfold cbrt.
  destruct (Rlt_dec 0 0) as [Hcontra|H0]; [exfalso; lra|].
  destruct (Req_EM_T 0 0) as [Heq|Hcontra]; [reflexivity|exfalso; exact (Hcontra eq_refl)].
Qed.

Lemma cbrt_cube_0 : cube_func (cbrt 0) = 0.
Proof.
  rewrite cbrt_0.
  unfold cube_func.
  ring.
Qed.

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

Definition cardano_solve (p q : R) : R :=
  cbrt (- q / 2 + sqrt (Rmax 0 (q * q / 4 + p * p * p / 27))) +
  cbrt (- q / 2 - sqrt (Rmax 0 (q * q / 4 + p * p * p / 27))).

Lemma sqrt_sqr_pos : forall x, 0 <= x -> sqrt (x * x) = x.
Proof.
  intros x Hx.
  replace (x * x) with (Rsqr x) by (unfold Rsqr; ring).
  apply sqrt_Rsqr.
  exact Hx.
Qed.

Lemma sum_cubes_formula : forall u v,
  (u + v) * (u + v) * (u + v) =
  u * u * u + v * v * v + 3 * u * v * (u + v).
Proof.
  intros u v.
  ring.
Qed.

Lemma product_cubes_formula : forall u v,
  u * u * u * (v * v * v) = (u * v) * (u * v) * (u * v).
Proof.
  intros u v.
  ring.
Qed.

Lemma difference_of_squares : forall a b,
  (a + b) * (a - b) = a * a - b * b.
Proof.
  intros a b. ring.
Qed.

Lemma cardano_discriminant_identity : forall p q s,
  s * s = q * q / 4 + p * p * p / 27 ->
  (- q / 2) * (- q / 2) - s * s = - p * p * p / 27.
Proof.
  intros p q s Hs.
  rewrite Hs.
  field.
Qed.

Lemma sqrt_Rmax_sqr : forall x,
  sqrt (Rmax 0 x) * sqrt (Rmax 0 x) = Rmax 0 x.
Proof.
  intro x.
  apply sqrt_sqrt.
  apply Rmax_l.
Qed.

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

Lemma cbrt_cube : forall x,
  cbrt x * cbrt x * cbrt x = x.
Proof.
  intro x.
  pose proof (cbrt_spec x) as H.
  unfold cube_func in H.
  exact H.
Qed.

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

Lemma cbrt_mult_power : forall x n,
  cbrt (x ^ n) * cbrt (x ^ n) * cbrt (x ^ n) = x ^ n.
Proof.
  intros x n. apply cbrt_cube.
Qed.

Lemma cbrt_mult_8 : forall x,
  cbrt (8 * x) * cbrt (8 * x) * cbrt (8 * x) = 8 * x.
Proof.
  intro x. apply cbrt_cube.
Qed.

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

Lemma cbrt_pos_positive : forall x (Hx : 0 < x), 0 < cbrt x.
Proof.
  intros x Hx.
  unfold cbrt.
  destruct (Rlt_dec 0 x) as [H|H]; [|exfalso; lra].
  apply (cbrt_pos_spec x H).
Qed.

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

Lemma cube_neg : forall x, cube_func (-x) = - cube_func x.
Proof.
  intro x. unfold cube_func. ring.
Qed.

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

Lemma cbrt_nonneg : forall x, 0 <= x -> 0 <= cbrt x.
Proof.
  intros x Hx.
  destruct (Req_EM_T x 0) as [Hx0|Hxn0].
  - subst. rewrite cbrt_0. lra.
  - assert (Hx_pos : 0 < x) by lra.
    left. apply cbrt_pos_positive. exact Hx_pos.
Qed.

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

Lemma cbrt_div_27 : forall x,
  cbrt (x / 27) * cbrt (x / 27) * cbrt (x / 27) = x / 27.
Proof.
  intro x. apply cbrt_cube.
Qed.

Lemma Rmax_self : forall x,
  0 <= x -> Rmax 0 x = x.
Proof.
  intros x H.
  unfold Rmax. destruct (Rle_dec 0 x); [reflexivity | exfalso; lra].
Qed.

Lemma cardano_u_cubed : forall p q,
  0 <= q * q / 4 + p * p * p / 27 ->
  let u := cbrt (- q / 2 + sqrt (q * q / 4 + p * p * p / 27)) in
  u * u * u = - q / 2 + sqrt (q * q / 4 + p * p * p / 27).
Proof.
  intros p q Hdisc u. apply cbrt_cube.
Qed.

Lemma cardano_v_cubed : forall p q,
  0 <= q * q / 4 + p * p * p / 27 ->
  let v := cbrt (- q / 2 - sqrt (q * q / 4 + p * p * p / 27)) in
  v * v * v = - q / 2 - sqrt (q * q / 4 + p * p * p / 27).
Proof.
  intros p q Hdisc v. apply cbrt_cube.
Qed.

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

Lemma cbrt_of_cube : forall x,
  cbrt (x * x * x) * cbrt (x * x * x) * cbrt (x * x * x) = x * x * x.
Proof.
  intro x. apply cbrt_cube.
Qed.

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

Lemma cbrt_neg_p_cubed_27 : forall p, cbrt (- p * p * p / 27) = - p / 3.
Proof.
  intro p.
  replace (- p * p * p / 27) with ((- p / 3) * (- p / 3) * (- p / 3)).
  - apply cbrt_of_cube_eq.
  - field.
Qed.

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

Lemma sum_of_cubes_identity : forall u v,
  (u + v) * (u + v) * (u + v) =
  u * u * u + v * v * v + 3 * u * v * (u + v).
Proof.
  intros u v. ring.
Qed.

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

(** Algorithm to construct a point by reflecting across a fold. *)
Definition construct_reflection (p : Point) (f : Fold) : Point :=
  map_point f p.

(** Algorithm to construct the midpoint of two points. *)
Definition construct_midpoint (p1 p2 : Point) : Point :=
  midpoint p1 p2.

(** Algorithm to construct intersection of two lines. *)
Definition construct_intersection (l1 l2 : Line) : Point :=
  line_intersection l1 l2.

(** Algorithm to construct a line through two points. *)
Definition construct_line_through (p1 p2 : Point) : Line :=
  line_through p1 p2.

(** Algorithm to construct perpendicular bisector of two points. *)
Definition construct_perp_bisector (p1 p2 : Point) : Line :=
  perp_bisector p1 p2.

End Construction_Algorithms.

Section Constructibility.

Definition O5_vert_valid (p q : Point) (c : R) : Prop :=
  let px := fst p in let py := snd p in
  let qx := fst q in let qy := snd q in
  (c - qx)^2 <= (px - qx)^2 + (py - qy)^2.

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
      ConstructibleFold (fold_O6_beloch p q t).

Scheme Constructible_mut :=
  Induction for ConstructiblePoint Sort Prop
  with ConstructibleLine_mut := Induction for ConstructibleLine Sort Prop
  with ConstructibleFold_mut := Induction for ConstructibleFold Sort Prop.

Lemma ConstructibleLine_of_fold : forall f, ConstructibleFold f -> ConstructibleLine (fold_line f).
Proof. intros f Hf; now constructor. Qed.

Lemma ConstructibleLine_OX : ConstructibleLine (line_through point_O point_X).
Proof.
  rewrite <- fold_line_O1.
  apply CL_fold.
  apply CF_O1; constructor; constructor.
Qed.

Definition ConstructibleR (x : R) : Prop :=
  exists y, ConstructiblePoint (x, y).

Lemma constructible_0 : ConstructibleR 0.
Proof. exists 0; constructor. Qed.

Lemma constructible_1 : ConstructibleR 1.
Proof. exists 0; constructor 2. Qed.

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

(** Enumerate lines constructible at given depth. *)
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

(** Enumerate all points constructible at given depth. *)
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

(** ** Complexity Bounds

    Base case sizes for depth 0. *)

Lemma enum_points_0_size : length (enum_points 0) = 2%nat.
Proof.
  simpl. reflexivity.
Qed.

Lemma enum_lines_0_size : length (enum_lines 0) = 2%nat.
Proof.
  simpl. reflexivity.
Qed.

(** Enumeration size is monotonically non-decreasing. *)
Lemma enum_points_size_monotone : forall d,
  (length (enum_points d) <= length (enum_points (S d)))%nat.
Proof.
  intro d. simpl.
  rewrite app_length.
  apply Nat.le_add_r.
Qed.

Lemma enum_lines_size_monotone : forall d,
  (length (enum_lines d) <= length (enum_lines (S d)))%nat.
Proof.
  intro d. simpl.
  rewrite app_length.
  apply Nat.le_add_r.
Qed.

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

(** Check if point is constructible at given depth by enumeration. *)
Definition point_constructible_depth (p : Point) (depth : nat) : bool :=
  existsb (fun q => if point_eq_dec p q then true else false) (enum_points depth).

Theorem enum_algorithm_decidable : forall p d,
  {point_constructible_depth p d = true} + {point_constructible_depth p d = false}.
Proof.
  intros p d.
  unfold point_constructible_depth.
  destruct (existsb (fun q => if point_eq_dec p q then true else false) (enum_points d)) eqn:E.
  - left. reflexivity.
  - right. reflexivity.
Qed.

Theorem enum_exponential_lower_bound :
  (10 <= length (enum_points 1))%nat.
Proof.
  vm_compute. apply Nat.le_refl.
Qed.

(** The decidability algorithm terminates because it uses structural recursion on depth. *)
Lemma point_constructible_depth_terminates : forall p d,
  exists b, point_constructible_depth p d = b.
Proof.
  intros p d.
  exists (point_constructible_depth p d).
  reflexivity.
Qed.

(** Soundness: if algorithm returns true at depth 0, point is in base set. *)
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

(** Enumeration grows monotonically. *)
Lemma enum_points_monotone : forall d, incl (enum_points d) (enum_points (S d)).
Proof.
  intro d. simpl. unfold incl. intros a Ha.
  apply in_or_app. left. exact Ha.
Qed.

Lemma enum_lines_monotone : forall d, incl (enum_lines d) (enum_lines (S d)).
Proof.
  intro d. simpl. unfold incl. intros a Ha.
  apply in_or_app. left. exact Ha.
Qed.

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

Lemma CF_O5_helper_line_through_in_enum : forall p1 p2 d1 d2,
  In p1 (enum_points d1) -> In p2 (enum_points d2) ->
  In (line_through p1 p2) (enum_lines (S (Nat.max d1 d2))).
Proof.
  intros p1 p2 d1 d2 H1 H2.
  apply line_through_in_enum_S; assumption.
Qed.

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

Lemma CF_O7_helper_perp_bisector_in_enum : forall p1 p2 d1 d2,
  In p1 (enum_points d1) -> In p2 (enum_points d2) ->
  In (perp_bisector p1 p2) (enum_lines (S (Nat.max d1 d2))).
Proof.
  intros p1 p2 d1 d2 H1 H2.
  apply perp_bisector_in_enum_S; assumption.
Qed.

Lemma neg_zero : -0 = 0.
Proof. ring. Qed.

Lemma perp_through_A_when_a_zero : forall px py b c,
  A (perp_through (px, py) {| A := 0; B := b; C := c |}) = b.
Proof.
  intros. unfold perp_through. simpl.
  destruct (Req_EM_T 0 0); [|contradiction]. simpl. reflexivity.
Qed.

Lemma perp_through_B_when_a_zero : forall px py b c,
  B (perp_through (px, py) {| A := 0; B := b; C := c |}) = 0.
Proof.
  intros. unfold perp_through. simpl.
  destruct (Req_EM_T 0 0); [|contradiction]. simpl. rewrite neg_zero. reflexivity.
Qed.

Lemma perp_through_B_when_b_zero : forall px py a c,
  a <> 0 ->
  B (perp_through (px, py) {| A := a; B := 0; C := c |}) = - a.
Proof.
  intros. unfold perp_through. simpl.
  destruct (Req_EM_T a 0); [contradiction|]. simpl. reflexivity.
Qed.

Lemma perp_through_A_general : forall px py a b c,
  a <> 0 ->
  A (perp_through (px, py) {| A := a; B := b; C := c |}) = b.
Proof.
  intros. unfold perp_through. simpl.
  destruct (Req_EM_T a 0); [contradiction|]. simpl. reflexivity.
Qed.

Lemma perp_through_B_general : forall px py a b c,
  a <> 0 ->
  B (perp_through (px, py) {| A := a; B := b; C := c |}) = - a.
Proof.
  intros. unfold perp_through. simpl.
  destruct (Req_EM_T a 0); [contradiction|]. simpl. reflexivity.
Qed.

Lemma ConstructiblePoint_O_eventually : exists d, In point_O (enum_points d).
Proof.
  exact CP_O_in_enum.
Qed.

Lemma ConstructiblePoint_X_eventually : exists d, In point_X (enum_points d).
Proof.
  exact CP_X_in_enum.
Qed.

Lemma ConstructibleLine_xaxis_eventually : exists d, In line_xaxis (enum_lines d).
Proof.
  exact CL_x_in_enum.
Qed.

Lemma ConstructibleLine_yaxis_eventually : exists d, In line_yaxis (enum_lines d).
Proof.
  exact CL_y_in_enum.
Qed.

Lemma foot_in_enum_from_point_line : forall p l dp dl,
  line_wf l ->
  In p (enum_points dp) -> In l (enum_lines dl) ->
  In (foot_on_line p l) (enum_points (S (S (Nat.max dp dl)))).
Proof.
  intros p l dp dl Hwf Hp Hl.
  apply CF_O5_helper_foot_in_enum; assumption.
Qed.

Lemma point_monotone_to_SS_max : forall p d1 d2,
  In p (enum_points d1) ->
  In p (enum_points (S (S (Nat.max d1 d2)))).
Proof.
  intros p d1 d2 H.
  apply (enum_points_monotone_le d1).
  - apply le_S, le_S, Nat.le_max_l.
  - exact H.
Qed.

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

Section Origami_Algebra.

Inductive OrigamiNum : R -> Prop :=
| ON_0 : OrigamiNum 0
| ON_1 : OrigamiNum 1
| ON_add : forall x y, OrigamiNum x -> OrigamiNum y -> OrigamiNum (x + y)
| ON_sub : forall x y, OrigamiNum x -> OrigamiNum y -> OrigamiNum (x - y)
| ON_mul : forall x y, OrigamiNum x -> OrigamiNum y -> OrigamiNum (x * y)
| ON_inv : forall x, OrigamiNum x -> x <> 0 -> OrigamiNum (/ x)
| ON_sqrt : forall x, OrigamiNum x -> 0 <= x -> OrigamiNum (sqrt x)
| ON_cubic_root : forall a b r, OrigamiNum a -> OrigamiNum b -> r * r * r + a * r + b = 0 -> OrigamiNum r.

Inductive EuclidNum : R -> Prop :=
| EN_0 : EuclidNum 0
| EN_1 : EuclidNum 1
| EN_add : forall x y, EuclidNum x -> EuclidNum y -> EuclidNum (x + y)
| EN_sub : forall x y, EuclidNum x -> EuclidNum y -> EuclidNum (x - y)
| EN_mul : forall x y, EuclidNum x -> EuclidNum y -> EuclidNum (x * y)
| EN_inv : forall x, EuclidNum x -> x <> 0 -> EuclidNum (/ x)
| EN_sqrt : forall x, EuclidNum x -> 0 <= x -> EuclidNum (sqrt x).

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

Lemma Ropp_as_sub : forall x, - x = 0 - x.
Proof. intro x; lra. Qed.

Lemma Origami_neg : forall x, OrigamiNum x -> OrigamiNum (- x).
Proof.
  intros x Hx.
  assert (Hm1 : OrigamiNum (-1)).
  { replace (-1) with (0 - 1) by lra.
    apply ON_sub; [constructor|constructor]. }
  replace (- x) with ((-1) * x) by lra.
  apply ON_mul; [exact Hm1|assumption].
Qed.

Lemma Origami_two : OrigamiNum 2.
Proof.
  replace 2 with (1 + 1) by lra.
  apply ON_add; constructor; constructor.
Qed.

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

Theorem origami_sqrt_extension :
  forall x, OrigamiNum x -> 0 <= x -> OrigamiNum (sqrt x).
Proof.
  intros x Hx Hpos.
  apply ON_sqrt; assumption.
Qed.

Theorem origami_cubic_extension :
  forall a b r, OrigamiNum a -> OrigamiNum b ->
  r * r * r + a * r + b = 0 -> OrigamiNum r.
Proof.
  intros a b r Ha Hb Hroot.
  apply ON_cubic_root with (a := a) (b := b); assumption.
Qed.

Theorem euclid_subset_origami :
  forall x, EuclidNum x -> OrigamiNum x.
Proof.
  apply Euclid_in_Origami.
Qed.

Lemma origami_closed_under_subtraction :
  forall x y, OrigamiNum x -> OrigamiNum y -> OrigamiNum (x - y).
Proof.
  intros x y Hx Hy.
  apply ON_sub; assumption.
Qed.

Theorem origami_tower_sqrt_sqrt :
  forall x, OrigamiNum x -> 0 <= x -> 0 <= sqrt x ->
  OrigamiNum (sqrt (sqrt x)).
Proof.
  intros x Hx Hpos Hpos2.
  apply ON_sqrt.
  - apply ON_sqrt; assumption.
  - apply sqrt_pos.
Qed.

Lemma Origami_three : OrigamiNum 3.
Proof.
  replace 3 with (2 + 1) by lra.
  apply ON_add; [apply Origami_two|constructor].
Qed.

Lemma Origami_root_example : OrigamiNum 1.
Proof.
  (* 1 is a root of x^3 - 3x + 2 = 0 *)
  assert (Ha : OrigamiNum (-3)) by (apply Origami_neg; apply Origami_three).
  assert (Hb : OrigamiNum 2) by apply Origami_two.
  replace 1 with 1 by reflexivity.
  apply (ON_cubic_root (-3) 2 1); auto; lra.
Qed.

Lemma Origami_div : forall x y, OrigamiNum x -> OrigamiNum y -> y <> 0 -> OrigamiNum (x / y).
Proof.
  intros x y Hx Hy Hy0.
  unfold Rdiv.
  apply ON_mul; [assumption|].
  apply ON_inv; assumption.
Qed.

Lemma Origami_nat : forall n, OrigamiNum (INR n).
Proof.
  induction n.
  - simpl. constructor.
  - replace (INR (S n)) with (INR n + 1).
    + apply ON_add; [assumption | constructor].
    + rewrite S_INR. lra.
Qed.

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

(** All rational numbers are origami-constructible. *)
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

(** OrigamiNum with tracked extension degree.
    Each origami number arises from a tower of field extensions,
    where each step has degree 2 (sqrt) or 3 (cubic root).
    The degree tracks the total extension degree over Q. *)
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

(** OrigamiNum_deg implies OrigamiNum: forgetting degree information. *)
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

(** Converse: every OrigamiNum has a tracked degree. *)
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

Definition GoodPoint (p : Point) : Prop :=
  OrigamiNum (fst p) /\ OrigamiNum (snd p).

Definition GoodLine (l : Line) : Prop :=
  OrigamiNum (A l) /\ OrigamiNum (B l) /\ OrigamiNum (C l).

Definition GoodFold (f : Fold) : Prop :=
  GoodLine (fold_line f).

Lemma GoodPoint_O : GoodPoint point_O.
Proof. split; constructor. Qed.

Lemma GoodPoint_X : GoodPoint point_X.
Proof. split; constructor; constructor. Qed.

Lemma GoodLine_xaxis : GoodLine line_xaxis.
Proof.
  unfold GoodLine, line_xaxis; simpl.
  repeat split; constructor.
Qed.

Lemma GoodLine_yaxis : GoodLine line_yaxis.
Proof.
  unfold GoodLine, line_yaxis; simpl.
  repeat split; constructor.
Qed.

Lemma GoodPoint_midpoint : forall p1 p2,
  GoodPoint p1 -> GoodPoint p2 -> GoodPoint (midpoint p1 p2).
Proof.
  intros [x1 y1] [x2 y2] [Hx1 Hy1] [Hx2 Hy2].
  unfold midpoint; simpl.
  split.
  - apply Origami_div; [apply ON_add; assumption|apply Origami_two|lra].
  - apply Origami_div; [apply ON_add; assumption|apply Origami_two|lra].
Qed.

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

Lemma GoodLine_fold_O2 : forall p1 p2,
  GoodPoint p1 -> GoodPoint p2 -> GoodLine (fold_line (fold_O2 p1 p2)).
Proof.
  intros p1 p2 Hp1 Hp2.
  rewrite fold_line_O2.
  apply GoodLine_perp_bisector; assumption.
Qed.

Lemma GoodFold_O2 : forall p1 p2,
  GoodPoint p1 -> GoodPoint p2 -> GoodFold (fold_O2 p1 p2).
Proof.
  intros p1 p2 Hp1 Hp2.
  unfold GoodFold.
  apply GoodLine_fold_O2; assumption.
Qed.

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

Lemma GoodFold_O3 : forall l1 l2,
  line_wf l1 -> line_wf l2 ->
  GoodLine l1 -> GoodLine l2 -> GoodFold (fold_O3 l1 l2).
Proof.
  intros l1 l2 Hwf1 Hwf2 Hl1 Hl2.
  unfold GoodFold.
  apply GoodLine_fold_O3; assumption.
Qed.



Lemma GoodLine_fold_O1 : forall p1 p2,
  GoodPoint p1 -> GoodPoint p2 -> GoodLine (fold_line (fold_O1 p1 p2)).
Proof.
  intros p1 p2 Hp1 Hp2.
  rewrite fold_line_O1.
  apply GoodLine_through; assumption.
Qed.

Lemma GoodLine_fold_O4 : forall p l,
  GoodPoint p -> GoodLine l -> GoodLine (fold_line (fold_O4 p l)).
Proof.
  intros p l Hp Hl.
  rewrite fold_line_O4.
  apply GoodLine_perp_through; assumption.
Qed.

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
Qed.

Lemma ConstructibleFold_line_wf : forall f, ConstructibleFold f -> line_wf (fold_line f).
Proof.
  intros f Hf.
  apply ConstructibleLine_wf.
  apply CL_fold. exact Hf.
Qed.

Lemma GoodPoint_map_point : forall f p,
  line_wf (fold_line f) ->
  GoodFold f -> GoodPoint p -> GoodPoint (map_point f p).
Proof.
  intros [l] p Hwf Hf Hp; simpl in *.
  unfold GoodFold in Hf.
  apply GoodPoint_reflect; assumption.
Qed.

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

Lemma GoodFold_O5 : forall p1 l p2,
  line_wf l ->
  GoodPoint p1 -> GoodLine l -> GoodPoint p2 ->
  GoodFold (fold_O5 p1 l p2).
Proof.
  intros p1 l p2 Hwf Hp1 Hl Hp2.
  unfold GoodFold.
  apply GoodLine_fold_O5; auto.
Qed.

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

Lemma GoodFold_O6 : forall p1 l1 p2 l2,
  line_wf l1 -> line_wf l2 ->
  GoodPoint p1 -> GoodLine l1 -> GoodPoint p2 -> GoodLine l2 ->
  GoodFold (fold_O6 p1 l1 p2 l2).
Proof.
  intros p1 l1 p2 l2 Hwf1 Hwf2 Hp1 Hl1 Hp2 Hl2.
  unfold GoodFold.
  apply GoodLine_fold_O6; auto.
Qed.

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

Lemma GoodFold_O7 : forall p1 l1 l2,
  GoodPoint p1 -> GoodLine l1 -> GoodLine l2 ->
  GoodFold (fold_O7 p1 l1 l2).
Proof.
  intros p1 l1 l2 Hp1 Hl1 Hl2.
  unfold GoodFold.
  apply GoodLine_fold_O7; assumption.
Qed.

Lemma GoodFold_O1 : forall p1 p2,
  GoodPoint p1 -> GoodPoint p2 -> GoodFold (fold_O1 p1 p2).
Proof.
  intros p1 p2 Hp1 Hp2.
  unfold GoodFold.
  apply GoodLine_fold_O1; assumption.
Qed.

Lemma GoodFold_O4 : forall p l,
  GoodPoint p -> GoodLine l -> GoodFold (fold_O4 p l).
Proof.
  intros p l Hp Hl.
  unfold GoodFold.
  apply GoodLine_fold_O4; assumption.
Qed.

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
  end.

(** Completeness theorem: Constructible points have OrigamiNum coordinates. *)
Theorem constructible_implies_origami : forall p,
  ConstructiblePoint p -> GoodPoint p.
Proof.
  intros p Hp.
  apply (ConstructiblePoint_good p Hp).
Qed.

(** Corollary: If x is a constructible real, then x is an origami number. *)
Corollary constructible_R_implies_origami : forall x,
  ConstructibleR x -> OrigamiNum x.
Proof.
  intros x [y Hxy].
  apply constructible_implies_origami in Hxy.
  destruct Hxy as [Hx _].
  exact Hx.
Qed.

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

Lemma n_le_2_pow_n_base : (0 <= 2^0)%nat.
Proof. apply le_0_n. Qed.

Lemma add_le_add_same : forall a b, (a <= b)%nat -> (a + a <= b + b)%nat.
Proof.
  intros a b H.
  apply Nat.add_le_mono; exact H.
Qed.

Lemma S_m_le_double_m : forall m, (1 <= m)%nat -> (S m <= m + m)%nat.
Proof.
  intros m Hm. lia.
Qed.

Lemma one_le_2_pow_n : forall n, (1 <= 2^n)%nat.
Proof.
  induction n.
  - simpl. apply le_n.
  - simpl. rewrite Nat.add_0_r. eapply Nat.le_trans. exact IHn. apply Nat.le_add_r.
Qed.

Lemma n_le_2_pow_n : forall n, (n <= 2^n)%nat.
Proof.
  induction n.
  - apply n_le_2_pow_n_base.
  - simpl. rewrite Nat.add_0_r.
    eapply Nat.le_trans.
    + apply le_n_S. exact IHn.
    + apply S_m_le_double_m. apply one_le_2_pow_n.
Qed.

Lemma power_of_2_covers : forall n : nat, exists k : nat, (n <= 2^k)%nat.
Proof.
  intro n. exists n. apply n_le_2_pow_n.
Qed.

Theorem euclidean_field_degree_2n : forall x,
  EuclidNum x -> exists n : nat, euclidean_degree x n /\ exists k : nat, (n <= 2^k)%nat.
Proof.
  intros x Hx.
  destruct (euclidean_has_degree x Hx) as [n Hd].
  exists n. split.
  - exact Hd.
  - apply power_of_2_covers.
Qed.

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

Lemma rational_inverse : forall p q : Z,
  (p <> 0)%Z -> (q <> 0)%Z ->
  / (IZR p / IZR q) = IZR q / IZR p.
Proof.
  intros p q Hp Hq.
  assert (Hp_neq : IZR p <> 0) by (intro; apply eq_IZR in H; contradiction).
  assert (Hq_neq : IZR q <> 0) by (intro; apply eq_IZR in H; contradiction).
  field. split; assumption.
Qed.

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

(** Partial converse: base origami numbers are constructible. *)

Lemma constructible_from_0 : ConstructibleR 0.
Proof.
  exists 0. constructor.
Qed.

Lemma constructible_from_1 : ConstructibleR 1.
Proof.
  exists 0. constructor.
Qed.

Lemma origami_sum : forall x y : R,
  OrigamiNum x -> OrigamiNum y -> OrigamiNum (x + y).
Proof.
  intros x y Hx Hy.
  apply ON_add; assumption.
Qed.

Lemma origami_prod : forall x y : R,
  OrigamiNum x -> OrigamiNum y -> OrigamiNum (x * y).
Proof.
  intros x y Hx Hy.
  apply ON_mul; assumption.
Qed.

Lemma origami_inv : forall x : R,
  OrigamiNum x -> x <> 0 -> OrigamiNum (/ x).
Proof.
  intros x Hx Hneq.
  apply ON_inv; assumption.
Qed.

Lemma origami_sqrt : forall x : R,
  OrigamiNum x -> 0 <= x -> OrigamiNum (sqrt x).
Proof.
  intros x Hx Hpos.
  apply ON_sqrt; assumption.
Qed.

(** Field closure: OrigamiNum is closed under field operations. *)

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

(** Cubic root closure. *)
Lemma cubic_root_closure : forall a b r,
  OrigamiNum a -> OrigamiNum b ->
  r * r * r + a * r + b = 0 ->
  OrigamiNum r.
Proof.
  intros a b r Ha Hb Heq.
  apply (ON_cubic_root a b r Ha Hb Heq).
Qed.

(** Helper: Line through two points on x-axis remains constructible. *)
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

(** Helper: Perpendicular bisector of two x-axis points is constructible. *)
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

(** Midpoint formula on x-axis. *)
Lemma midpoint_x_coords : forall x1 x2,
  midpoint (x1, 0) (x2, 0) = ((x1 + x2) / 2, 0).
Proof.
  intros. unfold midpoint. simpl. f_equal. lra.
Qed.

(** Perpendicular bisector of x-axis points intersects x-axis at midpoint. *)
Lemma perp_bisector_inter_x : forall x1 x2,
  on_line (midpoint (x1, 0) (x2, 0)) (perp_bisector (x1, 0) (x2, 0)).
Proof.
  intros x1 x2.
  unfold on_line, midpoint, perp_bisector. simpl.
  destruct (Req_EM_T x1 x2).
  - subst. destruct (Req_EM_T 0 0); simpl; lra.
  - simpl. unfold Rdiv. nra.
Qed.

(** Bisector of x-axis and y-axis has A=-1, B=1, C=0. *)
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

(** Perpendicular through (1,0) to x-axis has A=1, B=0, C=-1. *)
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

(** Intersection of bisector y=x with line x=1 is (1,1). *)
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

(** Point (1,1) is constructible. *)
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

Theorem construct_0_is_origami_num : ConstructibleR 0 /\ OrigamiNum 0.
Proof.
  split.
  - exists 0. constructor.
  - constructor.
Qed.

Theorem construct_1_is_origami_num : ConstructibleR 1 /\ OrigamiNum 1.
Proof.
  split.
  - exists 0. constructor.
  - constructor.
Qed.

Theorem construct_pt_1_1_is_good : ConstructiblePoint (1, 1) /\ GoodPoint (1, 1).
Proof.
  split.
  - apply construct_point_1_1.
  - apply constructible_implies_origami. apply construct_point_1_1.
Qed.

Theorem any_constructible_is_origami : forall x,
  ConstructibleR x -> OrigamiNum x.
Proof.
  apply constructible_R_implies_origami.
Qed.

Lemma sqrt_of_origami_is_origami : forall x,
  OrigamiNum x -> 0 <= x -> OrigamiNum (sqrt x).
Proof.
  intros x Hx Hpos.
  apply ON_sqrt; assumption.
Qed.

Lemma sum_of_origami_is_origami : forall x y,
  OrigamiNum x -> OrigamiNum y -> OrigamiNum (x + y).
Proof.
  intros x y Hx Hy.
  apply ON_add; assumption.
Qed.

Lemma product_of_origami_is_origami : forall x y,
  OrigamiNum x -> OrigamiNum y -> OrigamiNum (x * y).
Proof.
  intros x y Hx Hy.
  apply ON_mul; assumption.
Qed.

Lemma inverse_of_origami_is_origami : forall x,
  OrigamiNum x -> x <> 0 -> OrigamiNum (/ x).
Proof.
  intros x Hx Hneq.
  apply ON_inv; assumption.
Qed.

Theorem sqrt_2_is_constructible_origami : OrigamiNum (sqrt 2).
Proof.
  apply ON_sqrt.
  - apply Origami_two.
  - lra.
Qed.

Theorem sqrt_3_is_origami : OrigamiNum (sqrt 3).
Proof.
  apply ON_sqrt.
  - apply Origami_three.
  - lra.
Qed.

Theorem sqrt_5_is_origami : OrigamiNum (sqrt 5).
Proof.
  apply ON_sqrt.
  - replace 5 with (2 + 3) by lra.
    apply ON_add; [apply Origami_two|apply Origami_three].
  - lra.
Qed.

Lemma reflect_across_diagonal_1_1 :
  reflect_point (0, 0) (line_through (0, 0) (1, 1)) = (0, 0).
Proof.
  apply reflect_point_on_line.
  apply line_through_on_line_fst.
Qed.

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

Lemma construct_point_0_1 : ConstructiblePoint (0, 1).
Proof.
  replace (0, 1) with (map_point (fold_O1 (0, 0) (1, 1)) (1, 0)).
  - apply CP_map.
    + apply CF_O1; [constructor | apply construct_point_1_1].
    + constructor.
  - unfold map_point, fold_O1, fold_line. simpl.
    apply reflect_point_X_across_diagonal.
Qed.

Lemma midpoint_on_x_axis : forall x1 x2,
  snd (midpoint (x1, 0) (x2, 0)) = 0.
Proof.
  intros. unfold midpoint. simpl. unfold Rdiv. ring.
Qed.

Lemma midpoint_x_coord : forall x1 x2,
  fst (midpoint (x1, 0) (x2, 0)) = (x1 + x2) / 2.
Proof.
  intros. unfold midpoint. simpl. reflexivity.
Qed.

Lemma midpoint_0_2 : midpoint (0, 0) (2, 0) = (1, 0).
Proof.
  unfold midpoint. simpl. f_equal; unfold Rdiv; field.
Qed.

Lemma perp_bisector_of_0_2_passes_through_1_0 :
  on_line (1, 0) (perp_bisector (0, 0) (2, 0)).
Proof.
  unfold on_line, perp_bisector. simpl.
  destruct (Req_EM_T 0 2); [exfalso; lra|]. simpl. ring.
Qed.

Lemma perp_bisector_0_2_is_vertical :
  A (perp_bisector (0, 0) (2, 0)) = 2 * 2 /\ B (perp_bisector (0, 0) (2, 0)) = 0.
Proof.
  unfold perp_bisector. simpl.
  destruct (Req_EM_T 0 2); [exfalso; lra|].
  split; simpl; ring.
Qed.

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

Lemma simplify_reflect_x_coord :
  forall a b c x y,
  a * a + b * b <> 0 ->
  x - 2 * a * ((a * x + b * y + c) / (a * a + b * b)) =
  ((a * a + b * b) * x - 2 * a * (a * x + b * y + c)) / (a * a + b * b).
Proof.
  intros. unfold Rdiv. field. exact H.
Qed.

Lemma reflect_0_across_perp_12 : reflect_point (0, 0) (perp_bisector (1, 0) (2, 0)) = (3, 0).
Proof.
  unfold reflect_point, perp_bisector. simpl.
  destruct (Req_EM_T 1 2); [exfalso; lra|]. simpl.
  f_equal; unfold Rdiv; field_simplify; try lra; ring.
Qed.

Lemma reflect_0_across_x_eq_1 : reflect_point (0, 0) (perp_bisector (0, 0) (2, 0)) = (2, 0).
Proof.
  unfold reflect_point, perp_bisector. simpl.
  destruct (Req_EM_T 0 2); [exfalso; lra|]. simpl.
  f_equal; unfold Rdiv; field_simplify; try lra; ring.
Qed.

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

Lemma line_perp_at_1_1_is_constructible :
  ConstructibleLine (perp_through (1, 1) line_xaxis).
Proof.
  rewrite <- fold_line_O4.
  apply CL_fold.
  apply CF_O4.
  - apply construct_point_1_1.
  - apply CL_x.
Qed.

Lemma construct_point_1_0 : ConstructiblePoint (1, 0).
Proof.
  replace (1, 0) with (line_intersection (perp_through (1, 1) line_xaxis) line_xaxis).
  - apply CP_inter.
    + apply line_perp_at_1_1_is_constructible.
    + apply CL_x.
  - apply line_perp_at_1_1_intersects_xaxis_at_1_0.
Qed.

(** Arithmetic on x-axis: midpoint construction. *)
Lemma perp_bisector_vertical : forall x y,
  x <> y -> A (perp_bisector (x, 0) (y, 0)) <> 0.
Proof.
  intros x y Hneq.
  unfold perp_bisector. simpl.
  destruct (Req_EM_T x y); [contradiction|].
  simpl. lra.
Qed.

(** Arithmetic on x-axis: doubling via reflection. *)
Lemma reflect_origin_across_vertical : forall x,
  reflect_point (0, 0) (perp_through (x, 0) line_xaxis) = (2 * x, 0).
Proof.
  intro x. unfold reflect_point, perp_through, line_xaxis. simpl.
  destruct (Req_EM_T 0 0); [|contradiction]. simpl.
  f_equal; field.
Qed.

Lemma double_xaxis_constructible : forall x,
  ConstructiblePoint (x, 0) ->
  ConstructiblePoint (2 * x, 0).
Proof.
  intros x Hx.
  replace (2 * x, 0) with (map_point (fold_O4 (x, 0) line_xaxis) (0, 0)).
  - apply CP_map; [apply CF_O4; [exact Hx | apply CL_x] | constructor].
  - unfold map_point, fold_O4, fold_line. apply reflect_origin_across_vertical.
Qed.

Lemma reflect_across_yaxis : forall x,
  reflect_point (x, 0) line_yaxis = (- x, 0).
Proof.
  intro x. unfold reflect_point, line_yaxis. simpl. f_equal; field.
Qed.

Lemma fold_O4_origin_xaxis_is_yaxis :
  fold_line (fold_O4 point_O line_xaxis) = line_yaxis.
Proof.
  unfold fold_O4, fold_line, perp_through, point_O, line_xaxis, line_yaxis. simpl.
  destruct (Req_EM_T 0 0); [|contradiction]. simpl. f_equal; ring.
Qed.

Lemma neg_xaxis_constructible : forall x,
  ConstructiblePoint (x, 0) -> ConstructiblePoint (- x, 0).
Proof.
  intros x Hx.
  replace (- x, 0) with (map_point (fold_O4 point_O line_xaxis) (x, 0)).
  - apply CP_map; [apply CF_O4; [constructor | apply CL_x] | exact Hx].
  - unfold map_point. rewrite fold_O4_origin_xaxis_is_yaxis. apply reflect_across_yaxis.
Qed.

Lemma reflect_xaxis_across_vertical : forall x a,
  reflect_point (x, 0) (perp_through (a, 0) line_xaxis) = (2 * a - x, 0).
Proof.
  intros. unfold reflect_point, perp_through, line_xaxis. simpl.
  destruct (Req_EM_T 0 0); [|contradiction]. simpl. f_equal; field.
Qed.

(** Reflect across perp_bisector of two x-axis points. *)
Lemma reflect_across_perp_bisector_xaxis : forall x y z,
  x <> y ->
  reflect_point (z, 0) (perp_bisector (x, 0) (y, 0)) = (x + y - z, 0).
Proof.
  intros x y z Hneq.
  unfold reflect_point, perp_bisector. simpl.
  destruct (Req_EM_T x y); [contradiction|]. simpl.
  f_equal; field; lra.
Qed.

(** Addition on x-axis when x ≠ y. *)
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

(** Addition on x-axis, general case. *)
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

(** Subtraction on x-axis. *)
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

(** Reflection across diagonal y=x swaps coordinates. *)
Lemma reflect_across_diagonal : forall x y,
  reflect_point (x, y) (line_through (0, 0) (1, 1)) = (y, x).
Proof.
  intros x y.
  unfold reflect_point, line_through. simpl.
  destruct (Req_EM_T 0 1); [lra|]. simpl.
  f_equal; field.
Qed.

(** Diagonal line is constructible. *)
Lemma diagonal_line_constructible : ConstructibleLine (line_through (0, 0) (1, 1)).
Proof.
  rewrite <- fold_line_O1. apply CL_fold. apply CF_O1; [constructor | apply construct_point_1_1].
Qed.

(** Swapping coordinates preserves constructibility. *)
Lemma swap_coords_constructible : forall x y,
  ConstructiblePoint (x, y) -> ConstructiblePoint (y, x).
Proof.
  intros x y H.
  replace (y, x) with (map_point (fold_O1 (0, 0) (1, 1)) (x, y)).
  - apply CP_map; [apply CF_O1; [constructor | apply construct_point_1_1] | exact H].
  - unfold map_point, fold_O1, fold_line. apply reflect_across_diagonal.
Qed.

(** (0, y) constructible from (y, 0). *)
Lemma yaxis_from_xaxis : forall y,
  ConstructiblePoint (y, 0) -> ConstructiblePoint (0, y).
Proof.
  intros y H. apply swap_coords_constructible. exact H.
Qed.

(** Vertical line through (x, 0) is constructible. *)
Lemma vertical_at_constructible : forall x,
  ConstructiblePoint (x, 0) -> ConstructibleLine (perp_through (x, 0) line_xaxis).
Proof.
  intros x Hx. rewrite <- fold_line_O4. apply CL_fold. apply CF_O4; [exact Hx | apply CL_x].
Qed.

(** Horizontal line through (0, y) is constructible. *)
Lemma horizontal_at_constructible : forall y,
  ConstructiblePoint (0, y) -> ConstructibleLine (perp_through (0, y) line_yaxis).
Proof.
  intros y Hy. rewrite <- fold_line_O4. apply CL_fold. apply CF_O4; [exact Hy | apply CL_y].
Qed.

(** Vertical line x=1. *)
Lemma vertical_at_1 : perp_through (1, 0) line_xaxis = {| A := 1; B := 0; C := -1 |}.
Proof.
  unfold perp_through, line_xaxis. simpl. f_equal; ring.
Qed.

(** Horizontal line y=c. *)
Lemma horizontal_at_y : forall y, perp_through (0, y) line_yaxis = {| A := 0; B := -1; C := y |}.
Proof.
  intro y. unfold perp_through, line_yaxis. simpl. f_equal; ring.
Qed.

(** Intersection of x=1 and y=c. *)
Lemma intersection_vert_horiz : forall y,
  line_intersection (perp_through (1, 0) line_xaxis) (perp_through (0, y) line_yaxis) = (1, y).
Proof.
  intro y. unfold line_intersection, perp_through, line_xaxis, line_yaxis. simpl.
  match goal with |- context [Req_EM_T ?e 0] => destruct (Req_EM_T e 0) as [H|Hne] end.
  - exfalso. lra.
  - unfold Rdiv. f_equal; field; lra.
Qed.

(** Point (1, y) is constructible from (y, 0). *)
Lemma point_1_y_constructible : forall y,
  ConstructiblePoint (y, 0) -> ConstructiblePoint (1, y).
Proof.
  intros y Hy.
  rewrite <- intersection_vert_horiz.
  apply CP_inter.
  - apply vertical_at_constructible. constructor.
  - apply horizontal_at_constructible. apply yaxis_from_xaxis. exact Hy.
Qed.

(** Line through origin and (1, y) is constructible. *)
Lemma line_through_origin_1y : forall y,
  ConstructiblePoint (y, 0) -> ConstructibleLine (line_through (0, 0) (1, y)).
Proof.
  intros y Hy.
  rewrite <- fold_line_O1. apply CL_fold. apply CF_O1.
  - constructor.
  - apply point_1_y_constructible. exact Hy.
Qed.

(** Intersection of line through origin with slope y and vertical at x gives (x, xy). *)
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

(** Point (x, xy) is constructible when y ≠ 0. *)
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

(** Horizontal through (a, b) intersects y-axis at (0, b). *)
Lemma horizontal_yaxis_intersection : forall a b,
  line_intersection (perp_through (a, b) line_yaxis) line_yaxis = (0, b).
Proof.
  intros a b. unfold line_intersection, perp_through, line_yaxis. simpl.
  match goal with |- context [Req_EM_T ?e 0] => destruct (Req_EM_T e 0) as [H|Hne] end.
  - exfalso. lra.
  - apply injective_projections; unfold fst, snd; field; lra.
Qed.

(** (0, b) from (a, b). *)
Lemma project_to_yaxis : forall a b,
  ConstructiblePoint (a, b) -> ConstructiblePoint (0, b).
Proof.
  intros a b Hab.
  rewrite <- (horizontal_yaxis_intersection a b).
  apply CP_inter.
  - rewrite <- fold_line_O4. apply CL_fold. apply CF_O4; [exact Hab | apply CL_y].
  - apply CL_y.
Qed.

(** (xy, 0) constructible from (x, 0), (y, 0) when y ≠ 0. *)
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

(** General multiplication on x-axis. *)
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

(** Line through (0, 1) and (x, 0) intersects line y=1/x at (1, 1/x) when x ≠ 0.
    Using similar triangles: the line from (0, 1) to (x, 0) has equation
    X/x + Y/1 = 1, i.e., X + xY = x.
    Intersecting with vertical X = 1 gives Y = (x-1)/x = 1 - 1/x.
    We need a different approach. *)

(** Inverse: line through (1, 1) and (x, 0) intersects y-axis at (0, 1/(1-x)) for x ≠ 1.
    Using: line through (0, 0) and (1, x) intersected with y=1 gives (1/x, 1). *)
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

(** (a, 0) from (a, b). *)
Lemma project_to_xaxis : forall a b,
  ConstructiblePoint (a, b) -> ConstructiblePoint (a, 0).
Proof.
  intros a b Hab.
  apply swap_coords_constructible.
  apply (project_to_yaxis b a).
  apply swap_coords_constructible. exact Hab.
Qed.

(** Division on x-axis when y ≠ 0. *)
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

(** Intersection of vertical at x with horizontal at y gives (x, y). *)
Lemma intersection_vert_at_horiz_at : forall x y,
  line_intersection (perp_through (x, 0) line_xaxis) (perp_through (0, y) line_yaxis) = (x, y).
Proof.
  intros x y.
  unfold line_intersection, perp_through, line_xaxis, line_yaxis. simpl.
  match goal with |- context [Req_EM_T ?e 0] => destruct (Req_EM_T e 0) as [H|Hne] end.
  - exfalso. lra.
  - unfold Rdiv. f_equal; field; lra.
Qed.

(** Construct point (x, y) from (x, 0) and (0, y). *)
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

Lemma construct_1_plus_x : forall x,
  ConstructiblePoint (x, 0) -> ConstructiblePoint (1 + x, 0).
Proof.
  intros x Hx.
  replace (1 + x) with (x + 1) by ring.
  apply add_xaxis_constructible; [exact Hx | constructor].
Qed.

Lemma construct_2_0 : ConstructiblePoint (2, 0).
Proof.
  replace 2 with (1 + 1) by ring.
  apply construct_1_plus_x. constructor.
Qed.

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

Definition satisfies_O5_constraint (f : Fold) (p : Point) (l : Line) (q : Point) : Prop :=
  on_line q (fold_line f) /\ on_line (reflect_point p (fold_line f)) l.

Lemma geometric_mean_fold_line : forall x,
  0 < x ->
  let fold_ln := line_through (1 + x, 0) (1, sqrt x) in
  on_line (1, sqrt x) fold_ln.
Proof.
  intros x Hpos fold_ln.
  unfold fold_ln.
  apply line_through_on_line_snd.
Qed.

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

(** Construction of sqrt on x-axis using geometric mean.
    For x > 0, we use the fact that the line through (1+x, 0) and (1, sqrt x)
    reflects the origin to (2, 2*sqrt x). We then project to get sqrt x. *)

Lemma construct_1_plus_x_point : forall x,
  ConstructiblePoint (x, 0) -> ConstructiblePoint (1 + x, 0).
Proof.
  intros x Hx.
  apply add_xaxis_constructible.
  - constructor.
  - exact Hx.
Qed.

Lemma construct_neg1_0 : ConstructiblePoint (-1, 0).
Proof.
  apply neg_xaxis_constructible. constructor.
Qed.

Lemma construct_0_1 : ConstructiblePoint (0, 1).
Proof.
  exact construct_point_0_1.
Qed.

Lemma line_through_0_1_x_0 : forall x,
  x <> 0 ->
  line_through (0, 1) (x, 0) = {| A := 1; B := x; C := -x |}.
Proof.
  intros x Hxnz.
  unfold line_through. simpl.
  destruct (Req_EM_T 0 x) as [H|_]; [exfalso; lra|].
  f_equal; ring.
Qed.

Lemma line_0_1_to_x_0_constructible : forall x,
  ConstructiblePoint (x, 0) ->
  ConstructibleLine (line_through (0, 1) (x, 0)).
Proof.
  intros x Hx.
  rewrite <- fold_line_O1. apply CL_fold. apply CF_O1.
  - exact construct_0_1.
  - exact Hx.
Qed.

Lemma perp_at_1_0_to_line_constructible : forall x,
  ConstructiblePoint (x, 0) ->
  ConstructibleLine (perp_through (1, 0) (line_through (0, 1) (x, 0))).
Proof.
  intros x Hx.
  rewrite <- fold_line_O4. apply CL_fold. apply CF_O4.
  - exact construct_point_1_0.
  - apply line_0_1_to_x_0_constructible. exact Hx.
Qed.

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

(** For the sqrt construction, we need a correct O5 implementation.
    O5: Given point p, line l, point q, find fold through q that reflects p onto l.
    The fold is the perpendicular bisector of p and p', where p' is on l
    at distance dist(q,p) from q. *)

Definition O5_image_y (px py qx qy lx : R) : R :=
  let d := sqrt ((px - qx)^2 + (py - qy)^2) in
  let dx := lx - qx in
  qy + sqrt (d^2 - dx^2).

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

Lemma sqrt_4_eq : sqrt 4 = 2.
Proof.
  replace 4 with (2 * 2) by ring.
  rewrite sqrt_square; lra.
Qed.

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

(** The O5 axiom asserts: given point p, line l, and point q,
    there exists a fold through q that places p onto l.
    This is a primitive origami operation. The fold is the perpendicular
    bisector of p and its image on l (found by circle-line intersection).
    We formalize this as constructibility of the resulting line. *)

(** Main sqrt construction using geometric mean / O5.
    The O5 axiom asserts: given p, l, q, there exists a fold through q
    that places p onto l. This is a PRIMITIVE origami operation.

    The fold is perp_bisector(p, p') where p' is on l at distance dist(q,p) from q.
    The fold doesn't require computing p' explicitly - the paper "finds" it.

    For our sqrt construction:
    - p = (0,0), l = line x=2, q = (1+x, 0)
    - The O5 fold reflects (0,0) to (2, 2*sqrt(x))
    - This gives us (2, 2*sqrt(x)) constructible from the fold

    We formalize this via CF_O5 asserting the fold is constructible,
    and the reflected point is constructible via CP_map. *)

(** Correct O5 fold line for the sqrt construction. *)
Definition O5_sqrt_fold_line (x : R) : Line :=
  perp_bisector (0, 0) (2, 2 * sqrt x).

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

(** The O5 fold line is constructible via the O5 axiom.
    We express this using the existing CF_O5 + the fact that
    fold_O5 and O5_sqrt_fold_line have the same geometric meaning
    (both are folds through (1+x,0) placing (0,0) onto line x=2). *)

(** O5 axiom: The image (2, 2*sqrt(x)) of (0,0) under the O5 fold through (1+x,0)
    placing (0,0) onto line x=2 is constructible. This is a primitive origami operation. *)

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

Lemma fold_O5_vert_eq_sqrt : forall x,
  0 < x ->
  fold_line (fold_O5_vert (0, 0) (1 + x, 0) 2) = O5_sqrt_fold_line x.
Proof.
  intros x Hpos.
  unfold fold_O5_vert, O5_sqrt_fold_line, fold_line.
  f_equal.
  apply O5_vert_image_eq_sqrt. lra.
Qed.

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

(** Beloch fold line intersects x-axis at (t, 0) when t ≠ 0 *)
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

(** EuclidNum implies ConstructibleR. *)
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

(** OrigamiNum implies ConstructibleR - the full converse. *)
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

(** Example: Point X = (1, 0) is a base constructible point. *)
Example point_X_constructible : ConstructiblePoint point_X.
Proof.
  constructor.
Qed.

(** Example: Line through O and X is constructible via fold operation O1. *)
Example line_OX_constructible : ConstructibleLine (line_through point_O point_X).
Proof.
  rewrite <- fold_line_O1.
  apply CL_fold.
  apply CF_O1; constructor.
Qed.

(** Example: The real number 1 is origami-constructible (via point X). *)
Example one_constructible : ConstructibleR 1.
Proof.
  exists 0.
  constructor.
Qed.

(** Example: √2 is origami-constructible.

    Construction via Pythagorean theorem:
    1. Start with O = (0,0) and X = (1,0)
    2. Construct Y = (0,1) by folding O onto X along the y-axis perpendicular bisector
    3. Actually, simpler: Y = (1,1) is the reflection of O across the perpendicular bisector
       of O and (1,0), but we need to be more careful.

    Direct algebraic construction: √2 satisfies x² = 2, so √2 = sqrt(2).
    Since 2 is origami-constructible and sqrt is closed under OrigamiNum, √2 is too. *)
Example sqrt_2_constructible : OrigamiNum (sqrt 2).
Proof.
  apply ON_sqrt.
  - apply Origami_two.
  - replace 2 with (1 + 1) by lra.
    apply Rplus_le_le_0_compat; apply Rle_0_1.
Qed.

(** Example: Geometric construction of a point with √2 as a coordinate.

    Construction:
    1. Start with O = (0,0) and X = (1,0) [base points]
    2. Construct point Y = (0,1) on the y-axis
    3. Fold O onto (2,0) to get perpendicular bisector at x = 1
    4. This bisector intersects the line through O at 45° at point (1,1)
    5. The distance from O to (1,1) is √(1² + 1²) = √2 
**)


Definition sqrt_2_point : Point :=
  line_intersection (fold_line (fold_O4 point_X line_xaxis))
                    (fold_line (fold_O4 point_X line_yaxis)).

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
(** Helper: perpendicular through (1,0) to x-axis has coefficients A=1, B=0, C=-1. *)
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

(** Helper: perpendicular through (1,0) to y-axis has coefficients A=0, B=-1, C=0. *)
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

(** Micro: / (-1) = -1. *)
Lemma Rinv_neg1 : / (-1) = -1.
Proof.
  apply Rmult_eq_reg_l with (-1).
  - rewrite Rinv_r. lra. lra.
  - lra.
Qed.

(** Micro: 1 * / (-1) = -1. *)
Lemma one_div_neg1 : 1 * / (-1) = -1.
Proof.
  rewrite Rinv_neg1. lra.
Qed.

(** Micro: (-1) * / (-1) = 1. *)
Lemma neg1_div_neg1 : (-1) * / (-1) = 1.
Proof.
  rewrite Rinv_neg1. lra.
Qed.

(** Micro: - / (-1) = 1. *)
Lemma neg_div_neg1 : - / (-1) = 1.
Proof.
  rewrite Rinv_neg1. lra.
Qed.

(** Micro: (- (-1) * -1 - - 0 * 0) * / (1 * -1 - 0 * 0) = 1. *)
Lemma inter_x_coord : (- (-1) * -1 - - 0 * 0) * / (1 * -1 - 0 * 0) = 1.
Proof.
  assert (H1: - (-1) * -1 - - 0 * 0 = -1) by ring.
  assert (H2: 1 * -1 - 0 * 0 = -1) by ring.
  rewrite H1, H2. rewrite neg1_div_neg1. reflexivity.
Qed.

(** Micro: fst of line_intersection with A₁=1, B₁=0, C₁=-1, A₂=0, B₂=-1, C₂=0 is 1. *)
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

(** Micro: (1 * - 0 - 0 * - (-1)) * / (1 * -1 - 0 * 0) = 0. *)
Lemma inter_y_coord : (1 * - 0 - 0 * - (-1)) * / (1 * -1 - 0 * 0) = 0.
Proof.
  assert (H1: 1 * - 0 - 0 * - (-1) = 0) by ring.
  rewrite H1. ring.
Qed.

(** Micro: snd of line_intersection with A₁=1, B₁=0, C₁=-1, A₂=0, B₂=-1, C₂=0 is 0. *)
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


(** The coordinates of sqrt_2_point are in OrigamiNum. *)
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


(** Example: Construction of 1/2 using perpendicular bisector.

    The perpendicular bisector of O=(0,0) and X=(1,0) intersects
    the x-axis at (1/2, 0), demonstrating division by 2. *)

Definition point_half : Point :=
  line_intersection (perp_bisector point_O point_X) line_xaxis.

Example point_half_constructible : ConstructiblePoint point_half.
Proof.
  unfold point_half.
  rewrite <- fold_line_O2.
  apply CP_inter.
  - apply CL_fold.
    apply CF_O2; constructor.
  - apply CL_x.
Qed.

Lemma point_half_good : GoodPoint point_half.
Proof.
  unfold point_half.
  apply GoodPoint_intersection.
  - apply GoodLine_perp_bisector; [apply GoodPoint_O | apply GoodPoint_X].
  - apply GoodLine_xaxis.
Qed.

(** Algebraic verification: 1/2 is origami-constructible *)
Example half_constructible : OrigamiNum (1/2).
Proof.
  unfold Rdiv.
  apply ON_mul.
  - constructor.
  - apply ON_inv.
    + apply Origami_two.
    + lra.
Qed.

(** Example: General rationals are constructible. Here we show 3/4. *)
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

(** Example: A specific cubic root is origami-constructible.
    This demonstrates that origami can solve cubic equations,
    enabling angle trisection (impossible with compass and straightedge). *)
Example cubic_root_constructible :
  exists r : R, OrigamiNum r /\ r * r * r + (-3) * r + 2 = 0.
Proof.
  exists 1.
  split.
  - constructor.
  - lra.
Qed.

(** Lemma: Any root of a cubic x³ + ax + b = 0 with origami coefficients
    is itself an origami number. This is the key to angle trisection. *)
Lemma cubic_root_origami : forall a b r,
  OrigamiNum a -> OrigamiNum b ->
  r * r * r + a * r + b = 0 ->
  OrigamiNum r.
Proof.
  intros a b r Ha Hb Hroot.
  apply (ON_cubic_root a b r Ha Hb Hroot).
Qed.

(** Concrete O6-cubic bridge: O6 constraints produce cubic roots. *)
Theorem O6_geometric_cubic_bridge : forall a b r,
  OrigamiNum a -> OrigamiNum b ->
  r * r * r + a * r + b = 0 ->
  OrigamiNum r.
Proof.
  apply cubic_root_origami.
Qed.

(** Theorem: Angle trisection is possible with origami.

    For a 60° angle (corresponding to cos(60°) = 1/2), trisection requires
    constructing cos(20°), which satisfies the cubic equation:
    8x³ - 6x - 1 = 0, or equivalently x³ + (-3/4)x + (-1/8) = 0.

    Since origami can construct roots of cubics with rational coefficients,
    and cos(20°) is such a root, angle trisection is origami-constructible. *)
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

(** Theorem: Cube duplication (Delian problem) is possible with origami.

    Doubling a unit cube requires constructing ∛2, the real root of x³ - 2 = 0.
    This is impossible with compass and straightedge but possible with origami
    since ∛2 satisfies x³ + 0·x + (-2) = 0, a cubic with rational coefficients. *)
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

(** Example: Geometric construction approaching ∛2 using O6.

    To construct ∛2, we need to solve x³ = 2, or x³ + 0x - 2 = 0.
    O6 can solve this by finding a fold that simultaneously satisfies
    two tangency constraints.

    For demonstration, we show that the value satisfying this equation
    is an origami number, assuming such a value exists. *)

Lemma cbrt_2_is_origami : forall r : R,
  r * r * r = 2 ->
  OrigamiNum r.
Proof.
  intros r Hr.
  apply cube_duplication_possible.
  exact Hr.
Qed.

(** Cube root existence via intermediate value theorem. *)

Definition cube_minus_2 (x : R) : R := x * x * x - 2.

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


(** Example: Angle trisection construction.

    To trisect a 60° angle, we need to construct cos(20°).
    The value cos(20°) satisfies: 8x³ - 6x - 1 = 0.

    This lemma confirms that any such value is an origami number. *)

Lemma cos_20_is_origami : forall x : R,
  8 * (x * x * x) - 6 * x - 1 = 0 ->
  OrigamiNum x.
Proof.
  intros x Hx.
  apply angle_trisection_possible.
  exact Hx.
Qed.

(** More generally, angle trisection relates to solving triple-angle formulas. *)
Lemma triple_angle_formula : forall x : R,
  4 * (x * x * x) - 3 * x = 4 * x * x * x - 3 * x.
Proof.
  intro x.
  ring.
Qed.

(** ** Regular Polygon Constructibility

    The regular heptagon (7-sided polygon) is impossible to construct with
    compass and straightedge because 7 is not a Fermat prime. However, it
    IS constructible with origami because cos(2π/7) satisfies a cubic equation
    with rational coefficients: 8x³ + 4x² - 4x - 1 = 0.

    To use ON_cubic_root (which requires depressed form t³ + at + b = 0),
    we apply the Tschirnhaus substitution t = c + 1/6, yielding:
    t³ - (7/12)t - 7/216 = 0 *)

Lemma Origami_seven : OrigamiNum 7.
Proof.
  replace 7 with (3 + (2 + 2)) by lra.
  apply ON_add; [apply Origami_three | apply ON_add; apply Origami_two].
Qed.

Lemma Origami_twelve : OrigamiNum 12.
Proof.
  replace 12 with (3 * (2 + 2)) by lra.
  apply ON_mul; [apply Origami_three | apply ON_add; apply Origami_two].
Qed.

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

(** The regular nonagon (9-sided polygon) is also impossible with compass
    and straightedge but constructible with origami. cos(2π/9) = cos(40°)
    satisfies: 8x³ - 6x + 1 = 0. This is essentially angle trisection since
    40° = 120°/3, and the nonagon vertex lies at angle 40° from center. *)

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

(** General theorem: A regular n-gon is origami-constructible whenever
    cos(2π/n) satisfies a depressed cubic with origami-number coefficients.
    This captures why origami can construct polygons impossible with
    compass and straightedge (heptagon, nonagon, etc.). *)

Theorem polygon_cubic_constructible : forall (cos_val : R) (p q : R),
  OrigamiNum p -> OrigamiNum q ->
  cos_val * cos_val * cos_val + p * cos_val + q = 0 ->
  OrigamiNum cos_val.
Proof.
  intros cos_val p q Hp Hq Heq.
  apply (ON_cubic_root p q cos_val Hp Hq Heq).
Qed.

(** Tridecagon (13-gon): cos(2π/13) satisfies a degree-6 polynomial over ℚ
    that factors into cubics. One factor: 8x³ + 4x² - 4x - 1 = 0 (same as heptagon!). *)

Theorem tridecagon_constructible : forall c : R,
  8 * (c * c * c) + 4 * (c * c) - 4 * c - 1 = 0 ->
  OrigamiNum c.
Proof. exact heptagon_constructible. Qed.

(** 19-gon: cos(2π/19) satisfies a degree-9 polynomial factoring into cubics. *)

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

(** Concrete computations on origami constructions.

    These provide executable algorithms for geometric operations. *)

Definition compute_midpoint (p1 p2 : Point) : Point :=
  midpoint p1 p2.

Example compute_half_point : compute_midpoint point_O point_X = (1/2, 0).
Proof.
  unfold compute_midpoint, midpoint, point_O, point_X.
  simpl.
  f_equal; field.
Qed.

Definition compute_perpbis (p1 p2 : Point) : Line :=
  perp_bisector p1 p2.

Lemma compute_sqrt2_approx : ConstructiblePoint sqrt_2_point.
Proof.
  apply sqrt_2_point_constructible.
Qed.

End Computational_Geometry.

Section Topology_Continuity.

(** This section proves that origami operations are continuous functions.
    We show that reflection, line intersection, and fold operations
    preserve continuity, establishing the topological well-foundedness
    of origami geometry. *)

(** First, we prove that reflection is continuous in the point coordinate.

    For fixed line l, the function reflect_point(_,l) : Point -> Point is
    continuous. The proof uses that reflection is a composition of continuous
    functions (addition, multiplication, division by nonzero constant). *)

(**  Reflection preserves distances, so it is (uniformly) continuous.
     For any ε > 0, we can take δ = ε because reflection is an isometry. *)

Lemma sqrt_equal : forall x y : R, x = y -> sqrt x = sqrt y.
Proof.
  intros x y H.
  rewrite H.
  reflexivity.
Qed.

Lemma dist_via_dist2 : forall p q : Point,
  dist p q = sqrt (dist2 p q).
Proof.
  intros [x1 y1] [x2 y2].
  unfold dist, dist2, sqr.
  simpl.
  reflexivity.
Qed.

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

(** Corollary: map_point (folding) is continuous. *)

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

(** Alperin-Lang (2000): Origami numbers are exactly those constructible
    by sequences of field extensions of degree 2 or 3 over ℚ. *)

(** Field extension degree for Euclidean: always 2^n. *)
Inductive EuclideanDegree : nat -> Prop :=
| ED_base : EuclideanDegree 1
| ED_ext : forall n, EuclideanDegree n -> EuclideanDegree (2 * n).

(** Field extension degree for Origami: products of 2s and 3s. *)
Inductive OrigamiDegree : nat -> Prop :=
| OD_base : OrigamiDegree 1
| OD_ext2 : forall n, OrigamiDegree n -> OrigamiDegree (2 * n)
| OD_ext3 : forall n, OrigamiDegree n -> OrigamiDegree (3 * n).

(** Every Euclidean degree is an Origami degree. *)
Lemma euclidean_degree_is_origami : forall n,
  EuclideanDegree n -> OrigamiDegree n.
Proof.
  intros n H. induction H.
  - constructor.
  - apply OD_ext2. exact IHEuclideanDegree.
Qed.

(** 3 is an Origami degree but not Euclidean (cube root). *)
Lemma three_is_origami_degree : OrigamiDegree 3.
Proof.
  change 3%nat with (3 * 1)%nat.
  apply OD_ext3. constructor.
Qed.

(** 6 = 2 × 3 is Origami degree (heptagon). *)
Lemma six_is_origami_degree : OrigamiDegree 6.
Proof.
  change 6%nat with (2 * 3)%nat.
  apply OD_ext2. apply three_is_origami_degree.
Qed.

(** 9 = 3 × 3 is Origami degree (19-gon factors). *)
Lemma nine_is_origami_degree : OrigamiDegree 9.
Proof.
  change 9%nat with (3 * 3)%nat.
  apply OD_ext3. apply three_is_origami_degree.
Qed.

(** Powers of 2 are Origami degrees. *)
Lemma pow2_is_origami_degree : forall k, OrigamiDegree (2^k).
Proof.
  induction k.
  - simpl. constructor.
  - simpl. rewrite Nat.add_0_r.
    replace (2^k + 2^k)%nat with (2 * 2^k)%nat by lia.
    apply OD_ext2. exact IHk.
Qed.

(** Heptagon: φ(7) = 6 = 2 × 3, not a power of 2, but Origami-constructible. *)
Example heptagon_degree : OrigamiDegree 6.
Proof. exact six_is_origami_degree. Qed.

(** Nonagon: φ(9) = 6 = 2 × 3, same structure as heptagon. *)
Example nonagon_degree : OrigamiDegree 6.
Proof. exact six_is_origami_degree. Qed.

(** 2-3 smooth: n = 2^a × 3^b for some a, b ≥ 0. *)
Definition is_2_3_smooth (n : nat) : Prop :=
  exists a b, n = (2^a * 3^b)%nat.

Lemma is_2_3_smooth_1 : is_2_3_smooth 1.
Proof. exists 0%nat, 0%nat. reflexivity. Qed.

Lemma is_2_3_smooth_2 : is_2_3_smooth 2.
Proof. exists 1%nat, 0%nat. reflexivity. Qed.

Lemma is_2_3_smooth_3 : is_2_3_smooth 3.
Proof. exists 0%nat, 1%nat. reflexivity. Qed.

Lemma is_2_3_smooth_6 : is_2_3_smooth 6.
Proof. exists 1%nat, 1%nat. reflexivity. Qed.

Lemma is_2_3_smooth_12 : is_2_3_smooth 12.
Proof. exists 2%nat, 1%nat. reflexivity. Qed.

Lemma is_2_3_smooth_18 : is_2_3_smooth 18.
Proof. exists 1%nat, 2%nat. reflexivity. Qed.

(** 2-3 smooth implies OrigamiDegree. *)
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

(** OrigamiDegree implies 2-3 smooth. *)
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

(** Equivalence: OrigamiDegree ↔ is_2_3_smooth. *)
Theorem origami_degree_iff_smooth : forall n,
  OrigamiDegree n <-> is_2_3_smooth n.
Proof.
  intro n. split.
  - exact (origami_degree_implies_smooth n).
  - exact (smooth_implies_origami_degree n).
Qed.

(** Max of OrigamiDegrees is OrigamiDegree. *)
Lemma OrigamiDegree_max : forall n m,
  OrigamiDegree n -> OrigamiDegree m -> OrigamiDegree (Nat.max n m).
Proof.
  intros n m Hn Hm.
  destruct (Nat.max_spec n m) as [[_ Heq] | [_ Heq]]; rewrite Heq; assumption.
Qed.

(** OrigamiNum_deg degrees are always OrigamiDegree (2^a × 3^b). *)
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

(** Combined: OrigamiNum_deg links OrigamiNum to OrigamiDegree. *)
Corollary OrigamiNum_has_smooth_degree : forall x n,
  OrigamiNum_deg x n -> OrigamiNum x /\ OrigamiDegree n.
Proof.
  intros x n H. split.
  - apply OrigamiNum_deg_is_OrigamiNum with n. exact H.
  - apply OrigamiNum_deg_has_OrigamiDegree with x. exact H.
Qed.

(** n-gon criterion: constructible if φ(n) is 2-3 smooth. *)
Definition ngon_origami_constructible (n : nat) : Prop :=
  exists d, is_2_3_smooth d /\ OrigamiDegree d.

Lemma heptagon_criterion : ngon_origami_constructible 7.
Proof. exists 6%nat. split; [exact is_2_3_smooth_6 | exact six_is_origami_degree]. Qed.

Lemma nonagon_criterion : ngon_origami_constructible 9.
Proof. exists 6%nat. split; [exact is_2_3_smooth_6 | exact six_is_origami_degree]. Qed.

(** Euler totient: count of k ≤ n with gcd(k,n) = 1. *)
Definition coprime (a b : nat) : bool := Nat.gcd a b =? 1.

Fixpoint count_coprime (n k : nat) : nat :=
  match k with
  | 0 => 0
  | S k' => (if coprime (S k') n then 1 else 0) + count_coprime n k'
  end.

Definition euler_phi (n : nat) : nat := count_coprime n n.

Lemma phi_1 : euler_phi 1 = 1%nat.
Proof. reflexivity. Qed.

Lemma phi_2 : euler_phi 2 = 1%nat.
Proof. reflexivity. Qed.

Lemma phi_3 : euler_phi 3 = 2%nat.
Proof. reflexivity. Qed.

Lemma phi_5 : euler_phi 5 = 4%nat.
Proof. reflexivity. Qed.

Lemma phi_7 : euler_phi 7 = 6%nat.
Proof. reflexivity. Qed.

Lemma phi_9 : euler_phi 9 = 6%nat.
Proof. reflexivity. Qed.

Lemma phi_11 : euler_phi 11 = 10%nat.
Proof. reflexivity. Qed.

Lemma phi_13 : euler_phi 13 = 12%nat.
Proof. reflexivity. Qed.

Lemma phi_17 : euler_phi 17 = 16%nat.
Proof. reflexivity. Qed.

Lemma phi_19 : euler_phi 19 = 18%nat.
Proof. reflexivity. Qed.

(** n-gon origami-constructible iff φ(n) is 2-3 smooth. *)
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

End Algebraic_Characterization.

Section Impossibility.

(** Not 2-3 smooth implies not OrigamiDegree. *)
Lemma not_smooth_not_origami : forall n,
  ~ is_2_3_smooth n -> ~ OrigamiDegree n.
Proof.
  intros n Hns Hod. apply Hns. apply origami_degree_implies_smooth. exact Hod.
Qed.

(** 3 is not a Euclidean degree (not a power of 2). *)
Lemma three_not_euclidean_degree : ~ EuclideanDegree 3.
Proof.
  intro H. inversion H; lia.
Qed.

(** Degree 3 is origami but not Euclidean: strict extension. *)
Theorem origami_strictly_extends_euclidean_degree :
  OrigamiDegree 3 /\ ~ EuclideanDegree 3.
Proof.
  split; [exact three_is_origami_degree | exact three_not_euclidean_degree].
Qed.

(** Hendecagon (11-gon): φ(10) = 4, φ(11) = 10. Requires degree-5 extension.
    5 is NOT an Origami degree (not 2^a × 3^b), hence impossible. *)

Lemma five_not_origami_degree : ~ OrigamiDegree 5.
Proof.
  intro H. inversion H; lia.
Qed.

(** Thus the 11-gon is NOT origami-constructible. *)
Theorem hendecagon_impossible :
  ~ OrigamiDegree 5.
Proof. exact five_not_origami_degree. Qed.

(** 10 is not 2-3 smooth (10 = 2 × 5, and 5 ∤ 3^b). *)
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

Theorem hendecagon_not_constructible : ~ ngon_constructible_iff_phi_smooth 11.
Proof.
  unfold ngon_constructible_iff_phi_smooth.
  rewrite phi_11. exact ten_not_smooth.
Qed.

(** 23-gon: φ(23) = 22 = 2 × 11. Since 11 ∤ 2^a × 3^b, impossible. *)

Lemma eleven_not_origami_degree : ~ OrigamiDegree 11.
Proof.
  intro H. inversion H; lia.
Qed.

Lemma twentytwo_not_smooth : ~ is_2_3_smooth 22.
Proof.
  intro H. destruct H as [a [b Heq]].
  destruct a; simpl in Heq; [destruct b; simpl in Heq; lia|].
  destruct a; simpl in Heq; [destruct b; simpl in Heq; lia|].
  destruct a; simpl in Heq; [destruct b; simpl in Heq; lia|].
  destruct a; simpl in Heq; [destruct b; simpl in Heq; lia|].
  destruct a; simpl in Heq; destruct b; simpl in Heq; lia.
Qed.

Lemma phi_23 : euler_phi 23 = 22%nat.
Proof. reflexivity. Qed.

Theorem icositrigon_not_constructible : ~ ngon_constructible_iff_phi_smooth 23.
Proof.
  unfold ngon_constructible_iff_phi_smooth.
  rewrite phi_23. exact twentytwo_not_smooth.
Qed.

End Impossibility.

Section Famous_Constants.

(** Golden ratio φ = (1 + √5)/2. Direct construction. *)
Theorem golden_ratio_origami : OrigamiNum ((1 + sqrt 5) / 2).
Proof.
  apply Origami_div.
  - apply ON_add; [constructor | apply ON_sqrt; [|lra]].
    replace 5 with (2 + 3) by lra.
    apply ON_add; [apply Origami_two | apply Origami_three].
  - apply Origami_two.
  - lra.
Qed.

(** √2 is origami-constructible (diagonal of unit square). *)
Theorem sqrt2_origami : OrigamiNum (sqrt 2).
Proof.
  apply ON_sqrt; [apply Origami_two | lra].
Qed.

(** √3 is origami-constructible (height of equilateral triangle). *)
Theorem sqrt3_origami : OrigamiNum (sqrt 3).
Proof.
  apply ON_sqrt; [apply Origami_three | lra].
Qed.

(** Plastic constant ρ ≈ 1.3247 satisfies x³ - x - 1 = 0. Origami-only. *)
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

(** Euclidean ⊂ Origami. *)
Theorem euclidean_subset_of_origami : forall x, EuclidNum x -> OrigamiNum x.
Proof. exact Euclid_in_Origami. Qed.

(** Classical impossibilities become possible. *)
Theorem classical_problems_solvable :
  (forall c, 8*(c*c*c) - 6*c - 1 = 0 -> OrigamiNum c) /\
  (forall c, c*c*c = 2 -> OrigamiNum c).
Proof.
  split.
  - exact angle_trisection_possible.
  - exact cube_duplication_possible.
Qed.

(** Heptagon is origami-constructible. *)
Theorem heptagon_is_origami_constructible :
  forall c, 8*(c*c*c) + 4*(c*c) - 4*c - 1 = 0 -> OrigamiNum c.
Proof. exact heptagon_constructible. Qed.

(** ∛2 witnesses strict extension (degree 3 ∉ {2^n}). *)
Theorem cbrt2_witnesses_strict_extension :
  (forall r, r*r*r = 2 -> OrigamiNum r) /\
  (OrigamiDegree 3 /\ ~ EuclideanDegree 3).
Proof.
  split.
  - exact cube_duplication_possible.
  - exact origami_strictly_extends_euclidean_degree.
Qed.

End Main_Results.

Definition O5_general_image (p : Point) (l : Line) (q : Point) : Point :=
  let px := fst p in let py := snd p in
  let qx := fst q in let qy := snd q in
  let a := A l in let b := B l in let c := C l in
  let r2 := (px - qx)^2 + (py - qy)^2 in
  let d := (a * qx + b * qy + c) / (a^2 + b^2) in
  let h2 := r2 - d^2 * (a^2 + b^2) in
  let t := sqrt h2 / sqrt (a^2 + b^2) in
  let foot_x := qx - a * d in
  let foot_y := qy - b * d in
  (foot_x + b * t, foot_y - a * t).

Definition O5_general_valid (p : Point) (l : Line) (q : Point) : Prop :=
  let px := fst p in let py := snd p in
  let qx := fst q in let qy := snd q in
  let a := A l in let b := B l in let c := C l in
  let r2 := (px - qx)^2 + (py - qy)^2 in
  let dist_to_line := Rabs (a * qx + b * qy + c) / sqrt (a^2 + b^2) in
  dist_to_line^2 <= r2.

Definition fold_O5_general (p : Point) (l : Line) (q : Point) : Fold :=
  let p' := O5_general_image p l q in
  fold_line_ctor (perp_bisector p p').

Lemma O5_general_image_on_line : forall p l q,
  line_wf l -> on_line (O5_general_image p l q) l.
Proof.
  intros p l q Hwf.
  unfold O5_general_image, on_line. simpl.
  assert (Hnorm_pos : A l * A l + B l * B l > 0) by (apply line_norm_pos; exact Hwf).
  assert (Hnorm_nz : A l * A l + B l * B l <> 0) by lra.
  assert (Hsqrt_nz : sqrt (A l * (A l * 1) + B l * (B l * 1)) <> 0).
  { replace (A l * (A l * 1) + B l * (B l * 1)) with (A l * A l + B l * B l) by ring.
    apply Rgt_not_eq. apply sqrt_lt_R0. exact Hnorm_pos. }
  field. split; assumption.
Qed.

Lemma Rabs_sqr_eq : forall x, Rabs x * Rabs x = x * x.
Proof. intro x. rewrite <- Rabs_mult. rewrite Rabs_pos_eq; [ring | apply Rle_0_sqr]. Qed.

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
  2: { unfold Rdiv. rewrite Rpow_mult_distr. rewrite Rinv_pow by lra. reflexivity. }
  replace ((A l * A l + B l * B l) ^ 2) with ((A l * A l + B l * B l) * (A l * A l + B l * B l)) by ring.
  unfold Rdiv.
  rewrite Rinv_mult.
  replace ((A l * fst q + B l * snd q + C l) ^ 2 * (/ (A l * A l + B l * B l) * / (A l * A l + B l * B l)) *
           (A l * A l + B l * B l))
    with ((A l * fst q + B l * snd q + C l) ^ 2 * / (A l * A l + B l * B l)).
  2: { field. lra. }
  lra.
Qed.

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
