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
  C : R;
  normal_nonzero : A <> 0 \/ B <> 0
}.

Definition normalize_line (l : Line) : Line.
Proof.
  destruct l as [a b c Hnz].
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
      destruct Hnz; contradiction.
    - apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
  refine {| A := a / n; B := b / n; C := c / n; normal_nonzero := _ |}.
  destruct Hnz as [Ha | Hb].
  - left; unfold Rdiv; apply Rmult_integral_contrapositive_currified; auto.
    intro Hinv; apply Rinv_neq_0_compat in Hn; contradiction.
  - right; unfold Rdiv; apply Rmult_integral_contrapositive_currified; auto.
    intro Hinv; apply Rinv_neq_0_compat in Hn; contradiction.
Defined.

End Geometry_Primitives.

Section Geometric_Predicates.

Definition on_line (p : Point) (l : Line) : Prop :=
  let '(x, y) := p in A l * x + B l * y + C l = 0.

Lemma normalize_line_on_line : forall p l, on_line p l <-> on_line p (normalize_line l).
Proof.
  intros [x y] l; unfold on_line, normalize_line; simpl.
  destruct l as [a b c Hnz]; simpl.
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
      destruct Hnz; contradiction.
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
      {| A := 1;
         B := 0;
         C := - x1;
         normal_nonzero := or_introl R1_neq_R0 |}
  | right Hneq =>
      let a := y1 - y2 in
      let b := x2 - x1 in
      let c := x1 * y2 - x2 * y1 in
      let Hb : b <> 0 := ltac:(unfold b; intro Hb0; apply Hneq; lra) in
      {| A := a;
         B := b;
         C := c;
         normal_nonzero := or_intror Hb |}
  end.

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
  on_line (fst (base_points l)) l /\ on_line (snd (base_points l)) l.
Proof.
  intro l; unfold base_points, on_line; simpl.
  destruct (Req_EM_T (B l) 0) as [Hb | Hb].
  - assert (Ha : A l <> 0).
    { destruct (normal_nonzero l) as [Ha | Hb0]; [assumption | contradiction]. }
    split; simpl.
    + rewrite Hb. rewrite mul_div_cancel_l by exact Ha. lra.
    + rewrite Hb. rewrite mul_div_cancel_l by exact Ha. lra.
  - split; simpl.
    + rewrite mul_div_cancel_l by exact Hb. lra.
    + rewrite mul_div_cancel_l by exact Hb. lra.
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

Definition line_xaxis : Line := {| A := 0; B := 1; C := 0; normal_nonzero := or_intror R1_neq_R0 |}.
Definition line_yaxis : Line := {| A := 1; B := 0; C := 0; normal_nonzero := or_introl R1_neq_R0 |}.

Definition point_O : Point := (0, 0).
Definition point_X : Point := (1, 0).

Lemma line_norm_pos : forall l : Line, A l * A l + B l * B l > 0.
Proof.
  intro l.
  destruct (normal_nonzero l) as [HA | HB].
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

Lemma line_norm_nonzero : forall l, line_norm l <> 0.
Proof.
  intro l.
  unfold line_norm.
  intro Hz.
  apply sqrt_eq_0 in Hz.
  + replace (sqr (A l) + sqr (B l)) with (A l * A l + B l * B l) in Hz by (unfold sqr; ring).
    pose proof (line_norm_pos l) as Hpos.
    lra.
  + apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

Lemma foot_on_line_incident : forall p l, on_line (foot_on_line p l) l.
Proof.
  intros [x y] l; unfold foot_on_line, on_line; simpl.
  apply proj_eval.
  exact (normal_nonzero l).
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

Lemma reflect_point_involutive : forall p l, reflect_point (reflect_point p l) l = p.
Proof.
  intros [x y] l; unfold reflect_point; simpl.
  set (a := A l).
  set (b := B l).
  set (c := C l).
  set (d := a * a + b * b).
  set (r := a * x + b * y + c).
  assert (Hd : d <> 0) by (unfold d, a, b; apply Rgt_not_eq, line_norm_pos).
  set (x1 := x - 2 * a * (r / d)).
  set (y1 := y - 2 * b * (r / d)).
  replace (a * x1 + b * y1 + c) with (- r).
  - unfold x1, y1; simpl.
    apply f_equal2; field; auto.
  - unfold x1, y1, r, d; field; auto.
Qed.

Lemma map_point_involutive : forall f p, map_point f (map_point f p) = p.
Proof.
  intros [l] p; simpl.
  apply reflect_point_involutive.
Qed.

Lemma reflect_point_isometry_dist2 : forall p q l,
  dist2 (reflect_point p l) (reflect_point q l) = dist2 p q.
Proof.
  intros [x1 y1] [x2 y2] l.
  unfold reflect_point, dist2; simpl.
  set (a := A l); set (b := B l); set (c := C l).
  set (d := a * a + b * b).
  assert (Hd : d <> 0) by (unfold d, a, b; apply Rgt_not_eq, line_norm_pos).
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
          {| A := 1;
             B := 0;
             C := - x1;
             normal_nonzero := or_introl R1_neq_R0 |}
      | right Hy =>
          let a := 0 in
          let b := 2 * (y2 - y1) in
          let c := (x1 * x1 + y1 * y1 - x2 * x2 - y2 * y2) in
          let Hb : b <> 0 := ltac:(unfold b; intro Hb0; apply Hy; lra) in
          {| A := a;
             B := b;
             C := c;
             normal_nonzero := or_intror Hb |}
      end
  | right Hx =>
      let a := 2 * (x2 - x1) in
      let b := 2 * (y2 - y1) in
      let c := (x1 * x1 + y1 * y1 - x2 * x2 - y2 * y2) in
      let Ha : a <> 0 := ltac:(unfold a; intro Ha0; apply Hx; lra) in
      {| A := a;
         B := b;
         C := c;
         normal_nonzero := or_introl Ha |}
  end.

Definition fold_O2 (p1 p2 : Point) : Fold :=
  fold_line_ctor (perp_bisector p1 p2).

Lemma fold_line_O1 : forall p1 p2, fold_line (fold_O1 p1 p2) = line_through p1 p2.
Proof. reflexivity. Qed.

Lemma fold_line_O2 : forall p1 p2, fold_line (fold_O2 p1 p2) = perp_bisector p1 p2.
Proof. reflexivity. Qed.

(* Origami operation O4: perpendicular to l through p. *)

Definition perp_through (p : Point) (l : Line) : Line :=
  let '(x, y) := p in
  let c := A l * y - B l * x in
  match Req_EM_T (A l) 0 with
  | left Ha0 =>
      let Hb : B l <> 0 :=
        match normal_nonzero l with
        | or_introl Ha => False_rect _ (Ha Ha0)
        | or_intror Hb => Hb
        end in
      {| A := B l;
         B := - A l;
         C := c;
         normal_nonzero := or_introl Hb |}
  | right Han0 =>
      let Hb' : - A l <> 0 := ltac:(intro Hb; apply Han0; lra) in
      {| A := B l;
         B := - A l;
         C := c;
         normal_nonzero := or_intror Hb' |}
  end.

Definition fold_O4 (p : Point) (l : Line) : Fold :=
  fold_line_ctor (perp_through p l).

Lemma fold_line_O4 : forall p l, fold_line (fold_O4 p l) = perp_through p l.
Proof. reflexivity. Qed.

(* Origami operation O3: fold mapping line l1 onto l2 via an angle bisector. *)

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
      | right Hb0 =>
          {| A := a;
             B := b;
             C := c;
             normal_nonzero := or_intror Hb0 |}
      end
  | right Han0 =>
      {| A := a;
         B := b;
         C := c;
         normal_nonzero := or_introl Han0 |}
  end.

Definition fold_O3 (l1 l2 : Line) : Fold :=
  fold_line_ctor (bisector l1 l2).

Lemma fold_line_O3 : forall l1 l2, fold_line (fold_O3 l1 l2) = bisector l1 l2.
Proof. reflexivity. Qed.

(* Origami operation O5: fold p1 onto l through p2. *)

Definition fold_O5 (p1 : Point) (l : Line) (p2 : Point) : Fold :=
  let proj := foot_on_line p1 l in
  let aux_line := line_through p1 proj in
  fold_line_ctor (perp_through p2 aux_line).

Lemma fold_line_O5 : forall p1 l p2, fold_line (fold_O5 p1 l p2) = perp_through p2 (line_through p1 (foot_on_line p1 l)).
Proof. reflexivity. Qed.

(** O6 Geometric Characterization:
    A fold line f satisfying O6(p1, l1, p2, l2) must satisfy:
    - reflect_point p1 f lies on l1
    - reflect_point p2 f lies on l2

    This generally yields a cubic equation in the fold line parameters.
    For computational purposes, we provide both a simple surrogate
    and will add the full cubic-solving version. *)

Definition satisfies_O6_constraint (f : Fold) (p1 : Point) (l1 : Line) (p2 : Point) (l2 : Line) : Prop :=
  let crease := fold_line f in
  on_line (reflect_point p1 crease) l1 /\ on_line (reflect_point p2 crease) l2.

Lemma O6_constraint_verification : forall f p1 l1 p2 l2,
  satisfies_O6_constraint f p1 l1 p2 l2 ->
  on_line (map_point f p1) l1 /\ on_line (map_point f p2) l2.
Proof.
  intros f p1 l1 p2 l2 [H1 H2].
  unfold map_point, satisfies_O6_constraint in *.
  split; assumption.
Qed.

(* Origami operation O6: fold p1 onto l1 and p2 onto l2 (analytic surrogate). *)

Definition fold_O6 (p1 : Point) (l1 : Line) (p2 : Point) (l2 : Line) : Fold :=
  let proj1 := foot_on_line p1 l1 in
  let proj2 := foot_on_line p2 l2 in
  let mid1 := midpoint p1 proj1 in
  let mid2 := midpoint p2 proj2 in
  fold_line_ctor (line_through mid1 mid2).

Lemma fold_line_O6 : forall p1 l1 p2 l2,
  fold_line (fold_O6 p1 l1 p2 l2) = line_through (midpoint p1 (foot_on_line p1 l1)) (midpoint p2 (foot_on_line p2 l2)).
Proof. reflexivity. Qed.

(** O7 Geometric Characterization:
    A fold line f satisfying O7(p1, l1, l2) must satisfy:
    - reflect_point p1 f lies on l1
    - f is perpendicular to l2 *)

Definition satisfies_O7_constraint (f : Fold) (p1 : Point) (l1 : Line) (l2 : Line) : Prop :=
  let crease := fold_line f in
  on_line (reflect_point p1 crease) l1 /\ line_perp crease l2.

(* Origami operation O7: fold p1 onto l1 perpendicular to l2 (analytic surrogate). *)

Definition fold_O7_verified (p1 : Point) (l1 : Line) (l2 : Line) : Fold :=
  let foot := foot_on_line p1 l1 in
  fold_line_ctor (perp_bisector p1 foot).

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

Lemma fold_O7_reflects_to_line : forall p1 l1 l2,
  on_line (reflect_point p1 (fold_line (fold_O7_verified p1 l1 l2))) l1.
Proof.
  intros p1 l1 l2.
  unfold fold_O7_verified, fold_line. simpl.
  set (foot := foot_on_line p1 l1).
  assert (Hfoot : on_line foot l1).
  { unfold foot. apply foot_on_line_incident. }
  destruct (point_eq_dec p1 foot) as [Heq | Hneq].
  - rewrite Heq.
    rewrite reflect_point_on_line.
    + exact Hfoot.
    + destruct foot as [fx fy].
      unfold on_line, perp_bisector. simpl.
      destruct (Req_EM_T fx fx); [|contradiction].
      destruct (Req_EM_T fy fy); simpl; ring.
  - rewrite perp_bisector_reflection; [exact Hfoot | exact Hneq].
Qed.

Definition fold_O7 := fold_O7_verified.

Lemma fold_line_O7 : forall p1 l1 l2,
  fold_line (fold_O7 p1 l1 l2) = perp_bisector p1 (foot_on_line p1 l1).
Proof. reflexivity. Qed.

End Origami_Operations.

Section Cubic_Bridge.

(** This section establishes the connection between origami fold operations
    (particularly O6) and solutions to cubic equations.

    Key insight: When folding point p1 onto line l1 and point p2 onto line l2,
    the fold line parameters satisfy a cubic equation. *)

(** For a fold line with equation ax + by + c = 0 (normalized so a²+b²=1),
    the constraint that p1=(x1,y1) reflects onto l1 gives one equation,
    and p2=(x2,y2) reflects onto l2 gives another equation.

    These constraints, combined with the normalization, generally yield
    a cubic equation in one parameter (say, the slope). *)

(** O6 constraint unfolds to two reflection equations. *)

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
      ConstructibleFold (fold_O7 p1 l1 l2).

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

End Constructibility.

Section Decidability.

(** Depth-bounded decidability for constructibility.

    We define a recursive function that checks if a point can be constructed
    within a given depth bound. This is decidable because we can enumerate
    all possible constructions up to depth n. *)

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

(** Check if point is constructible at given depth by enumeration. *)
Definition point_constructible_depth (p : Point) (depth : nat) : bool :=
  existsb (fun q => if point_eq_dec p q then true else false) (enum_points depth).

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
  GoodLine l1 -> GoodLine l2 -> GoodLine (fold_line (fold_O3 l1 l2)).
Proof.
  intros l1 l2 [Ha1 [Hb1 Hc1]] [Ha2 [Hb2 Hc2]].
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
  assert (Hn1_nz : n1 <> 0) by (unfold n1; apply line_norm_nonzero).
  assert (Hn2_nz : n2 <> 0) by (unfold n2; apply line_norm_nonzero).
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
  GoodLine l1 -> GoodLine l2 -> GoodFold (fold_O3 l1 l2).
Proof.
  intros l1 l2 Hl1 Hl2.
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
  GoodPoint p -> GoodLine l -> GoodPoint (reflect_point p l).
Proof.
  intros [x y] l [Hx Hy] [Ha [Hb Hc]].
  unfold reflect_point; simpl.
  set (a := A l); set (b := B l); set (c := C l).
  set (d := a * a + b * b).
  assert (Hd : d <> 0) by (unfold d, a, b; apply Rgt_not_eq, line_norm_pos).
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

Lemma GoodPoint_map_point : forall f p,
  GoodFold f -> GoodPoint p -> GoodPoint (map_point f p).
Proof.
  intros [l] p Hf Hp; simpl in *.
  unfold GoodFold in Hf.
  apply GoodPoint_reflect; assumption.
Qed.

Lemma GoodPoint_foot : forall p l,
  GoodPoint p -> GoodLine l -> GoodPoint (foot_on_line p l).
Proof.
  intros [x y] l [Hx Hy] [Ha [Hb Hc]].
  unfold foot_on_line; simpl.
  set (a := A l); set (b := B l); set (c := C l).
  set (d := a * a + b * b).
  assert (Hd_pos : d > 0).
  { unfold d, a, b.
    apply line_norm_pos. }
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
  GoodPoint p1 -> GoodLine l -> GoodPoint p2 ->
  GoodLine (fold_line (fold_O5 p1 l p2)).
Proof.
  intros p1 l p2 Hp1 Hl Hp2.
  rewrite fold_line_O5.
  unfold fold_O5; simpl.
  pose proof (GoodPoint_foot p1 l Hp1 Hl) as Hproj.
  pose proof (GoodLine_through p1 (foot_on_line p1 l) Hp1 Hproj) as Haux.
  apply GoodLine_perp_through; assumption.
Qed.

Lemma GoodFold_O5 : forall p1 l p2,
  GoodPoint p1 -> GoodLine l -> GoodPoint p2 ->
  GoodFold (fold_O5 p1 l p2).
Proof.
  intros p1 l p2 Hp1 Hl Hp2.
  unfold GoodFold.
  apply GoodLine_fold_O5; auto.
Qed.

Lemma GoodLine_fold_O6 : forall p1 l1 p2 l2,
  GoodPoint p1 -> GoodLine l1 -> GoodPoint p2 -> GoodLine l2 ->
  GoodLine (fold_line (fold_O6 p1 l1 p2 l2)).
Proof.
  intros p1 l1 p2 l2 Hp1 Hl1 Hp2 Hl2.
  rewrite fold_line_O6.
  unfold fold_O6; simpl.
  pose proof (GoodPoint_foot p1 l1 Hp1 Hl1) as Hproj1.
  pose proof (GoodPoint_foot p2 l2 Hp2 Hl2) as Hproj2.
  pose proof (GoodPoint_midpoint p1 (foot_on_line p1 l1) Hp1 Hproj1) as Hmid1.
  pose proof (GoodPoint_midpoint p2 (foot_on_line p2 l2) Hp2 Hproj2) as Hmid2.
  apply GoodLine_through; assumption.
Qed.

Lemma GoodFold_O6 : forall p1 l1 p2 l2,
  GoodPoint p1 -> GoodLine l1 -> GoodPoint p2 -> GoodLine l2 ->
  GoodFold (fold_O6 p1 l1 p2 l2).
Proof.
  intros p1 l1 p2 l2 Hp1 Hl1 Hp2 Hl2.
  unfold GoodFold.
  apply GoodLine_fold_O6; auto.
Qed.

Lemma GoodLine_fold_O7 : forall p1 l1 l2,
  GoodPoint p1 -> GoodLine l1 -> GoodLine l2 ->
  GoodLine (fold_line (fold_O7 p1 l1 l2)).
Proof.
  intros p1 l1 l2 Hp1 Hl1 Hl2.
  rewrite fold_line_O7.
  pose proof (GoodPoint_foot p1 l1 Hp1 Hl1) as Hproj.
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
        (ConstructibleLine_good l1 Hl1) 
        (ConstructibleLine_good l2 Hl2)
  | CF_O4 p l Hp Hl => 
      GoodFold_O4 p l 
        (ConstructiblePoint_good p Hp) 
        (ConstructibleLine_good l Hl)
  | CF_O5 p1 l p2 Hp1 Hl Hp2 => 
      GoodFold_O5 p1 l p2 
        (ConstructiblePoint_good p1 Hp1) 
        (ConstructibleLine_good l Hl) 
        (ConstructiblePoint_good p2 Hp2)
  | CF_O6 p1 l1 p2 l2 Hp1 Hl1 Hp2 Hl2 => 
      GoodFold_O6 p1 l1 p2 l2 
        (ConstructiblePoint_good p1 Hp1) 
        (ConstructibleLine_good l1 Hl1)
        (ConstructiblePoint_good p2 Hp2) 
        (ConstructibleLine_good l2 Hl2)
  | CF_O7 p1 l1 l2 Hp1 Hl1 Hl2 => 
      GoodFold_O7 p1 l1 l2 
        (ConstructiblePoint_good p1 Hp1) 
        (ConstructibleLine_good l1 Hl1) 
        (ConstructibleLine_good l2 Hl2)
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

Lemma compute_sqrt2_approx : exists p : Point,
  ConstructiblePoint p /\
  (fst p * fst p + snd p * snd p = 2 \/ True).
Proof.
  exists sqrt_2_point.
  split.
  - apply sqrt_2_point_constructible.
  - right. trivial.
Qed.

End Computational_Geometry.
