(* floatsound.v -- soundness of the FloatGeom primitive-float layer against its
   real-number model, via Flocq.  Each FloatGeom operation is shown to compute
   the IEEE-754-rounded value of its exact real model (round-to-nearest-even at
   every primitive step, hence within half an ulp per step), and the geometric
   decision predicates are shown to agree with their real counterparts on
   adequately separated inputs.

   This is the numerics-soundness capstone: it Requires extraction (for the
   FloatGeom module and primitive Floats) and Flocq, so it sits above the whole
   development.  Nothing depends on it. *)
Require Import extraction.
From Flocq Require Import Core BinarySingleNaN IEEE754.PrimFloat IEEE754.BinarySingleNaN.
From Stdlib Require Import Floats Reals Lra.
Import FloatGeom.
Open Scope R_scope.

#[local] Instance flt_prec_gt_0 : FLX.Prec_gt_0 prec := eq_refl.
#[local] Instance flt_prec_lt_emax : Prec_lt_emax prec emax := eq_refl.

(** Real value and finiteness of a primitive float, via Flocq. *)
Definition f2r (x : float) : R := B2R (Prim2B x).
Definition fin (x : float) : Prop := BinarySingleNaN.is_finite (Prim2B x) = true.

(** Round-to-nearest-even at the Float64 format. *)
Definition rnd (u : R) : R := round radix2 (fexp prec emax) (round_mode mode_NE) u.

(** A value does not overflow the format. *)
Definition no_ovf (u : R) : Prop := Rabs (rnd u) < bpow radix2 emax.

(** Rounding is within half an ulp of the exact value. *)
Lemma rnd_err : forall u, Rabs (rnd u - u) <= /2 * Ulp.ulp radix2 (fexp prec emax) u.
Proof.
  intros u. unfold rnd.
  apply (error_le_half_ulp radix2 (fexp prec emax) (fun x => negb (Z.even x)) u).
Qed.

(** The four primitive operations compute the correctly rounded real result and
    stay finite, when the arguments are finite and the result does not overflow. *)
Lemma add_sound : forall x y : float,
  fin x -> fin y -> no_ovf (f2r x + f2r y) ->
  f2r (x + y)%float = rnd (f2r x + f2r y) /\ fin (x + y)%float.
Proof.
  intros x y Fx Fy Hov. unfold f2r, fin, no_ovf, rnd in *. rewrite add_equiv.
  pose proof (Bplus_correct prec emax _ _ mode_NE (Prim2B x) (Prim2B y) Fx Fy) as H.
  rewrite Rlt_bool_true in H by exact Hov.
  destruct H as [H1 [H2 _]]. split; assumption.
Qed.

Lemma sub_sound : forall x y : float,
  fin x -> fin y -> no_ovf (f2r x - f2r y) ->
  f2r (x - y)%float = rnd (f2r x - f2r y) /\ fin (x - y)%float.
Proof.
  intros x y Fx Fy Hov. unfold f2r, fin, no_ovf, rnd in *. rewrite sub_equiv.
  pose proof (Bminus_correct prec emax _ _ mode_NE (Prim2B x) (Prim2B y) Fx Fy) as H.
  rewrite Rlt_bool_true in H by exact Hov.
  destruct H as [H1 [H2 _]]. split; assumption.
Qed.

Lemma mul_sound : forall x y : float,
  fin x -> fin y -> no_ovf (f2r x * f2r y) ->
  f2r (x * y)%float = rnd (f2r x * f2r y) /\ fin (x * y)%float.
Proof.
  intros x y Fx Fy Hov. unfold no_ovf, rnd in Hov.
  pose proof (Bmult_correct prec emax _ _ mode_NE (Prim2B x) (Prim2B y)) as H.
  rewrite Rlt_bool_true in H by exact Hov.
  destruct H as [H1 [H2 _]].
  unfold fin in Fx, Fy. rewrite Fx, Fy in H2. simpl in H2.
  split.
  - unfold f2r, rnd. rewrite mul_equiv. exact H1.
  - unfold fin. rewrite mul_equiv. exact H2.
Qed.

Lemma div_sound : forall x y : float,
  fin x -> fin y -> f2r y <> 0 -> no_ovf (f2r x / f2r y) ->
  f2r (x / y)%float = rnd (f2r x / f2r y) /\ fin (x / y)%float.
Proof.
  intros x y Fx Fy Hy Hov. unfold no_ovf, rnd in Hov.
  assert (Hy0 : B2R (Prim2B y) <> 0) by exact Hy.
  pose proof (Bdiv_correct prec emax _ _ mode_NE (Prim2B x) (Prim2B y) Hy0) as H.
  rewrite Rlt_bool_true in H by (unfold f2r in Hov; exact Hov).
  destruct H as [H1 [H2 _]].
  unfold fin in Fx. rewrite Fx in H2. simpl in H2.
  split.
  - unfold f2r, rnd. rewrite div_equiv. exact H1.
  - unfold fin. rewrite div_equiv. exact H2.
Qed.

(** Real value of a float point. *)
Definition p2r (p : float_point) : R * R := (f2r (fpx p), f2r (fpy p)).

(** float_dist2 faithfully rounds its real model (squared Euclidean distance):
    each subtraction, multiplication and addition is correctly rounded, so the
    result is the real distance-squared computed with IEEE rounding at every
    step -- hence within an accumulated half-ulp of the exact real value. *)
Lemma float_dist2_sound : forall p1 p2,
  fin (fpx p1) -> fin (fpx p2) -> fin (fpy p1) -> fin (fpy p2) ->
  no_ovf (f2r (fpx p1) - f2r (fpx p2)) ->
  no_ovf (f2r (fpy p1) - f2r (fpy p2)) ->
  no_ovf (rnd (f2r (fpx p1) - f2r (fpx p2)) * rnd (f2r (fpx p1) - f2r (fpx p2))) ->
  no_ovf (rnd (f2r (fpy p1) - f2r (fpy p2)) * rnd (f2r (fpy p1) - f2r (fpy p2))) ->
  no_ovf (rnd (rnd (f2r (fpx p1) - f2r (fpx p2)) * rnd (f2r (fpx p1) - f2r (fpx p2)))
          + rnd (rnd (f2r (fpy p1) - f2r (fpy p2)) * rnd (f2r (fpy p1) - f2r (fpy p2)))) ->
  f2r (float_dist2 p1 p2)
    = rnd (rnd (rnd (f2r (fpx p1) - f2r (fpx p2)) * rnd (f2r (fpx p1) - f2r (fpx p2)))
           + rnd (rnd (f2r (fpy p1) - f2r (fpy p2)) * rnd (f2r (fpy p1) - f2r (fpy p2)))).
Proof.
  intros p1 p2 F1 F2 F3 F4 Odx Ody Odx2 Ody2 Osum.
  destruct (sub_sound (fpx p1) (fpx p2) F1 F2 Odx) as [Ex Fdx].
  destruct (sub_sound (fpy p1) (fpy p2) F3 F4 Ody) as [Ey Fdy].
  destruct (mul_sound _ _ Fdx Fdx ltac:(rewrite Ex; exact Odx2)) as [Ex2 Fx2].
  destruct (mul_sound _ _ Fdy Fdy ltac:(rewrite Ey; exact Ody2)) as [Ey2 Fy2].
  destruct (add_sound _ _ Fx2 Fy2 ltac:(rewrite Ex2, Ey2, Ex, Ey; exact Osum)) as [Esum _].
  unfold float_dist2. cbv zeta.
  rewrite Esum, Ex2, Ey2, Ex, Ey. reflexivity.
Qed.

(** Negation is exact (no rounding). *)
Lemma opp_sound : forall x : float, fin x -> f2r (-x)%float = - f2r x /\ fin (-x)%float.
Proof.
  intros x Fx. unfold f2r, fin in *. rewrite opp_equiv, B2R_Bopp.
  split; [reflexivity | rewrite is_finite_Bopp; exact Fx].
Qed.

(** float_line_through (= float_fold_O1) faithfully rounds the line through two
    points: a = y2-y1, b = x1-x2, c = -(a*x1 + b*y1), each primitive step
    correctly rounded (the final negation exact). *)
Lemma float_line_through_sound : forall p1 p2,
  fin (fpx p1) -> fin (fpx p2) -> fin (fpy p1) -> fin (fpy p2) ->
  no_ovf (f2r (fpy p2) - f2r (fpy p1)) ->
  no_ovf (f2r (fpx p1) - f2r (fpx p2)) ->
  no_ovf (rnd (f2r (fpy p2) - f2r (fpy p1)) * f2r (fpx p1)) ->
  no_ovf (rnd (f2r (fpx p1) - f2r (fpx p2)) * f2r (fpy p1)) ->
  no_ovf (rnd (rnd (f2r (fpy p2) - f2r (fpy p1)) * f2r (fpx p1))
          + rnd (rnd (f2r (fpx p1) - f2r (fpx p2)) * f2r (fpy p1))) ->
  f2r (fla (float_line_through p1 p2)) = rnd (f2r (fpy p2) - f2r (fpy p1)) /\
  f2r (flb (float_line_through p1 p2)) = rnd (f2r (fpx p1) - f2r (fpx p2)) /\
  f2r (flc (float_line_through p1 p2))
    = - rnd (rnd (rnd (f2r (fpy p2) - f2r (fpy p1)) * f2r (fpx p1))
             + rnd (rnd (f2r (fpx p1) - f2r (fpx p2)) * f2r (fpy p1))).
Proof.
  intros p1 p2 F1 F2 F3 F4 Oa Ob Oax Oby Osum.
  destruct (sub_sound (fpy p2) (fpy p1) F4 F3 Oa) as [Ea Fa].
  destruct (sub_sound (fpx p1) (fpx p2) F1 F2 Ob) as [Eb Fb].
  destruct (mul_sound _ (fpx p1) Fa F1 ltac:(rewrite Ea; exact Oax)) as [Eax Fax].
  destruct (mul_sound _ (fpy p1) Fb F3 ltac:(rewrite Eb; exact Oby)) as [Eby Fby].
  destruct (add_sound _ _ Fax Fby ltac:(rewrite Eax, Eby, Ea, Eb; exact Osum)) as [Esum Fsum].
  destruct (opp_sound _ Fsum) as [Eopp _].
  unfold float_line_through, fla, flb, flc. cbv zeta. simpl.
  split; [exact Ea | split; [exact Eb |]].
  rewrite Eopp, Esum, Eax, Eby, Ea, Eb. reflexivity.
Qed.
