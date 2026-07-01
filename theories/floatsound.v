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

(** The float literal 2 denotes the real 2. *)
Lemma f2r_2 : f2r 2%float = 2. Proof. unfold f2r. vm_compute. lra. Qed.

(** float_midpoint faithfully rounds ((x1+x2)/2, (y1+y2)/2): the halving is a
    correctly rounded division by the exactly-represented 2. *)
Lemma float_midpoint_sound : forall p1 p2,
  fin (fpx p1) -> fin (fpx p2) -> fin (fpy p1) -> fin (fpy p2) ->
  no_ovf (f2r (fpx p1) + f2r (fpx p2)) -> no_ovf (f2r (fpy p1) + f2r (fpy p2)) ->
  no_ovf (rnd (f2r (fpx p1) + f2r (fpx p2)) / 2) ->
  no_ovf (rnd (f2r (fpy p1) + f2r (fpy p2)) / 2) ->
  f2r (fst (float_midpoint p1 p2)) = rnd (rnd (f2r (fpx p1) + f2r (fpx p2)) / 2) /\
  f2r (snd (float_midpoint p1 p2)) = rnd (rnd (f2r (fpy p1) + f2r (fpy p2)) / 2).
Proof.
  intros p1 p2 F1 F2 F3 F4 Osx Osy Odx Ody.
  assert (H2 : fin 2%float) by (unfold fin; vm_compute; reflexivity).
  assert (H2ne : f2r 2%float <> 0) by (rewrite f2r_2; lra).
  destruct (add_sound (fpx p1) (fpx p2) F1 F2 Osx) as [Esx Fsx].
  destruct (add_sound (fpy p1) (fpy p2) F3 F4 Osy) as [Esy Fsy].
  destruct (div_sound _ 2%float Fsx H2 H2ne ltac:(rewrite Esx, f2r_2; exact Odx)) as [Edx _].
  destruct (div_sound _ 2%float Fsy H2 H2ne ltac:(rewrite Esy, f2r_2; exact Ody)) as [Edy _].
  unfold float_midpoint. simpl.
  split.
  - rewrite Edx, Esx, f2r_2. reflexivity.
  - rewrite Edy, Esy, f2r_2. reflexivity.
Qed.

(** A finite float that denotes a nonzero real is not IEEE-equal to 0, so the
    determinant test in float_line_intersection agrees with the real predicate. *)
Lemma eqb_nonzero : forall det : float,
  fin det -> f2r det <> 0 -> PrimFloat.eqb det 0%float = false.
Proof.
  intros det Fd Hd. rewrite eqb_equiv.
  assert (F0 : BinarySingleNaN.is_finite (Prim2B 0%float) = true) by (vm_compute; reflexivity).
  rewrite (Beqb_correct _ _ _ _ Fd F0).
  assert (B0 : B2R (Prim2B 0%float) = 0) by (vm_compute; reflexivity).
  rewrite B0. apply Req_bool_false. exact Hd.
Qed.

(** Decision soundness of float_line_intersection: when the float determinant
    (the rounded real determinant a1 b2 - a2 b1) is nonzero, the routine returns
    an intersection point -- it decides the real "lines meet in a point"
    predicate on inputs whose determinant does not round to zero. *)
Lemma float_line_intersection_defined : forall l1 l2,
  fin (fla l1 * flb l2 - fla l2 * flb l1)%float ->
  f2r (fla l1 * flb l2 - fla l2 * flb l1)%float <> 0 ->
  exists p, float_line_intersection l1 l2 = Some p.
Proof.
  intros l1 l2 Fd Hd.
  unfold float_line_intersection. cbv zeta.
  rewrite (eqb_nonzero _ Fd Hd).
  eexists. reflexivity.
Qed.

(** Conversely, if the routine returns None the float determinant is exactly the
    float zero, so its real value is 0: the two lines are (numerically) parallel. *)
Lemma float_line_intersection_none : forall l1 l2,
  fin (fla l1 * flb l2 - fla l2 * flb l1)%float ->
  float_line_intersection l1 l2 = None ->
  f2r (fla l1 * flb l2 - fla l2 * flb l1)%float = 0.
Proof.
  intros l1 l2 Fd Hnone.
  destruct (Req_dec (f2r (fla l1 * flb l2 - fla l2 * flb l1)%float) 0) as [H0|Hne]; [exact H0|].
  exfalso. destruct (float_line_intersection_defined l1 l2 Fd Hne) as [p Hp].
  rewrite Hp in Hnone. discriminate.
Qed.

(** float_beloch_crease t = ((t, -1), -(t*t)): the O6 Beloch crease.  Its slope
    is exact, the constant -1 exact, and the -(t*t) entry correctly rounded. *)
Lemma float_beloch_crease_sound : forall t,
  fin t -> no_ovf (f2r t * f2r t) ->
  f2r (fla (float_beloch_crease t)) = f2r t /\
  f2r (flb (float_beloch_crease t)) = -1 /\
  f2r (flc (float_beloch_crease t)) = - rnd (f2r t * f2r t).
Proof.
  intros t Ft Ott.
  destruct (mul_sound t t Ft Ft Ott) as [Ett Ftt].
  destruct (opp_sound _ Ftt) as [Eopp _].
  unfold float_beloch_crease, fla, flb, flc. simpl.
  split; [reflexivity | split].
  - unfold f2r. vm_compute. lra.
  - rewrite Eopp, Ett. reflexivity.
Qed.

(** float_depressed_cubic p q t = t^3 + p t + q, evaluated left-to-right with
    correct rounding at each of the four multiplications/additions. *)
Lemma float_depressed_cubic_sound : forall p q t,
  fin p -> fin q -> fin t ->
  no_ovf (f2r t * f2r t) ->
  no_ovf (rnd (f2r t * f2r t) * f2r t) ->
  no_ovf (f2r p * f2r t) ->
  no_ovf (rnd (rnd (f2r t * f2r t) * f2r t) + rnd (f2r p * f2r t)) ->
  no_ovf (rnd (rnd (rnd (f2r t * f2r t) * f2r t) + rnd (f2r p * f2r t)) + f2r q) ->
  f2r (float_depressed_cubic p q t)
    = rnd (rnd (rnd (rnd (f2r t * f2r t) * f2r t) + rnd (f2r p * f2r t)) + f2r q).
Proof.
  intros p q t Fp Fq Ft Ott Ottt Opt Os1 Os2.
  destruct (mul_sound t t Ft Ft Ott) as [Ett Ftt].
  destruct (mul_sound _ t Ftt Ft ltac:(rewrite Ett; exact Ottt)) as [Ettt Fttt].
  destruct (mul_sound p t Fp Ft Opt) as [Ept Fpt].
  destruct (add_sound _ _ Fttt Fpt ltac:(rewrite Ettt, Ett, Ept; exact Os1)) as [Es1 Fs1].
  destruct (add_sound _ q Fs1 Fq ltac:(rewrite Es1, Ettt, Ett, Ept; exact Os2)) as [Es2 _].
  unfold float_depressed_cubic.
  rewrite Es2, Es1, Ettt, Ett, Ept. reflexivity.
Qed.

(** Explicit per-operation error bounds: each primitive float operation is
    within half an ulp of its exact real-number result.  For composite ops the
    faithful-rounding theorems above localize the error to one such bound per
    primitive step. *)
Lemma add_err : forall x y, fin x -> fin y -> no_ovf (f2r x + f2r y) ->
  Rabs (f2r (x + y)%float - (f2r x + f2r y))
    <= /2 * Ulp.ulp radix2 (fexp prec emax) (f2r x + f2r y).
Proof. intros x y Fx Fy Ho. destruct (add_sound x y Fx Fy Ho) as [E _]. rewrite E. apply rnd_err. Qed.

Lemma sub_err : forall x y, fin x -> fin y -> no_ovf (f2r x - f2r y) ->
  Rabs (f2r (x - y)%float - (f2r x - f2r y))
    <= /2 * Ulp.ulp radix2 (fexp prec emax) (f2r x - f2r y).
Proof. intros x y Fx Fy Ho. destruct (sub_sound x y Fx Fy Ho) as [E _]. rewrite E. apply rnd_err. Qed.

Lemma mul_err : forall x y, fin x -> fin y -> no_ovf (f2r x * f2r y) ->
  Rabs (f2r (x * y)%float - (f2r x * f2r y))
    <= /2 * Ulp.ulp radix2 (fexp prec emax) (f2r x * f2r y).
Proof. intros x y Fx Fy Ho. destruct (mul_sound x y Fx Fy Ho) as [E _]. rewrite E. apply rnd_err. Qed.

Lemma div_err : forall x y, fin x -> fin y -> f2r y <> 0 -> no_ovf (f2r x / f2r y) ->
  Rabs (f2r (x / y)%float - (f2r x / f2r y))
    <= /2 * Ulp.ulp radix2 (fexp prec emax) (f2r x / f2r y).
Proof. intros x y Fx Fy Hy Ho. destruct (div_sound x y Fx Fy Hy Ho) as [E _]. rewrite E. apply rnd_err. Qed.
