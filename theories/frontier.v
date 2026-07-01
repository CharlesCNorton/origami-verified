(* frontier.v -- scratchpad for beyond-known-origami math; sibling of extraction.v.
   Build on the settled core (foundations/cyclotomic/geometry); promote matured
   results DOWN into them. Never Require extraction (it rebinds sqrt to float). *)
From Stdlib Require Import Reals Lra Field R_sqr Psatz Nsatz Ring Ranalysis1 RingMicromega List ProofIrrelevance ClassicalDescription PeanoNat ZArith Classical ClassicalEpsilon Permutation Bool Arith.Wf_nat.
From Stdlib Require Znumtheory.
Import ListNotations.
Require Import foundations cyclotomic geometry.
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
