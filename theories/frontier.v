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
