(* frontier.v -- staging ground for results beyond established origami and
   constructibility mathematics: open conjectures and theorems not yet proved on
   paper.  A result already in the literature belongs in the settled core
   (foundations / cyclotomic / geometry) at the file its dependencies dictate;
   matured frontier results migrate there.

   Sibling of extraction.v; both build on the settled core and neither depends on
   the other.  Never Require extraction: it rebinds sqrt to the primitive machine
   float.

   Currently empty of theorems: the two-fold origami development -- the two-fold
   (Bring-Jerrard) quintic fold {t,-1,-t^4} grounding OrigamiNum2, and
   OrigamiNum2 = the two-fold-constructible numbers (OrigamiNum2_eq_TwoFold) --
   has graduated into geometry.v, being settled Alperin-Lang two-fold theory
   rather than open frontier mathematics.  New, not-yet-on-paper constructions go
   here first, then migrate down into the core once established. *)
From Stdlib Require Import Reals Lra Field R_sqr Psatz Nsatz Ring Ranalysis1 RingMicromega List ProofIrrelevance ClassicalDescription PeanoNat ZArith Classical Permutation Bool Arith.Wf_nat.
From Stdlib Require Znumtheory.
Import ListNotations.
Require Import foundations cyclotomic geometry.
Open Scope R_scope.
