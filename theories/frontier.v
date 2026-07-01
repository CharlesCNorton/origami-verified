(* frontier.v -- reserved for results genuinely beyond established origami and
   constructibility mathematics: open conjectures and theorems not yet proved on
   paper, let alone mechanized.  A result that is already classical -- a theorem
   in the literature -- does not belong here, even transiently: it goes straight
   into the settled core (foundations / cyclotomic / geometry) at the file its
   dependencies dictate.  Matured frontier results migrate DOWN the same way.

   Sibling of extraction.v; both build on the settled core and neither depends on
   the other.  Never Require extraction: it rebinds sqrt to the primitive machine
   float.  Currently empty. *)
From Stdlib Require Import Reals Lra Field R_sqr Psatz Nsatz Ring Ranalysis1 RingMicromega List ProofIrrelevance ClassicalDescription PeanoNat ZArith Classical ClassicalEpsilon Permutation Bool Arith.Wf_nat.
From Stdlib Require Znumtheory.
Import ListNotations.
Require Import foundations cyclotomic geometry.
Open Scope R_scope.
