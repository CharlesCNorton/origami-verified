(* frontier.v -- scratchpad for beyond-known-origami math; sibling of extraction.v.
   Build on the settled core (foundations/cyclotomic/geometry); promote matured
   results DOWN into them. Never Require extraction (it rebinds sqrt to float). *)
From Stdlib Require Import Reals Lra Field R_sqr Psatz Nsatz Ring Ranalysis1 RingMicromega List ProofIrrelevance ClassicalDescription PeanoNat ZArith Classical ClassicalEpsilon Permutation Bool Arith.Wf_nat.
From Stdlib Require Znumtheory.
Import ListNotations.
Require Import foundations cyclotomic geometry.
Open Scope R_scope.
