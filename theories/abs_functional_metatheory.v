From ABS Require Import abs_defs.
From Coq Require Import List.
Import ListNotations.

(** * ABS Functional Metatheory *)

Definition subG (G1 G2 : G) : Prop :=
  forall (key : string) (elt : ctxv), 
    Map.find key G1 = Some elt ->
    Map.find key G2 = Some elt.
