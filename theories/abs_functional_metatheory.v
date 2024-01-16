From ABS Require Import abs_defs.
From Coq Require Import List.
Import ListNotations.

(** * ABS Functional Metatheory *)

Definition subG (G1 G2 : G) : Prop :=
  forall (key : string) (elt : ctxv), 
    Map.find key G1 = Some elt ->
    Map.find key G2 = Some elt.

Definition G_vdash_s (G5 : G) (s5 : s) :=
 forall (x5 : x) (t5 : t) (T5 : T),
  Map.find x5 s5 = Some t5 ->
  Map.find x5 G5 = Some (ctxv_T T5) ->
  typ_e G5 (e_t t5) T5.

Lemma type_preservation : forall (G5 : G) (s5 : s), 
  G_vdash_s G5 s5 ->
  forall (Flist : list F) (e5 : e) (T5 : T) (s' : s) (e' : e),
    typ_e G5 e5 T5 ->
    red_e Flist s5 e5 s' e' ->
    exists G', subG G5 G' /\ G_vdash_s G' s' /\ typ_e G' e' T5.
Proof.
Admitted.

