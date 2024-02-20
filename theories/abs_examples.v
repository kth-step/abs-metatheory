From ABS Require Import abs_defs.
From stdpp Require Import prelude.

(** * ABS Examples *)

Definition e_const_5 : e := 
  e_t (t_int 5%Z).

Definition func_const_5 : F := 
  F_fn T_int "const_5"%string [] e_const_5.

Definition e_call_const_5 : e :=
  e_fn_call "const_5"%string [].

Lemma e_const_5_T_int :
 typ_e (Map.empty ctxv) e_const_5 T_int.
Proof. by apply typ_int. Qed.

Lemma e_call_const_5_T_int :
 typ_e (Map.empty ctxv) e_call_const_5 T_int.
Proof.
Admitted.
