From stdpp Require Import prelude strings.
From ABS Require Import abs_defs.

(** * ABS Examples *)

Definition e_const_5 : e := 
  e_t (t_int 5%Z).

Definition func_const_5 : F := 
  F_fn T_int "const_5"%string [] e_const_5.

Definition e_call_const_5 : e :=
  e_fn_call "const_5"%string [].

Definition Ctx : G :=
  insert ("const_5"%string) (ctxv_sig (sig_sig [] T_int)) empty.

Lemma e_const_5_T_int :
 typ_e Ctx e_const_5 T_int.
Proof. by apply typ_int. Qed.

Lemma e_call_const_typ_F :
 typ_F Ctx func_const_5.
Proof.
  apply typ_func_decl.
  - easy.
  - apply e_const_5_T_int.
  - simpl; constructor.
Qed.

Lemma e_call_const_5_T_int :
 typ_e Ctx e_call_const_5 T_int.
Proof.
  unfold e_call_const_5.
  replace [] with (map (fun (pat_:(e*T)) => match pat_ with (e_,T_) => e_ end ) [])
    by auto.
  by apply typ_func_expr.
Qed.
