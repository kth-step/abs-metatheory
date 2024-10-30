From ABS Require Import abs_defs.
From stdpp Require Import prelude.

Inductive typ_e_alt : G -> e -> T -> Prop :=
| typ_bool_alt : forall (G5:G) (b5:b),
    typ_e_alt G5 (e_t (t_b b5)) T_bool
| typ_int_alt : forall (G5:G) (z5:z),
    typ_e_alt G5 (e_t (t_int z5)) T_int
| typ_var_alt : forall (G5:G) (x5:x) (T5:T),
    Map.find x5 G5  = Some (ctxv_T T5) ->
    typ_e_alt G5 (e_var x5) T5
| typ_func_expr_alt : forall (el:list e) (Tl : list T) (G5:G) (fn5:fn) (T_5:T),
    length el = length Tl ->
    Forall2 (fun e0 T0 => typ_e_alt G5 e0 T0) el Tl ->
    Map.find fn5 G5 = Some (ctxv_sig (sig_sig Tl T_5)) ->
    typ_e_alt G5 (e_fn_call fn5 el) T_5.

Lemma typ_e_alt_typ_e : 
 forall (G5:G) (e0:e) (T0 : T),
  typ_e_alt G5 e0 T0 -> typ_e G5 e0 T0.
Proof.
Admitted.

Lemma typ_e_typ_e_alt : 
 forall (G5:G) (e0:e) (T0 : T),
  typ_e G5 e0 T0 -> typ_e_alt G5 e0 T0.
Proof.
Admitted.

Theorem typ_e_equiv_typ_e_alt : 
 forall (G5:G) (e0:e) (T0 : T),
  typ_e G5 e0 T0 <-> typ_e_alt G5 e0 T0.
Proof.
by split; intro Ht; [apply typ_e_typ_e_alt|apply typ_e_alt_typ_e].
Qed.

Inductive typ_F_alt : G -> F -> Prop :=
| type_func_decl_alt : forall (Tl : list T) (xl:list x)
  (G5:G) (T_5:T) (fn5:fn) (e5:e),
   length xl = length Tl ->
   Map.find fn5 G5 = Some (ctxv_sig (sig_sig Tl T_5)) ->
   typ_e_alt (fold_right (fun '(T0,x0) G0 => Map.add x0 (ctxv_T T0) G0) G5 (zip Tl xl)) e5 T_5 ->
   typ_F_alt G5 (F_fn T_5 fn5 (zip Tl xl) e5).

Lemma typ_F_alt_typ_F : 
 forall (G5:G) (F0 : F),
  typ_F_alt G5 F0 -> typ_F G5 F0.
Proof.
Admitted.

Lemma typ_F_typ_F_alt : 
 forall (G5:G) (F0 : F),
  typ_F G5 F0 -> typ_F_alt G5 F0.
Proof.
Admitted.

Theorem typ_F_equiv_typ_F_alt : 
 forall (G5:G) (F0 : F),
  typ_F G5 F0 <-> typ_F_alt G5 F0.
Proof.
by split; intro Ht; [apply typ_F_typ_F_alt|apply typ_F_alt_typ_F].
Qed.

Inductive red_e_alt : list F -> s -> e -> s -> e -> Prop :=
| red_var_alt : forall (F_list:list F) (s5:s) (x5:x) (t5:t),
    Map.find x5 s5 = Some t5 ->
    red_e_alt F_list s5 (e_var x5) s5 (e_t t5).
