(* generated by Ott 0.33 from: src/abs.ott *)

Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Ott.ott_list_core.


Require Export Ascii.
Require Export String.
Require Export ZArith.
Require Import Lia.
Require Coq.Program.Wf.

Require Import FMapList OrderedTypeEx.
Module Map <: FMapInterface.S := FMapList.Make String_as_OT.

#[export] Hint Resolve bool_dec : ott_coq_equality.
#[export] Hint Resolve ascii_dec : ott_coq_equality.
#[export] Hint Resolve Pos.eq_dec : ott_coq_equality.

(** * ABS Definitions *)

Definition i : Set := nat. (*r index variables (subscripts) *)
Lemma eq_i: forall (x y : i), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_i : ott_coq_equality.
Definition fn : Set := string. (*r function name *)
Lemma eq_fn: forall (x y : fn), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_fn : ott_coq_equality.
Definition x : Set := string. (*r variable *)
Lemma eq_x: forall (x' y : x), {x' = y} + {x' <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_x : ott_coq_equality.
Definition b : Set := bool. (*r boolean *)
Lemma eq_b: forall (x y : b), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_b : ott_coq_equality.
Definition z : Set := Z. (*r integer *)
Lemma eq_z: forall (x y : z), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_z : ott_coq_equality.

Inductive T : Set :=  (*r ground type *)
 | T_bool : T
 | T_int : T.

Inductive t : Set :=  (*r ground term *)
 | t_b (b5:b) (*r boolean *)
 | t_int (z5:z) (*r integer *).

Inductive sig : Set := 
 | sig_sig (_:list T) (T_5:T).

Inductive e : Set :=  (*r expression *)
 | e_t (t5:t) (*r term *)
 | e_var (x5:x) (*r variable *)
 | e_fn_call (fn5:fn) (_:list e) (*r function call *).

Inductive ctxv : Set := 
 | ctxv_T (T5:T)
 | ctxv_sig (sig5:sig).

Inductive F : Set :=  (*r function definition *)
 | F_fn (T_5:T) (fn5:fn) (_:list (T*x)) (e5:e).

Definition s : Type := Map.t t.

Definition G : Type := Map.t ctxv.
(** induction principles *)
Section e_rect.

Variables
  (P_e : e -> Prop)
  (P_list_e : list e -> Prop).

Hypothesis
  (H_e_t : forall (t5:t), P_e (e_t t5))
  (H_e_var : forall (x5:x), P_e (e_var x5))
  (H_e_fn_call : forall (e_list:list e), P_list_e e_list -> forall (fn5:fn), P_e (e_fn_call fn5 e_list))
  (H_list_e_nil : P_list_e nil)
  (H_list_e_cons : forall (e0:e), P_e e0 -> forall (e_l:list e), P_list_e e_l -> P_list_e (cons e0 e_l)).

Fixpoint e_ott_ind (n:e) : P_e n :=
  match n as x return P_e x with
  | (e_t t5) => H_e_t t5
  | (e_var x5) => H_e_var x5
  | (e_fn_call fn5 e_list) => H_e_fn_call e_list (((fix e_list_ott_ind (e_l:list e) : P_list_e e_l := match e_l as x return P_list_e x with nil => H_list_e_nil | cons e1 xl => H_list_e_cons e1(e_ott_ind e1)xl (e_list_ott_ind xl) end)) e_list) fn5
end.

End e_rect.
Fixpoint get_val (k:x) (l:list(x*x)): option x :=
  match l with
  | nil => None
  | (k', v) :: l' =>
      match eq_x k k' with
      | left _ => Some v
      | _ => get_val k l'
      end
  end.

Fixpoint e_var_subst (e5:e) (l:list (x*x)) : e :=
  match e5 with
  | e_t t => e_t t
  | e_var x =>
      match get_val x l with
              | None => e_var x
              | Some y => e_var y
              end
  | e_fn_call fn e_list =>
      e_fn_call fn (map (fun e => e_var_subst e l) e_list)
  end.

(* we actually need to do some work to convince Coq fresh_vars is well founded *)
Fixpoint e_size (e0 : e) : nat :=
  match e0 with
  | e_t _ => 1
  | e_var _ => 1
  | e_fn_call _ es => 1 + list_sum (map e_size es)
  end.

Lemma size_ge_1: forall e0,
     1 <= e_size e0.
Proof. destruct e0;cbn;lia. Qed.

Program Fixpoint fresh_vars (l : list x) (e0 : e) {measure (e_size e0)} : Prop :=
  match e0 with
  | e_t _ => True
  | e_var x => ~ In x l
  | e_fn_call fn es =>
      match es with
      | nil => True
      | e1::es' => fresh_vars l e1
                 /\ fresh_vars l (e_fn_call fn es')
      end
  end.
Next Obligation. cbn;lia. Qed.
Next Obligation.
  induction es';cbn; specialize (size_ge_1 e1);intro; lia.
Qed.


(** definitions *)

(* defns expression_well_typing *)
Inductive typ_e : G -> e -> T -> Prop :=    (* defn e *)
 | typ_bool : forall (G5:G) (b5:b),
     typ_e G5 (e_t (t_b b5)) T_bool
 | typ_int : forall (G5:G) (z5:z),
     typ_e G5 (e_t (t_int z5)) T_int
 | typ_var : forall (G5:G) (x5:x) (T5:T),
      (Map.find  x5   G5  = Some (ctxv_T  T5 ))  ->
     typ_e G5 (e_var x5) T5
 | typ_func_expr : forall (e_T_list:list (e*T)) (G5:G) (fn5:fn) (T_5:T),
     (forall e_ T_, In (e_,T_) (map (fun (pat_: (e*T)) => match pat_ with (e_,T_) => (e_,T_) end) e_T_list) -> (typ_e G5 e_ T_)) ->
      (Map.find  fn5   G5  = Some (ctxv_sig  (sig_sig (map (fun (pat_:(e*T)) => match pat_ with (e_,T_) => T_ end ) e_T_list) T_5) ))  ->
     typ_e G5 (e_fn_call fn5 (map (fun (pat_:(e*T)) => match pat_ with (e_,T_) => e_ end ) e_T_list)) T_5.
(** definitions *)

(* defns function_well_typing *)
Inductive typ_F : G -> F -> Prop :=    (* defn F *)
 | typ_func_decl : forall (T_x_list:list (T*x)) (G5:G) (T_5:T) (fn5:fn) (e5:e),
      (Map.find  fn5   G5  = Some (ctxv_sig  (sig_sig (map (fun (pat_:(T*x)) => match pat_ with (T_,x_) => T_ end ) T_x_list) T_5) ))  ->
     typ_e  (fold_right (fun (ax : x * T) (G5 : G) => Map.add (fst ax) (ctxv_T (snd ax)) G5)  G5   (map (fun (pat_:(T*x)) => match pat_ with (T_,x_) => (x_,T_) end ) T_x_list) )  e5 T_5 ->
     typ_F G5 (F_fn T_5 fn5 T_x_list e5).
(** definitions *)

(* defns evaluation_reduction *)
Inductive red_e : list F -> s -> e -> s -> e -> Prop :=    (* defn e *)
 | red_var : forall (F_list:list F) (s5:s) (x5:x) (t5:t),
      (Map.find  x5   s5  = Some ( t5 ))  ->
     red_e F_list s5 (e_var x5) s5 (e_t t5)
 | red_fun_exp : forall (e'_list e_list:list e) (F_list:list F) (s5:s) (fn5:fn) (e_5:e) (s':s) (e':e),
     red_e F_list s5 e_5 s' e' ->
     red_e F_list s5 (e_fn_call fn5 ((app e_list (app (cons e_5 nil) (app e'_list nil))))) s' (e_fn_call fn5 ((app e_list (app (cons e' nil) (app e'_list nil)))))
 | red_fun_ground : forall (T_x_t_y_list:list (T*x*t*x)) (F'_list F_list:list F) (T_5:T) (fn5:fn) (e5:e) (s5:s),
      (fresh_vars  (map (fun (pat_:(T*x*t*x)) => match pat_ with (T_,x_,t_,y_) => y_ end ) T_x_t_y_list)   e5 )  ->
     red_e ((app F_list (app (cons (F_fn T_5 fn5 (map (fun (pat_:(T*x*t*x)) => match pat_ with (T_,x_,t_,y_) => (T_,x_) end ) T_x_t_y_list) e5) nil) (app F'_list nil)))) s5 (e_fn_call fn5 (map (fun (pat_:(T*x*t*x)) => match pat_ with (T_,x_,t_,y_) => (e_t t_) end ) T_x_t_y_list))  (fold_right (fun (xt : x * t) (s5 : s) => Map.add (fst xt) (snd xt) s5)  s5   (map (fun (pat_:(T*x*t*x)) => match pat_ with (T_,x_,t_,y_) => (y_,t_) end ) T_x_t_y_list) )   (e_var_subst  e5   (map (fun (pat_:(T*x*t*x)) => match pat_ with (T_,x_,t_,y_) => (x_,y_) end ) T_x_t_y_list) ) .


