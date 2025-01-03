(* generated by Ott 0.34 from: src/abs.ott *)

Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Ott.ott_list_core.


From Equations Require Import Equations.
From stdpp Require Import prelude strings gmap gmultiset countable.

(** * ABS Definitions *)

Definition i : Set := nat. (* index variables (subscripts) *)
Definition fc : Set := string. (* function name *)
Definition x : Set := string. (* variable *)
Definition fut : Set := nat. (* future type *)
Definition f : Set := string. (* future name *)
Definition o : Set := string. (* object name *)
Definition m : Set := string. (* method name *)
Definition C : Set := string. (* class name *)

Definition z : Set := Z.

Definition b : Set := bool.

Inductive t : Set :=  (* ground term *)
 | t_b (b5:b) (* boolean *)
 | t_int (z5:z) (* integer *)
 | t_fut (fut5:fut) (* future *).

Inductive T : Set :=  (* ground type *)
 | T_bool : T
 | T_int : T.

Inductive e : Set :=  (* expression *)
 | e_t (t5:t) (* term *)
 | e_var (x5:x) (* variable *)
 | e_fn_call (fc5:fc) (_:list e) (* function call *)
 | e_neg (e5:e)
 | e_not (e5:e)
 | e_add (e1:e) (e2:e)
 | e_mul (e1:e) (e2:e)
 | e_eq (e1:e) (e2:e)
 | e_lt (e1:e) (e2:e).

Inductive sig : Set := 
 | sig_sig (_:list T) (T_5:T).

Inductive rhs : Set :=  (* right-hand side in assignment *)
 | rhs_e (e5:e) (* expression *)
 | rhs_invoc (o5:o) (m5:m) (_:list e) (* method invocation *)
 | rhs_get (f5:f) (* value of future *).

Inductive ctxv : Set := 
 | ctxv_T (T5:T)
 | ctxv_sig (sig5:sig)
 | ctxv_fut (T5:T).

Inductive stmt : Set :=  (* statement *)
 | stmt_seq (stmt1:stmt) (stmt2:stmt)
 | stmt_skip : stmt
 | stmt_asgn (x5:x) (rhs5:rhs)
 | stmt_cond (e5:e) (stmt1:stmt) (stmt2:stmt)
 | stmt_loop (e5:e) (stmt5:stmt)
 | stmt_ret (e5:e).

Inductive F : Set :=  (* function definition *)
 | F_fn (T_5:T) (fc5:fc) (_:list (T*x)) (e5:e).

Definition s : Type := gmap x t.

Definition G : Type := gmap x ctxv.

Inductive M : Set :=  (* method definition *)
 | M_m (T_5:T) (m5:m) (_:list (T*x)) (_:list (T*x)) (stmt5:stmt).

Inductive CL : Set :=  (* class definition *)
 | class (C5:C) (_:list (T*x)) (_:list M).

Definition to : Set := (option t).

Inductive P : Set :=  (* program *)
 | program (_:list CL) (_:list (T*x)) (stmt5:stmt).

Inductive task : Type :=  (* runtime task *)
 | tsk (stmt5:stmt) (s5:s).
(** induction principles *)
Section e_rect.

Variables
  (P_list_e : list e -> Prop)
  (P_e : e -> Prop).

Hypothesis
  (H_e_t : forall (t5:t), P_e (e_t t5))
  (H_e_var : forall (x5:x), P_e (e_var x5))
  (H_e_fn_call : forall (e_list:list e), P_list_e e_list -> forall (fc5:fc), P_e (e_fn_call fc5 e_list))
  (H_e_neg : forall (e5:e), P_e e5 -> P_e (e_neg e5))
  (H_e_not : forall (e5:e), P_e e5 -> P_e (e_not e5))
  (H_e_add : forall (e1:e), P_e e1 -> forall (e2:e), P_e e2 -> P_e (e_add e1 e2))
  (H_e_mul : forall (e1:e), P_e e1 -> forall (e2:e), P_e e2 -> P_e (e_mul e1 e2))
  (H_e_eq : forall (e1:e), P_e e1 -> forall (e2:e), P_e e2 -> P_e (e_eq e1 e2))
  (H_e_lt : forall (e1:e), P_e e1 -> forall (e2:e), P_e e2 -> P_e (e_lt e1 e2))
  (H_list_e_nil : P_list_e nil)
  (H_list_e_cons : forall (e0:e), P_e e0 -> forall (e_l:list e), P_list_e e_l -> P_list_e (cons e0 e_l)).

Fixpoint e_ott_ind (n:e) : P_e n :=
  match n as x return P_e x with
  | (e_t t5) => H_e_t t5
  | (e_var x5) => H_e_var x5
  | (e_fn_call fc5 e_list) => H_e_fn_call e_list (((fix e_list_ott_ind (e_l:list e) : P_list_e e_l := match e_l as x return P_list_e x with nil => H_list_e_nil | cons e1 xl => H_list_e_cons e1(e_ott_ind e1)xl (e_list_ott_ind xl) end)) e_list) fc5
  | (e_neg e5) => H_e_neg e5 (e_ott_ind e5)
  | (e_not e5) => H_e_not e5 (e_ott_ind e5)
  | (e_add e1 e2) => H_e_add e1 (e_ott_ind e1) e2 (e_ott_ind e2)
  | (e_mul e1 e2) => H_e_mul e1 (e_ott_ind e1) e2 (e_ott_ind e2)
  | (e_eq e1 e2) => H_e_eq e1 (e_ott_ind e1) e2 (e_ott_ind e2)
  | (e_lt e1 e2) => H_e_lt e1 (e_ott_ind e1) e2 (e_ott_ind e2)
end.

End e_rect.

Equations e_var_subst_one (e5:e) (x_ y_: x) : e := {
 e_var_subst_one (e_t t) _ _ := e_t t;
 e_var_subst_one (e_var x0) x_ y_ := if decide (x0 = x_) then (e_var y_) else (e_var x0);
 e_var_subst_one (e_neg e0) _ _ := e_neg (e_var_subst_one e0 x_ y_);
 e_var_subst_one (e_not e0) _ _ := e_not (e_var_subst_one e0 x_ y_);
 e_var_subst_one (e_add e1 e2) _ _ := e_add (e_var_subst_one e1 x_ y_) (e_var_subst_one e2 x_ y_);
 e_var_subst_one (e_mul e1 e2) _ _ := e_mul (e_var_subst_one e1 x_ y_) (e_var_subst_one e2 x_ y_);
 e_var_subst_one (e_eq e1 e2) _ _ := e_eq (e_var_subst_one e1 x_ y_) (e_var_subst_one e2 x_ y_);
 e_var_subst_one (e_lt e1 e2) _ _ := e_lt (e_var_subst_one e1 x_ y_) (e_var_subst_one e2 x_ y_);
 e_var_subst_one (e_fn_call fn0 arg_list) x_ y_ := e_fn_call fn0 (e_list_subst_one arg_list x_ y_) }
where e_list_subst_one (es:list e) (x_ y_: x) : list e := {
 e_list_subst_one nil _ _ := nil;
 e_list_subst_one (e0::es) x_ y_ := e_var_subst_one e0 x_ y_ :: e_list_subst_one es x_ y_
}.

Definition e_var_subst (e5:e) (l:list (x*x)) : e := foldr (fun '(x', y') e' => e_var_subst_one e' x' y') e5 l.

Equations fresh_vars_e (l : list x) (e0 : e) : Prop := {
 fresh_vars_e _ (e_t _) := True;
 fresh_vars_e l (e_var x) := ~ In x l;
 fresh_vars_e l (e_neg e0) := fresh_vars_e l e0;
 fresh_vars_e l (e_not e0) := fresh_vars_e l e0;
 fresh_vars_e l (e_add e1 e2) := fresh_vars_e l e1 /\ fresh_vars_e l e2;
 fresh_vars_e l (e_mul e1 e2) := fresh_vars_e l e1 /\ fresh_vars_e l e2;
 fresh_vars_e l (e_eq e1 e2) := fresh_vars_e l e1 /\ fresh_vars_e l e2;
 fresh_vars_e l (e_lt e1 e2) := fresh_vars_e l e1 /\ fresh_vars_e l e2;
 fresh_vars_e l (e_fn_call fn el) := fresh_vars_el l el }
where fresh_vars_el (l : list x) (el0 : list e) : Prop := {
 fresh_vars_el l nil := True;
 fresh_vars_el l (e1::el0) := fresh_vars_e l e1 /\ fresh_vars_el l el0 }.

Fixpoint fresh_vars_s (l : list x) (s0 : s): Prop :=
  match l with
  | nil => True
  | (y::ys) => lookup y s0 = None /\ fresh_vars_s ys s0
  end.

Definition fresh_vars (l : list x) (e0: e) (s0: s) : Prop :=
  fresh_vars_s l s0 /\ fresh_vars_e l e0.

Definition well_formed (e0: e) (s0: s) (l:list x) : Prop := fresh_vars l e0 s0 /\ NoDup l.

#[export] Instance t_eq_dec : EqDecision t.
Proof. by solve_decision. Defined.

Section e_rec.
  Variables
    (P_e : e -> Set)
    (P_list_e : list e -> Set).

  Hypothesis
    (H_e_t : forall (t5:t), P_e (e_t t5))
    (H_e_var : forall (x5:x), P_e (e_var x5))
    (H_e_neg : forall (e5:e), P_e e5 -> P_e (e_neg e5))
    (H_e_not : forall (e5:e), P_e e5 -> P_e (e_not e5))
    (H_e_add : forall (e1:e), P_e e1 -> forall (e2:e), P_e e2 -> P_e (e_add e1 e2))
    (H_e_mul : forall (e1:e), P_e e1 -> forall (e2:e), P_e e2 -> P_e (e_mul e1 e2))
    (H_e_eq : forall (e1:e), P_e e1 -> forall (e2:e), P_e e2 -> P_e (e_eq e1 e2))
    (H_e_lt : forall (e1:e), P_e e1 -> forall (e2:e), P_e e2 -> P_e (e_lt e1 e2))
    (H_e_fn_call : forall (e_list:list e), P_list_e e_list -> forall (fc5:fc), P_e (e_fn_call fc5 e_list))
    (H_list_e_nil : P_list_e nil)
    (H_list_e_cons : forall (e0:e), P_e e0 -> forall (e_l:list e), P_list_e e_l -> P_list_e (cons e0 e_l)).

  Fixpoint e_ott_rec (n:e) : P_e n :=
    match n as x return P_e x with
    | (e_t t5) => H_e_t t5
    | (e_var x5) => H_e_var x5
    | (e_neg e5) => H_e_neg e5 (e_ott_rec e5)
    | (e_not e5) => H_e_not e5 (e_ott_rec e5)
    | (e_add e1 e2) => H_e_add e1 (e_ott_rec e1) e2 (e_ott_rec e2)
    | (e_mul e1 e2) => H_e_mul e1 (e_ott_rec e1) e2 (e_ott_rec e2)
    | (e_eq e1 e2) => H_e_eq e1 (e_ott_rec e1) e2 (e_ott_rec e2)
    | (e_lt e1 e2) => H_e_lt e1 (e_ott_rec e1) e2 (e_ott_rec e2)
    | (e_fn_call fn5 e_list) => H_e_fn_call e_list
      (((fix e_list_ott_rec (e_l:list e) : P_list_e e_l :=
         match e_l as x return P_list_e x with
	 | nil => H_list_e_nil
         | cons e1 xl => H_list_e_cons e1(e_ott_rec e1)xl (e_list_ott_rec xl)
         end)) e_list) fn5
    end.
End e_rec.

#[export] Instance e_eq_dec : EqDecision e.
Proof.
  unfold EqDecision,Decision.
  induction x0 using e_ott_rec with
    (P_list_e := fun e_list => forall e_list', {e_list = e_list'} + {e_list <> e_list'});
    intros; try (destruct y; auto).
  - destruct (decide (t5 = t0)) as [H_t|H_t].
    + by left; rewrite H_t.
    + by right; inv 1.
  - destruct (decide (x5 = x0)) as [H_x|H_x].
    + by left; rewrite H_x.
    + by right; inv 1.
  - destruct (IHx0 y); subst; first by auto.
    by right; inv 1.
  - destruct (IHx0 y); subst; first by auto.
    by right; inv 1.
  - destruct (IHx0_1 y1), (IHx0_2 y2); subst; first by auto.
    + by right; inv 1.
    + by right; inv 1.
    + by right; inv 1.
  - destruct (IHx0_1 y1), (IHx0_2 y2); subst; first by auto.
    + by right; inv 1.
    + by right; inv 1.
    + by right; inv 1.
  - destruct (IHx0_1 y1), (IHx0_2 y2); subst; first by auto.
    + by right; inv 1.
    + by right; inv 1.
    + by right; inv 1.
  - destruct (IHx0_1 y1), (IHx0_2 y2); subst; first by auto.
    + by right; inv 1.
    + by right; inv 1.
    + by right; inv 1.
  - destruct (decide (fc5 = fc0)) as [H_f|H_f].
    + rewrite H_f; destruct (IHx0 l); subst; auto.
      by right; intro Hl; inversion Hl.
    + by right; inv 1.
  - by destruct e_list'; auto.
  - destruct e_list'; first by auto.
    destruct (IHx0 e0); subst.
    + destruct (IHx1 e_list'); subst; first by auto.
      by right; inv 1.
    + by right; inv 1.
Defined.

#[export] Instance rhs_eq_dec : EqDecision rhs.
Proof. by solve_decision. Defined.

#[export] Instance stmt_eq_dec : EqDecision stmt.
Proof. by solve_decision. Defined.

#[export] Instance task_eq_dec: EqDecision task.
Proof. by solve_decision. Defined.

Definition t2gt (t0:t) : gen_tree (b + z + fut) :=
match t0 with
| t_b b1 => GenNode 0 [GenLeaf (inl (inl b1))]
| t_int z1 => GenNode 1 [GenLeaf (inl (inr z1))]
| t_fut f1 => GenNode 2 [GenLeaf (inr f1)]
end.

Definition gt2t (gt : gen_tree (b + z + fut)) : option t :=
match gt with
| GenNode 0 [GenLeaf (inl (inl b1))] => Some (t_b b1)
| GenNode 1 [GenLeaf (inl (inr z1))] => Some (t_int z1)
| GenNode 2 [GenLeaf (inr f1)] => Some (t_fut f1)
| _ => None
end.

Definition task2gt (ts:task) : gen_tree (stmt + s) :=
match ts with
| tsk stmt1 s1 => GenNode 0 [GenLeaf (inl stmt1); GenLeaf (inr s1)]
end.

Definition gt2task (gt : gen_tree (stmt + s)) : option task :=
match gt with
| GenNode 0 [GenLeaf (inl stmt1); GenLeaf (inr s1)] => Some (tsk stmt1 s1)
| _ => None
end.

Fixpoint e2gt (e0:e) : gen_tree (t + string) :=
match e0 with
| e_t t1 =>
    GenNode 0 [GenLeaf (inl t1)]
| e_var x1 =>
    GenNode 1 [GenLeaf (inr x1)]
| e_fn_call fc1 el =>
    GenNode 2 (GenLeaf (inr fc1) :: map e2gt el)
| e_neg e1 =>
    GenNode 3 [e2gt e1]
| e_not e1 =>
    GenNode 4 [e2gt e1]
| e_add e1 e2 =>
    GenNode 5 [e2gt e1; e2gt e2]
| e_mul e1 e2 =>
    GenNode 6 [e2gt e1; e2gt e2]
| e_eq e1 e2 =>
    GenNode 7 [e2gt e1; e2gt e2]
| e_lt e1 e2 =>
    GenNode 8 [e2gt e1; e2gt e2]
end.

Fixpoint gt2e (gt : gen_tree (t + string)) : option e :=
match gt with
| GenNode 0 [GenLeaf (inl t1)] =>
    Some (e_t t1)
| GenNode 1 [GenLeaf (inr x1)] =>
    Some (e_var x1)
| GenNode 2 (GenLeaf (inr fc1) :: gtl) =>
    Some (e_fn_call fc1 (omap gt2e gtl))
| GenNode 3 [gt1] =>
    match gt2e gt1 with
    | Some e1 => Some (e_neg e1)
    | None => None
    end
| GenNode 4 [gt1] =>
    match gt2e gt1 with
    | Some e1 => Some (e_not e1)
    | None => None
    end
| GenNode 5 [gt1; gt2] =>
    match gt2e gt1, gt2e gt2 with
    | Some e1, Some e2 => Some (e_add e1 e2)
    | _, _ => None
    end
| GenNode 6 [gt1; gt2] =>
    match gt2e gt1, gt2e gt2 with
    | Some e1, Some e2 => Some (e_mul e1 e2)
    | _, _ => None
    end
| GenNode 7 [gt1; gt2] =>
    match gt2e gt1, gt2e gt2 with
    | Some e1, Some e2 => Some (e_eq e1 e2)
    | _, _ => None
    end
| GenNode 8 [gt1; gt2] =>
    match gt2e gt1, gt2e gt2 with
    | Some e1, Some e2 => Some (e_lt e1 e2)
    | _, _ => None
    end
| _ => None
end.

Definition rhs2gt (rhs0:rhs) : gen_tree (list e + string) :=
match rhs0 with
| rhs_e e1 =>
    GenNode 0 [GenLeaf (inl [e1])]
| rhs_invoc o1 m1 el =>
    GenNode 1 [GenLeaf (inr o1); GenLeaf (inr m1); GenLeaf (inl el)]
| rhs_get f1 =>
    GenNode 2 [GenLeaf (inr f1)]
end.

Definition gt2rhs (gt : gen_tree (list e + string)) : option rhs :=
match gt with
| GenNode 0 [GenLeaf (inl [e1])] =>
    Some (rhs_e e1)
| GenNode 1 [GenLeaf (inr o1); GenLeaf (inr m1); GenLeaf (inl el)] =>
    Some (rhs_invoc o1 m1 el)
| GenNode 2 [GenLeaf (inr f1)] =>
    Some (rhs_get f1)
| _ => None
end.

Fixpoint stmt2gt (stmt0:stmt) : gen_tree (string + rhs + e) :=
match stmt0 with
| stmt_seq stmt1 stmt2 =>
    GenNode 0 [stmt2gt stmt1; stmt2gt stmt2]
| stmt_skip =>
    GenNode 1 []
| stmt_asgn x1 rhs1 =>
    GenNode 2 [GenLeaf (inl (inl x1)); GenLeaf (inl (inr rhs1))]
| stmt_cond e1 stmt1 stmt2 =>
    GenNode 3 [GenLeaf (inr e1); stmt2gt stmt1; stmt2gt stmt2]
| stmt_loop e1 stmt1 =>
    GenNode 4 [GenLeaf (inr e1); stmt2gt stmt1]
| stmt_ret e1 =>
    GenNode 5 [GenLeaf (inr e1)]
end.

Fixpoint gt2stmt (gt : gen_tree (string + rhs + e)) : option stmt :=
match gt with
| GenNode 0 [gt1; gt2] =>
    match gt2stmt gt1, gt2stmt gt2 with
    | Some stmt1, Some stmt2 => Some (stmt_seq stmt1 stmt2)
    | _, _ => None
    end
| GenNode 1 [] =>
    Some stmt_skip
| GenNode 2 [GenLeaf (inl (inl x1)); GenLeaf (inl (inr rhs1))] =>
    Some (stmt_asgn x1 rhs1)
| GenNode 3 [GenLeaf (inr e1); gt1; gt2] =>
    match gt2stmt gt1, gt2stmt gt2 with
    | Some stmt1, Some stmt2 => Some (stmt_cond e1 stmt1 stmt2)
    | _, _ => None
    end
| GenNode 4 [GenLeaf (inr e1); gt] =>
    match gt2stmt gt with
    | Some stmt1 => Some (stmt_loop e1 stmt1)
    | None => None
    end
| GenNode 5 [GenLeaf (inr e1)] =>
    Some (stmt_ret e1)
| _ => None
end.

#[export] Instance countable_t : Countable t.
Proof.
by apply (inj_countable t2gt gt2t); destruct x0.
Qed.

#[export] Instance countable_e : Countable e.
Proof.
apply (inj_countable e2gt gt2e).
induction x0 using e_ott_rec with
 (P_list_e := fun e_list => forall e, e ∈ e_list -> gt2e (e2gt e) = Some e); try done.
- by cbn; rewrite IHx0.
- by cbn; rewrite IHx0.
- by cbn; rewrite IHx0_1, IHx0_2.
- by cbn; rewrite IHx0_1, IHx0_2.
- by cbn; rewrite IHx0_1, IHx0_2.
- by cbn; rewrite IHx0_1, IHx0_2.
- induction e_list; cbn; try done.
  assert (Hl: ∀ e0 : e, e0 ∈ e_list → gt2e (e2gt e0) = Some e0). {
    intros e0 Hel.
    apply IHx0.
    by right.
  }
  specialize (IHe_list Hl).
  injection IHe_list; intros Heq.
  rewrite Heq.
  by rewrite IHx0; [|left].
- by intros e0 He0; inversion He0.
- intros e0 He.
  inversion He; subst; [done|].
  by apply IHx1.
Defined.

#[export] Instance countable_rhs : Countable rhs.
Proof.
by apply (inj_countable rhs2gt gt2rhs); destruct x0.
Defined.

#[export] Instance countable_stmt : Countable stmt.
Proof.
apply (inj_countable stmt2gt gt2stmt); induction x0; try done.
- by cbn; rewrite IHx0_1, IHx0_2.
- by cbn; rewrite IHx0_1, IHx0_2.
- by cbn; rewrite IHx0.
Defined.

#[export] Instance countable_task: Countable task.
Proof.
by apply (inj_countable task2gt gt2task); destruct x0.
Defined.


Definition queue : Set := (gmultiset task).

Definition tasko : Type := (option task).

Inductive cn : Type :=  (* configuration *)
 | cn_future (f5:f) (to5:to)
 | cn_object (C5:C) (s5:s) (tasko5:tasko) (queue5:queue)
 | cn_invoc (o5:o) (f5:f) (m5:m) (_:list t).
(* definitions *)

(* defns expression_well_typing *)
Inductive typ_e : G -> e -> T -> Prop :=    (* defn e *)
 | typ_bool : forall (G5:G) (b5:b),
     typ_e G5 (e_t (t_b b5)) T_bool
 | typ_int : forall (G5:G) (z5:z),
     typ_e G5 (e_t (t_int z5)) T_int
 | typ_var : forall (G5:G) (x5:x) (T5:T),
      (lookup  x5   G5  = Some (ctxv_T  T5 ))  ->
     typ_e G5 (e_var x5) T5
 | typ_neg : forall (G5:G) (e5:e),
     typ_e G5 e5 T_int ->
     typ_e G5 (e_neg e5) T_int
 | typ_not : forall (G5:G) (e5:e),
     typ_e G5 e5 T_bool ->
     typ_e G5 (e_not e5) T_bool
 | typ_add : forall (G5:G) (e1 e2:e),
     typ_e G5 e1 T_int ->
     typ_e G5 e2 T_int ->
     typ_e G5 (e_add e1 e2) T_int
 | typ_mul : forall (G5:G) (e1 e2:e),
     typ_e G5 e1 T_int ->
     typ_e G5 e2 T_int ->
     typ_e G5 (e_mul e1 e2) T_int
 | typ_eq : forall (G5:G) (e1 e2:e),
     typ_e G5 e1 T_int ->
     typ_e G5 e2 T_int ->
     typ_e G5 (e_eq e1 e2) T_bool
 | typ_lt : forall (G5:G) (e1 e2:e),
     typ_e G5 e1 T_int ->
     typ_e G5 e2 T_int ->
     typ_e G5 (e_lt e1 e2) T_bool
 | typ_func_expr : forall (e_T_list:list (e*T)) (G5:G) (fc5:fc) (T_5:T),
     (forall e_ T_, In (e_,T_) (map (fun (pat_: (e*T)) => match pat_ with (e_,T_) => (e_,T_) end) e_T_list) -> (typ_e G5 e_ T_)) ->
      (lookup  fc5   G5  = Some (ctxv_sig  (sig_sig (map (fun (pat_:(e*T)) => match pat_ with (e_,T_) => T_ end ) e_T_list) T_5) ))  ->
     typ_e G5 (e_fn_call fc5 (map (fun (pat_:(e*T)) => match pat_ with (e_,T_) => e_ end ) e_T_list)) T_5.
(* definitions *)

(* defns function_well_typing *)
Inductive typ_F : G -> F -> Prop :=    (* defn F *)
 | typ_func_decl : forall (T_x_list:list (T*x)) (G5:G) (T_5:T) (fc5:fc) (e5:e),
      (lookup  fc5   G5  = Some (ctxv_sig  (sig_sig (map (fun (pat_:(T*x)) => match pat_ with (T_,x_) => T_ end ) T_x_list) T_5) ))  ->
     typ_e  (foldr (fun (xT : x * T) (G0 : G) => insert (fst xT) (ctxv_T (snd xT)) G0)  G5   (map (fun (pat_:(T*x)) => match pat_ with (T_,x_) => (x_,T_) end ) T_x_list) )  e5 T_5 ->
      (NoDup  (map (fun (pat_:(T*x)) => match pat_ with (T_,x_) => x_ end ) T_x_list) )  ->
     typ_F G5 (F_fn T_5 fc5 T_x_list e5).
(* definitions *)

(* defns evaluation_reduction *)
Inductive red_e : list F -> s -> e -> s -> e -> Prop :=    (* defn e *)
 | red_var : forall (F_list:list F) (s5:s) (x5:x) (t5:t),
      (lookup  x5   s5  = Some ( t5 ))  ->
     red_e F_list s5 (e_var x5) s5 (e_t t5)
 | red_neg : forall (F_list:list F) (s5:s) (z5:z),
     red_e F_list s5 (e_neg (e_t (t_int z5))) s5 (e_t (t_int  (Z.sub Z.zero  z5 ) ))
 | red_not : forall (F_list:list F) (s5:s) (b5:b),
     red_e F_list s5 (e_not (e_t (t_b b5))) s5 (e_t (t_b  (negb  b5 ) ))
 | red_add : forall (F_list:list F) (s5:s) (z1 z2:z),
     red_e F_list s5 (e_add (e_t (t_int z1)) (e_t (t_int z2))) s5 (e_t (t_int  (Z.add  z1   z2 ) ))
 | red_mul : forall (F_list:list F) (s5:s) (z1 z2:z),
     red_e F_list s5 (e_mul (e_t (t_int z1)) (e_t (t_int z2))) s5 (e_t (t_int  (Z.mul  z1   z2 ) ))
 | red_eq : forall (F_list:list F) (s5:s) (z1 z2:z),
     red_e F_list s5 (e_eq (e_t (t_int z1)) (e_t (t_int z2))) s5 (e_t (t_b  (Z.eqb  z1   z2 ) ))
 | red_lt : forall (F_list:list F) (s5:s) (z1 z2:z),
     red_e F_list s5 (e_lt (e_t (t_int z1)) (e_t (t_int z2))) s5 (e_t (t_b  (Z.ltb  z1   z2 ) ))
 | red_neg' : forall (F_list:list F) (s5:s) (e5:e) (s':s) (e':e),
     red_e F_list s5 e5 s' e' ->
     red_e F_list s5 (e_neg e5) s' (e_neg e')
 | red_not' : forall (F_list:list F) (s5:s) (e5:e) (s':s) (e':e),
     red_e F_list s5 e5 s' e' ->
     red_e F_list s5 (e_not e5) s' (e_not e')
 | red_add_l : forall (F_list:list F) (s5:s) (e1 e2:e) (s':s) (e':e),
     red_e F_list s5 e1 s' e' ->
     red_e F_list s5 (e_add e1 e2) s' (e_add e' e2)
 | red_add_r : forall (F_list:list F) (s5:s) (e1 e2:e) (s':s) (e':e),
     red_e F_list s5 e2 s' e' ->
     red_e F_list s5 (e_add e1 e2) s' (e_add e1 e')
 | red_mul_l : forall (F_list:list F) (s5:s) (e1 e2:e) (s':s) (e':e),
     red_e F_list s5 e1 s' e' ->
     red_e F_list s5 (e_mul e1 e2) s' (e_add e' e2)
 | red_mul_r : forall (F_list:list F) (s5:s) (e1 e2:e) (s':s) (e':e),
     red_e F_list s5 e2 s' e' ->
     red_e F_list s5 (e_mul e1 e2) s' (e_add e1 e')
 | red_eq_l : forall (F_list:list F) (s5:s) (e1 e2:e) (s':s) (e':e),
     red_e F_list s5 e1 s' e' ->
     red_e F_list s5 (e_eq e1 e2) s' (e_eq e' e2)
 | red_eq_r : forall (F_list:list F) (s5:s) (e1 e2:e) (s':s) (e':e),
     red_e F_list s5 e2 s' e' ->
     red_e F_list s5 (e_eq e1 e2) s' (e_eq e1 e')
 | red_lt_l : forall (F_list:list F) (s5:s) (e1 e2:e) (s':s) (e':e),
     red_e F_list s5 e1 s' e' ->
     red_e F_list s5 (e_lt e1 e2) s' (e_lt e' e2)
 | red_lt_r : forall (F_list:list F) (s5:s) (e1 e2:e) (s':s) (e':e),
     red_e F_list s5 e2 s' e' ->
     red_e F_list s5 (e_lt e1 e2) s' (e_lt e1 e')
 | red_fun_exp : forall (e'_list e_list:list e) (F_list:list F) (s5:s) (fc5:fc) (e_5:e) (s':s) (e':e),
     red_e F_list s5 e_5 s' e' ->
     red_e F_list s5 (e_fn_call fc5 ((app e_list (app (cons e_5 nil) (app e'_list nil))))) s' (e_fn_call fc5 ((app e_list (app (cons e' nil) (app e'_list nil)))))
 | red_fun_ground : forall (T_x_t_y_list:list (T*x*t*x)) (F'_list F_list:list F) (T_5:T) (fc5:fc) (e5:e) (s5:s),
      (well_formed  e5   s5   (map (fun (pat_:(T*x*t*x)) => match pat_ with (T_,x_,t_,y_) => y_ end ) T_x_t_y_list) )  ->
      (disjoint  (map (fun (pat_:(T*x*t*x)) => match pat_ with (T_,x_,t_,y_) => y_ end ) T_x_t_y_list)   (map (fun (pat_:(T*x*t*x)) => match pat_ with (T_,x_,t_,y_) => x_ end ) T_x_t_y_list) )  ->
     red_e ((app F_list (app (cons (F_fn T_5 fc5 (map (fun (pat_:(T*x*t*x)) => match pat_ with (T_,x_,t_,y_) => (T_,x_) end ) T_x_t_y_list) e5) nil) (app F'_list nil)))) s5 (e_fn_call fc5 (map (fun (pat_:(T*x*t*x)) => match pat_ with (T_,x_,t_,y_) => (e_t t_) end ) T_x_t_y_list))  (foldr (fun (xt : x * t) (s0 : s) => insert (fst xt) (snd xt) s0)  s5   (map (fun (pat_:(T*x*t*x)) => match pat_ with (T_,x_,t_,y_) => (y_,t_) end ) T_x_t_y_list) )   (e_var_subst  e5   (map (fun (pat_:(T*x*t*x)) => match pat_ with (T_,x_,t_,y_) => (x_,y_) end ) T_x_t_y_list) ) .


