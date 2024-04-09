(* Imperative semantics based on FASE-20 paper – not generated from Ott, but probably should be *)
From stdpp Require Export
  tactics
  fin_maps
  natmap
  gmultiset
  sets
  relations
.
From ABS Require Import abs_defs
utils
abs_functional_metatheory
.

Tactic Notation "simp" := simplify_map_eq.
Tactic Notation "is_eq" ident(a) ident(b) :=
  destruct (decide (a = b)) as [<- | ?].

Definition f : Set := string. (*r future names *)
Lemma eq_f: forall (x y : f), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.

Definition o : Set := string. (*r object names *)
Lemma eq_o: forall (x y : o), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.

Definition m : Set := string. (*r method names *)
Lemma eq_m: forall (x y : m), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.

Definition C : Set := string. (*r class names *)
Lemma eq_C: forall (x y : C), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.

Inductive rhs : Set :=
| rhs_e (e0:e)
(* we invoke on an object directly, not by some mysterious evaluation to object identifiers *)
| rhs_invoc (o0:o) (m0:m) (es:list e)
| rhs_get (f0:f)
.

Inductive stmt : Set :=
| stmt_seq (s1 s2: stmt)
| stmt_skip
| stmt_asgn (x0:x) (r:rhs)
| stmt_cond (e0:e) (s1 s2: stmt)
| stmt_loop (e0:e) (s: stmt)
| stmt_ret (e0:e).

Variant M : Set :=  (*r method definition *)
 | M_m (T_5:T) (m0:m) (params decl:list (T*x)) (body:stmt).

(* Class definition *)
Variant CL: Set :=
  | class (name:C) (_: list(T*x)) (_: list M).

Equations get_class_name (CL0:CL): C := {get_class_name (class name _ _) := name}.
Equations get_fields (CL0:CL): list (T*x) := {get_fields (class _ fields _) := fields}.

Variant P: Set :=
  | program (_: list CL) (decl : list (T*x)) (main: stmt).

Lemma cons_neq{X:Type}: forall (x:X) l, x :: l <> l.
Proof.
  induction l; auto.
  intro.
  inversion H; subst.
  now apply IHl.
Qed.

#[global] Instance t_eq_dec : EqDecision t.
Proof.
  unfold EqDecision, Decision.
  decide equality; auto with ott_coq_equality arith.
Qed.
Hint Resolve t_eq_dec : ott_coq_equality.
#[global] Instance e_eq_dec : EqDecision e.
Proof.
  unfold EqDecision, Decision.
  decide equality; auto with ott_coq_equality arith.
  - is_eq t0 t5; auto.
  - admit.
Admitted.
Hint Resolve e_eq_dec : ott_coq_equality.

#[global] Instance rhs_eq_dec : EqDecision rhs.
Proof.
  unfold EqDecision, Decision.
  decide equality; auto with ott_coq_equality arith.
  - apply e_eq_dec.
  - apply list_eq_dec.
Qed.
Hint Resolve rhs_eq_dec : ott_coq_equality.

#[global] Instance stmt_eq_dec : EqDecision stmt.
Proof.
  unfold EqDecision, Decision.
  decide equality; auto with ott_coq_equality arith.
  - apply rhs_eq_dec.
  - apply e_eq_dec.
  - apply e_eq_dec.
  - apply e_eq_dec.
Qed.

#[global]
Instance proc_eq_dec : EqDecision (stmt * s).
Proof.
  unfold EqDecision, Decision.
  apply prod_eq_dec.
Qed.

Variant task: Set := tsk (p:stmt) (l:s).

#[global]
Instance s_eq_dec: EqDecision s.
Admitted.
#[global]
Instance task_eq_dec: EqDecision task.
Proof.
  unfold EqDecision, Decision.
  decide equality; auto with ott_coq_equality arith.
  - apply s_eq_dec.
  - apply stmt_eq_dec.
Qed.

#[global]
Instance countable_task: Countable task.
Admitted.

Notation queue := (gmultiset task).

Inductive cn: Set :=
| cn_future (f0:f) (v:option t)
| cn_object (C0:C) (a:s) (p:option task) (q: queue)
| cn_invoc (o0:o) (f0:f) (m0:m) (vs: list t).

Notation config := (natmap cn).
Definition add (p:task) (q:queue) := q ⊎ {[+ p +]}.
Definition remove (p:task) (q:queue) := difference q {[+ p +]}.

Equations get_method_decl (m0:m) (l: list M) : option M := {
  get_method_decl _ [] := None ;
  get_method_decl m ((M_m T m' params decl body)::Ms) :=
      if String.eqb m m' then Some (M_m T m' params decl body) else get_method_decl m Ms
  }.

Equations bind_params_aux (s0:s) (vs: list t) (params: list (T*x)): s := {
  bind_params_aux s0 [] _ := s0;
  bind_params_aux s0 _ [] := s0;
  bind_params_aux s0 (v::vs) ((_,x)::Txs) := insert x v (bind_params_aux s0 vs Txs)
  }.
Definition bind_params := bind_params_aux empty.

Equations bind (m0:m) (vs: list t) (f0:f) (CL0:CL) : option task := {
  bind m vs f (class n params m_list) :=
  match get_method_decl m m_list with
  | None => None
  | Some (M_m T m' params decl body) =>
      Some (tsk body (bind_params vs params))
  end
  }.

Definition reduce (Fs: list F): relation (e * s) :=
  fun  x y => let (e0, s0) := x in let (e1, s1) := y in red_e Fs s0 e0 s1 e1.
Definition eval (Fs: list F) (s0:s) (e0:e) (v:t): Prop :=
  exists sf, (rtc (reduce Fs)) (e0, s0) (e_t v, sf).

Equations eval_list (Fs: list F) (s0:s) (es: list e) (vs: list t): Prop := {
    eval_list _ _ [] [] := True;
    eval_list Fs s0 (e::es) (v::vs) := eval Fs s0 e v /\ eval_list Fs s0 es vs;
    eval_list _ _ _ _ := False
  }.

#[global]
Instance elem_of_map: ElemOf x s := fun x s => s !! x <> None.
#[global]
Instance elem_of_config: ElemOf nat config := fun x s => s !! x <> None.

Definition destiny: f := "destiny"%string.

Inductive stmt_step (Fs:list F): list CL -> config -> config -> Prop :=
| step_activate: forall Cs σ p q i a C,
    p ∈ q ->
    σ !! i = Some (cn_object C a None q) ->
    stmt_step Fs Cs σ (<[i:=(cn_object C a (Some p) (remove p q))]> σ)

| step_asgn1: forall Cs σ i a C l x e s q v,
    x ∈ l ->
    eval Fs (union a l) e v ->
    σ !! i = Some (cn_object C a (Some (tsk (stmt_seq (stmt_asgn x (rhs_e e)) s) l)) q) ->
    stmt_step Fs Cs σ (<[i:=(cn_object C a (Some (tsk s (<[x:=v]> l))) q)]> σ)

| step_asgn2: forall Cs σ o a C l x e s q v,
    ~ x ∈ l ->
    eval Fs (union a l) e v ->
    σ !! o = Some (cn_object C a (Some (tsk (stmt_seq (stmt_asgn x (rhs_e e)) s) l)) q) ->
    stmt_step Fs Cs σ (<[o:=(cn_object C (<[x:=v]> a) (Some (tsk s l)) q)]> σ)

| step_cond1: forall Cs σ o a C l e s1 s2 s q,
    eval Fs (union a l) e (t_b true) ->
    σ !! o = Some (cn_object C a (Some (tsk (stmt_seq (stmt_cond e s1 s2) s) l)) q) ->
    stmt_step Fs Cs σ (<[o:=cn_object C a (Some (tsk (stmt_seq s1 s) l)) q]> σ)

| step_cond2: forall Cs σ o a C l e s1 s2 s q,
    eval Fs (union a l) e (t_b false) ->
    σ !! o = Some (cn_object C a (Some (tsk (stmt_seq (stmt_cond e s1 s2) s) l)) q) ->
    stmt_step Fs Cs σ (<[o:=cn_object C a (Some (tsk (stmt_seq s2 s) l)) q]> σ)

| step_skip1: forall Cs σ o a C l s q,
    σ !! o = Some (cn_object C a (Some (tsk (stmt_seq stmt_skip s) l)) q) ->
    stmt_step Fs Cs σ (<[o:=cn_object C a (Some (tsk s l)) q]> σ)

| step_skip2: forall Cs σ o a C l q,
    σ !! o = Some (cn_object C a (Some (tsk stmt_skip l)) q) ->
    stmt_step Fs Cs σ (<[o:=cn_object C a None q]> σ)

| step_while: forall Cs σ o a C l e s1 s2 q,
    σ !! o = Some (cn_object C a (Some (tsk (stmt_seq (stmt_loop e s1) s2) l)) q) ->
    stmt_step Fs Cs σ (<[o:=cn_object C a (Some ( tsk (stmt_seq (stmt_cond e (stmt_seq s1 (stmt_loop e s1)) stmt_skip) s2) l)) q]> σ)

| step_call: forall Cs σ oi o' a C l q x m es vs s f fi i,
    ~ fi ∈ σ ->
    ~ i ∈ σ ->
    eval_list Fs (union a l) es vs ->
    σ !! oi = Some (cn_object C a (Some (tsk (stmt_seq (stmt_asgn x (rhs_invoc o' m es)) s) l)) q) ->
    stmt_step Fs Cs σ (<[oi:=cn_object C a (Some (tsk (stmt_seq (stmt_asgn x (rhs_get f)) s) l)) q]>
                      (<[i:=cn_invoc o' f m vs]>
                         (<[fi:=cn_future f None]> σ)))

| step_return: forall Cs σ o a C l e v q f fi,
    eval Fs (union a l) e v ->
    σ !! fi = Some (cn_future f None) ->
    σ !! o = Some (cn_object C a (Some (tsk (stmt_ret e) l)) q) ->
    l !! destiny = Some (t_fut fi) ->
    stmt_step Fs Cs σ (<[o:=cn_object C a None q]>
                      (<[fi:=cn_future f (Some v)]> σ))

| step_read: forall Cs σ o a C l x s v q f fi,
    σ !! fi = Some (cn_future f (Some v)) ->
    σ !! o = Some (cn_object C a (Some (tsk (stmt_seq (stmt_asgn x (rhs_get f)) s) l)) q) ->
    stmt_step Fs Cs σ (<[o:=cn_object C a (Some (tsk (stmt_seq (stmt_asgn x (rhs_e (e_t v))) s) l)) q]> σ)

| step_load: forall σ o oi i a p p' q f m vs C CL Cs Cs',
    σ !! oi = Some (cn_object C a p q) ->
    σ !! i = Some (cn_invoc o f m vs) ->
    get_class_name CL = C ->
    bind m vs f CL = Some p' ->
    stmt_step Fs (Cs ++ [CL] ++ Cs') σ
    (<[oi:=cn_object C a p (add p' q)]>
       (delete i σ))
.

(** Typing *)
Inductive typ_method: list CL -> G -> C -> m -> list e -> T -> Prop :=
(* TODO: implement this *).
Inductive typ_CL: G -> CL -> Prop :=
(* TODO: implement this *).

Inductive typ_rhs (Cs: list CL): G -> rhs -> ctxv -> Prop :=
| typ_rhs_e: forall G e T,
    typ_e G e T ->
    typ_rhs Cs G (rhs_e e) (ctxv_T T)
| typ_rhs_invoc: forall G o m es T,
    typ_method Cs G o m es T ->
    typ_rhs Cs G (rhs_invoc o m es) (ctxv_fut T)
| typ_rhs_get: forall G f T,
    G !! f = Some (ctxv_fut T) ->
    typ_rhs Cs G (rhs_get f) (ctxv_T T)
.

Inductive typ_stmt (Cs: list CL): G -> stmt -> Prop :=
| typ_stmt_seq: forall G s1 s2,
    typ_stmt Cs G s1 ->
    typ_stmt Cs G s2 ->
    typ_stmt Cs G (stmt_seq s1 s2)

| typ_stmt_skip: forall G,
    typ_stmt Cs G stmt_skip

|typ_stmt_asgn: forall G x r T,
    G !! x = Some T ->
    typ_rhs Cs G r T ->
    typ_stmt Cs G (stmt_asgn x r)

| typ_stmt_cond: forall G b s1 s2,
    typ_e G b T_bool ->
    typ_stmt Cs G s1 ->
    typ_stmt Cs G s2 ->
    typ_stmt Cs G (stmt_cond b s1 s2)

| typ_stmt_loop: forall G b s,
    typ_e G b T_bool ->
    typ_stmt Cs G s ->
    typ_stmt Cs G (stmt_loop b s)

| typ_stmt_return: forall G e T,
    typ_e G e T ->
    G !! destiny = Some (ctxv_fut T) ->
    typ_stmt Cs G (stmt_ret e)
.

Definition class_of: o -> C.
Admitted.

Equations task_well_typed (Cs: list CL) (G0:G) (t:task): Prop := {
  task_well_typed Cs G0 (tsk p l) := G_vdash_s G0 l /\ typ_stmt Cs G0 p
  }.
(* this is a bit weird: the paper treats l sometimes as a list of typed variable bindings and sometimes as local state :/
 if variable bindings then the typ_stmt judgement here should bind those vars in G0 *)

Definition queue_well_typed (Cs: list CL) (G0:G) (q:queue): Prop :=
  forall t, t ∈ q -> task_well_typed Cs G0 t.

Inductive cn_well_typed (Cs: list CL): G -> cn -> Prop :=
| wt_future_none: forall G f T,
    G !! f = Some (ctxv_fut T) ->
    cn_well_typed Cs G (cn_future f None)

| wt_future_some: forall G f t T,
    G !! f = Some (ctxv_fut T) ->
    typ_e G (e_t t) T ->
    cn_well_typed Cs G (cn_future f (Some t))

| wt_invoc: forall G o f m vs T,
    typ_method Cs G (class_of o) m (map e_t vs) T ->
    G !! f = Some (ctxv_fut T) ->
    cn_well_typed Cs G (cn_invoc o f m vs)

| wt_object_none: forall G C a q,
    queue_well_typed Cs G q ->
    cn_well_typed Cs G (cn_object C a None q)

| wt_object_some: forall G C a p q,
    queue_well_typed Cs G q ->
    task_well_typed Cs G p ->
    cn_well_typed Cs G (cn_object C a (Some p) q)
.

Definition config_well_typed (Cs: list CL) (G0:G) (conf: config) :=
  forall i ob, conf !! i = Some ob -> cn_well_typed Cs G0 ob.

Theorem type_preservation : forall (Fs: list F) (Cs: list CL) (G0: G),
  Forall (typ_F G0) Fs ->
  Forall (typ_CL G0) Cs ->
  forall σ σ',
    config_well_typed Cs G0 σ ->
    stmt_step Fs Cs σ σ' ->
    exists G',
      G0 ⊆ G' /\ config_well_typed Cs G' σ'.
Admitted.

(*TODO: subject reduction for stmt_step *)
(*TODO: labels + traces? *)
