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
  utils.

Tactic Notation "simp" := simplify_map_eq.
Tactic Notation "is_eq" ident(a) ident(b) :=
  destruct (decide (a = b)) as [<- | ?].

Definition f : Set := nat. (*r future identifier *)
Lemma eq_f: forall (x y : f), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.

Definition o : Set := nat. (*r object identifier *)
Lemma eq_o: forall (x y : o), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.

Definition m : Set := string. (*r method names *)
Lemma eq_m: forall (x y : m), {x = y} + {x <> y}.
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

Inductive task: Set := tsk (p:stmt) (l:s) (destiny:f).

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
| cn_future (*f0:f*) (v:option t)
| cn_object (*o0:o*) (a:s) (p:option task) (q: queue)
| cn_invoc (o0:o) (f0:f) (m0:m) (vs: list t).

Notation config := (natmap cn).
Definition add (p:task) (q:queue) := q ⊎ {[+ p +]}.
Definition remove (p:task) (q:queue) := difference q {[+ p +]}.

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

Inductive stmt_step (Fs:list F) : config -> config -> Prop :=
| step_activate: forall σ p q o a,
    p ∈ q ->
    σ !! o = Some (cn_object a None q) ->
    stmt_step Fs σ (<[o:=(cn_object a (Some p) (remove p q))]> σ)

| step_asgn1: forall σ o a l destiny x e s q v,
    x ∈ l ->
    eval Fs (union a l) e v ->
    σ !! o = Some (cn_object a (Some (tsk (stmt_seq (stmt_asgn x (rhs_e e)) s) l destiny)) q) ->
    stmt_step Fs σ (<[o:=(cn_object a (Some (tsk s (<[x:=v]> l) destiny)) q)]> σ)

| step_asgn2: forall σ o a l destiny x e s q v,
    ~ x ∈ l ->
    eval Fs (union a l) e v ->
    σ !! o = Some (cn_object a (Some (tsk (stmt_seq (stmt_asgn x (rhs_e e)) s) l destiny)) q) ->
    stmt_step Fs σ (<[o:=(cn_object (<[x:=v]> a) (Some (tsk s l destiny)) q)]> σ)

| step_cond1: forall σ o a l destiny e s1 s2 s q,
    eval Fs (union a l) e (t_b true) ->
    σ !! o = Some (cn_object a (Some (tsk (stmt_seq (stmt_cond e s1 s2) s) l destiny)) q) ->
    stmt_step Fs σ (<[o:=cn_object a (Some (tsk (stmt_seq s1 s) l destiny)) q]> σ)

| step_cond2: forall σ o a l destiny e s1 s2 s q,
    eval Fs (union a l) e (t_b false) ->
    σ !! o = Some (cn_object a (Some (tsk (stmt_seq (stmt_cond e s1 s2) s) l destiny)) q) ->
    stmt_step Fs σ (<[o:=cn_object a (Some (tsk (stmt_seq s2 s) l destiny)) q]> σ)

| step_skip1: forall σ o a l destiny s q,
    σ !! o = Some (cn_object a (Some (tsk (stmt_seq stmt_skip s) l destiny)) q) ->
    stmt_step Fs σ (<[o:=cn_object a (Some (tsk s l destiny)) q]> σ)

| step_skip2: forall σ o a l destiny q,
    σ !! o = Some (cn_object a (Some (tsk stmt_skip l destiny)) q) ->
    stmt_step Fs σ (<[o:=cn_object a None q]> σ)

| step_while: forall σ o a l destiny e s1 s2 q,
    σ !! o = Some (cn_object a (Some (tsk (stmt_seq (stmt_loop e s1) s2) l destiny)) q) ->
    stmt_step Fs σ (<[o:=cn_object a (Some ( tsk (stmt_seq (stmt_cond e (stmt_seq s1 (stmt_loop e s1)) stmt_skip) s2) l destiny)) q]> σ)

| step_call: forall σ o o' a l destiny q x m es vs s f i,
    ~ f ∈ σ ->
    ~ i ∈ σ ->
    eval_list Fs (union a l) es vs ->
    σ !! o = Some (cn_object a (Some (tsk (stmt_seq (stmt_asgn x (rhs_invoc o' m es)) s) l destiny)) q) ->
    stmt_step Fs σ (<[o:=cn_object a (Some (tsk (stmt_seq (stmt_asgn x (rhs_get f)) s) l destiny)) q]>
                      (<[i:=cn_invoc o' f m vs]>
                         (<[f:=cn_future None]> σ)))

| step_return: forall σ o a l destiny e v q f,
    eval Fs (union a l) e v ->
    σ !! f = Some (cn_future None) ->
    σ !! o = Some (cn_object a (Some (tsk (stmt_ret e) l destiny)) q) ->
    stmt_step Fs σ (<[o:=cn_object a None q]>
                      (<[f:=cn_future (Some v)]> σ))
| step_read: forall σ o a l destiny x s v q f,
    σ !! f = Some (cn_future (Some v)) ->
    σ !! o = Some (cn_object a (Some (tsk (stmt_seq (stmt_asgn x (rhs_get f)) s) l destiny)) q) ->
    stmt_step Fs σ (<[o:=cn_object a (Some (tsk (stmt_seq (stmt_asgn x (rhs_e (e_t v))) s) l destiny)) q]> σ)
(*missing: load because it requires resolving method names to objects > something like typ_F?*)
.

(*TODO: typing judgement for stmt *)
(*TODO: subject reduction for stmt_step *)
(*TODO: labels + traces? *)
