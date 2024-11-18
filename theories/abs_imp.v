From stdpp Require Import prelude strings fin_maps natmap gmap gmultiset.
From ABS Require Import list_util abs_defs abs_util abs_functional_metatheory.

(** * Concurrent object level semantics for Core ABS *)

Notation id := nat.

(* Imperative semantics based on FASE-20 paper – not generated from Ott, but probably should be *)

Equations get_class_name (CL0:CL): C := {get_class_name (class name _ _) := name}.
Equations get_fields (CL0:CL): list (T*x) := {get_fields (class _ fields _) := fields}.
Equations get_methods (CL0:CL): list M := {get_methods (class _ _ methods) := methods}.

Equations get_params (_:M): list (T*x) := {get_params (M_m _ _ params _ _ ) := params}.
Equations get_type (_:M): T := {get_type (M_m type _ _ _ _ ) := type}.

Variant is_fut: cn -> Prop := is_fut_intro: forall f v, is_fut (cn_future f v).

Definition config := (natmap cn).
Definition add (p:task) (q:queue) := (q ⊎ {[+ p +]}).
Definition remove (p:task) (q:queue) := (q ∖ {[+ p +]}).
Equations get_method_decl (m0:m) (l: list M) : option M := {
    get_method_decl _ [] := None ;
    get_method_decl m ((M_m T m' params decl body)::Ms) :=
      if decide (m = m') then Some (M_m T m' params decl body) else get_method_decl m Ms
  }.

Equations get_class_decl (c:C) (l: list CL) : option CL := {
    get_class_decl _ [] := None ;
    get_class_decl c ((class name fields methods)::Cs) :=
      if decide (c = name) then Some (class name fields methods) else get_class_decl c Cs
  }.

Lemma get_class_decl_some: forall c l C,
    get_class_decl c l = Some C -> In C l.
Proof.
  induction l; intros; try (now inv H).
  destruct a.
  autorewrite with get_class_decl in *.
  case_decide; inv H.
  + now left.
  + right; auto.
Qed.

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

Definition eval (Fs: list F) (s0:s) (e0:e) (v:t): Prop :=
  exists sf, (rtc (reduce Fs)) (e0, s0) (e_t v, sf).

Equations eval_list (Fs: list F) (s0:s) (es: list e) (vs: list t): Prop := {
    eval_list _ _ [] [] := True;
    eval_list Fs s0 (e::es) (v::vs) := eval Fs s0 e v /\ eval_list Fs s0 es vs;
    eval_list _ _ _ _ := False
  }.

Definition destiny: f := "destiny"%string.

Definition fresh (f0:f) (σ:config) : Prop := forall i f v, σ !! i = Some (cn_future f v) -> f <> f0.
(* should we also require no invocations that mention f?
   alternatively we could assume (id_of f) is always present for invocations
 *)

Inductive stmt_step {Fs: list F}: config -> config -> Prop :=
| step_activate: forall σ p q i a C,
    p ∈ q ->
    σ !! i = Some (cn_object C a None q) ->
    stmt_step σ (<[i:=(cn_object C a (Some p) (remove p q))]> σ)

| step_asgn1: forall σ i a C l x e s q v,
    x ∈ dom l ->
    eval Fs (union a l) e v ->
    σ !! i = Some (cn_object C a (Some (tsk (stmt_seq (stmt_asgn x (rhs_e e)) s) l)) q) ->
    stmt_step σ (<[i:=(cn_object C a (Some (tsk s (<[x:=v]> l))) q)]> σ)

| step_asgn2: forall σ o a C l x e s q v,
    x ∈ dom a ->
    eval Fs (union a l) e v ->
    σ !! o = Some (cn_object C a (Some (tsk (stmt_seq (stmt_asgn x (rhs_e e)) s) l)) q) ->
    stmt_step σ (<[o:=(cn_object C (<[x:=v]> a) (Some (tsk s l)) q)]> σ)

| step_cond1: forall σ o a C l e s1 s2 s q,
    eval Fs (union a l) e (t_b true) ->
    σ !! o = Some (cn_object C a (Some (tsk (stmt_seq (stmt_cond e s1 s2) s) l)) q) ->
    stmt_step σ (<[o:=cn_object C a (Some (tsk (stmt_seq s1 s) l)) q]> σ)

| step_cond2: forall σ o a C l e s1 s2 s q,
    eval Fs (union a l) e (t_b false) ->
    σ !! o = Some (cn_object C a (Some (tsk (stmt_seq (stmt_cond e s1 s2) s) l)) q) ->
    stmt_step σ (<[o:=cn_object C a (Some (tsk (stmt_seq s2 s) l)) q]> σ)

| step_skip1: forall σ o a C l s q,
    σ !! o = Some (cn_object C a (Some (tsk (stmt_seq stmt_skip s) l)) q) ->
    stmt_step σ (<[o:=cn_object C a (Some (tsk s l)) q]> σ)

| step_skip2: forall σ o a C l q,
    σ !! o = Some (cn_object C a (Some (tsk stmt_skip l)) q) ->
    stmt_step σ (<[o:=cn_object C a None q]> σ)

| step_while: forall σ o a C l e s1 s2 q,
    σ !! o = Some (cn_object C a (Some (tsk (stmt_seq (stmt_loop e s1) s2) l)) q) ->
    stmt_step σ (<[o:=cn_object C a (Some ( tsk (stmt_seq (stmt_cond e (stmt_seq s1 (stmt_loop e s1)) stmt_skip) s2) l)) q]> σ)

| step_call: forall σ oi o' a C l q x m es vs s f i j,
    fresh f σ ->
    ~ i ∈ dom σ ->
    ~ j ∈ dom σ ->
    eval_list Fs (union a l) es vs ->
    σ !! oi = Some (cn_object C a (Some (tsk (stmt_seq (stmt_asgn x (rhs_invoc o' m es)) s) l)) q) ->
    stmt_step σ (<[oi:=cn_object C a (Some (tsk (stmt_seq (stmt_asgn x (rhs_get f)) s) l)) q]>
                   (<[i:=cn_invoc o' f m vs]>
                      (<[j:=cn_future f None]> σ)))

| step_return: forall σ o a C l e v q f fi,
    eval Fs (union a l) e v ->
    σ !! fi = Some (cn_future f None) ->
    σ !! o = Some (cn_object C a (Some (tsk (stmt_ret e) l)) q) ->
    l !! destiny = Some (t_fut fi) ->
    stmt_step σ (<[o:=cn_object C a None q]>
                   (<[fi:=cn_future f (Some v)]> σ))

| step_read: forall σ o a C l x s v q f fi,
    σ !! fi = Some (cn_future f (Some v)) ->
    σ !! o = Some (cn_object C a (Some (tsk (stmt_seq (stmt_asgn x (rhs_get f)) s) l)) q) ->
    stmt_step σ (<[o:=cn_object C a (Some (tsk (stmt_seq (stmt_asgn x (rhs_e (e_t v))) s) l)) q]> σ)

| step_load: forall σ o oi i a p p' q f m vs C CL,
    σ !! oi = Some (cn_object C a p q) ->
    σ !! i = Some (cn_invoc o f m vs) ->
    get_class_name CL = C ->
    bind m vs f CL = Some p' ->
    stmt_step σ (<[oi:=cn_object C a p (add p' q)]> (delete i σ))
.
