From stdpp Require Import prelude strings fin_maps natmap gmap gmultiset.
From ABS Require Import list_util abs_defs abs_util abs_functional_metatheory.

(** * ABS Imperative Metatheory *)

Notation id := nat.

(* Imperative semantics based on FASE-20 paper – not generated from Ott, but probably should be *)
Section Semantics.
  Context
      (Cs: list CL)
      (Fs: list F)
      (name_of: id -> f)
      (id_of: f -> id)
  .

  Equations get_class_name (CL0:CL): C := {get_class_name (class name _ _) := name}.
  Equations get_fields (CL0:CL): list (T*x) := {get_fields (class _ fields _) := fields}.
  Equations get_methods (CL0:CL): list M := {get_methods (class _ _ methods) := methods}.

  Equations get_params (_:M): list (T*x) := {get_params (M_m _ _ params _ _ ) := params}.
  Equations get_type (_:M): T := {get_type (M_m type _ _ _ _ ) := type}.

  Definition queue := (gmultiset task).

  Inductive cn: Type :=
  | cn_future (f0:f) (v:option t)
  | cn_object (C0:C) (a:s) (p:option task) (q: queue)
  | cn_invoc (o0:o) (f0:f) (m0:m) (vs: list t).

  Definition config := (natmap cn).
  Definition add (p:task) (q:queue) := (q ⊎ {[+ p +]}).
  Definition remove (p:task) (q:queue) := (q ∖ {[+ p +]}).
  Equations get_method_decl (m0:m) (l: list M) : option M := {
      get_method_decl _ [] := None ;
      get_method_decl m ((M_m T m' params decl body)::Ms) :=
        if String.eqb m m' then Some (M_m T m' params decl body) else get_method_decl m Ms
    }.

  #[global] Instance elem_of_list_m: ElemOf m (list M) := fun m ms => get_method_decl m ms <> None.

  Equations get_class_decl (c:C) (l: list CL) : option CL := {
      get_class_decl _ [] := None ;
      get_class_decl c ((class name fields methods)::Cs) :=
        if String.eqb c name then Some (class name fields methods) else get_class_decl c Cs
    }.

  #[global] Instance elem_of_list_CL: ElemOf C (list CL) := fun c Cs => get_class_decl c Cs <> None.

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

  Definition eval (s0:s) (e0:e) (v:t): Prop :=
    exists sf, (rtc (reduce Fs)) (e0, s0) (e_t v, sf).

  Equations eval_list (s0:s) (es: list e) (vs: list t): Prop := {
      eval_list _ [] [] := True;
      eval_list s0 (e::es) (v::vs) := eval s0 e v /\ eval_list s0 es vs;
      eval_list _ _ _ := False
    }.

  Definition destiny: f := "destiny"%string.

  Definition fresh (f0:f) (σ:config) : Prop := forall i f v, σ !! i = Some (cn_future f v) -> f <> f0.

  Inductive stmt_step: config -> config -> Prop :=
  | step_activate: forall σ p q i a C,
      p ∈ q ->
      σ !! i = Some (cn_object C a None q) ->
      stmt_step σ (<[i:=(cn_object C a (Some p) (remove p q))]> σ)

  | step_asgn1: forall σ i a C l x e s q v,
      x ∈ dom l ->
      eval (union a l) e v ->
      σ !! i = Some (cn_object C a (Some (tsk (stmt_seq (stmt_asgn x (rhs_e e)) s) l)) q) ->
      stmt_step σ (<[i:=(cn_object C a (Some (tsk s (<[x:=v]> l))) q)]> σ)

  | step_asgn2: forall σ o a C l x e s q v,
      x ∈ dom a ->
      eval (union a l) e v ->
      σ !! o = Some (cn_object C a (Some (tsk (stmt_seq (stmt_asgn x (rhs_e e)) s) l)) q) ->
      stmt_step σ (<[o:=(cn_object C (<[x:=v]> a) (Some (tsk s l)) q)]> σ)

  | step_cond1: forall σ o a C l e s1 s2 s q,
      eval (union a l) e (t_b true) ->
      σ !! o = Some (cn_object C a (Some (tsk (stmt_seq (stmt_cond e s1 s2) s) l)) q) ->
      stmt_step σ (<[o:=cn_object C a (Some (tsk (stmt_seq s1 s) l)) q]> σ)

  | step_cond2: forall σ o a C l e s1 s2 s q,
      eval (union a l) e (t_b false) ->
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

  | step_call: forall σ oi o' a C l q x m es vs s f i,
      fresh f σ ->
      ~ i ∈ dom σ ->
      eval_list (union a l) es vs ->
      σ !! oi = Some (cn_object C a (Some (tsk (stmt_seq (stmt_asgn x (rhs_invoc o' m es)) s) l)) q) ->
      stmt_step σ (<[oi:=cn_object C a (Some (tsk (stmt_seq (stmt_asgn x (rhs_get f)) s) l)) q]>
                     (<[i:=cn_invoc o' f m vs]>
                        (<[id_of f:=cn_future f None]> σ)))

  | step_return: forall σ o a C l e v q f fi,
      eval (union a l) e v ->
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
      CL ∈ Cs ->
      get_class_name CL = C ->
      bind m vs f CL = Some p' ->
      stmt_step σ (<[oi:=cn_object C a p (add p' q)]> (delete i σ))
  .
End Semantics.

Section Typing.
(* based on https://link.springer.com/chapter/10.1007/978-3-642-25271-6_8 *)

  Context
      (Cs: list CL)
      (Fs: list F)
      (name_of: id -> f)
      (id_of: f -> id)
      (class_of: o -> C)
  .

  Hypothesis (vars_fs_distinct: forall (x_:x) (fn:fc), x_ <> fn).

  Equations typ_es: G -> list e -> list T -> Prop := {
      typ_es _ [] [] := True ;
      typ_es Γ (e::es) (T::Ts) := typ_e Γ e T /\ typ_es Γ es Ts ;
      typ_es _ _ _ := False
    }.

  Lemma type_preservation_eval: forall Γ,
      Forall (typ_F Γ) Fs ->
      forall σ, G_vdash_s Γ σ ->
           forall e0 e1 T0,
             typ_e Γ e0 T0 ->
             eval Fs σ e0 e1 ->
             typ_e Γ (e_t e1) T0.
  Proof.
    intros.
    destruct H2 as [σ' COMP].
    pose proof type_preservation vars_fs_distinct  _ _ _ H0 H _ _ _ H1 COMP
      as (Γ' & SUB & VDASH & TYP).
    now inv TYP; constructor.
  Qed.

  Lemma type_preservation_eval_list: forall Γ,
      Forall (typ_F Γ) Fs ->
      forall σ, G_vdash_s Γ σ ->
        forall es vs Ts,
          typ_es Γ es Ts ->
          eval_list Fs σ es vs ->
          typ_es Γ (map e_t vs) Ts.
  Proof.
    induction es; intros;
      destruct vs;
      destruct Ts;
      cbn;
      autorewrite with typ_es eval_list in *;
      try intuition.
    eapply type_preservation_eval; eauto.
  Qed.

  Definition add_G (Γ:G) (Tx:T*x): G := <[Tx.2:=ctxv_T Tx.1]> Γ.
  Definition extend_G (Γ:G) (l:list (T*x)): G := foldr (flip add_G) Γ l.

  Variant match_method: m -> list T -> T -> CL -> Prop :=
    match_intro: forall m method Cl,
        get_method_decl m (get_methods Cl) = Some method ->
        match_method m (map fst (get_params method)) (get_type method) Cl.

  Variant typ_rhs: G -> rhs -> ctxv -> Prop :=
    | typ_rhs_e: forall Γ e T,
        typ_e Γ e T ->
        typ_rhs Γ (rhs_e e) (ctxv_T T)
    | typ_rhs_invoc: forall Γ m o es Cl Ts T,
        typ_es Γ es Ts ->
        get_class_decl (class_of o) Cs = Some Cl ->
        match_method m Ts T Cl ->
        typ_rhs Γ (rhs_invoc o m es) (ctxv_fut T)
    | typ_rhs_fut: forall Γ f T,
        Γ !! f = Some (ctxv_fut T) ->
        typ_rhs Γ (rhs_get f) (ctxv_T T)
  .

  Inductive stmt_well_typed: G -> stmt -> Prop :=
  | typ_stmt_seq: forall G s1 s2,
      stmt_well_typed G s1 ->
      stmt_well_typed G s2 ->
      stmt_well_typed G (stmt_seq s1 s2)

  | stmt_well_typed_skip: forall G,
      stmt_well_typed G stmt_skip

  | stmt_well_typed_asgn: forall G x r T,
      G !! x = Some T ->
      typ_rhs G r T ->
      stmt_well_typed G (stmt_asgn x r)

  | stmt_well_typed_cond: forall G b s1 s2,
      typ_e G b T_bool ->
      stmt_well_typed G s1 ->
      stmt_well_typed G s2 ->
      stmt_well_typed G (stmt_cond b s1 s2)

  | stmt_well_typed_loop: forall G b s,
      typ_e G b T_bool ->
      stmt_well_typed G s ->
      stmt_well_typed G (stmt_loop b s)

  | stmt_well_typed_return: forall G e T,
      typ_e G e T ->
      G !! destiny = Some (ctxv_fut T) ->
      stmt_well_typed G (stmt_ret e)
  .

  Variant task_well_typed: G -> option task -> Prop :=
    | task_wt_idle: forall Γ, task_well_typed Γ None
    | task_wt: forall Γ stmt l,
        (* this differs from the paper since we do not treat l as a typed list *)
        G_vdash_s Γ l ->
        stmt_well_typed Γ stmt ->
        task_well_typed Γ (Some (tsk stmt l))
  .

  Definition queue_well_typed (Γ:G) (q:queue) := forall t, t ∈ q -> task_well_typed Γ (Some t).

  Variant cn_well_typed: G -> cn -> Prop :=
    | ob_wt: forall Γ c Cl a p q fields,
        (* The paper also checks fields(Γ(o)), but we would need another case for ctxv *)
        get_class_decl c Cs = Some Cl ->
        get_fields Cl = fields ->
        queue_well_typed (extend_G Γ fields) q ->
        task_well_typed (extend_G Γ fields) p ->
        G_vdash_s (extend_G Γ fields) a ->
        cn_well_typed Γ (cn_object c a p q)
    | inv_wt: forall Γ o f T Ts m vs Cl,
        Γ !! f = Some (ctxv_fut T) ->
        typ_es Γ (map e_t vs) Ts ->
        get_class_decl (class_of o) Cs = Some Cl ->
        match_method m Ts T Cl ->
        cn_well_typed Γ (cn_invoc o f m vs)
    | fut_wt_none: forall G f T,
        G !! f = Some (ctxv_fut T) ->
        cn_well_typed  G (cn_future f None)
    | fut_wt_some: forall G f t T,
        G !! f = Some (ctxv_fut T) ->
        typ_e G (e_t t) T ->
        cn_well_typed  G (cn_future f (Some t))
  .
  Definition config_well_typed (G0:G) (conf: config) :=
    forall i ob, conf !! i = Some ob -> cn_well_typed G0 ob.

  (** useful tactics and lemmas *)

  Ltac lookup_cases H i j :=
    is_eq i j; [setoid_rewrite lookup_insert in H; inv H
               | setoid_rewrite lookup_insert_ne in H; auto].

  Ltac unfold_typing :=
    repeat (match goal with
            | H: cn_well_typed _ _ |- _ => inv H
            | H: task_well_typed _ _ |- _ => inv H
            | H: stmt_well_typed _ (stmt_seq _ _) |- _ => inv H
            | H: stmt_well_typed _ (stmt_asgn _ _) |- _ => inv H
            | H: stmt_well_typed _ (stmt_cond _ _ _) |- _ => inv H
            | H: stmt_well_typed _ (stmt_loop _ _) |- _ => inv H
            | H: stmt_well_typed _ (stmt_ret _) |- _ => inv H
            | H: typ_rhs _ _ _ |- _ => inv H
            (* | H: match_method _ _ _ _ |- _ => inv H *)
            end).

  (* should be a theorem, but will require some assumptions on name_of/id_of and typing of futures *)
  Hypothesis id_of_consistent: forall (σ:config) f f' v, σ !! (id_of f) = Some (cn_future f' v) -> f = f'.
  Variant is_fut: cn -> Prop := is_fut_intro: forall f v, is_fut (cn_future f v).
  Hypothesis id_of_well_typed: forall (σ:config) f c, σ !! (id_of f) = Some c -> is_fut c.

  Lemma fresh_config_wt: forall Γ f σ,
      fresh f σ -> config_well_typed Γ σ -> f ∉ dom Γ.
  Proof.
    unfold fresh, config_well_typed.
    intros.
    destruct (σ !! id_of f) eqn:?.
    - specialize (id_of_well_typed _ _ _ Heqo) as FUT_WT; auto.
      inv FUT_WT.
      specialize (H0 _ _ Heqo).
      specialize (id_of_consistent _ _ _ _ Heqo).
      intro.
      eapply H; eauto.
    - admit.
      (* this seems problematic *)
  Admitted.

  Lemma subG_extend: forall Γ l,
      Forall (fun '(_, x) => x ∉ dom Γ) l ->
      Γ ⊆ extend_G Γ l.
  Proof.
    induction l; intros; auto.
    destruct a; simpl in *.
    inv H.
    eapply subG_add; auto.
    simpl.
    now apply not_elem_of_dom.
  Qed.

  Lemma q_wt_remove: forall  G0 q,
      queue_well_typed  G0 q ->
      forall t, queue_well_typed  G0 (remove t q).
  Proof.
    intros*.
    apply H.
    multiset_solver.
  Qed.

  Lemma q_wt_add: forall  G0 q,
      queue_well_typed  G0 q ->
      forall t,
        task_well_typed G0 (Some t) ->
        queue_well_typed  G0 (add t q).
  Proof.
    intros*.
    apply gmultiset_elem_of_disj_union in H1.
    destruct H1; auto.
    now apply gmultiset_elem_of_singleton in H1; subst.
  Qed.

  Lemma G_vdash_union: forall Γ σ σ',
      G_vdash_s Γ σ ->
      (* somewhat surprisingly we do not need σ' because map_union prefers the left*)
      (* G_vdash_s Γ σ' -> *)
      G_vdash_s Γ (union σ σ').
  Proof.
    intros*.
    apply H in H0.
    destruct H0 as (?t & LU & TYP).
    exists t.
    split; simp; auto.
  Qed.

  (* this is a problem: well-typing of tasks is not closed under extensions *)
  Fact subG_task_wt : exists Γ1 Γ2 t,
      Γ1 ⊆ Γ2 /\ task_well_typed  Γ1 t /\ ~ task_well_typed  Γ2 t.
  Proof.
    exists ∅, (<["x":=ctxv_T T_bool]> ∅), (Some (tsk stmt_skip (<["x":=t_int Z0]> ∅))).
    splits.
    - now apply insert_subseteq.
    - econstructor.
      + intros*.
        inv H.
      + constructor.
    - inv 1.
      pose proof H3 "x" (ctxv_T T_bool) as (?t' & ? & ?); auto.
      simpl in H0.
      inv H0.
  Qed.

  (* this substitution and subsequent well-typing is not currently used *)
  (* I thought I might use it, and then didn't, but may be useful later? *)
  Equations e_subst_s : s -> e -> e := {
      e_subst_s _ (e_t t) := e_t t;
      e_subst_s σ (e_var x_) := match σ !! x_ with | Some t => (e_t t) | None => (e_var x_) end ;
      e_subst_s σ (e_fn_call fn_ es) := e_fn_call fn_ (e_subst_list_s σ es) }
  where e_subst_list_s: s -> list e -> list e := {
      e_subst_list_s _ [] := [] ;
      e_subst_list_s σ (e_::es) := e_subst_s σ e_ :: e_subst_list_s σ es
    }.

  (* the well-typedness from the paper, ours is a little stricter *)
  Definition sub_well_typed (Γ : G) (σ : s) :=
    forall (x_: x) (T_: T),
      x_ ∈ dom σ ->
      Γ !! x_ = Some (ctxv_T T_) ->
      typ_e Γ (e_subst_s σ (e_var x_)) T_.

  Lemma vdash_implies_wt: forall Γ σ,
      G_vdash_s Γ σ ->
      sub_well_typed Γ σ.
  Proof.
    intros*.
    pose proof H x_ (ctxv_T T_) H1 as (?t_ & LU & TYP).
    autorewrite with e_subst_s.
    now rewrite LU.
  Qed.

  (* just like our vdash, this is the wrong way *)
  Lemma subG_sub_wt: forall Γ1 Γ2 σ,
      Γ1 ⊆ Γ2 -> sub_well_typed Γ2 σ -> sub_well_typed Γ1 σ.
  Proof.
    intros*.
    specialize (H0 x_ T_ H1).
    autorewrite with e_subst_s in *.
    apply elem_of_dom in H1.
    inv H1.
    setoid_rewrite H3.
    eapply map_subseteq_spec in H; eauto.
    apply H0 in H.
    setoid_rewrite H3 in H.
    inv H; constructor.
  Qed.

  Lemma subG_typ_es: forall G1 G2 es Ts,
      subseteq G1 G2 -> typ_es G1 es Ts -> typ_es G2 es Ts.
  Proof.
    induction es; destruct Ts; auto; intros.
    autorewrite with typ_es in *.
    destruct H0.
    split; auto.
    eapply subG_type; eauto.
  Qed.

  Lemma subG_typ_rhs: forall G1 G2 r T0,
      subseteq G1 G2 -> typ_rhs G1 r T0 -> typ_rhs G2 r T0.
  Proof.
    intros.
    inv H0.
    - econstructor.
      eapply subG_type; eauto.
    - econstructor; eauto.
      eapply subG_typ_es; eauto.
    - econstructor.
      eapply lookup_weaken; eauto.
  Qed.

  Lemma subG_stmt_wt: forall G1 G2 st,
      subseteq G1 G2 -> stmt_well_typed G1 st -> stmt_well_typed G2 st.
  Proof.
    intros.
    induction H0; eauto;
      try (now econstructor; eauto).
    - econstructor.
      + eapply lookup_weaken; eauto.
      + eapply subG_typ_rhs; eauto.
    - econstructor; eauto.
      eapply subG_type; eauto.
    - econstructor; eauto.
      eapply subG_type; eauto.
    - econstructor.
      + eapply subG_type; eauto.
      + eapply lookup_weaken; eauto.
  Qed.

  Lemma fresh_extend_wt: forall Γ σ f,
      config_well_typed Γ σ ->
      fresh f σ ->
      forall T_,
        config_well_typed (<[f:=T_]> Γ) σ.
  Proof.
  Admitted.

  Theorem type_preservation : forall (Γ: G),
      Forall (typ_F Γ) Fs ->
      forall σ σ',
        config_well_typed Γ σ ->
        stmt_step Cs Fs id_of σ σ' ->
        exists Γ', Γ ⊆ Γ' /\ config_well_typed Γ' σ'.
  Proof.
    intros.
    inv H1.
    - exists Γ; split; auto.
      intros*.
      lookup_cases H1 i i0.
      + specialize (H0 _ _ H3).
        unfold_typing.
        destruct p.
        econstructor; eauto.
        now apply q_wt_remove.
      + eapply H0;eauto.

    - destruct H3 as [sf ?].
      pose proof H1 as Conf_wt.
      specialize (H0 _ _ H4).
      unfold_typing.
      epose proof type_preservation _ _ _ _ _ _ _ _ _ H5 H1
        as (?Γ & ?SUB & ? & ?TYP_E).
      (* are tasks actually well-typed under this extension? *)
      admit.
      Unshelve.
      + apply vars_fs_distinct.
      + now apply G_vdash_union.
      + apply subG_typ_F_forall with Γ; auto.
        apply subG_extend.
        admit. (* can we guarantee that the fields are not already in the context? *)

    - destruct H3 as [sf ?].
      pose proof H1 as Conf_wt.
      specialize (H0 _ _ H4).
      unfold_typing.
      epose proof type_preservation _ _ _ _ _ _ _ _ _ H5 H1
        as (?Γ & ?SUB & ? & ?TYP_E).
      admit.

    (* the trivial cases (ifs, skips, loops) are very similar*)
    (* TODO: automate *)
    - pose proof H0 as Conf_wt.
      specialize (H0 _ _ H3).
      unfold_typing.
      exists Γ; split; auto.
      intros*.
      lookup_cases H0 o i.
      + repeat (econstructor; eauto).
      + eapply Conf_wt; eauto.

    - pose proof H0 as Conf_wt.
      specialize (H0 _ _ H3).
      unfold_typing.
      exists Γ; split; auto.
      intros*.
      lookup_cases H0 o i.
      + repeat (econstructor; eauto).
      + eapply Conf_wt; eauto.

    - pose proof H0 as Conf_wt.
      specialize (H0 _ _ H2).
      unfold_typing.
      exists Γ; split; auto.
      intros*.
      lookup_cases H0 o i.
      + repeat (econstructor; eauto).
      + eapply Conf_wt; eauto.

    - pose proof H0 as Conf_wt.
      specialize (H0 _ _ H2).
      unfold_typing.
      exists Γ; split; auto.
      intros*.
      lookup_cases H0 o i.
      + repeat (econstructor; eauto).
      + eapply Conf_wt; eauto.

    - pose proof H0 as Conf_wt.
      specialize (H0 _ _ H2).
      unfold_typing.
      exists Γ; split; auto.
      intros*.
      lookup_cases H0 o i.
      + repeat (econstructor; eauto).
      + eapply Conf_wt; eauto.

    - pose proof H0 as Conf_wt.
      specialize (H0 _ _ H5).
      unfold_typing.
      pose proof H18 as Method_wt.
      inv H18.
      destruct method.
      autorewrite with get_type get_params in *.
      epose proof type_preservation_eval_list _ _ _ _ _ _ _ H15 H4 as TYP_ARGS.
      exists (<[f:=ctxv_fut T_5]> Γ).
      split.
      + apply subG_add; auto.
        apply not_elem_of_dom.
        eapply fresh_config_wt; eauto.
      + intros*.
        lookup_cases H1 oi i0.
        * econstructor; eauto.
          -- admit.
          -- constructor; auto.
             ++ admit.
             ++ econstructor.
                ** econstructor; eauto.
                   --- admit.
                   --- econstructor.
                       eapply lookup_weaken with (<[f:=ctxv_fut T_5]> Γ).
                       +++ apply lookup_insert.
                       +++ apply subG_extend.
                           admit.
                ** eapply subG_stmt_wt.
                   --- admit.
                   --- eauto.
          -- admit. (* should follow from freshness *)
        * lookup_cases H1 i i0.
          -- econstructor; eauto.
             ++ apply lookup_insert.
             ++ admit. (* I would like to use TYP_ARGS, but that includes the fields from the object *)
          -- set (fi:=id_of f).
             is_eq fi i0; subst fi.
             ++ setoid_rewrite lookup_insert in H1.
                inv H1.
                econstructor.
                apply lookup_insert.
             ++ setoid_rewrite lookup_insert_ne in H1; auto.
                eapply fresh_extend_wt; eauto.

    - pose proof H0 _ _ H3 as fut_well_typed.
      pose proof H0 _ _ H4 as ob_well_typed.
      exists Γ; split; auto.
      intros*.
      unfold_typing.
      lookup_cases H1 o i.
      + econstructor; eauto.
        econstructor.
      + lookup_cases H1 fi i.
        * econstructor; eauto.
          epose proof type_preservation_eval _ _ _ _ _ _ _ H7 H2.
          enough (T0 = T) by (subst; inv H1; constructor).
          pose proof (H11 _ _ H14) as (?t & ? & ?); simp.
          inv H1; inv H9.
        * eapply H0; eauto.

    - pose proof H0 _ _ H2 as fut_well_typed.
      pose proof H0 _ _ H3 as ob_well_typed.
      exists Γ; split; auto.
      intros*.
      unfold_typing.
      lookup_cases H1 o i.
      + repeat (econstructor; eauto).
        replace T1 with T by admit. (* follows from f ∉ fields(Cl) *)
        eapply subG_type with Γ; auto.
        apply subG_extend.
        admit.
      + eapply H0; eauto.

    - pose proof H0 _ _ H2 as ob_well_typed.
      pose proof H0 _ _ H3 as inv_well_typed.
      exists Γ; split; auto.
      intros*.
      unfold_typing.
      + lookup_cases H1 oi i0.
        * repeat (econstructor; eauto).
          apply q_wt_add; auto.
          admit. (* here we need Γ ⊢ Cl -> Γ ⊢ bind m vs f*)
        * is_eq i i0.
          -- exfalso.
             setoid_rewrite (lookup_delete σ i) in H1.
             inv H1.
          -- setoid_rewrite lookup_delete_ne in H1; auto.
             eapply H0; eauto.
      + lookup_cases H1 oi i0.
        * repeat (econstructor; eauto).
          apply q_wt_add; auto.
          admit. (* here we need Γ ⊢ Cl -> Γ ⊢ bind m vs f*)
        * is_eq i i0.
          -- exfalso.
             setoid_rewrite (lookup_delete σ i) in H1.
             inv H1.
          -- setoid_rewrite lookup_delete_ne in H1; auto.
             eapply H0; eauto.

             Unshelve.
             all: try eauto.
             all: try (now apply G_vdash_union).
             (*remaining: typ_F closed under (well-typed?) extensions *)
  Admitted.
End Typing.
(*TODO: labels + traces? *)
