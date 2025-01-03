From stdpp Require Import prelude strings fin_maps natmap gmap gmultiset.
From ABS Require Import list_util abs_defs abs_util abs_functional_metatheory abs_imp.

(* based on https://link.springer.com/chapter/10.1007/978-3-642-25271-6_8 *)
Section Typing.
Context
  (Cs: list CL)
    (Fs: list F)
    (*name_of should probably be partial to account for non-future ids *)
    (name_of: id -> f)
    (id_of: f -> id)
    (class_of: o -> C)
.

Hypothesis (vars_fs_distinct: forall (x_:x) (fn:fc), x_ <> fn).
Hypothesis id_of_consistent: forall (σ:config) f f' v, σ !! (id_of f) = Some (cn_future f' v) -> f = f'.
Hypothesis id_of_well_typed: forall (σ:config) f c, σ !! (id_of f) = Some c -> is_fut c.
Hypothesis id_of_name_of: forall i, id_of (name_of i) = i.
Hypothesis name_of_id_of: forall f, name_of (id_of f) = f.

Lemma vdash_implies_wt: forall Γ σ,
    G_vdash_s Γ σ ->
    sub_well_typed Γ σ.
Proof.
  intros*.
  pose proof H x_ (ctxv_T T_) H1 as (?t_ & LU & TYP).
  autorewrite with e_subst_s.
  now rewrite LU.
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

Lemma typ_term_invariant: forall Γ v T,
    typ_e Γ (e_t v) T ->
    forall Γ',
      typ_e Γ' (e_t v) T.
Proof.
  intros.
  inv H; constructor.
Qed.

Lemma typ_term_list_invariant: forall Γ vs Ts,
    typ_es Γ (map e_t vs) Ts ->
    forall Γ',
      typ_es Γ' (map e_t vs) Ts.
Proof.
  induction vs; destruct Ts; intros; auto.
  simpl in *.
  autorewrite with typ_es in *.
  destruct H.
  split; auto.
  eapply typ_term_invariant; eauto.
Qed.

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
      typ_rhs Γ (rhs_invoc o m es) (ctxv_T T)
  | typ_rhs_get: forall Γ f T,
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
      (* G_vdash_s Γ l -> *)
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
          end).

Definition config_well_typed (G0:G) (conf: config) :=
  forall i ob, conf !! i = Some ob -> cn_well_typed G0 ob.

(* should be a theorem, but will require some assumptions on name_of/id_of and typing of futures *)
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

(* this is a problem: well-typing of tasks is not closed under extensions *)
(* currently commented out along with the G_vdash_part of task_well_typed *)
(* Fact subG_task_wt : exists Γ1 Γ2 t, *)
(*     Γ1 ⊆ Γ2 /\ task_well_typed  Γ1 t /\ ~ task_well_typed  Γ2 t. *)
(* Proof. *)
(*   exists ∅, (<["x":=ctxv_T T_bool]> ∅), (Some (tsk stmt_skip (<["x":=t_int Z0]> ∅))). *)
(*   splits. *)
(*   - now apply insert_subseteq. *)
(*   - econstructor. *)
(*     + intros*. *)
(*       inv H. *)
(*     + constructor. *)
(*   - inv 1. *)
(*     pose proof H3 "x" (ctxv_T T_bool) as (?t' & ? & ?); auto. *)
(*     simpl in H0. *)
(*     inv H0. *)
(* Qed. *)

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

Lemma subG_task_wt : forall Γ1 Γ2 t,
    Γ1 ⊆ Γ2 -> task_well_typed  Γ1 t -> task_well_typed  Γ2 t.
Proof.
  intros.
  destruct t.
  - destruct t.
    constructor.
    inv H0.
    eapply subG_stmt_wt; eauto.
  - constructor.
Qed.

Lemma subG_queue_wt : forall Γ1 Γ2 q,
    Γ1 ⊆ Γ2 -> queue_well_typed  Γ1 q -> queue_well_typed  Γ2 q.
Proof.
  intros*.
  eapply subG_task_wt; eauto.
Qed.

Lemma fresh_extend_wt: forall Γ σ f,
    config_well_typed Γ σ ->
    fresh f σ ->
    forall T_,
      config_well_typed (<[f:=T_]> Γ) σ.
Proof.
  intros.
  intros i ob LUi.
  remember (id_of f) as fi.
  is_eq i fi; subst.
  - pose proof id_of_well_typed _ _ _ LUi as FUT.
    inv FUT.
    pose proof H0 _ _ _ LUi.
    pose proof id_of_consistent _ _ _ _ LUi as <- .
    contradiction.
  - epose proof H i ob LUi.
    destruct ob.
    + enough (diff : f <> f5).
      {
        destruct to5.
        - inv H1.
          econstructor; auto.
          + setoid_rewrite lookup_insert_ne; eauto.
          + inv H6; constructor.
        - inv H1.
          econstructor.
          setoid_rewrite lookup_insert_ne; eauto.
      }
      intro.
      replace i with (id_of (name_of i)) in *
          by apply id_of_name_of.
      pose proof id_of_consistent _ _ _ _ LUi.
      subst.
      contradiction.
    + admit.
    (* adding a future to the context does not impact typing of an object *)
    + admit.
      (* for invocations it is less obvious *)
Admitted.

Lemma bind_wt: forall m Ts T CL vs f tsk,
    match_method m Ts T CL ->
    bind m vs f CL = tsk ->
    forall Γ,
      Γ !! f = Some (ctxv_fut T) ->
      typ_es Γ (map e_t vs) Ts ->
      task_well_typed Γ tsk.
Proof.
Admitted.

Lemma insert_lookup_ne_extend: forall Γ i j T_ l,
    i <> j ->
    extend_G (<[j:=T_]> Γ) l !! i = extend_G Γ l !! i.
Proof.
  induction l; intros; simpl.
  - now apply lookup_insert_ne.
  - unfold add_G; destruct a; simpl.
    is_eq i x.
    + now setoid_rewrite lookup_insert.
    + setoid_rewrite lookup_insert_ne; eauto.
Qed.

Definition CL_well_typed: G -> CL -> Prop := fun _ _ => True. (*TODO: implement*)

Lemma CL_wt_fields_fresh: forall Γ C,
    CL_well_typed Γ C ->
    Forall (λ '(_, x), x ∉ dom Γ) (get_fields C).
Admitted.
(* arguably too strong, we only really need them to agree *)
(* replace subG_extend with a weaker version *)

Lemma CL_wt_add_f: forall Γ C (f:f) T,
    CL_well_typed Γ C ->
    CL_well_typed (<[f:=T]> Γ) C.
Admitted.

Lemma Forall_typ_F_extension: forall Γ Fs Cl,
    Forall (typ_F Γ) Fs ->
    Forall (CL_well_typed Γ) Cs ->
    In Cl Cs ->
    Forall (typ_F (extend_G Γ (get_fields Cl))) Fs.
Admitted.

Theorem type_preservation : forall (Γ: G),
    Forall (typ_F Γ) Fs ->
    Forall (CL_well_typed Γ) Cs ->
    forall σ σ',
      config_well_typed Γ σ ->
      @stmt_step Fs σ σ' ->
      exists Γ', Γ ⊆ Γ' /\ config_well_typed Γ' σ'.
Proof.
  intros Γ TYP_Fs TYP_Cs σ σ' WT STEP.
  inv STEP.
  - exists Γ; split; auto.
    intros*.
    lookup_cases H1 i i0.
    + specialize (WT _ _ H0).
      unfold_typing.
      destruct p.
      econstructor; eauto.
      now apply q_wt_remove.
    + eapply WT;eauto.

  - destruct H0 as [sf ?].
    pose proof WT as Conf_wt.
    specialize (WT _ _ H1).
    unfold_typing.
    epose proof type_preservation _ _ _ _ _ _ _ _ _ H4 H0
      as (?Γ & ?SUB & ? & ?TYP_E).
    (* are tasks actually well-typed under this extension? *)
    eexists.
    split; eauto.
    intros*.
    lookup_cases H3 i i0.
    + econstructor; eauto.
      econstructor; eauto.
    + eapply Conf_wt; eauto.

  - destruct H0 as [sf ?].
    pose proof WT as Conf_wt.
    specialize (WT _ _ H1).
    unfold_typing.
    epose proof type_preservation _ _ _ _ _ _ _ _ _ H4 H0
      as (?Γ & ?SUB & ? & ?TYP_E).
    exists Γ0.
    split.
    + eapply extend_subG_2; eauto.
      apply CL_wt_fields_fresh.
      eapply Forall_forall; eauto.
      eapply get_class_decl_some; eauto.
    + intros*.
      lookup_cases H3 o i.
      * assert (extend_G Γ (get_fields Cl) ⊆ extend_G Γ0 (get_fields Cl)). {
          eapply extend_subG.
          eapply extend_subG_2; eauto.
          apply CL_wt_fields_fresh.
          eapply Forall_forall; eauto.
          eapply get_class_decl_some; eauto.
        }
        econstructor; eauto.
        -- eapply subG_queue_wt; eauto.
        -- constructor.
            eapply subG_stmt_wt; eauto.
        -- admit. (* here we are lost without consistency of a *)
      * admit. (* we need cn_well_typed closed under extensions *)

  (* the trivial cases (ifs, skips, loops) are very similar*)
  (* TODO: automate *)
  - pose proof WT as Conf_wt.
    specialize (WT _ _ H0).
    unfold_typing.
    exists Γ; split; auto.
    intros*.
    lookup_cases H1 o i.
    + repeat (econstructor; eauto).
    + eapply Conf_wt; eauto.

  - pose proof WT as Conf_wt.
    specialize (WT _ _ H0).
    unfold_typing.
    exists Γ; split; auto.
    intros*.
    lookup_cases H1 o i.
    + repeat (econstructor; eauto).
    + eapply Conf_wt; eauto.

  - pose proof WT as Conf_wt.
    specialize (WT _ _ H).
    unfold_typing.
    exists Γ; split; auto.
    intros*.
    lookup_cases H0 o i.
    + repeat (econstructor; eauto).
    + eapply Conf_wt; eauto.

  - pose proof WT as Conf_wt.
    specialize (WT _ _ H).
    unfold_typing.
    exists Γ; split; auto.
    intros*.
    lookup_cases H0 o i.
    + repeat (econstructor; eauto).
    + eapply Conf_wt; eauto.

  - pose proof WT as Conf_wt.
    specialize (WT _ _ H).
    unfold_typing.
    exists Γ; split; auto.
    intros*.
    lookup_cases H0 o i.
    + repeat (econstructor; eauto).
    + eapply Conf_wt; eauto.

  - pose proof WT as Conf_wt.
    specialize (WT _ _ H3).
    unfold_typing.
    pose proof H17 as Method_wt.
    inv H17.
    destruct method.
    autorewrite with get_type get_params in *.
    epose proof type_preservation_eval_list _ _ _ _ _ _ _ H14 H2 as TYP_ARGS.
    exists (<[f:=ctxv_fut T_5]> Γ).
    split.
    + apply subG_add; auto.
      apply not_elem_of_dom.
      eapply fresh_config_wt; eauto.
    + intros*.
      lookup_cases H5 oi i0.
      * econstructor; eauto.
        -- eapply subG_queue_wt; last apply H11.
            eapply extend_subG.
            apply subG_add; auto.
            apply not_elem_of_dom_1.
            eapply fresh_config_wt; eauto.
        -- constructor.
            econstructor.
            ++ econstructor; eauto.
              ** rewrite insert_lookup_ne_extend; eauto.
              ** econstructor.
                  eapply lookup_weaken with (<[f:=ctxv_fut T_5]> Γ).
                  --- now setoid_rewrite lookup_insert.
                  --- apply subG_extend.
                      apply CL_wt_fields_fresh.
                      apply CL_wt_add_f.
                      eapply Forall_forall; eauto.
                      eapply get_class_decl_some; eauto.
            ++ eapply subG_stmt_wt; last apply H10.
              eapply extend_subG.
              apply subG_add; auto.
              apply not_elem_of_dom_1.
              eapply fresh_config_wt; eauto.
        -- admit. (* should follow from freshness *)

      * lookup_cases H5 i i0.
        -- econstructor; eauto.
            ++ apply lookup_insert.
            ++ eapply typ_term_list_invariant; eauto.
        -- set (fi:=id_of f).
           replace j with (id_of f) in * by admit. (* we need id_of to be consistent with j*)
           is_eq fi i0; subst fi.
           ++ setoid_rewrite lookup_insert in H5.
              inv H5.
              econstructor.
              apply lookup_insert.
            ++ setoid_rewrite lookup_insert_ne in H5; auto.
              eapply fresh_extend_wt; eauto.

  - pose proof WT _ _ H0 as fut_well_typed.
    pose proof WT _ _ H1 as ob_well_typed.
    exists Γ; split; auto.
    intros*.
    unfold_typing.
    lookup_cases H3 o i.
    + econstructor; eauto.
      econstructor.
    + lookup_cases H3 fi i.
      * econstructor; eauto.
        epose proof type_preservation_eval _ _ _ _ _ _ _ H5 H.
        enough (T0 = T) by (subst; inv H3; constructor).
        (* now we have a problem since the local state is not required to be consistent *)
        (* pose proof (H15 _ _ H5) as (?t & ? & ?); simp. *)
        (* inv H1; inv H9. *)
        admit.
      * eapply WT; eauto.

  - pose proof WT _ _ H as fut_well_typed.
    pose proof WT _ _ H0 as ob_well_typed.
    exists Γ; split; auto.
    intros*.
    unfold_typing.
    lookup_cases H1 o i.
    + repeat (econstructor; eauto).
      enough (T1 = T) by (subst; eapply typ_term_invariant; eauto).
      eapply lookup_weaken with (m2:=extend_G Γ (get_fields Cl)) in H5.
      now simp.
      apply subG_extend.
      apply CL_wt_fields_fresh.
      eapply Forall_forall; eauto.
      eapply get_class_decl_some; eauto.
    + eapply WT; eauto.

  - pose proof WT _ _ H as ob_well_typed.
    pose proof WT _ _ H0 as inv_well_typed.
    exists Γ; split; auto.
    intros*.
    unfold_typing.
    + lookup_cases H1 oi i0.
      * repeat (econstructor; eauto).
        apply q_wt_add; auto.
        replace CL with Cl in * by admit. (* by welformedness of class_of, probably *)
        eapply bind_wt; eauto.
        -- apply lookup_weaken with Γ; auto.
            apply subG_extend.
            apply CL_wt_fields_fresh.
            eapply Forall_forall; eauto.
            eapply get_class_decl_some; eauto.
        -- eapply subG_typ_es; last apply H9.
            apply subG_extend.
            apply CL_wt_fields_fresh.
            eapply Forall_forall; eauto.
            eapply get_class_decl_some; eauto.
      * is_eq i i0.
        -- exfalso.
            setoid_rewrite (lookup_delete σ i) in H1.
            inv H1.
        -- setoid_rewrite lookup_delete_ne in H1; auto.
            eapply WT; eauto.
    + lookup_cases H1 oi i0.
      * repeat (econstructor; eauto).
        apply q_wt_add; auto.
        replace CL with Cl in * by admit. (* by welformedness of class_of, probably *)
        eapply bind_wt; eauto.
        -- apply lookup_weaken with Γ; auto.
            apply subG_extend.
            apply CL_wt_fields_fresh.
            eapply Forall_forall; eauto.
            eapply get_class_decl_some; eauto.
        -- eapply subG_typ_es; last apply H9.
            apply subG_extend.
            apply CL_wt_fields_fresh.
            eapply Forall_forall; eauto.
            eapply get_class_decl_some; eauto.

      * is_eq i i0.
        -- exfalso.
            setoid_rewrite (lookup_delete σ i) in H1.
            inv H1.
        -- setoid_rewrite lookup_delete_ne in H1; auto.
            eapply WT; eauto.

            Unshelve.
            all: try eauto.
            all: try (now apply G_vdash_union).
            all: apply Forall_typ_F_extension; auto;
              eapply get_class_decl_some; eauto.
Admitted.
End Typing.
(*TODO: labels + traces? *)
