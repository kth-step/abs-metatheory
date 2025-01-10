From stdpp Require Import prelude strings fin_maps natmap gmap gmultiset.
From ABS Require Import list_util abs_defs abs_util abs_functional_metatheory abs_imp.

(* first some useful lemmas *)
(* it would maybe be good to have these in abs_util and export abs_functional_metatheory from there *)
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

Lemma typ_term_unique: forall Γ v T,
    typ_e Γ (e_t v) T ->
    forall Γ' T',
      typ_e Γ' (e_t v) T' -> T = T'.
Proof.
  intros.
  inv H; inv H0; auto.
Qed.

(* based on https://link.springer.com/chapter/10.1007/978-3-642-25271-6_8 *)
Section Typing.
Context
  (Cs: list CL)
    (Fs: list F)
    (*name_of should probably be partial to account for non-future ids *)
    (name_of: id -> f)
    (id_of: string -> id)
    (class_of: o -> C)
.

Hypothesis (vars_fs_distinct: forall (x_:x) (fn:fc), x_ <> fn).
Hypothesis id_of_consistent: forall (σ:config) f f' v, σ !! (id_of f) = Some (cn_future f' v) -> f = f'.
Hypothesis id_of_well_typed: forall (σ:config) f c, σ !! (id_of f) = Some c -> is_fut c.
Hypothesis id_of_name_of: forall i, id_of (name_of i) = i.
Hypothesis name_of_id_of: forall f, name_of (id_of f) = f.

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

(* I don't really like this formulation *)
Definition state_well_typed: G -> a -> Prop :=
  fun Γ l => forall x (T:ctxv) (v:t), l !! x = Some (T, v) ->
                   Γ !! x = Some T /\ typ_e Γ (e_t v) (abs_functional_metatheory.get_type T).

Definition new_T: option ctxv -> option (ctxv*t) -> option ctxv :=
  diag_None (fun To Tto =>
               match Tto with
               | Some (T, v) => Some T
               | None => match To with
                        |Some T => Some T
                        | None => None
                        end
               end).

Definition extendG_by_a: G -> a -> G := merge new_T.

Lemma lookup_a_to_s: forall l x v,
    (exists T, l !! x = Some (T, v)) <-> (a_to_s l) !! x = Some v.
Proof.
  unfold a_to_s;
    setoid_rewrite lookup_fmap.
  split; intros.
  - destruct H as (?T & ?).
    now setoid_rewrite H.
  - apply fmap_Some in H.
    destruct H as ((?T&?v)&?&->).
    exists T; auto.
Qed.

Lemma state_wt_insert: forall Γ ρ x v T,
    state_well_typed Γ ρ ->
    Γ !! x = Some (ctxv_T T) ->
    typ_e Γ (e_t v) T ->
    state_well_typed Γ (update_a x v ρ).
Proof.
  intros*.
    is_eq x0 x.
    - unfold a_to_s, update_a in *.
      setoid_rewrite lookup_partial_alter in H2.
      apply fmap_Some in H2.
      destruct H2 as ((?T&?v) & ? & ?).
      inv H3.
      pose proof H _ _ _ H2 as (?&?).
      split; now simplify_map_eq.
    - unfold a_to_s, update_a in *.
      setoid_rewrite lookup_partial_alter_ne in H2; auto.
Qed.

Lemma state_extend_wt: forall Γ l,
    state_well_typed Γ l ->
    state_well_typed (extendG_by_a Γ l) l.
Proof.
  intros*.
  specialize (H _ _ _ H0) as (?&?).
  split.
  - setoid_rewrite lookup_merge.
    setoid_rewrite H0.
    setoid_rewrite H.
    now simplify_map_eq.
  - eapply typ_term_invariant; eauto.
Qed.

Lemma a_to_s_wt: forall Γ l,
    state_well_typed Γ l ->
    G_vdash_s Γ (a_to_s l) ->
    G_vdash_s (extendG_by_a Γ l) (a_to_s l).
Proof.
  unfold extendG_by_a.
  intros*.
  setoid_rewrite lookup_merge in H1.
  destruct (l !! x5) eqn:?.
  - destruct p.
    specialize (H _ _ _ Heqo) as (?&?).
    setoid_rewrite Heqo in H1.
    setoid_rewrite H in H1.
    inv H1.
    exists t.
    split; auto.
    + apply lookup_a_to_s.
      eexists; eauto.
    + eapply typ_term_invariant; eauto.
  - setoid_rewrite Heqo in H1.
    destruct (Γ !! x5) eqn:?;
      setoid_rewrite Heqo0 in H1;
      inv H1.
    pose proof H0 _ _ Heqo0 as (?t & ? & ?).
    exfalso.
    apply lookup_a_to_s in H1.
    destruct H1.
    simplify_map_eq.
Qed.

Lemma subG_state_wt: forall Γ1 Γ2 σ,
    Γ1 ⊆ Γ2 -> state_well_typed Γ1 σ -> state_well_typed Γ2 σ.
Proof.
  intros*.
  specialize (H0 _ _ _ H1) as (?&?).
  split.
  - eapply lookup_weaken; last apply H.
    eapply H0; eauto.
  - eapply typ_term_invariant; eauto.
Qed.

Variant process_well_typed: G -> option task -> Prop :=
  | process_wt_idle: forall Γ, process_well_typed Γ None
  | process_wt: forall Γ stmt l,
      state_well_typed (extendG_by_a Γ l) l ->
      stmt_well_typed (extendG_by_a Γ l) stmt ->
      process_well_typed Γ (Some (tsk stmt l))
.

Lemma extend_by_a_subG: forall Γ1 Γ2 l,
    Γ1 ⊆ Γ2 -> extendG_by_a Γ1 l ⊆ extendG_by_a Γ2 l.
Proof.
  intros*; simpl.
  unfold extendG_by_a.
  destruct (merge new_T Γ1 l !! i) eqn:?, (merge new_T Γ2 l !! i) eqn:?; simpl;
    rewrite lookup_merge in *;
  destruct (Γ1 !! i) eqn:?,
    (Γ2 !! i) eqn:?,
    (l !! i) eqn:?;
    setoid_rewrite Heqo1 in Heqo;
    setoid_rewrite Heqo2 in Heqo0;
    setoid_rewrite Heqo3 in Heqo;
    setoid_rewrite Heqo3 in Heqo0;
    inv Heqo;
    inv Heqo0; simplify_map_eq; auto.

    epose proof lookup_weaken _ _ _ _ Heqo1 H.
    setoid_rewrite H0 in Heqo2.
    discriminate.
Qed.

Lemma subG_extend_insert: forall Γ l x v,
    state_well_typed Γ l ->
    extendG_by_a Γ l ⊆ extendG_by_a Γ (update_a x v l).
Proof.
  intros*.
  destruct (extendG_by_a Γ l !! i) eqn:?,
    (extendG_by_a Γ (update_a x v l) !! i) eqn:?;
    setoid_rewrite Heqo;
    setoid_rewrite Heqo0;
    simpl;

  try (unfold update_a, extendG_by_a in *;
    setoid_rewrite lookup_merge in Heqo;
    setoid_rewrite lookup_merge in Heqo0;
    is_eq x i;
    [ setoid_rewrite lookup_partial_alter in Heqo0;
      destruct (Γ !! x) eqn:?, (l !! x) eqn:?;
        setoid_rewrite Heqo1 in Heqo;
      setoid_rewrite Heqo2 in Heqo;
      setoid_rewrite Heqo1 in Heqo0;
      setoid_rewrite Heqo2 in Heqo0;
      try destruct p;
      simplify_map_eq; auto
    | setoid_rewrite lookup_partial_alter_ne in Heqo0;
      destruct (Γ !! i) eqn:?, (l !! i) eqn:?;
        setoid_rewrite Heqo1 in Heqo;
      setoid_rewrite Heqo2 in Heqo;
      setoid_rewrite Heqo1 in Heqo0;
      try setoid_rewrite Heqo2 in Heqo0;
      try destruct p;
      simplify_map_eq; auto
    ]).
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

Definition queue_well_typed (Γ:G) (q:queue) := forall t, t ∈ q -> process_well_typed Γ (Some t).

Variant cn_well_typed: G -> cn -> Prop :=
  | ob_wt: forall Γ c Cl a p q fields,
      get_class_decl c Cs = Some Cl ->
      get_fields Cl = fields ->
      queue_well_typed (extend_G Γ fields) q ->
      process_well_typed (extend_G Γ fields) p ->
      state_well_typed (extend_G Γ fields) a ->
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
          | H: process_well_typed _ _ |- _ => inv H
          | H: stmt_well_typed _ (stmt_seq _ _) |- _ => inv H
          | H: stmt_well_typed _ (stmt_asgn _ _) |- _ => inv H
          | H: stmt_well_typed _ (stmt_cond _ _ _) |- _ => inv H
          | H: stmt_well_typed _ (stmt_loop _ _) |- _ => inv H
          | H: stmt_well_typed _ (stmt_ret _) |- _ => inv H
          | H: typ_rhs _ _ _ |- _ => inv H
          end).

Definition config_well_typed (G0:G) (conf: config) :=
  forall i ob, conf !! i = Some ob -> cn_well_typed G0 ob.

Definition minimal (Γ:G) (conf:config): Prop := forall (y:string), y ∈ dom Γ -> occurs_in conf y.

Lemma fresh_config_wt: forall Γ f σ,
    fresh f σ -> config_well_typed Γ σ -> minimal Γ σ -> f ∉ dom Γ.
Proof.
  intros.
  destruct (σ !! id_of f) eqn:?.
  - specialize (id_of_well_typed _ _ _ Heqo) as FUT_WT; auto.
  - intro.
    apply H.
    now apply H1.
Qed.

Lemma q_wt_empty: forall Γ, queue_well_typed Γ ∅.
Proof. intros*. inv H. Qed.

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
      process_well_typed G0 (Some t) ->
      queue_well_typed  G0 (add t q).
Proof.
  intros*.
  apply gmultiset_elem_of_disj_union in H1.
  destruct H1; auto.
  now apply gmultiset_elem_of_singleton in H1; subst.
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

Lemma subG_process_wt: forall G1 G2 p,
    subseteq G1 G2 -> process_well_typed G1 p -> process_well_typed G2 p.
Proof.
  intros.
  destruct p; try constructor.
  inv H0.
  constructor.
  - eapply subG_state_wt; last apply H2.
    apply extend_by_a_subG; auto.
  - eapply subG_stmt_wt; last apply H4.
    apply extend_by_a_subG; auto.
Qed.

Lemma subG_queue_wt: forall G1 G2 q,
    subseteq G1 G2 -> queue_well_typed G1 q -> queue_well_typed G2 q.
Proof.
  intros*.
  eapply subG_process_wt; eauto.
Qed.

Lemma subG_cn_wt: forall G1 G2 cn,
    subseteq G1 G2 -> cn_well_typed G1 cn -> cn_well_typed G2 cn.
Proof.
  destruct cn; intros.
  - inv H0; econstructor.
    + eapply lookup_weaken; last apply H; eauto.
    + eapply lookup_weaken; last apply H; eauto.
    + eapply typ_term_invariant; eauto.
  - inv H0.
    econstructor; eauto.
    + eapply subG_queue_wt; last apply H8.
      now apply extend_subG.
    + eapply subG_process_wt; last apply H9.
      now apply extend_subG.
    + eapply subG_state_wt; last apply H10.
      now apply extend_subG.
  - inv H0.
    econstructor; eauto.
    eapply lookup_weaken; eauto.
    eapply subG_typ_es; eauto.
Qed.

Lemma fresh_extend_wt: forall Γ σ f,
    config_well_typed Γ σ ->
    fresh f σ ->
    minimal Γ σ ->
    forall T_,
      config_well_typed (<[f:=T_]> Γ) σ.
Proof.
  intros * WT FRESH MIN T i ob LUi.
  remember (id_of f) as fi.
  is_eq i fi; subst.
  - pose proof id_of_well_typed _ _ _ LUi as FUT.
    inv FUT.
    exfalso.
    apply FRESH.
    pose proof id_of_consistent _ _ _ _ LUi as <- .
    eapply occurs_in_future; eauto.
  - epose proof WT i ob LUi.
    destruct ob.
    + enough (diff : f <> f5).
      {
        destruct to5.
        - inv H.
          econstructor; auto.
          + setoid_rewrite lookup_insert_ne; eauto.
          + eapply typ_term_invariant; eauto.
        - inv H.
          econstructor.
          setoid_rewrite lookup_insert_ne; eauto.
      }
      intro.
      replace i with (id_of (name_of i)) in *
          by apply id_of_name_of.
      pose proof id_of_consistent _ _ _ _ LUi.
      subst.
      contradiction.
    + inv H.
      assert (SUB: extend_G Γ (get_fields Cl) ⊆ extend_G (<[f:=T]> Γ) (get_fields Cl)). {
        apply extend_subG.
        apply subG_add; auto.
        apply not_elem_of_dom.
        eapply fresh_config_wt; eauto.
      }
      econstructor; eauto.
      * eapply subG_queue_wt; [apply SUB | apply H7].
      * eapply subG_process_wt; [apply SUB | apply H8].
      * eapply subG_state_wt; [apply SUB | apply H9].
    + enough (diff : f <> f5).
      {
        inv H.
        econstructor; eauto.
        + setoid_rewrite lookup_insert_ne; eauto.
        + eapply typ_term_list_invariant; eauto.
      }
      intro.
      apply FRESH.
      subst.
      eapply occurs_in_invoc_fut; eauto.
Qed.

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

Lemma insert_lookup_ne_extend_extend: forall Γ i j T_ l l',
    i <> j ->
    extend_G (extend_G (<[j:=T_]> Γ) l) l' !! i = extend_G (extend_G Γ l) l' !! i.
Proof.
  induction l'; intros; simpl.
  - now apply insert_lookup_ne_extend.
  - unfold add_G; destruct a; simpl.
    is_eq i x.
    + now setoid_rewrite lookup_insert.
    + setoid_rewrite lookup_insert_ne; eauto.
Qed.

Lemma insert_lookup_ne_extend_a_extend: forall Γ i j T_ l l',
    i <> j ->
    extendG_by_a (extend_G (<[j:=T_]> Γ) l) l' !! i = extendG_by_a (extend_G Γ l) l' !! i.
Proof.
  intros.
  setoid_rewrite lookup_merge.
  now rewrite insert_lookup_ne_extend; auto.
Qed.

Fixpoint last_stmt (s:stmt): stmt :=
  match s with
  | stmt_seq _ s' => last_stmt s'
  | _ => s
  end.

Variant is_return: stmt -> Prop :=
  | return_intro: forall e, is_return (stmt_ret e).

Lemma is_return_expression: forall s,
    is_return s <-> exists e, s = stmt_ret e.
Proof.
  split.
  - inv 1; now exists e.
  - now intros (?e & ->).
Qed.

Definition typ_body (Γ:G) (s:stmt) (T_:T): Prop :=
  stmt_well_typed Γ s /\ exists e, last_stmt s = stmt_ret e /\ typ_e Γ e T_.

(* Inductive var_list_well_typed: G -> list (T*x) -> Prop := *)
(* | var_list_wt_nil: forall Γ, var_list_well_typed Γ [] *)
(* | var_list_wt_cons: forall Γ T x params, *)
(*     Γ !! x = Some (ctxv_T T) -> *)
(*     var_list_well_typed Γ params -> *)
(*     var_list_well_typed Γ ((T, x) :: params). *)

(* Definition var_list_well_typed' (Γ:G) (l:list (T*x)): Prop := *)
(*   forall T T' x, Γ !! x = Some (ctxv_T T) -> (T', x) ∈ l -> T = T'. *)

(* Lemma var_list_wt_cons': forall Γ Tx params, *)
(*   var_list_well_typed' Γ (Tx :: params) -> *)
(*   var_list_well_typed' Γ params. *)
(* Proof. *)
(*   intros*. *)
(*   eapply H; eauto. *)
(*   now right. *)
(* Qed. *)

(* Lemma var_list_wt_wt': forall Γ params, *)
(*     var_list_well_typed Γ params <-> var_list_well_typed' Γ params. *)
(*   Proof. *)
(*     induction params; split; intros*. *)
(*     - inv H1. *)
(*     - constructor. *)
(*     - inv H. *)
(*       inv H1; auto. *)
(*       apply IHparams in H6. *)
(*       eapply H6; eauto. *)
(*     - destruct a. *)
(*       pose proof H t t x. *)
(*       apply var_list_wt_cons' in H. *)
(*       apply IHparams in H. *)
(*       constructor; auto. *)


(* Lemma fresh_list_wt: forall Γ l, *)
(*     Forall (fun '(T, x) => x ∉ dom Γ) l -> var_list_well_typed Γ l. *)
(* Proof. *)
(*   intros. *)
(*   induction l; intros*; inv H1. *)
(*   - inv H. *)
(*     apply not_elem_of_dom in H3. *)
(*     setoid_rewrite H3 in H0. *)
(*     discriminate. *)
(*   - inv H. *)
(*     eapply IHl; eauto. *)
(* Qed. *)

Variant M_well_typed: G -> M -> Prop :=
  M_wt_intro: forall Γ T name params fields body,
      typ_body (<[destiny:=ctxv_fut T]> (extend_G Γ params)) body T ->
      Forall (λ '(_, x), x ∉ dom Γ) params ->
      NoDup (map snd params) ->
      M_well_typed Γ (M_m T name params fields body).

Variant CL_well_typed: G -> CL -> Prop :=
  CL_wt_intro: forall Γ name fields methods,
      Forall (M_well_typed Γ) methods ->
      (* var_list_well_typed Γ fields -> *)
      CL_well_typed Γ (class name fields methods).

Lemma get_method_in_list: forall m l method,
    get_method_decl m l = Some method -> method ∈ l.
Proof.
  induction l; intros; inv H.
  destruct a.
  autorewrite with get_method_decl in *.
  case_decide; subst.
  - inv H1.
    now left.
  - right.
    now apply IHl.
Qed.

Lemma not_in_not_eq: forall x0 (params:list (T*x)),
    ~ In x0 (map snd params) ->
    Forall (fun '(_,y) => y <> x0) params.
Proof.
  induction params; intros; auto.
  destruct a; simpl in *.
  apply Decidable.not_or in H.
  destruct H.
  constructor; auto.
Qed.

Lemma extend_by_empty_a: forall Γ,
    extendG_by_a Γ ∅ = Γ.
Proof.
  intros.
  apply fin_maps.map_eq.
  intros.
  unfold extendG_by_a.
  setoid_rewrite lookup_merge.
  setoid_rewrite lookup_empty.
  destruct (Γ !! i) eqn:?; setoid_rewrite Heqo; auto.
Qed.

Lemma lookup_extend_by_a: forall Γ l y T v,
    l !! y = Some (T, v) ->
    extendG_by_a Γ l !! y = Some T.
Proof.
  intros.
  setoid_rewrite lookup_merge.
  setoid_rewrite H.
  destruct (Γ !! y) eqn:?;
    setoid_rewrite Heqo; simpl; auto.
Qed.

Lemma bind_params_extend: forall Γ vs l,
    length vs = length l ->
    (extendG_by_a Γ (bind_params vs l)) = extend_G Γ l.
Proof.
  induction vs; destruct l; intros*; autorewrite with bind_params;
    try (now inv H).
  - now rewrite extend_by_empty_a.
  - destruct p.
    inv H.
    autorewrite with bind_params.
    simpl.
    apply fin_maps.map_eq.
    intros*.
    is_eq i x.
    + setoid_rewrite lookup_insert; simpl.
      setoid_rewrite lookup_extend_by_a with (l:=(<[i:=(ctxv_T t, a)]> (bind_params vs l))); eauto.
      apply lookup_insert.
    + setoid_rewrite lookup_insert_ne; auto.
      rewrite <- IHvs; auto.
      unfold extendG_by_a.
      rewrite 2 lookup_merge.
      setoid_rewrite lookup_insert_ne; auto.
Qed.

Lemma bind_params_wt: forall Γ vs l,
    typ_es Γ (map e_t vs) (map fst l) ->
    state_well_typed (extend_G Γ l) (bind_params vs l).
Proof.
  induction vs; destruct l; intros*;
    autorewrite with bind_params in H0;
    inv H0.
  destruct p; simpl in *.
  autorewrite with typ_es in H.
  destruct H.
  autorewrite with bind_params in H2.
  is_eq x x0.
  - setoid_rewrite lookup_insert in H2.
    inv H2.
    split.
    + apply lookup_insert.
    + eapply typ_term_invariant; eauto.
  - setoid_rewrite lookup_insert_ne in H2; auto.
    setoid_rewrite lookup_insert_ne; auto.
    apply IHvs in H0.
    specialize (H0 _ _ _ H2) as (?&?).
    split; auto.
    eapply typ_term_invariant; eauto.
Qed.

(* in the paper, this is an assumptiom *)
(* should be reasonable from well typed classes and methods *)

Lemma destiny_not_in_stmt: forall Γ T s,
    stmt_well_typed (<[destiny:=T]> Γ) s ->
    stmt_well_typed Γ s.
Admitted.

Lemma bind_wt: forall m Ts T CL vs f tsk,
    length vs = length Ts ->
    match_method m Ts T CL ->
    bind m vs f CL = tsk ->
    forall Γ,
      Γ !! f = Some (ctxv_fut T) ->
      typ_es Γ (map e_t vs) Ts ->
      CL_well_typed Γ CL ->
      process_well_typed Γ tsk.
Proof.
  intros.
  destruct tsk; last constructor.
  destruct t, CL.
  inv H0.
  inv H4.
  assert (method_wt: M_well_typed Γ method). {
    eapply Forall_forall; eauto.
    apply elem_of_list_In.
    autorewrite with get_methods in *.
    eapply get_method_in_list; eauto.
  }
  destruct method.
  autorewrite with bind get_methods get_type in *.
  autorewrite with get_params in *.
  destruct (get_method_decl m l0); inv H1.
  rewrite map_length in H.
  econstructor.
  -  rewrite bind_params_extend; auto.
     now apply bind_params_wt.
  - inv method_wt.
    destruct H6 as (? & ?ret & ? & ?).
    rewrite bind_params_extend; auto.
    eapply destiny_not_in_stmt; eauto.
Qed.

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

Lemma lookup_extend_by_a_not_in: forall Γ l y,
    y ∉ dom l -> extendG_by_a Γ l !! y = Γ !! y.
Proof.
  intros.
  unfold extendG_by_a.
  setoid_rewrite lookup_merge.
  apply not_elem_of_dom in H.
  rewrite H.
  destruct (Γ !! y) eqn:?; setoid_rewrite Heqo;
    auto.
Qed.

Lemma lookup_extend_not_in: forall Γ l y,
    y ∉ (map snd l) -> extend_G Γ l !! y = Γ !! y.
Proof.
  induction l as [ | (?&?) ]; simpl; intros; auto.
  is_eq x y.
  - exfalso.
    apply H.
    now left.
  - setoid_rewrite lookup_insert_ne; simpl; auto.
    apply IHl.
    intro.
    apply H.
    now right.
Qed.

Lemma subG_extend_a: forall Γ l,
    (forall x, x ∈ dom l -> x ∉ dom Γ) ->
    Γ ⊆ extendG_by_a Γ l.
Proof.
  intros*.
  unfold extendG_by_a.
  setoid_rewrite lookup_merge.
  destruct (Γ !! i) eqn:?,
                    (l !! i) eqn:?;
    setoid_rewrite Heqo;
    setoid_rewrite Heqo0;
    simpl; auto.
  - exfalso.
    eapply (H i); apply elem_of_dom; auto.
  - now destruct p.
Qed.

(* the paper's Lemma 2 *)
Lemma task_to_ob_wt: forall l s Γ,
    process_well_typed Γ (Some (tsk s l)) ->
    forall c C,
      (* the class exists and its fields are disjoint from the context *)
      get_class_decl c Cs = Some C ->
      Forall (λ '(_, x), x ∉ dom Γ) (get_fields C) ->
      cn_well_typed Γ (cn_object c ∅ (Some (tsk s l)) ∅).
(* TODO: and Γ is minimal *)
Proof.
  intros.
  econstructor; eauto.
  - apply q_wt_empty.
  - eapply subG_process_wt with Γ; eauto.
    apply subG_extend; auto.
  - intros*.
    inv H2.
Qed.

Lemma lookup_extend_wt: forall Γ l,
    state_well_typed (extendG_by_a Γ l) l ->
    forall x x' v,
      extendG_by_a Γ l !! x = extendG_by_a Γ (update_a x' v l) !! x.
Proof.
  unfold extendG_by_a, update_a.
  intros*.
  setoid_rewrite lookup_merge.
  is_eq x x'; simp.
  - setoid_rewrite lookup_partial_alter.
    destruct (Γ !! x) eqn:?, (l !! x) eqn:?;
      setoid_rewrite Heqo;
      setoid_rewrite Heqo0;
      simpl; try destruct p; auto.
  - setoid_rewrite lookup_partial_alter_ne; auto.
Qed.

Lemma stmt_wt_extend_insert: forall Γ l,
    state_well_typed Γ l ->
    forall x v s,
      stmt_well_typed (extendG_by_a Γ l) s ->
      stmt_well_typed (extendG_by_a Γ (update_a x v l)) s.
Proof.
  intros.
  eapply subG_stmt_wt; last apply H0.
  now apply subG_extend_insert.
Qed.

Lemma state_wt_same_G: forall Γ l,
    state_well_typed (extendG_by_a Γ l) l ->
    forall x v,
       extendG_by_a Γ (update_a x v l) = extendG_by_a Γ l.
Proof.
  intros.
  apply fin_maps.map_eq.
  intros.
  unfold extendG_by_a, update_a.
  setoid_rewrite lookup_merge.
  is_eq i x.
  - setoid_rewrite lookup_partial_alter.
    destruct (Γ !! i) eqn:?, (l !! i) eqn:?;
      setoid_rewrite Heqo;
      setoid_rewrite Heqo0;
      try (destruct p);
      simpl; auto.
  - setoid_rewrite lookup_partial_alter_ne; auto.
Qed.

(* solves all the easy preservation of minimality leaving the one goal that requires internvention *)
Ltac solve_minimality :=
  match goal with
    MIN: minimal _ _ |- _ => intros ?y ?IN_DOM; apply MIN in IN_DOM; inv IN_DOM;
      match goal with
        _ : ?σ !! ?i = _, _ : ?σ !! ?j = _ |- _ => is_eq i j
      end;
      simplify_map_eq;
      try (now eapply occurs_in_object_fields; eauto;
        apply lookup_insert);
      try (now eapply occurs_in_object_fields; eauto;
        setoid_rewrite lookup_insert_ne; eauto);
      try (now eapply occurs_in_object_task; eauto;
        apply lookup_insert);
      try (now eapply occurs_in_object_task; eauto;
        setoid_rewrite lookup_insert_ne; eauto);
      try (now eapply occurs_in_object_queue; eauto;
        apply lookup_insert);
      try (now eapply occurs_in_object_queue; eauto;
        setoid_rewrite lookup_insert_ne; eauto);
      try (now eapply occurs_in_future;
        setoid_rewrite lookup_insert_ne; eauto);
      try (now eapply occurs_in_invoc_fut;
        setoid_rewrite lookup_insert_ne; eauto);
      try (now eapply occurs_in_invoc_ob;
        setoid_rewrite lookup_insert_ne; eauto)
  end.

Lemma elem_of_dom_update_a: forall l x y v,
    y ∈ dom l ->
    x ∈ dom l ->
    y ∈ dom (update_a x v l).
Proof.
  intros.
  apply elem_of_dom in H, H0.
  inv H.
  inv H0.
  apply elem_of_dom.
  unfold update_a.
  is_eq x y; simplify_map_eq.
  - destruct x0.
    eexists.
    setoid_rewrite lookup_partial_alter.
    now setoid_rewrite H1.
  - eexists.
    now setoid_rewrite lookup_partial_alter_ne; eauto.
Qed.

Theorem type_preservation : forall (Γ: G),
    Forall (typ_F Γ) Fs ->
    Forall (CL_well_typed Γ) Cs ->
    forall σ σ',
      config_well_typed Γ σ ->
      minimal Γ σ ->
      @stmt_step Fs σ σ' ->
      exists Γ', Γ ⊆ Γ' /\ minimal Γ' σ' /\ config_well_typed Γ' σ'.
Proof.
  intros Γ TYP_Fs TYP_Cs σ σ' WT MIN STEP.
  inv STEP.
  - exists Γ; repeat split; auto.
    + solve_minimality.
      destruct (task_eq_dec p (tsk p0 l)); subst.
      * eapply occurs_in_object_task; eauto.
        eapply lookup_insert.
      * assert (tsk p0 l ∈ (remove p q)). {
          set_unfold.
          apply not_eq_sym in n.
          setoid_rewrite (multiplicity_singleton_ne _ _ n).
          lia.
        }
        eapply occurs_in_object_queue with (q:=remove p q); eauto.
        apply lookup_insert.
    + intros*.
      lookup_cases H1 i i0.
      * specialize (WT _ _ H0).
        unfold_typing.
        destruct p.
        econstructor; eauto.
        now apply q_wt_remove.
      * eapply WT;eauto.

  - (* (local) assignment *)
    destruct H1 as [sf ?].
    pose proof WT as Conf_wt.
    specialize (WT _ _ H2).
    unfold_typing.
    remember (extendG_by_a (extend_G Γ (get_fields Cl)) l) as Γ'.
    assert (stmt_well_typed Γ' (stmt_seq (stmt_asgn x (rhs_e e)) s)) by repeat (econstructor; eauto).
    epose proof type_preservation _ _ _ _ _ _ _ _ _ H5 H1
      as (?Γ & ?SUB & ? & ?TYP_E).
    exists Γ.
    repeat split; auto.
    + solve_minimality.
      eapply occurs_in_object_task with (l:=(update_a x v l)).
      * apply elem_of_dom_update_a; auto.
      * apply lookup_insert.

    + intros*.
      lookup_cases H9 i i0.
      * do 2 (econstructor; eauto).
        -- eapply state_wt_insert with (T:=T0).
           ++ now rewrite state_wt_same_G.
           ++ erewrite <- lookup_extend_by_a; eauto.
              setoid_rewrite lookup_partial_alter.
              apply elem_of_dom in H.
              inv H.
              destruct x0.
              rewrite H9; simpl.
              erewrite lookup_extend_by_a in H8; eauto.
              now inv H8.
           ++ eapply typ_term_invariant; eauto.
        -- now rewrite state_wt_same_G.
      * eapply subG_cn_wt; last eapply Conf_wt; eauto.

  - (* (field) assignment *)
    destruct H1 as [sf ?].
    pose proof WT as Conf_wt.
    specialize (WT _ _ H2).
    unfold_typing.
    remember (extendG_by_a (extend_G Γ (get_fields Cl)) l) as Γ'.
    assert (stmt_well_typed Γ' (stmt_seq (stmt_asgn x (rhs_e e)) s)) by repeat (econstructor; eauto).
    epose proof type_preservation _ _ _ _ _ _ _ _ _ H5 H1
      as (?Γ & ?SUB & ? & ?TYP_E).
    exists Γ.
    repeat split; auto.
    + solve_minimality.
      eapply occurs_in_object_fields with (a:=(update_a x v a)).
      * apply elem_of_dom_update_a; auto.
      * apply lookup_insert.
    + intros*.
      lookup_cases H9 i o.
    * econstructor; eauto.
      -- econstructor; eauto.
      -- eapply state_wt_insert with (T:=T0); auto.
        ++ erewrite <- lookup_extend_by_a_not_in; eauto.
        ++ eapply typ_term_invariant; eauto.
    * eapply subG_cn_wt; last eapply Conf_wt; eauto.

  (* the trivial cases (ifs, skips, loops) are very similar*)
  (* TODO: automate *)
  - pose proof WT as Conf_wt.
    specialize (WT _ _ H0).
    unfold_typing.
    exists Γ; repeat split; auto.
    + solve_minimality.
    + intros*.
      lookup_cases H1 o i.
      * repeat (econstructor; eauto).
      * eapply Conf_wt; eauto.

  - pose proof WT as Conf_wt.
    specialize (WT _ _ H0).
    unfold_typing.
    exists Γ; repeat split; auto.
    + solve_minimality.
    + intros*.
      lookup_cases H1 o i.
      * repeat (econstructor; eauto).
      * eapply Conf_wt; eauto.

  - pose proof WT as Conf_wt.
    specialize (WT _ _ H).
    unfold_typing.
    exists Γ; repeat split; auto.
    + solve_minimality.
    + intros*.
      lookup_cases H0 o i.
      * repeat (econstructor; eauto).
      * eapply Conf_wt; eauto.

  - pose proof WT as Conf_wt.
    specialize (WT _ _ H).
    unfold_typing.
    exists Γ; repeat split; auto.
    + solve_minimality.
      admit.
      (*problem: when we end a task, the context is no longer minimal since we removed a task with its local state *)
    + intros*.
      lookup_cases H0 o i.
      * repeat (econstructor; eauto).
      * eapply Conf_wt; eauto.

  - pose proof WT as Conf_wt.
    specialize (WT _ _ H).
    unfold_typing.
    exists Γ; repeat split; auto.
    + solve_minimality.
    + intros*.
      lookup_cases H0 o i.
      * repeat (econstructor; eauto).
      * eapply Conf_wt; eauto.

  - pose proof WT as Conf_wt.
    specialize (WT _ _ H3).
    unfold_typing.
    pose proof H18 as Method_wt.
    inv H18.
    destruct method.
    autorewrite with get_type get_params in *.
    epose proof type_preservation_eval_list _ _ _ _ _ _ _ H15 H2 as TYP_ARGS.
    exists (<[f:=ctxv_fut T_5]> Γ).
    repeat split; auto.
    + apply subG_add; auto.
      apply not_elem_of_dom.
      eapply fresh_config_wt; eauto.
    + intros*.
      setoid_rewrite dom_insert in H5.
      apply elem_of_union in H5.
      destruct H5.
      * apply elem_of_singleton in H5; subst.
        eapply occurs_in_invoc_fut with (i:=i).
        setoid_rewrite lookup_insert_ne.
        apply lookup_insert.
        intros ->.
        apply H0.
        now apply elem_of_dom.
      * revert H5.
        generalize dependent y.
        solve_minimality.
        -- eapply occurs_in_object_fields with (i:=i0); eauto.
           repeat setoid_rewrite lookup_insert_ne; eauto.
           ++ intros ->.
              apply H1.
              now apply elem_of_dom.
           ++ intros ->.
              apply H0.
              now apply elem_of_dom.
        -- eapply occurs_in_object_task with (i:=i0); eauto.
           repeat setoid_rewrite lookup_insert_ne; eauto.
           ++ intros ->.
              apply H1.
              now apply elem_of_dom.
           ++ intros ->.
              apply H0.
              now apply elem_of_dom.
        -- eapply occurs_in_object_queue with (i:=i0); eauto.
           repeat setoid_rewrite lookup_insert_ne; eauto.
           ++ intros ->.
              apply H1.
              now apply elem_of_dom.
           ++ intros ->.
              apply H0.
              now apply elem_of_dom.
        -- eapply occurs_in_future with (i:=i0); eauto.
           repeat setoid_rewrite lookup_insert_ne; eauto.
           ++ intros ->.
              apply H1.
              now apply elem_of_dom.
           ++ intros ->.
              apply H0.
              now apply elem_of_dom.
        -- eapply occurs_in_invoc_fut with (i:=i0); eauto.
           repeat setoid_rewrite lookup_insert_ne; eauto.
           ++ intros ->.
              apply H1.
              now apply elem_of_dom.
           ++ intros ->.
              apply H0.
              now apply elem_of_dom.
        -- eapply occurs_in_invoc_ob with (i:=i0); eauto.
           repeat setoid_rewrite lookup_insert_ne; eauto.
           ++ intros ->.
              apply H1.
              now apply elem_of_dom.
           ++ intros ->.
              apply H0.
              now apply elem_of_dom.
    + intros*.
      lookup_cases H5 oi i0.
      * econstructor; eauto.
        -- eapply subG_queue_wt; last apply H11.
            eapply extend_subG.
            apply subG_add; auto.
            apply not_elem_of_dom_1.
            eapply fresh_config_wt; eauto.
        -- constructor.
           ++ eapply subG_state_wt; last apply H7.
              apply extend_by_a_subG.
              apply extend_subG.
              apply subG_add; auto.
              apply not_elem_of_dom_1.
              eapply fresh_config_wt; eauto.
           ++ econstructor.
              ** econstructor; eauto.
                 --- rewrite insert_lookup_ne_extend_a_extend; eauto.
                 --- econstructor.
                     apply lookup_weaken with (extend_G (<[f:=ctxv_fut T_5]> Γ) (get_fields Cl)).
                     +++ apply lookup_weaken with (<[f:=ctxv_fut T_5]> Γ).
                         *** now apply lookup_insert.
                         *** apply subG_extend.
                             apply CL_wt_fields_fresh.
                             eapply Forall_forall with (l:=Cs).
                             ---- admit. (* we need closure under extension for CL_wt*)
                             ---- eapply get_class_decl_some; eauto.
                     +++ apply subG_extend_a.
                         admit. (* fields are fresh – from minimality of Γ*)
              ** eapply subG_stmt_wt; last apply H12.
                 apply extend_by_a_subG.
                 apply extend_subG.
                 apply subG_add; auto.
                 apply not_elem_of_dom_1.
                 eapply fresh_config_wt; eauto.
        -- eapply subG_state_wt; last apply H13.
           apply extend_subG.
           apply subG_add; auto.
           apply not_elem_of_dom_1.
           eapply fresh_config_wt; eauto.

      * lookup_cases H5 i i0.
        -- econstructor; eauto.
            ++ apply lookup_insert.
            ++ eapply typ_term_list_invariant; eauto.
        -- set (fi:=id_of f).
           replace j with (id_of f) in *.
           is_eq fi i0; subst fi.
           ++ setoid_rewrite lookup_insert in H5.
              inv H5.
              econstructor.
              apply lookup_insert.
            ++ setoid_rewrite lookup_insert_ne in H5; auto.
              eapply fresh_extend_wt; eauto.

              (* silly consistency shuffling for the replace *)
            ++ enough (<[j:=cn_future f None]> σ !! j = Some (cn_future f None)); last apply lookup_insert.
               rewrite <- (name_of_id_of f) in H6.
               rewrite <- (id_of_name_of j) in *.
               apply id_of_consistent in H6.
               rewrite name_of_id_of in H6.
               now rewrite H6.

  - pose proof WT _ _ H0 as fut_well_typed.
    pose proof WT _ _ H1 as ob_well_typed.
    exists Γ; repeat split; auto.
    + solve_minimality.
      * eapply occurs_in_object_fields with (i:=i); eauto.
        repeat setoid_rewrite lookup_insert_ne; eauto.
        intros ->; simplify_map_eq.
      * admit.
      (* another problematic case of removing an object *)
      * eapply occurs_in_object_task with (i:=i); eauto.
        repeat setoid_rewrite lookup_insert_ne; eauto.
        intros ->; simplify_map_eq.
      * eapply occurs_in_object_queue with (i:=i); eauto.
        repeat setoid_rewrite lookup_insert_ne; eauto.
        intros ->; simplify_map_eq.
      * is_eq i fi; simplify_map_eq.
        -- eapply occurs_in_future with (i:=i); eauto.
           setoid_rewrite lookup_insert_ne; eauto.
           apply lookup_insert.
        -- eapply occurs_in_future with (i:=i); eauto.
           repeat setoid_rewrite lookup_insert_ne; eauto.
      * eapply occurs_in_invoc_fut with (i:=i); eauto.
        repeat setoid_rewrite lookup_insert_ne; eauto.
        intros ->; simplify_map_eq.
      * eapply occurs_in_invoc_ob with (i:=i); eauto.
        repeat setoid_rewrite lookup_insert_ne; eauto.
        intros ->; simplify_map_eq.
    + intros*.
    unfold_typing.
    lookup_cases H3 o i.
    * econstructor; eauto.
      econstructor.
    * lookup_cases H3 fi i.
      -- econstructor; eauto.
        epose proof type_preservation_eval _ _ _ _ _ _ _ H5 H.
        enough (T0 = T) by (subst; inv H3; constructor).
        erewrite lookup_extend_by_a in H12; eauto.
        inv H12.
        rewrite <- (id_of_name_of fi) in H0.
        epose proof id_of_consistent σ (name_of fi) f None H0 as <-.
        pose proof H9 _ _ _ H2 as (?&?).
        inv H7.
      -- eapply WT; eauto.

  - pose proof WT _ _ H as fut_well_typed.
    pose proof WT _ _ H0 as ob_well_typed.
    exists Γ; repeat split; auto.
    { solve_minimality. }
    intros*.
    unfold_typing.
    lookup_cases H1 o i.
    + repeat (econstructor; eauto).
      enough (T1 = T) by (subst; eapply typ_term_invariant; eauto).
      eapply lookup_weaken with (m2:=extendG_by_a (extend_G Γ (get_fields Cl)) l) in H5.
      now simp.
      etransitivity.
      * eapply subG_extend.
        apply CL_wt_fields_fresh.
        eapply Forall_forall; eauto.
        eapply get_class_decl_some; eauto.
      * apply subG_extend_a.
        admit.
        (* params are disjoint from fields *)
    + eapply WT; eauto.

  - pose proof WT _ _ H as ob_well_typed.
    pose proof WT _ _ H0 as inv_well_typed.
    exists Γ; repeat split; auto.
    + solve_minimality.
      * is_eq i0 oi; simplify_map_eq.
        -- eapply occurs_in_object_fields with (i:=i0); eauto.
           apply lookup_insert.
        -- eapply occurs_in_object_fields with (i:=i0); eauto.
           setoid_rewrite lookup_insert_ne; eauto.
           setoid_rewrite lookup_delete_ne; eauto.
      * is_eq i0 oi; simplify_map_eq.
        -- eapply occurs_in_object_task with (i:=i0); eauto.
           apply lookup_insert.
        -- eapply occurs_in_object_task with (i:=i0); eauto.
           setoid_rewrite lookup_insert_ne; auto.
           setoid_rewrite lookup_delete_ne; eauto.
      * is_eq i0 oi; simplify_map_eq.
        --  assert (tsk p0 l ∈ (add p' q)). {
              set_unfold.
              now left.
            }
            eapply occurs_in_object_queue with (i:=i0) (q:= add p' q); eauto.
            apply lookup_insert.
        -- eapply occurs_in_object_queue with (i:=i0); eauto.
           setoid_rewrite lookup_insert_ne; auto.
           setoid_rewrite lookup_delete_ne; eauto.

      * is_eq i0 oi; simplify_map_eq.
        eapply occurs_in_future with (i:=i0); eauto.
        setoid_rewrite lookup_insert_ne; auto.
        setoid_rewrite lookup_delete_ne; eauto.

      * admit.
        (* problem: we delete the invocation that contained the future *)
      * is_eq i0 oi; simplify_map_eq.
        eapply occurs_in_invoc_fut with (i:=i0); eauto.
        setoid_rewrite lookup_insert_ne; auto.
        setoid_rewrite lookup_delete_ne; eauto.
      * admit.
      (* problem: we delete the invocation that contained the object *)
      * is_eq i0 oi; simplify_map_eq.
        eapply occurs_in_invoc_ob with (i:=i0); eauto.
        setoid_rewrite lookup_insert_ne; auto.
        setoid_rewrite lookup_delete_ne; eauto.

    + intros*.
      unfold_typing.
      * lookup_cases H1 oi i0.
        -- repeat (econstructor; eauto).
           apply q_wt_add; auto.
           replace CL with Cl in * by admit. (* by welformedness of class_of, probably *)
           destruct p'.
           eapply bind_wt; eauto.
           ++ admit. (* consistency between arguments and type list *)
           ++ apply lookup_weaken with Γ; auto.
              apply subG_extend.
              apply CL_wt_fields_fresh.
              eapply Forall_forall; eauto.
              eapply get_class_decl_some; eauto.
           ++ eapply subG_typ_es; last apply H9.
              apply subG_extend.
              apply CL_wt_fields_fresh.
              eapply Forall_forall; eauto.
              eapply get_class_decl_some; eauto.
           ++ admit. (* well-typedness of classes (and closure under extensions) *)
      -- is_eq i i0.
        ++ exfalso.
            setoid_rewrite (lookup_delete σ i) in H1.
            inv H1.
        ++ setoid_rewrite lookup_delete_ne in H1; auto.
            eapply WT; eauto.
    * lookup_cases H1 oi i0.
      -- repeat (econstructor; eauto).
        apply q_wt_add; auto.
        replace CL with Cl in * by admit. (* by welformedness of class_of, probably *)
        eapply bind_wt; eauto.
        ++ admit. (* consistency between arguments and type list *)
        ++ apply lookup_weaken with Γ; auto.
            apply subG_extend.
            apply CL_wt_fields_fresh.
            eapply Forall_forall; eauto.
            eapply get_class_decl_some; eauto.
        ++ eapply subG_typ_es; last apply H9.
            apply subG_extend.
            apply CL_wt_fields_fresh.
            eapply Forall_forall; eauto.
            eapply get_class_decl_some; eauto.
        ++ admit. (* well-typedness of classes (and closure under extensions) *)

      -- is_eq i i0.
        ++ exfalso.
            setoid_rewrite (lookup_delete σ i) in H1.
            inv H1.
        ++ setoid_rewrite lookup_delete_ne in H1; auto.
            eapply WT; eauto.

            Unshelve.
            all: try eauto.
            (* we have a_to_s_wt, but what about the one where we are extending by l, but want a? *)
            (* these all stem from the ambiguity of whther fields and local states carry their types...*)
            (* the rest are closure of typ_F under context extensions *)
Admitted.
End Typing.
