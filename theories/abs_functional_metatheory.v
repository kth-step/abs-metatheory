From ABS Require Import abs_defs
  utils.

From Coq Require Import List
  FSets.FMapFacts
  Lia.

From Equations Require Import Equations.

Require Import FMapList.
Module MapFacts := FSets.FMapFacts.Facts Map.
Import ListNotations.

(** * ABS Functional Metatheory *)

Section FunctionalMetatheory.

Hypothesis (vars_fs_distinct: forall (x_:x) (fn_:fn), x_ <> fn_).
Hypothesis (vars_well_typed: forall (x_:x) (G0: G) T0,
             Map.find x_ G0 = Some T0 ->
             exists T_, T0 = ctxv_T T_).

Definition subG (G1 G2 : G) : Prop :=
  forall (key : string) (elt : ctxv),
    Map.find key G1 = Some elt ->
    Map.find key G2 = Some elt.

Notation "G ⊢ e : T" := (typ_e G e T) (at level 5).
Notation "G F⊢ F" := (typ_F G F) (at level 5).
Notation "G1 ⊆ G2" := (subG G1 G2) (at level 5).

Lemma subG_refl: forall G0,
  subG G0 G0.
Proof. easy. Qed.

Lemma subG_add: forall G0 G1 y T_,
  subG G0 G1 ->
  ~ Map.In y G0 ->
  subG G0 (Map.add y T_ G1).
Proof.
  intros.
  intros ?x_ ?T_ ?.

  destruct (eq_x y x_); subst.
  - exfalso.
    apply H0.
    apply MapFacts.in_find_iff.
    intro.
    rewrite H1 in H2.
    discriminate.
  - apply Map.find_1.
    apply MapFacts.add_neq_mapsto_iff; auto.
    pose proof H x_ T_0 H1.
    apply Map.find_2.
    assumption.
Qed.

Lemma subG_add_2: forall G0 G1 y T_,
  subG G0 G1 ->
  Map.find y G0 = Some T_ ->
  subG G0 (Map.add y T_ G1).
Proof.
  intros.
  intros ?x_ ?T_ ?.

  destruct (eq_x y x_); subst.
  - rewrite H0 in H1.
    inv H1.
    apply Map.find_1.
    now apply Map.add_1.
  - apply Map.find_1.
    apply MapFacts.add_neq_mapsto_iff; auto.
    pose proof H x_ T_0 H1.
    apply Map.find_2.
    assumption.
Qed.

(* this is stricter than the ABS paper *)
(* we require that any variables in the typing context also exist in the state *)
Definition G_vdash_s (G5 : G) (s5 : s) :=
 forall (x5 : x) (T5 : T),
  Map.find x5 G5 = Some (ctxv_T T5) ->
  exists t5,
  Map.find x5 s5 = Some t5 /\ typ_e G5 (e_t t5) T5.

Notation "G1 G⊢ s1" := (G_vdash_s G1 s1) (at level 5).

Lemma fresh_subG: forall G0 s0 (sub_list: list (T*x*t*x)),
  G_vdash_s G0 s0 ->
  fresh_vars_s (map (fun '(_,_,_,y)=>y) sub_list) s0 ->
  NoDup (map (fun '(_,_,_,y)=>y) sub_list) ->
  subG G0 (fold_right (fun '(T_,_,_,y_) G0 => Map.add y_ (ctxv_T T_) G0) G0 sub_list).
Proof.
  intros.
  induction sub_list.
  - easy.
  - destruct a as (((?T_, ?x_), ?t_), y).
    inv H1.
    inv H0.
    pose proof IHsub_list H2 H5.
    cbn.
    apply subG_add; auto.
    intro.

    apply MapFacts.in_find_iff in H3.
    apply MapFacts.not_find_in_iff in H1.
    pose proof map_neq_none_is_some _ _ H3 as (?T_, ?).
    pose proof vars_well_typed _ _ _ H6 as (?T_, ->).
    pose proof H _ _ H6 as (?t_, (?, _)).
    rewrite H1 in H7.
    discriminate.
Qed.

Lemma fresh_consistent: forall G0 s0 (sub_list: list (T*x*t*x)),
  G_vdash_s G0 s0 ->
  (forall T_ t_, In (T_, t_) (map (fun '(T_, _, t_, _) => (T_, t_)) sub_list) ->
            typ_e G0 (e_t t_) T_) ->
  fresh_vars_s (map (fun '(_,_,_,y)=>y) sub_list) s0 ->
  NoDup (map (fun '(_,_,_,y)=>y) sub_list) ->
  G_vdash_s (fold_right (fun '(T_,_,_,y_) G0 => Map.add y_ (ctxv_T T_) G0) G0 sub_list)
    (fold_right (fun '(_,_,t_,y_) s0 => Map.add y_ t_ s0) s0 sub_list).
Proof.
  intros.
  induction sub_list.
  * easy.
  * destruct a as (((?T_, ?x_), ?t_), y).
    inv H1.
    inv H2.

    cbn.
    intros ?y ?T_ ?.
    destruct (eq_x y y0); subst.
  - exists t_.
    split...
    + apply Map.find_1.
      now apply Map.add_1.
    + assert (T_ = T_0).
      {
        apply Map.find_2 in H1.
        apply MapFacts.add_mapsto_iff in H1.
        destruct H1 as [(_, ?) | (?, ?)].
        + now inv H1.
        + exfalso.
          now apply H1.
      }
      assert (In (T_0, t_) (map (fun '(T_, _, t_, _) => (T_, t_)) ((T_, x_, t_, y0) :: sub_list)))
        by (left; now rewrite H2).
      specialize (H0 _ _ H5).
      inv H0; constructor.
  - apply Map.find_2 in H1.
    apply Map.add_3 in H1; auto.
    apply Map.find_1 in H1.
    assert (forall (T_ : T) (t_ : t),
             In (T_, t_) (map (fun '(T_0, _, t_0, _) => (T_0, t_0)) sub_list) ->
             typ_e G0 (e_t t_) T_).
    {
      intros.
      apply H0.
      right.
      assumption.
    }
    pose proof IHsub_list H2 H4 H7 _ _ H1 as (?t_, (?, ?)).
    exists t_0.
    split...
    + apply Map.find_1.
      apply Map.add_2; auto.
      apply Map.find_2; assumption.
    + inv H8; constructor.
Qed.

Lemma subG_consistent: forall G1 G2 s0,
  subG G1 G2 -> G_vdash_s G2 s0 -> G_vdash_s G1 s0.
Proof.
  intros.
  intros x_ t_ ?.

  pose proof H _ _ H1.
  pose proof H0 _ _ H2 as (?t, (?, ?)).
  exists t.
  split; auto.
  inv H4;constructor.
Qed.

Lemma subG_type: forall G1 G2 e0 T0,
  subG G1 G2 -> typ_e G1 e0 T0 -> typ_e G2 e0 T0.
Proof.
  intros.
  induction H0.
  - constructor.
  - constructor.
  - apply H in H0.
    constructor.
    apply H0.
  - constructor.
    + intros.
      apply H1; auto.
    + apply H in H2.
      apply H2.
Qed.

(* this is 9.3.8 from Types and Programming Languages *)
(* it has not yet proven useful *)
Lemma subst_lemma_one_alt: forall (x0 x1:x) G0 e0 T0 T1,
  typ_e (Map.add x0 (ctxv_T T1) G0) e0 T0 ->
  typ_e G0 (e_var x1) T1 ->
  typ_e G0 (e_var_subst_one e0 x0 x1) T0.
Proof.
  intros.
  generalize dependent T0.
  generalize dependent T1.
  generalize dependent G0.
  eapply e_ott_ind with
      (n:=e0)
      (P_list_e:= fun e_list => forall e0,
                    In e0 e_list ->
                    forall G0 T0 T1,
                    typ_e (Map.add x0 (ctxv_T T1) G0) e0 T0 ->
                    typ_e G0 (e_var x1) T1 ->
                    typ_e G0 (e_var_subst e0 [(x0, x1)]) T0)
  ;cbn; intros.
  - inv H; simp e_var_subst_one; constructor.
  - inv H.
    simp e_var_subst_one.
    destruct (eq_x x5 x0); subst.
    + apply Map.find_2 in H3.
      apply MapFacts.add_mapsto_iff in H3.
      destruct H3 as [(?&?) | (?&?)]; subst.
      * inv H1.
        assumption.
      * contradiction.
    + constructor.
      apply Map.find_1.
      eapply Map.add_3.
      * apply not_eq_sym.
        apply n.
      * apply Map.find_2 in H3.
        apply H3.
  - inv H1.
    simp e_var_subst_one.
    rewrite <- subst_fst_commute.
    replace (map (fun x : e * T => let (e_, _) := let '(e_, T_) := x in (e_var_subst_one e_ x0 x1, T_) in e_) e_T_list)
      with
        (map (fun pat_ : e * T => let (e_, _) := pat_ in e_)
           (map (fun '(e_, T_) => (e_var_subst_one e_ x0 x1, T_)) e_T_list))
    by apply map_map.
    constructor.
    + rewrite map_map.
      intros.
      apply in_map_iff in H1.
      destruct H1 as ((?e_&?T_) & ? & ?).
      inv H1.
      eapply H.
      * apply in_map_iff.
        exists (e_0, T_).
        split; eauto.
      * apply H5.
        apply in_map_iff.
        exists (e_0, T_).
        split; auto.
      * apply H0.
    + apply Map.find_1.
      apply Map.find_2 in H7.
      rewrite subst_snd_commutes.
      eapply Map.add_3; eauto.
  - inv H.
  - inv H1.
    + eapply H; eauto.
    + eapply H0; eauto.
Qed.

Lemma same_type_sub: forall (sub_list: list (x*x)) G0 e0 T0,
    typ_e G0 e0 T0 ->
    (forall x0 y0 T0,
      In (x0, y0) sub_list ->
      Map.find x0 G0 = Some T0 ->
      Map.find y0 G0 = Some T0) ->
    typ_e G0 (e_var_subst e0 sub_list) T0.
Proof.
  {
  intros.
  generalize dependent T0.
  eapply e_ott_ind with
      (n:= e0)
      (P_list_e:= fun e_list => forall e0 T0,
                    In e0 e_list ->
                    typ_e G0 e0 T0 ->
                    typ_e G0 (e_var_subst e0 sub_list) T0)
  ; intros.
  - rewrite subst_term.
    simp e_var_subst_one.
  - rewrite subst_var.
    constructor.
    induction sub_list.
    + inv H.
      now simpl.
    + destruct a.
      simpl.
      destruct (eq_x (replace_var x5 sub_list) x); subst.
      * eapply H0; eauto.
        -- now left.
        -- apply IHsub_list; eauto.
           intros.
           eapply H0; eauto.
           now right.
      * eapply IHsub_list; eauto.
        intros.
        eapply H0; eauto.
        now right.
  - inv H1.
    rewrite subst_fn.
    rewrite map_map.
    replace (map (fun x : e * T => e_var_subst (let (e_, _) := x in e_) sub_list) e_T_list)
      with (map (fun pat_:e*T => let (e, _) := pat_ in e) (map (fun '(e, T) => (e_var_subst e sub_list, T)) e_T_list))
      by (rewrite map_map; apply map_ext; now intros (?, ?)).
    constructor.
    + intros.
      apply in_map_iff in H1.
      destruct H1 as ((?e, ?T), (?, ?)).
      inv H1.
      apply in_map_iff in H2.
      destruct H2 as ((?e_, ?T_), (?, ?)).
      inv H1.
      apply H.
      * apply in_map_iff.
        exists (e_0, T_).
        split; eauto.
      * apply H5.
        apply in_map_iff.
        exists (e_0, T_).
        split; eauto.
    + now replace (map (fun pat_ : e * T => let (_, T_) := pat_ in T_) (map (fun '(e, T) => (e_var_subst e sub_list, T)) e_T_list))
        with(map (fun pat_ : e * T => let (_, T_) := pat_ in T_) e_T_list)
      by (rewrite map_map; apply map_ext; now intros (?, ?)).
  - inv H.
  - inv H2.
    + now apply H.
    + now apply H1.
  }

Qed.

Lemma subst_lemma_one: forall G0 x0 y0 e0 Ai A,
  typ_e (Map.add x0 Ai G0) e0 A ->
  fresh_vars_e [y0] e0 ->
  typ_e (Map.add y0 Ai G0) (e_var_subst_one e0 x0 y0) A.
Proof.
  {
    intros.
    generalize dependent A.
    revert H0.
    apply e_ott_ind with
        (n:=e0)
        (P_list_e:= fun e_list =>
                      forall e0 A,
                      In e0 e_list ->
                      fresh_vars_e [y0] e0 ->
                      typ_e (Map.add x0 Ai G0) e0 A ->
                      typ_e (Map.add y0 Ai G0) (e_var_subst_one e0 x0 y0) A);
      intros.
    - simp e_var_subst_one.
      inv H; constructor.
    - simp e_var_subst_one.
      inv H.
      apply Map.find_2 in H3.
      apply MapFacts.add_mapsto_iff in H3.
      destruct H3 as [(?,?)|(?,?)]; subst.
      + destruct (eq_x x5 x5); subst.
        * constructor.
          apply Map.find_1.
          now apply Map.add_1.
        * contradiction.

      + destruct (eq_x x5 x0); subst.
        * contradiction.
        * destruct (eq_x x5 y0); subst.
          -- simp fresh_vars_e in H0.
             exfalso.
             apply H0.
             now left.
          -- constructor.
             apply Map.find_1.
             apply Map.add_2; eauto.
    - simp e_var_subst_one.
      inv H1.
      replace (e_list_subst_one (map (fun pat_ : e * T => let (e_, _) := pat_ in e_) e_T_list) x0 y0)
        with (map (fun pat_:e*T => let (e, _) := pat_ in e) (map (fun '(e, T) => (e_var_subst_one e x0 y0, T)) e_T_list))
        by (rewrite e_list_subst_map;
            rewrite 2 map_map;
            apply map_ext;
            now intros (?,?)).
      constructor.
      + intros.
        apply in_map_iff in H1.
        destruct H1 as ((?e, ?T), (?, ?)).
        inv H1.
        apply in_map_iff in H2.
        destruct H2 as ((?e_, ?T_), (?, ?)).
        inv H1.
        apply H.
        * apply in_map_iff.
          exists (e_0, T_).
          split; eauto.
        * simp fresh_vars_e in H0.
          eapply e_list_fresh.
          apply H0.
          apply in_map_iff.
          eexists (e_0, T_).
          split; auto.
        * apply H5.
          apply in_map_iff.
          exists (e_0, T_).
          split; eauto.
      + replace (map (fun pat_ : e * T => let (_, T_) := pat_ in T_) (map (fun '(e, T) => (e_var_subst_one e x0 y0, T)) e_T_list))
          with(map (fun pat_ : e * T => let (_, T_) := pat_ in T_) e_T_list)
          by (rewrite map_map; apply map_ext; now intros (?, ?)).

        apply Map.find_2 in H7.
        apply MapFacts.add_mapsto_iff in H7.
        destruct H7 as [(?,?)|(?,?)].
        * exfalso.
          apply (vars_fs_distinct _ _ H1).
        * apply Map.find_1.
          apply Map.add_2; eauto.
    - inv H.
    - destruct H1; subst.
      + apply H; eauto.
      + apply H0; eauto.
  }
Qed.

Lemma typ_e_G_Equal_equiv_imp : 
 forall G1 G2 e T, Map.Equal G1 G2 -> typ_e G1 e T -> typ_e G2 e T.
Proof.
intros G1 G2 e0 T0 Heq.
intros Ht.
induction Ht.
- apply typ_bool.
- apply typ_int.
- apply typ_var.
  symmetry in Heq.
  rewrite <- H.
  apply Heq.
- apply typ_func_expr.
  * intros.
    apply H0; auto.
  * rewrite <- H1.
    symmetry in Heq.
    apply Heq.
Qed.

Lemma typ_e_G_Equal_equiv : 
 forall G1 G2 e T, Map.Equal G1 G2 -> (typ_e G1 e T <-> typ_e G2 e T).
Proof.
intros G1 G2 e0 T0 Heq; split; apply typ_e_G_Equal_equiv_imp; auto.
symmetry; assumption.
Qed.



Lemma fold_map5 {A X Y Z W: Type}: forall (f : _ -> _ -> A -> A) (l: list (X*Y*Z*W)) a0,
    fold_right (fun '(z, _, _, w) a => f z w a) a0 l =
      fold_right (fun '(z, w) a => f z w a) a0
        (map (fun '(z, _, _, w) => (z, w)) l).
Proof.
  induction l; intros; eauto.
  destruct a as [[[? ?] ?] ?].
  simpl.
  now rewrite IHl.
Qed.

Lemma subst_lemma: forall (T_x_t_y_list:list (T*x*t*x)) G0 e0 A,
  typ_e (fold_right (fun '(Ai, x_, _, _) (G0 : G) => Map.add x_ (ctxv_T Ai) G0) G0 T_x_t_y_list) e0 A ->
  NoDup (map (fun '(_, _, _, y) => y) T_x_t_y_list) ->
  NoDup (map (fun '(_, x, _, _) => x) T_x_t_y_list) ->
  fresh_vars_e (map (fun '(_, _, _, y) => y) T_x_t_y_list) e0 ->
  disjoint (map (fun '(_, _, _, y) => y) T_x_t_y_list) (map (fun '(_, x, _, _) => x) T_x_t_y_list) ->
  typ_e (fold_right (fun '(Ai, _, _, y) (G0 : G) => Map.add y (ctxv_T Ai) G0) G0 T_x_t_y_list)
    (e_var_subst e0 (map (fun '(_, x_, _, y_) => (x_, y_)) T_x_t_y_list)) A.
Proof.
  intros.
  generalize dependent G0.
  generalize dependent e0.
  induction T_x_t_y_list; intros.
  - easy.
  - destruct a as (((?T_,?x_),?t_),?y).
    unfold e_var_subst.
    simpl in *.
    inv H0.
    inv H1.
    pose proof fresh_first_e _ _ _ H2.
    pose proof fresh_monotone_e _ _ _ H2.
    epose proof disjoint_monotone _ _ _ _ H3.
    assert (~ In x_ (map (fun '(_, y) => y) (map (fun '(Ai, _, _, y1) => (Ai, y1)) T_x_t_y_list))).
    { intro.
      apply (H3 x_).
      - right.
        rewrite map_map in H9.
        replace (map (fun '(_, _, _, y1) => y1) T_x_t_y_list)
          with
            (map (fun x0 : T * x * t * x => let '(_, y) := let '(Ai, _, _, y1) := x0 in (Ai, y1) in y) T_x_t_y_list).
        apply H9.
        apply map_eq.
        now intros (((?, ?), ?), ?).
      - now left.
    }
    assert (Map.Equal
     (Map.add x_ (ctxv_T T_) (fold_right (fun '(Ai, x_0, _, _) (G0 : G) => Map.add x_0 (ctxv_T Ai) G0) G0 T_x_t_y_list))
     (fold_right (fun '(Ai, x_, _, _) (G0 : G) => Map.add x_ (ctxv_T Ai) G0) (Map.add x_ (ctxv_T T_) G0) T_x_t_y_list))
      as HMEqualx.
    {
      (*
      epose proof fold_add_comm G0 x_ T_ (map (fun '(Ai, x1, _, _) => (Ai, x1)) T_x_t_y_list).
      rewrite 2 fold_map5.
      assumption.
      *)
      admit.
    }
    assert (Map.Equal
     (fold_right (fun '(Ai, _, _, y) (G0 : G) => Map.add y (ctxv_T Ai) G0) (Map.add x_ (ctxv_T T_) G0) T_x_t_y_list)
     (Map.add x_ (ctxv_T T_) (fold_right (fun '(Ai, _, _, y) (G0 : G) => Map.add y (ctxv_T Ai) G0) G0 T_x_t_y_list)))
      as HMEqualy.
    {
      epose proof fold_add_comm G0 x_ T_ (map (fun '(Ai, _, _, y1) => (Ai, y1)) T_x_t_y_list) H9.
      rewrite fold_map5.
      set (fd := fold_right _ _ _).
      rewrite fold_map5.
      unfold fd; clear fd.
      symmetry.
      assumption.
    }
    apply (typ_e_G_Equal_equiv _ _ _ _ HMEqualx) in H.
    pose proof IHT_x_t_y_list H7 H8 H4 _ H1 _ H as IH.
    apply (typ_e_G_Equal_equiv _ _ _ _ HMEqualy) in IH.
    assert (fresh_vars_e [y] (e_var_subst e0 (map (fun '(_, x_, _, y_) => (x_, y_)) T_x_t_y_list))).
    {
      assert (map snd (map (fun '(_, x_0, _, y_) => (x_0, y_)) T_x_t_y_list) = map (fun '(_, _, _, y) => y) T_x_t_y_list).
      {
        rewrite map_map.
        apply map_eq.
        now intros (((?, ?), ?), ?).
      }
      apply fresh_var_subst; try rewrite H10; auto.
    }
    now apply (subst_lemma_one _ _ _ _ _ _ IH H10).
Admitted.

Lemma type_preservation : forall (Flist : list F) (G5 : G) (s5 : s),
  G_vdash_s G5 s5 ->
  Forall (typ_F G5) Flist ->
  forall (e5 : e) (T5 : T) (s' : s) (e' : e),
    typ_e G5 e5 T5 ->
    red_e Flist s5 e5 s' e' ->
    exists G', subG G5 G' /\ G_vdash_s G' s' /\ typ_e G' e' T5.
Proof.
  intros Fs G5 s0 s_well_typed F_well_typed.
  intros e0 T0 s' e' e0_type reduction.
  generalize dependent T0.
  generalize dependent G5.
  induction reduction.
  - intros.
    exists G5; splits.
    1,2: easy.
    inv e0_type.
    destruct (s_well_typed x5 T0 H2) as (?, (?, ?)).
    rewrite H in H0.
    inv H0.
    assumption.

  - (* RED_FUN_EXPR *)
    intros.
    inv e0_type.
    rewrite app_nil_r in H0.
    pose proof split_corresponding_list e_T_list e_list e_5 e'_list H0
      as (T_list & T_5 & T'_list & ? & ? & ?).
    assert (In (e_5, T_5) (map (fun pat_ : e * T => let (e_0, T_0) := pat_ in (e_0, T_0)) e_T_list)). {
      rewrite H3.
      apply in_map_iff.
      exists (e_5, T_5).
      split; auto.
      apply in_combine_split with (2:=eq_refl); auto.
    }
    pose proof H2 e_5 T_5 H5.
    destruct (IHreduction G5 s_well_typed F_well_typed _ H6) as (G' & G'extends & G'consistent & ?).
    exists G'.
    splits.
    1,2: easy.
    replace (e_list ++ [e'] ++ e'_list ++ []) with
        (map (fun (pat_:(e*T)) => match pat_ with (e_,T_) => e_ end )
           (combine (e_list ++ [e'] ++ e'_list ++[]) (map (fun pat_ : e * T => let (_, T_) := pat_ in T_) e_T_list))).
    apply typ_func_expr.
      * intros.
        rewrite pat2_id in H8.
        rewrite H3 in H8.
        rewrite combine_snd in H8.
        rewrite combine_app in H8...
        apply in_app_iff in H8.
        destruct H8.
        -- apply subG_type with (G1:=G5); auto.
           apply H2.
           apply in_map_iff.
           exists (e_, T_).
           split; auto.
           rewrite H3.
           rewrite combine_app; auto.
           {
             eapply in_app_iff.
             now left.
           }
           rewrite 2 app_length.
           simpl.
           rewrite H1.
           reflexivity.
        -- rewrite combine_app in H8; auto.
           apply in_app_iff in H8.
           destruct H8.
           ++ inv H8;[|contradiction].
              inv H9.
              apply H7.
           ++ apply subG_type with (G1:=G5); auto.
              apply H2.
              apply in_map_iff.
              exists (e_, T_).
              split; auto.
              rewrite H3.
              rewrite combine_app; auto.
              {
                eapply in_app_iff.
                right.
                right.
                rewrite app_nil_r in H8.
                apply H8.
              }
           rewrite 2 app_length.
           simpl.
           rewrite H1.
           reflexivity.
           ++ rewrite app_nil_r.
              apply H1.
        -- auto.
        -- rewrite app_nil_r.
           simpl.
           rewrite H1.
           reflexivity.
        -- rewrite 4 app_length.
           simpl.
           lia.
      * rewrite combine_snd.
        ++ apply G'extends.
           apply H4.
        ++ rewrite map_length.
           rewrite H3.
           rewrite 2 combine_app; auto.
           ** repeat (rewrite app_length).
              rewrite 3 combine_length.
              simpl.
              rewrite H, H1.
              lia.
           ** rewrite 2 app_length.
              simpl.
              rewrite H1.
              reflexivity.
      * rewrite app_nil_r.
        rewrite combine_fst; auto.
        rewrite map_length.
        rewrite H3.
        rewrite combine_length.
        repeat (rewrite app_length).
        rewrite H, H1.
        simpl.
        lia.

  - (* RED_FUN_GROUND *)
    intros.
    set (fn_def:=(F_fn T_5 fn5 (map (fun '(T_, x_, _, _) => (T_, x_)) T_x_t_y_list) e5)).
    pose proof utils.in_split F_list F'_list fn_def .
    rewrite app_nil_r in *.
    pose proof Forall_forall (typ_F G5) (F_list ++ [fn_def] ++ F'_list) as (? & _).
    pose proof H2 F_well_typed fn_def H1 as fn_typed.
    inv fn_typed.
    inv e0_type.
    destruct H as ((?, ?), ?).
    assert (e_T_list = map (fun '(T_, _, t_, _) => (e_t t_, T_)) T_x_t_y_list).
    {
      (* inv H11. *)
      eapply map_split'.
      - replace (map fst e_T_list) with (map (fun pat_ : e * T => let (e_, _) := pat_ in e_) e_T_list) by easy.
        rewrite H4.
        apply map_ext.
        easy.
      - replace (map snd e_T_list) with (map (fun pat_ : e * T => let (_, T_) := pat_ in T_) e_T_list) by easy.
        rewrite H7 in H11.
        inv H11.
        rewrite map_map.
        apply map_ext.
        intros.
        now destruct a as (((?, ?), ?), ?).
    }
    exists (fold_right (fun '(T_, _, _, y) G0 => Map.add y (ctxv_T T_) G0) G5 T_x_t_y_list).
    splits.
    + eapply fresh_subG; eauto.
    + rewrite <- fold_map.
      apply fresh_consistent; eauto.
      intros.
      apply in_map_iff in H12.
      destruct H12 as (Txty, (?, ?)).
      apply H6.
      inv H12.
      rewrite map_map.
      apply in_map_iff.
      exists Txty.
      split; auto.
      destruct Txty as (((?, ?), ?), ?).
      now inv H15.

    + rewrite H7 in H11.
      inv H11.
      apply subst_lemma; auto.
      * rewrite <- fold_map_reshuffle; eauto.
      * rewrite map_xs in H10.
        apply H10.
Qed.
End FunctionalMetatheory.
