From ABS Require Import abs_defs
  utils.

From Coq Require Import List
  FSets.FMapFacts
  Lia.

Module MapFacts := FSets.FMapFacts.Facts Map.
Import ListNotations.

(** * ABS Functional Metatheory *)

Section FunctionalMetatheory.

Hypothesis (vars_fs_distinct: forall (x_:x) (fn_:fn), x_ <> fn_).
Hypothesis (vars_well_typed: forall (x_:x) (G0: G) T0,
             Map.find x_ G0 = Some T0 ->
             exists T_, T0 = ctxv_T T_).

Notation "G ⊢ e : T" := (typ_e G e T) (at level 5).
Notation "G F⊢ F" := (typ_F G F) (at level 5).
(* Notation "Fs , s ⊢ e ⇝ s' ⊢ e'" := (red_e Fs s e s' e') (at level 10). *)

Definition subG (G1 G2 : G) : Prop :=
  forall (key : string) (elt : ctxv), 
    Map.find key G1 = Some elt ->
    Map.find key G2 = Some elt.

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

(* this is stricter than the ABS paper *)
(* we require that any variables in the typing context also exist in the state *)
Definition G_vdash_s (G5 : G) (s5 : s) :=
 forall (x5 : x) (T5 : T),
  Map.find x5 G5 = Some (ctxv_T T5) ->
  exists t5,
  Map.find x5 s5 = Some t5 /\ typ_e G5 (e_t t5) T5.

Notation "G1 G⊢ s1" := (G_vdash_s G1 s1) (at level 5).

(* how is this not in MapFacts? *)
Lemma map_neq_none_is_some{elt:Type}: forall m x,
  Map.find x m <> None ->
  exists y, Map.find (elt:=elt) x m = Some y.
Proof.
  intros.
  destruct (MapFacts.In_dec m x).
  - inv i.
    exists x0.
    apply Map.find_1.
    apply H0.
  - apply MapFacts.not_find_in_iff in n.
    rewrite n in H.
    contradiction.
Qed.

Lemma fresh_subG: forall G0 s0 (sub_list: list (T*x*t*x)),
  G_vdash_s G0 s0 ->
  fresh_vars_s (map (fun '(_,_,_,y)=>y) sub_list) s0 ->
  distinct (map (fun '(_,_,_,y)=>y) sub_list) ->
  subG G0 (fold_right (fun '(T_,_,_,y_) G0 => Map.add y_ (ctxv_T T_) G0) G0 sub_list).
Proof with try easy.
  intros.
  induction sub_list...
  destruct a as (((?T_, ?x_), ?t_), y).
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
  distinct (map (fun '(_,_,_,y)=>y) sub_list) ->
  G_vdash_s (fold_right (fun '(T_,_,_,y_) G0 => Map.add y_ (ctxv_T T_) G0) G0 sub_list)
    (fold_right (fun '(_,_,t_,y_) s0 => Map.add y_ t_ s0) s0 sub_list).
Proof with try easy.
  intros.
  induction sub_list...
  destruct a as (((?T_, ?x_), ?t_), y).
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

(* some slightly ad-hoc equalities *)
Lemma subst_fst_commute: forall x0 x1 e_T_list,
  map (fun x : e * T => let (e_, _) := let '(e_, T_) := x in (e_var_subst_one e_ x0 x1, T_) in e_) e_T_list =
  (fix e_list_subst_one (es : list e) (x_ y_ : x) {struct es} : list e :=
     match es with
     | [] => fun _ _ : x => []
     | e :: l => fun x_0 y_0 : x => e_var_subst_one e x_0 y_0 :: e_list_subst_one l x_0 y_0
     end x_ y_) (map (fun pat_ : e * T => let (e_, _) := pat_ in e_) e_T_list) x0 x1.
Proof.
  induction e_T_list; auto.
  destruct a.
  simpl.
  rewrite <- IHe_T_list.
  reflexivity.
Qed.

Lemma subst_snd_commutes: forall x0 s e_T_list,
  map (fun pat_ : e * T => let (_, T_) := pat_ in T_)
    (map (fun pat_ : e * T => let (e_, T_) := pat_ in (e_var_subst_one e_ x0 s, T_)) e_T_list) =
    map (fun pat_ : e * T => let (_, T_) := pat_ in T_) e_T_list.
Proof with auto.
  intros.
  induction e_T_list...
  destruct a;cbn in *.
  rewrite IHe_T_list...
Qed.

Lemma fold_map_reshuffle: forall (l: list (T*x*t*x)) G0,
  (fold_right (fun (ax : x * T) (G' : G) => Map.add (fst ax) (ctxv_T (snd ax)) G') G0
     (map (fun pat_ : T * x => let (T_, x_) := pat_ in (x_, T_)) (map (fun '(T_0, x_, _, _) => (T_0, x_)) l)))
  = (fold_right (fun '(T1, x_, _, _) (G' : G) => Map.add x_ (ctxv_T T1) G') G0 l).
Proof.
  induction l;intros;auto.
  destruct a as (((?T_ & ?x_) & ?t_) & ?y).
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

(* this is 9.3.8 from Types and Programming Languages *)
(* it has not yet proven useful *)
Lemma subst_lemma_one: forall (x0 x1:x) G0 e0 T0 T1,
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
  - inv H; constructor.
  - inv H.
    simpl.
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

(* pipe dream: might need some stronger assumptions*)
Lemma subst_lemma: forall (T_x_t_y_list:list (T*x*t*x)) G0 e0 T0,
  typ_e (fold_right (fun '(T_, x_, _, _) (G0 : G) => Map.add x_ (ctxv_T T_) G0) G0 T_x_t_y_list) e0 T0 ->
  typ_e (fold_right (fun '(T_, _, _, y) (G0 : G) => Map.add y (ctxv_T T_) G0) G0 T_x_t_y_list)
    (e_var_subst e0 (map (fun '(_, x_, _, y_) => (x_, y_)) T_x_t_y_list))
    T0.
Admitted.

Lemma type_preservation : forall (Flist : list F) (G5 : G) (s5 : s),
  G_vdash_s G5 s5 ->
  Forall (typ_F G5) Flist ->
  forall (e5 : e) (T5 : T) (s' : s) (e' : e),
    typ_e G5 e5 T5 ->
    red_e Flist s5 e5 s' e' ->
    exists G', subG G5 G' /\ G_vdash_s G' s' /\ typ_e G' e' T5.
Proof with try easy.
  intros Fs G5 s0 s_well_typed F_well_typed.
  intros e0 T0 s' e' e0_type reduction.
  generalize dependent T0.
  generalize dependent G5.
  induction reduction.
  - intros.
    exists G5; splits...
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
      split...
      apply in_combine_split with (2:=eq_refl)...
    }
    pose proof H2 e_5 T_5 H5.
    destruct (IHreduction G5 s_well_typed F_well_typed _ H6) as (G' & G'extends & G'consistent & ?).
    exists G'.
    splits...
    replace (e_list ++ [e'] ++ e'_list ++ []) with
        (map (fun (pat_:(e*T)) => match pat_ with (e_,T_) => e_ end )
           (combine (e_list ++ [e'] ++ e'_list ++[]) (map (fun pat_ : e * T => let (_, T_) := pat_ in T_) e_T_list))).
    apply typ_func_expr...
      * intros.
        rewrite pat2_id in H8.
        rewrite H3 in H8.
        rewrite combine_snd in H8.
        rewrite combine_app in H8...
        apply in_app_iff in H8.
        destruct H8.
        -- apply subG_type with (G1:=G5)...
           apply H2.
           apply in_map_iff.
           exists (e_, T_).
           split...
           rewrite H3.
           rewrite combine_app... {
             eapply in_app_iff.
             left...
           }
           rewrite 2 app_length.
           simpl.
           rewrite H1.
           reflexivity.
        -- rewrite combine_app in H8...
           apply in_app_iff in H8.
           destruct H8.
           ++ inv H8;[|contradiction].
              inv H9.
              apply H7.
           ++ apply subG_type with (G1:=G5)...
              apply H2.
              apply in_map_iff.
              exists (e_, T_).
              split...
              rewrite H3.
              rewrite combine_app... {
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
           rewrite 2 combine_app...
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
        rewrite combine_fst...
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
    pose proof H1 F_well_typed fn_def H0 as fn_typed.
    inv fn_typed.
    inv e0_type.
    destruct H as ((?, ?), ?).
    assert (e_T_list = map (fun '(T_, _, t_, _) => (e_t t_, T_)) T_x_t_y_list).
    {
      rewrite H5 in H9.
      inv H9.
      eapply map_split'.
      - replace (map fst e_T_list) with (map (fun pat_ : e * T => let (e_, _) := pat_ in e_) e_T_list) by easy.
        rewrite H3.
        apply map_ext.
        easy.
      - replace (map snd e_T_list) with (map (fun pat_ : e * T => let (_, T_) := pat_ in T_) e_T_list) by easy.
        rewrite <- H10.
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
      (* some slightly silly reshuffling *)
      intros.
      apply in_map_iff in H10.
      destruct H10 as (Txty, (?, ?)).
      apply H6.
      rewrite H7.
      rewrite map_map.
      apply in_map_iff.
      exists Txty.
      split...
      destruct Txty as (((?, ?), ?), ?).
      now inv H10.

(* here the ABS paper appeals to type preservation under substitutions, but that seems like overkill*)
    + rewrite H5 in H9.
      inv H9.
      apply subst_lemma.
      rewrite <- fold_map_reshuffle.
      apply H8.
Qed.

End FunctionalMetatheory.
