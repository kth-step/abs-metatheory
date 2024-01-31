From ABS Require Import abs_defs
  utils.

From Coq Require Import List
  FSets.FMapFacts
  Lia.

Module MapFacts := FSets.FMapFacts.Facts Map.
Import ListNotations.

(** * ABS Functional Metatheory *)

Notation "G ⊢ e : T" := (typ_e G e T) (at level 5).
Notation "G F⊢ F" := (typ_F G F) (at level 5).
(* Notation "Fs , s ⊢ e ⇝ s' ⊢ e'" := (red_e Fs s e s' e') (at level 10). *)

Definition subG (G1 G2 : G) : Prop :=
  forall (key : string) (elt : ctxv), 
    Map.find key G1 = Some elt ->
    Map.find key G2 = Some elt.

Notation "G1 ⊆ G2" := (subG G1 G2) (at level 5).

Definition G_vdash_s (G5 : G) (s5 : s) :=
 forall (x5 : x) (t5 : t) (T5 : T),
  Map.find x5 s5 = Some t5 ->
  Map.find x5 G5 = Some (ctxv_T T5) ->
  typ_e G5 (e_t t5) T5.

Notation "G1 G⊢ s1" := (G_vdash_s G1 s1) (at level 5).

Lemma subG_consistent: forall G1 G2 s0,
  subG G1 G2 -> G_vdash_s G2 s0 -> G_vdash_s G1 s0.
Proof.
  intros.
  intros x_ t_ T_ ? ?.
  apply H in H2.
  pose proof H0 x_ t_ T_ H1 H2.
  inv H3;constructor.
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
Lemma subst_fst_commutes: forall x0 s e_T_list,
  map (fun pat_ : e * T => let (e_, _) := pat_ in e_)
    (map (fun pat_ : e * T => let (e_, T_) := pat_ in (e_var_subst e_ [(x0, s)], T_)) e_T_list) =
    map (fun e : e => e_var_subst e [(x0, s)]) (map (fun pat_ : e * T => let (e_, _) := pat_ in e_) e_T_list).
Proof with auto.
  intros.
  induction e_T_list...
  destruct a;cbn.
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

Lemma e_var_subst_empty: forall e0, e_var_subst e0 [] = e0.
Proof.
  eapply e_ott_ind with
    (P_list_e:= fun es => map (fun e0 => e_var_subst e0 []) es = es);simpl;intros;auto.
  { rewrite H. auto. }
  induction e_l.
  - rewrite H.
    reflexivity.
  - inv H0.
    simpl.
    rewrite H.
    rewrite 2 H2.
    rewrite 2 H3.
    reflexivity.
Qed.

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
    apply (s_well_typed _ _ _ H H2).

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
      apply in_combine_app with (2:=eq_refl)...
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

  - (* RED_FUN_CALL *)
    admit.
Admitted.
