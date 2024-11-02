From stdpp Require Import prelude fin_maps.

Ltac splits := repeat split.
Tactic Notation "intros*" := repeat intro.

Ltac forward H :=
  match type of H with
  | ?x -> _ =>
      let name := fresh in assert x as name; [| specialize (H name); clear name]
  end.
Tactic Notation "forward" ident(H) :=
  forward H.

Tactic Notation "is_eq" ident(a) ident(b) :=
  destruct (decide (a = b)) as [<- | ?].

Section ListLemmas.
  Context {X Y: Type}.

  Lemma map_eq: forall (l: list X) (f g: X -> Y),
      (forall x, f x = g x) ->
      map f l = map g l.
  Proof.
    induction l; intros; auto.
    simpl.
    rewrite (H a).
    erewrite (IHl); eauto.
  Qed.

  Lemma map_split {Z W: Type}: forall (l: list (Z*X)) (l2: list (X*Y*Z*W)),
      map fst l = map (fun '(_, _, z, _) => z) l2 ->
      map snd l = map (fun '(x, _, _, _) => x) l2 ->
      l = map (fun '(x, _, z,_) => (z, x)) l2.
  Proof.
    induction l; intros.
    - inv H.
      symmetry in H2.
      apply map_eq_nil in H2.
      now subst.
    - destruct a.
      destruct l2.
      + inv H.
      + destruct p as (((?, ?), ?), ?).
        inv H.
        rewrite (IHl l2); auto.
  Qed.

  Lemma map_xs {Z W: Type}: forall (T_x_t_y_list: list (X*Y*Z*W)),
      map (fun pat_ : X * Y => let (_, x_) := pat_ in x_) (map (fun '(T_, x_, _, _) => (T_, x_)) T_x_t_y_list) =
        map (fun '(_, x, _, _) => x) T_x_t_y_list.
  Proof.
    induction T_x_t_y_list.
    - easy.
    - destruct a as (((?, ?), ?), ?).
      simpl.
      now rewrite IHT_x_t_y_list.
  Qed.

  Lemma map_split' {Z Z' W: Type}: forall (l: list (Z'*X)) (l2: list (X*Y*Z*W)) (f: Z -> Z'),
      map fst l = map (fun '(_, _, z, _) => f z) l2 ->
      map snd l = map (fun '(x, _, _, _) => x) l2 ->
      l = map (fun '(x, _, z,_) => (f z, x)) l2.
  Proof.
    induction l; intros.
    - inv H.
      symmetry in H2.
      apply map_eq_nil in H2.
      now subst.
    - destruct a.
      destruct l2.
      + inv H.
      + destruct p as (((?, ?), ?), ?).
        inv H.
        rewrite (IHl l2 f); auto.
  Qed.

  Lemma combine_fst: forall (l1: list X) (l2: list Y),
      length l1 = length l2 ->
      map (fun pat_: (X*Y) => let (e_, _) := pat_ in e_) (combine l1 l2) = l1.
  Proof.
    induction l1;intros.
    - easy.
    - destruct l2.
      + inv H.
      + inv H.
        simpl.
        rewrite (IHl1 l2 H1).
        reflexivity.
  Qed.

  Lemma combine_nil: forall (l1: list X),
      @combine X Y l1 [] = [].
  Proof. destruct l1; easy. Qed.

  Lemma combine_snd: forall (l1: list X) (l2: list Y),
      length l1 = length l2 ->
      map (fun pat_: (X*Y) => let (_, e_) := pat_ in e_) (combine l1 l2) = l2.
  Proof.
    intros.
    generalize dependent l1.
    induction l2; intros.
    - rewrite combine_nil.
      auto.
    - destruct l1.
      + inv H.
      + inv H.
        simpl.
        rewrite (IHl2 l1 H1).
        reflexivity.
  Qed.

  Lemma in_combine: forall (l1: list X) (l2: list Y) x y,
      In (x,y) (combine l1 l2) -> In x l1 /\ In y l2.
  Proof.
    induction l1;intros.
    - inv H.
    - destruct l2.
      + inv H.
      + destruct H.
        * inv H.
          split; left; auto.
        * destruct (IHl1 l2 x y H).
          split; right; auto.
  Qed.

  Lemma combine_app: forall (l1 l2: list X) (l1' l2': list Y),
      length l1 = length l1' ->
      length l2 = length l2' ->
      combine (l1 ++ l2) (l1' ++ l2') = combine l1 l1' ++ combine l2 l2'.
  Proof.
    induction l1; intros.
    - inv H.
      symmetry in H2.
      apply length_zero_iff_nil in H2.
      rewrite H2.
      easy.
    - destruct l1'.
      + inv H.
      + inv H.
        simpl.
        rewrite IHl1; easy.
  Qed.

  Lemma in_split: forall (l1 l2: list X) x,
      x ∈ (l1 ++ [x] ++ l2).
  Proof.
    induction l1; intros.
    - left; auto.
    - right.
      apply IHl1.
  Qed.

  Lemma in_combine_split: forall (l: list (X*Y)) l1 l1' l2 l2' x y,
      length l1 = length l2 ->
      l = combine (l1 ++ [x] ++ l1') (l2 ++ [y] ++ l2') ->
      In (x, y) l.
  Proof.
    induction l; intros; subst.
    - destruct l1, l2; easy.
    - destruct a.
      destruct l1,l2.
      + inv H0.
        left;auto.
      + inv H.
      + inv H.
      + inv H.
        right.
        inv H0.
        eapply IHl.
        apply H2.
        reflexivity.
  Qed.

  Lemma in_fst_iff: forall (l : list (X*Y)) x,
      (exists y, In (x, y) l) <-> In x (map (fun pat_ : X * Y => let (e_, _) := pat_ in e_) l).
  Proof.
    split; intros.
    - induction l.
      + destruct H.
        inv H.
      + destruct H as (?y & H).
        inv H.
        * left; auto.
        * right.
          apply IHl.
          exists y; auto.
    - induction l.
      + inv H.
      + destruct a as (?x & ?y).
        inv H.
        * exists y.
          left;auto.
        * destruct (IHl H0) as (?y & ?).
          exists y0.
          right.
          apply H.
  Qed.

  Lemma pat2_id: forall l: list (X*Y),
      map (fun pat_ : X*Y => let (x_, y_) := pat_ in (x_,y_)) l = l.
  Proof.
    induction l;auto.
    destruct a; cbn.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma fold_map {A Z W: Type}: forall (f: W -> Z -> A -> A) (l: list (X*Y*Z*W)) a0,
      foldr (fun '(_, _, z, w) a => f w z a) a0 l =
        foldr (fun (xt : W * Z) a => f (fst xt) (snd xt) a) a0
          (map (fun pat_ : X*Y*Z*W => let (p, y_) := pat_ in let (p0, t_) := p in let (_, _) := p0 in (y_, t_)) l).
  Proof.
    induction l; intros; eauto.
    destruct a as [[[? ?] ?] ?].
    simpl.
    now rewrite IHl.
  Qed.

  Lemma fold_map1 {A Z W: Type}: forall (f: W -> X -> A -> A) (l: list (X*Y*Z*W)) a0,
      foldr (fun '(z, _, _, w) a => f w z a) a0 l =
        foldr (fun '(z, w) a => f z w a) a0
          (map (fun '(z, _, _, w) => (w, z)) l).
  Proof.
    induction l; intros; eauto.
    destruct a as [[[? ?] ?] ?].
    simpl.
    now rewrite IHl.
  Qed.

  Lemma fold_map2 {A Z W: Type}: forall (f: Y -> X -> A -> A) (l: list (X*Y*Z*W)) a0,
      foldr (fun '(z, w, _, _) a => f w z a) a0 l =
        foldr (fun '(z, w) a => f z w a) a0
          (map (fun '(z, w, _, _) => (w, z)) l).
  Proof.
    induction l; intros; eauto.
    destruct a as [[[? ?] ?] ?].
    simpl.
    now rewrite IHl.
  Qed.

  Lemma fold_map3 {A Z W: Type}: forall (f: W -> Y -> A -> A) (l: list (X*Y*Z*W)) a0,
      foldr (fun '(_, z, _, w) a => f w z a) a0 l =
        foldr (fun '(z, w) a => f z w a) a0
          (map (fun '(_, z, _, w) => (w, z)) l).
  Proof.
    induction l; intros; eauto.
    destruct a as [[[? ?] ?] ?].
    simpl.
    now rewrite IHl.
  Qed.

  Lemma fold_map4 {A Z W: Type}: forall (f : _ -> _ -> A -> A) (l: list (X*Y*Z*W)) a0,
      foldr (fun '(z, w, _, _) a => f z w a) a0 l =
        foldr (fun '(z, w) a => f z w a) a0
          (map (fun '(z, w, _, _) => (z, w)) l).
  Proof.
    induction l; intros; eauto.
    destruct a as [[[? ?] ?] ?].
    simpl.
    now rewrite IHl.
  Qed.

  Lemma fold_map5 {A Z W: Type}: forall (f : _ -> _ -> A -> A) (l: list (X*Y*Z*W)) a0,
      foldr (fun '(z, _, _, w) a => f z w a) a0 l =
        foldr (fun '(z, w) a => f z w a) a0
          (map (fun '(z, _, _, w) => (z, w)) l).
  Proof.
    induction l; intros; eauto.
    destruct a as [[[? ?] ?] ?].
    simpl.
    now rewrite IHl.
  Qed.

  Lemma combine_map: forall (l: list (X*Y)),
      combine (map fst l) (map snd l) = l.
  Proof.
    induction l; auto.
    destruct a; simpl.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma split_corresponding_list: forall (l: list (X*Y)) left_list mid right_list,
      map (fun '(x, _) => x) l = left_list ++ [mid] ++ right_list ->
      exists left_list' mid' right_list',
        length left_list = length left_list'
        /\ length right_list = length right_list'
        /\ l = combine (left_list ++ [mid] ++ right_list) (left_list' ++ [mid'] ++ right_list').
  Proof with auto.
    induction l;intros.
    - apply app_cons_not_nil in H.
      contradiction.
    - destruct a.
      destruct left_list, right_list;
        inv H.
      + exists [], y, [].
        apply map_eq_nil in H2.
        rewrite H2.
        splits...
      + destruct (IHl [] x0 right_list H2)
          as (left_list' & mid' & right_list' & ? & ? & ?).
        exists [], y, (left_list' ++ [mid'] ++ right_list').
        splits...
        * inv H.
          symmetry in H4.
          apply length_zero_iff_nil in H4.
          rewrite H4.
          rewrite 2 app_nil_l.
          rewrite map_length.
          rewrite combine_length.
          rewrite 2 app_length.
          simpl.
          rewrite H0.
          lia.
        * simpl.
          rewrite H1.
          rewrite combine_fst.
          { easy. }
          rewrite app_nil_l.
          rewrite 3 app_length.
          rewrite <- H.
          rewrite H0.
          easy.
      + destruct (IHl left_list mid [] H2)
          as (left_list' & mid' & right_list' & ? & ? & ?).
        exists (y::left_list'), mid', right_list'.
        splits...
        * inv H0.
          simpl.
          rewrite H.
          easy.
        * rewrite H1.
          easy.
      + destruct (IHl left_list mid (x1::right_list) H2)
          as (left_list' & mid' & right_list' & ? & ? & ?).
        exists (y::left_list'), mid', (right_list').
        splits...
        * simpl.
          rewrite H.
          easy.
        * rewrite H1.
          easy.
  Qed.

  (* I thought this would be useful, but turns out we usually need the length *)
  Corollary split_corresponding_list_no_length: forall (l: list (X*Y)) left_list mid right_list,
      map (fun '(x, _) => x) l = left_list ++ [mid] ++ right_list ->
      exists left_list' mid' right_list', l = combine (left_list ++ [mid] ++ right_list) (left_list' ++ [mid'] ++ right_list').
  Proof.
    intros.
    destruct (split_corresponding_list _ _ _ _ H)
      as (left_list' & mid' & right_list' & _ & _ & EQ).
    exists left_list', mid', right_list'.
    apply EQ.
  Qed.

End ListLemmas.

From ABS Require Import abs_defs.
From Equations Require Import Equations.


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
Proof.
  intros.
  induction e_T_list; auto.
  destruct a;cbn in *.
  now rewrite IHe_T_list.
Qed.

(* Characterizing substitution *)

Lemma subst_term: forall t sub,
  e_var_subst (e_t t) sub = (e_t t).
Proof.
  induction sub.
  - trivial.
  - destruct a.
    simpl.
    rewrite IHsub.
    now simp e_var_subst_one.
Qed.

Definition replace_var (x0:x) (sub:list(x*x)) :=
 fold_right (fun '(x_, y_) x0 => if (eq_x x0 x_) then y_ else x0) x0 sub.

Lemma subst_var: forall x0 sub,
  e_var_subst (e_var x0) sub = e_var (replace_var x0 sub).
Proof.
  induction sub.
  - trivial.
  - destruct a; simpl.
    rewrite IHsub.
    simp e_var_subst_one.
    destruct (eq_x (replace_var x0 sub)); subst; eauto.
Qed.

Lemma e_list_subst_map: forall x0 y0 e_list,
  e_list_subst_one e_list x0 y0 = map (fun e_ => e_var_subst_one e_ x0 y0) e_list.
Proof.
  induction e_list; [easy|];
  destruct a;
    simpl;
    now rewrite IHe_list.
Qed.

Lemma subst_fn: forall fn0 sub e_list,
  e_var_subst (e_fn_call fn0 e_list) sub = (e_fn_call fn0 (map (fun e' => e_var_subst e' sub) e_list)).
Proof.
  induction sub; intros.
  - simpl.
    now rewrite map_id.
  - destruct a.
    simpl.
    rewrite IHsub.
    simp e_var_subst_one.
    now rewrite e_list_subst_map, map_map.
Qed.

Lemma e_list_subst: forall el x0 y0,
  e_list_subst_one el x0 y0 = map (fun e => e_var_subst_one e x0 y0) el.
Proof.
  induction el; intros.
  - trivial.
  - simpl.
    now rewrite IHel.
Qed.

Lemma e_list_fresh: forall e0 ys el,
  fresh_vars_el ys el ->
  In e0 el ->
  fresh_vars_e ys e0.
Proof.
  induction el.
  - easy.
  - simpl; intros.
    destruct H0; subst.
    + now destruct H.
    + destruct H.
      apply IHel; eauto.
Qed.

(* Properties of fresh_e*)
Lemma fresh_first_e: forall e0 y ys,
  fresh_vars_e (y::ys) e0 -> fresh_vars_e [y] e0.
Proof.
  induction e0 using e_ott_ind
    with (P_list_e := fun e_list =>
                        forall e0 y ys,
                        In e0 e_list ->
                        fresh_vars_e (y::ys) e0 -> fresh_vars_e [y] e0);
     intros; try easy.
  - simp fresh_vars_e in *.
    intro.
    inv H0.
    + apply H.
    now left.
    + inv H1.
  - simp fresh_vars_e in *.
    induction e_list.
    + easy.
    + inv H.
      split.
      * eapply IHe0; eauto.
        now left.
      * eapply IHe_list; eauto.
        intros; eapply IHe0; eauto.
        now right.
  - inv H.
    + eapply IHe0; eauto.
    + eapply IHe1; eauto.
Qed.

Lemma fresh_monotone_e: forall e0 y ys,
  fresh_vars_e (y::ys) e0 -> fresh_vars_e ys e0.
Proof.
  induction e0 using e_ott_ind
    with (P_list_e := fun e_list =>
                        forall e0 y ys,
                        In e0 e_list ->
                        fresh_vars_e (y::ys) e0 -> fresh_vars_e ys e0);
     intros; try easy.
  - simp fresh_vars_e in *.
    intro.
    apply H.
    right.
    assumption.
  - simp fresh_vars_e in *.
    induction e_list.
    + easy.
    + inv H.
      split.
      * eapply IHe0; eauto.
        now left.
      * apply IHe_list; eauto.
        intros; eapply IHe0; eauto.
        now right.
  - inv H.
    + eapply IHe0; eauto.
    + eapply IHe1; eauto.
Qed.

Lemma fresh_first_el: forall el y ys,
    fresh_vars_el (y::ys) el -> fresh_vars_el [y] el.
Proof.
  induction el; intros.
  - now inv H.
  - inv H.
    split.
    + now apply fresh_first_e in H0.
    + eapply IHel; eauto.
Qed.

Lemma fresh_monotone_el: forall el y ys,
  fresh_vars_el (y::ys) el -> fresh_vars_el ys el.
Proof.
  induction el; intros.
  - now inv H.
  - inv H.
    split.
    + now apply fresh_monotone_e in H0.
    + eapply IHel; eauto.
Qed.

Lemma fresh_var_subst: forall e0 y sub,
  fresh_vars_e (map snd sub) e0 ->
  fresh_vars_e [y] e0 ->
  ~ In y (map snd sub) ->
  fresh_vars_e [y] (e_var_subst e0 sub).
Proof.
  intros.
  generalize dependent y.
  generalize dependent e0.
  induction e0 using e_ott_ind
    with
    (P_list_e := fun e_list => forall y,
                     fresh_vars_el (map snd sub) e_list ->
                     fresh_vars_el [y] e_list ->
                     ~ In y (map snd sub) ->
                     fresh_vars_el [y] (map (fun e' => e_var_subst e' sub) e_list))
  ; intros; auto.
  - rewrite subst_term.
    now simp e_var_subst_one.
  - induction sub; auto.
    destruct a as (?x_, ?y); simpl.
    rewrite subst_var.
    simp e_var_subst_one.
    destruct (eq_x (replace_var x5 sub) x_).
    + simp fresh_vars_e.
      intro.
      apply H1.
      left.
      now inv H2.
    + rewrite <- subst_var.
      apply Decidable.not_or in H1.
      destruct H1.
      apply fresh_monotone_e in H.
      eapply IHsub; auto.
  - rewrite subst_fn.
    simp fresh_vars_e in *.
  - destruct H,H0.
    split.
    + apply IHe0; auto.
    + apply IHe1; eauto.
Qed.

Lemma disjoint_monotone {A:Type}: forall (l1 l2: list A) a1 a2,
  disjoint (a1::l1) (a2::l2) -> disjoint l1 l2.
Proof.
  intros.
  intros x ? ?.
  apply (H x); now right.
Qed.

Section MapLemmas.

  Context `{FinMap x mp}.

  Lemma neq_none_is_some: forall A (x: option A),
      x <> None -> exists y, x = Some y.
  Proof.
    destruct x; intros; eauto.
    contradiction.
  Qed.

  Lemma map_neq_none_is_some {A}: forall (m: mp A) x,
      lookup x m <> None ->
      exists y, lookup x m = Some y.
  Proof.
    intros.
    apply neq_none_is_some in H7.
    apply H7.
  Qed.

  Lemma fold_map_reshuffle: forall (l: list (T*x*t*x)) G0,
      (foldr (fun (ax : x * T) (G' : G) => insert (fst ax) (ctxv_T (snd ax)) G') G0
         (map (fun pat_ : T * x => let (T_, x_) := pat_ in (x_, T_)) (map (fun '(T_0, x_, _, _) => (T_0, x_)) l)))
      = (foldr (fun '(T1, x_, _, _) (G' : G) => insert x_ (ctxv_T T1) G') G0 l).
  Proof.
    induction l;intros;auto.
    destruct a as (((?T_ & ?x_) & ?t_) & ?y).
    simpl.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma fold_add_comm: forall (G0: G) y T_ (upd: list (T*x)),
      ~ y ∈ (map (fun '(_, y) => y) upd) ->
      (insert y (ctxv_T T_) (foldr (fun '(T_, y) G0 => insert y (ctxv_T T_) G0) G0 upd)) =
        (foldr (fun '(T_, y) G0 => insert y (ctxv_T T_) G0) (insert y (ctxv_T T_) G0) upd).
  Proof.
    induction upd; intros.
    - easy.
    - destruct a; simpl in *.
      is_eq x y.
      + exfalso.
        apply H7.
        left.
      + rewrite <- IHupd; eauto.
        setoid_rewrite insert_commute with (i:=x); eauto.
        intro.
        apply H7.
        now right.
  Qed.
End MapLemmas.
