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
