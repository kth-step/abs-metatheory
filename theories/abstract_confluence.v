(*| We prove confluence in an abstract setting
=======================================

The idea is to define an abstract actor system in which confluence is trivial,
and then instantiate other actor systems for it. We need notions of:
- local state
- local computations
- messages
- (unordered) queues

The resulting system has three important properties:
- encapsulation: only local transitions affect local state
- queue monotonicity: only local transitions *remove* messages from queues
- queue commutations: add m (add m' q)) = add m' (add m q)
|*)

From stdpp Require Export
  tactics
  gmultiset
  fin_maps
  gmap
  sets
.
Tactic Notation "simp" := simplify_map_eq.
Tactic Notation "is_eq" ident(a) ident(b) :=
  destruct (decide (a = b)) as [<- | ?].

Section AbstractActors.
  (** Syntax / setup *)
  (* The appendix indexes everything, but for now we will assume that all actors
     have the same type of local state, messages and transition functions.
     In practice this actually does not matter at all, since Σ could be a sum type
   *)

  (* Local states and messages *)
  Variable Σ : Set.
  Variable M : Set.
  (* The type of messages must be countable and have decidable equality in order to form multisets *)
  Context `{M_count: Countable M}.

  (* The context contains denotations for messages (like a method table)*)
  Definition context := M -> (Σ -> option Σ).
  Variable ctx : context.

  (* A queue is a multiset of messages *)
  Notation queue := (gmultiset M).
  Definition add (m:M) (q:queue) := q ⊎ {[+ m +]}.
  Definition remove (m:M) (q:queue) := difference q {[+ m +]}.

  Notation tid := nat.
  Notation configL := (Σ * queue)%type.
  Notation config := (gmap tid configL)%type.

  (* A transition function is a partial function from states to states that may
emit a message *)
  Definition transition_function := (Σ -> option (Σ * option (M * tid))).
  Variable T: transition_function.

  (** Semantics *)
  Variant stepG (i:tid): config -> config -> Prop :=
    | stepL: forall C σ σ' q,
        C !! i = Some (σ, q) ->
        T σ = Some (σ', None) ->
        stepG i C (<[i:=(σ', q)]> C)
    | stepL_message: forall C σi σj σ' m j qi qj,
        i <> j ->
        C !! i = Some (σi, qi) ->
        C !! j = Some (σj, qj) ->
        T σi = Some (σ', Some (m, j)) ->
        stepG i C (<[i:=(σ', qi)]> (<[j:=(σj, add m qj)]> C))
    | stepL_message_self: forall C σ σ' q m,
        C !! i = Some (σ, q) ->
        T σ = Some (σ', Some (m, i)) ->
        stepG i C (<[i:=(σ', add m q)]> C)
    | stepPop: forall C m σ σ' q,
        C !! i = Some (σ, q) ->
        m ∈ q ->
        T σ = None ->
        ctx m σ = Some σ' ->
        stepG i C (<[i:=(σ', remove m q)]> C)
  .
  Notation "c ->[ i ] c'" := (stepG i c c') (at level 90).

  (* Convenient alternative stepping rules for unification *)
  Lemma estepL: forall i C C' σ σ' q,
      C !! i = Some (σ, q) ->
      T σ = Some (σ', None) ->
      C' = <[i:=(σ', q)]> C ->
      C ->[i] C'.
  Proof. intros; subst; econstructor; eauto. Qed.

  Lemma estepL_message: forall C C' i j σi σj σ' m qi qj,
      i <> j ->
      C !! i = Some (σi, qi) ->
      C !! j = Some (σj, qj) ->
      T σi = Some (σ', Some (m, j)) ->
      C' = (<[i:=(σ', qi)]> (<[j:=(σj, add m qj)]> C)) ->
      C ->[i] C'.
  Proof. intros; subst; econstructor; eauto. Qed.

  Lemma estepL_message_self: forall C C' i σ σ' q m,
      C !! i = Some (σ, q) ->
      T σ = Some (σ', Some (m, i)) ->
      C' = (<[i:=(σ', add m q)]> C) ->
      C ->[i] C'.
  Proof. intros; subst; eapply stepL_message_self; eauto. Qed.

  Lemma estepPop: forall C C' i m σ σ' q,
      C !! i = Some (σ, q) ->
      m ∈ q ->
      T σ = None ->
      ctx m σ = Some σ' ->
      C' = (<[i:=(σ', remove m q)]> C) ->
      C ->[i] C'.
  Proof. intros; subst; eapply stepPop; eauto. Qed.

  Definition state_of (j:tid) (C:config) : option Σ :=
    match C !! j with
    | None => None
    | Some (σ, _) => Some σ
    end.

  Definition queue_of (j:tid) (C:config) : queue :=
    match C !! j with
    | None => empty
    | Some (_, q) => q
    end.

  (** StepG enjoys three key properties *)
  Fact encapsulation: forall C C' i j,
      C ->[ i ] C' ->
      i <> j ->
      state_of j C = state_of j C'.
  Proof.
    intros.
    induction H;
      try (now unfold state_of; simp; destruct (C !! j); auto).
    is_eq j j0; unfold state_of; now simp.
  Qed.

  Lemma add_monotone: forall m q, q ⊆ add m q.
  Proof. set_unfold; intros; lia. Qed.

  Fact queue_monotonicity: forall C C' i j,
      C ->[ i ] C' ->
      i <> j ->
      queue_of j C ⊆ queue_of j C'.
  Proof.
    intros.
    induction H;
      try (now unfold queue_of; simp; destruct (C !! j); auto).
    is_eq j j0; unfold queue_of; simp.
    - apply add_monotone.
    - now destruct (C !! j).
  Qed.

  Fact add_commutes: forall q m m',
      add m (add m' q) = add m' (add m q).
  Proof. set_unfold; intros; lia. Qed.

  Fact add_remove_commutes: forall q m m',
      m' ∈ q ->
      add m (remove m' q) = remove m' (add m q).
  Proof.
    intros.
    is_eq m m'; set_unfold; unfold multiplicity in *; intros.
    - is_eq x m; simp; lia.
    - is_eq x m'; is_eq x m; simp; lia.
  Qed.

  (* and is confluent! *)
  Theorem confluence: forall C C1 C2 i j,
      i <> j ->
      C ->[ i ] C1 ->
      C ->[ j ] C2 ->
      exists C', (C1 ->[ j ] C') /\ (C2 ->[ i ] C').
  Proof.
  (* an extremely tedious proof of this: should be ripe for automation *)
    intros.
    destruct H0, H1.
    - eexists. split.
      + eapply stepL; simp; eauto.
      + rewrite insert_commute; eauto.
        eapply stepL; simp; eauto.
    - is_eq i j0.
      + eexists. split.
        * eapply stepL_message; simp; eauto.
        * eapply estepL; simp; eauto.
          rewrite (insert_commute _ i j); eauto.
          now rewrite 2 insert_insert.
      + eexists. split.
        * eapply stepL_message; [apply H1|..]; simp; eauto.
        * eapply estepL; simp; eauto.
          rewrite (insert_commute _ i j); eauto.
          rewrite (insert_commute _ i j0); eauto.
    - eexists. split.
      + eapply stepL_message_self; simp; eauto.
      + eapply estepL; simp; eauto.
        rewrite insert_commute; eauto.
    - eexists. split.
      + eapply stepPop; simp; eauto.
      + eapply estepL; simp; eauto.
        rewrite insert_commute; eauto.
    - is_eq j j0.
      + eexists. split.
        * eapply stepL; simp; eauto.
        * eapply estepL_message; simp; eauto.
          rewrite (insert_commute _ i j); eauto.
          rewrite 2 insert_insert.
          now rewrite insert_commute; eauto.
      + eexists. split.
        * eapply stepL; simp; eauto.
        * eapply estepL_message; [apply H0|..]; simp; eauto.
          rewrite (insert_commute _ j i); eauto.
          rewrite (insert_commute _ j j0); eauto.
    - is_eq j j0.
      + is_eq i j1.
        * eexists. split.
          -- eapply estepL_message; simp; eauto.
          -- eapply estepL_message; simp; eauto.
             rewrite 2 insert_insert.
             rewrite 2 (insert_commute _ i j); eauto.
             now rewrite 2 insert_insert.

        * eexists. split.
          -- eapply estepL_message; [apply H1|..]; simp; eauto.
          -- eapply estepL_message; simp; eauto.
             rewrite (insert_commute _ i j); eauto.
             rewrite (insert_commute _ j1 j); eauto.
             rewrite 2 insert_insert.
             rewrite (insert_commute _ i j); eauto.
             rewrite (insert_commute _ i j1); eauto.
      + is_eq i j1.
        * eexists. split.
          -- eapply estepL_message; [apply H1|..]; simp; eauto.
          -- eapply estepL_message; [apply H0|..]; simp; eauto.
             rewrite (insert_commute _ i j0 (σ', add m0 qi)); eauto.
             rewrite (insert_commute _ i j (σ', add m0 qi)); eauto.
             rewrite 2 insert_insert.
             rewrite (insert_commute _ j0 j); eauto.
             rewrite (insert_commute _ i j0); eauto.
        * is_eq j0 j1.
          -- eexists. split.
             ++ eapply estepL_message; [apply H1|..]; simp; eauto.
             ++ eapply estepL_message; [apply H0|..]; simp; eauto.
                rewrite (insert_commute _ j0 i); eauto.
                rewrite (insert_commute _ j0 j); eauto.
                rewrite 2 insert_insert.
                rewrite (insert_commute _ j i); eauto.
                now rewrite add_commutes.
          -- eexists. split.
             ++ eapply estepL_message; [apply H1|..]; simp; eauto.
             ++ eapply estepL_message; [apply H0|..]; simp; eauto.
                rewrite (insert_commute _ j0 j); eauto.
                rewrite (insert_commute _ i j); eauto.
                rewrite (insert_commute _ j0 j1); eauto.
                rewrite (insert_commute _ i j1); eauto.
    - is_eq j0 j.
      + eexists. split.
        * eapply estepL_message_self; simp; eauto.
        * eapply estepL_message; simp; eauto.
          rewrite (insert_commute _ j0 i); eauto.
          rewrite 2 insert_insert.
          now rewrite add_commutes.
      + eexists. split.
        * eapply estepL_message_self; simp; eauto.
        * eapply estepL_message;[apply H0|..]; simp; eauto.
          rewrite (insert_commute _ j i); eauto.
          rewrite (insert_commute _ j j0); eauto.
    - is_eq j0 j.
      + eexists. split.
        * eapply stepPop; simp; eauto.
          set_unfold; eauto.
        * eapply estepL_message; simp; eauto.
          rewrite (insert_commute _ i j0); eauto.
          rewrite 2 (insert_insert).
          rewrite insert_commute, add_remove_commutes; eauto.
      + eexists. split.
        * eapply stepPop; simp; eauto.
        * eapply estepL_message;[apply H0|..]; simp; eauto.
          rewrite (insert_commute _ j i); eauto.
          rewrite (insert_commute _ j j0); eauto.
    - eexists. split.
      + eapply stepL; simp; eauto.
      + eapply estepL_message_self; simp; eauto.
        apply insert_commute; eauto.
    - is_eq i j0.
      + eexists. split.
        * eapply stepL_message; simp; eauto.
        * eapply estepL_message_self; simp; eauto.
          rewrite (insert_commute _ i j); eauto.
          now rewrite 2 insert_insert, add_commutes.
      + eexists. split.
        * eapply stepL_message; [apply H1|..]; simp; eauto.
        * eapply estepL_message_self; simp; eauto.
          rewrite (insert_commute _ i j); eauto.
          rewrite (insert_commute _ i j0); eauto.
    - eexists. split.
      + eapply stepL_message_self; simp; eauto.
      + eapply estepL_message_self; simp; eauto.
        rewrite insert_commute; eauto.
    - eexists. split.
      + eapply stepPop; simp; eauto.
      + eapply estepL_message_self; simp; eauto.
        rewrite insert_commute; eauto.
    - eexists. split.
      + eapply stepL; simp; eauto.
      + eapply estepPop; simp; eauto.
        rewrite insert_commute; eauto.
    - is_eq i j0.
      + eexists. split.
        * eapply stepL_message; simp; eauto.
        * eapply estepPop; simp; eauto.
          -- set_unfold; eauto.
          -- rewrite (insert_commute _ i j); eauto.
             rewrite 2 insert_insert, add_remove_commutes; eauto.
      + eexists. split.
        * eapply stepL_message; [apply H1|..]; simp; eauto.
        * eapply estepPop; simp; eauto.
          rewrite (insert_commute _ i j); eauto.
          rewrite (insert_commute _ i j0); eauto.
    - eexists. split.
      + eapply stepL_message_self; simp; eauto.
      + eapply estepPop; simp; eauto.
        apply insert_commute; eauto.
    - eexists. split.
      + eapply stepPop; simp; eauto.
      + eapply estepPop; simp; eauto.
        apply insert_commute; eauto.
  Qed.


  Variable step: tid -> config -> config -> Prop.
  Parameter step_correspondence: forall i o o', step i o o' <-> stepG i o o'.

  Theorem step_confluence: forall i j o oa ob,
      i <> j ->
      step i o oa ->
      step j o ob ->
      exists o', step j oa o' /\ step i ob o'.
  Proof.
    intros.
    epose proof confluence o oa ob _ _ H as (?o & ?stepa & ?stepb).
    { now apply step_correspondence. }
    { now apply step_correspondence. }
    exists o0.
    split; apply step_correspondence; auto.
  Qed.
End AbstractActors.

Arguments stepG {Σ} {M} {_} {_}.
