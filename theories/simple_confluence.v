(* Lets define some very simple actor languages and see if we can use abstract_confluence to prove its confluence *)
(* Examples from https://doi.org/10.1016/S0304-3975(01)00365-6 ? *)

From ABS Require Import abstract_confluence.

From stdpp Require Export fin_maps gmap gmultiset.

Section Tick.
(* We need to make some changes to fit the format:
    1) we add server actors to put time_at messages into the system
    2) t actors need more states because we cannot send and receive messages at the same time
    3) servers and non-idle t actors need to store their own id to send messages with only local info
    4) additionally we require some consistency axioms to make this work
*)
  Definition A_id: Set := nat.
  Definition Time: Set := nat.
  Variant Msg: Set := Time_at (c:A_id) | Tick (i:A_id) | Reply (n:Time).
  Variant T_state := Idle | Ans (i:A_id) | Ticking (i:A_id).
  Variant Local_state: Set := T (n:nat) (_:T_state) | Server (p:list A_id) (i:A_id).

  Instance msg_EqDec: EqDecision Msg.
  Proof.
    intros x y.
    destruct x, y;
      try (now left);
      try (now right).
    - is_eq c c0.
      + now left.
      + right.
        intro.
        apply n.
        inv H.
    - is_eq i i0.
      + now left.
      + right.
        intro.
        apply n.
        inv H.
    - is_eq n n0.
      + now left.
      + right.
        intro.
        apply n1.
        inv H.
  Qed.

  Definition g: (nat + nat + nat) -> option Msg :=
    fun x =>
      match x with
      | inr n => Some (Reply n)
      | inl (inl n) => Some (Time_at n)
      | inl (inr i) => Some (Tick i)
      end.
  Definition f: Msg -> (nat + nat + nat) :=
    fun m =>
      match m with
      | Time_at c => (inl (inl c))
      | Tick i => (inl (inr i))
      | Reply n => (inr n)
      end.

  Instance msg_countable: Countable Msg.
  Proof.
    apply inj_countable with (f:=f) (g:=g).
    intros [| |]; simpl; auto.
  Qed.

  Definition Config: Set := gmap A_id (Local_state * gmultiset Msg).

  Variant step (i:A_id): Config -> Config -> Prop :=
    | tick_pop o n q:
      o !! i = Some (T n Idle, q) ->
      (Tick i) ∈ q ->
      (* doesn't actually change the queue *)
      step i o (<[i:=(T n (Ticking i), q ∖ {[+ Tick i +]})]> o)
    | tick_step o n q:
      o !! i = Some (T n (Ticking i), q) ->
      step i o (<[i:=(T (n+1) Idle, q ⊎ {[+ Tick i +]})]> o)
    | req_step o p q j sj q':
      i <> j ->
      o !! i = Some (Server (j::p) i, q) ->
      o !! j = Some (sj, q') ->
      step i o (<[i:=(Server p i, q)]> (<[j:=(sj, q' ⊎ {[+ Time_at i +]})]> o))
    | ans_step o q j n:
      i <> j ->
      o !! i = Some (T n Idle, q) ->
      Time_at j ∈ q ->
      step i o (<[i:=(T n (Ans j), q ∖ {[+ Time_at j +]})]> o)
    (* the servers don't actually do anything with their replies*)
    | ans_rec o q j n sj q':
      i <> j ->
      o !! i = Some (T n (Ans j), q) ->
      o !! j = Some (sj, q') ->
      step i o (<[i:=(T n Idle, q)]> (<[j:=(sj, q' ⊎ {[+ Reply n +]})]> o))
  .

  Definition ctx (m:Msg) (s:Local_state): option Local_state :=
    match m, s with
    | Tick i, T n Idle => Some (T n (Ticking i))
    | Time_at j, T n Idle => Some (T n (Ans j))
    | _, _ => None
    end.

  Definition trans (s:Local_state): option (Local_state * option (Msg * A_id)) :=
    match s with
    | Server (j::rest) i => Some (Server rest i, Some (Time_at i, j))
    | T n (Ans j) => Some (T n Idle, Some (Reply n, j))
    | T n (Ticking i) => Some (T (n+1) Idle, Some (Tick i, i))
    | _ => None
    end.

  Axiom server_consistent: forall (o:Config) i j p q,
      o !! i = Some (Server p j, q) -> i = j.
  Axiom ticking_consistent: forall (o:Config) i j n q,
      o !! i = Some (T n (Ticking j), q) ->  i = j.
  Axiom ans_consistent: forall (o:Config) i j n q,
      o !! i = Some (T n (Ans j), q) ->  i <> j.
  Axiom no_self_call: forall (o:Config) i j p q,
      o !! i = Some (Server (j::p) i, q) -> i <> j.
  Axiom tick_consistent: forall (o:Config) i j n t q,
      o !! i = Some (T n t, q) -> Tick j ∈ q -> i = j.
  Axiom time_at_consistent: forall (o:Config) i j n t q,
      o !! i = Some (T n t, q) -> Time_at j ∈ q -> i <> j.

  Theorem step_correspondence: forall i o o', step i o o' <-> stepG ctx trans i o o'.
  Proof.
    split; intros.
    - destruct H.
      + eapply estepPop; eauto.
      + eapply estepL_message_self; eauto.
      + eapply estepL_message; eauto.
      + eapply estepPop; eauto.
      + eapply estepL_message; eauto.
    - destruct H.
      + destruct σ.
        * destruct t; inv H0.
        * destruct p; inv H0.
      + destruct σi.
        * destruct t; inv H2.
          -- eapply ans_rec; auto.
          -- enough (i = j) by contradiction.
             eapply ticking_consistent; eauto.
        * destruct p; inv H2.
          replace i0 with i in * by (eapply server_consistent; eauto).
          eapply req_step; eauto.
      + destruct σ.
        * destruct t; inv H0.
          -- enough (i <> i) by contradiction.
             eapply ans_consistent; eauto.
          -- eapply tick_step; eauto.
        * destruct p; inv H0.
          enough (i <> i) by contradiction.
          replace i0 with i in * by (eapply server_consistent; eauto).
          eapply no_self_call; eauto.
      + destruct m; inv H2.
        * destruct σ; inv H4.
          destruct t; inv H3.
          inv H1.
          eapply ans_step; eauto.
          eapply time_at_consistent; eauto.
        * destruct σ; inv H4.
          destruct t; inv H3.
          replace i0 with i in * by (eapply tick_consistent; eauto).
          eapply tick_pop; eauto.
  Qed.

  Theorem step_conf: forall i j o oa ob,
      i <> j ->
      step i o oa ->
      step j o ob ->
      exists o', step j oa o' /\ step i ob o'.
  Proof.
    eapply step_confluence.
    - exact ctx.
    - exact trans.
  Qed.
End Tick.
