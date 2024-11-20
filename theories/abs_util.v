From stdpp Require Import prelude fin_maps countable gmap.
From ABS Require Import abs_defs list_util.
From Equations Require Import Equations.

(** * ABS Utility Results *)

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

Lemma subst_neg: forall e0 sub,
    e_var_subst (e_neg e0) sub = e_neg (e_var_subst e0 sub).
Proof.
  induction sub as [ | (?&?) ]; intros; simpl; auto.
  now rewrite IHsub.
Qed.

Lemma subst_not: forall e0 sub,
    e_var_subst (e_not e0) sub = e_not (e_var_subst e0 sub).
Proof.
  induction sub as [ | (?&?) ]; intros; simpl; auto.
  now rewrite IHsub.
Qed.

Lemma subst_add: forall e1 e2 sub,
    e_var_subst (e_add e1 e2) sub = e_add (e_var_subst e1 sub) (e_var_subst e2 sub).
Proof.
  induction sub as [ | (?&?) ]; intros; simpl; auto.
  now rewrite IHsub.
Qed.

Lemma subst_mul: forall e1 e2 sub,
    e_var_subst (e_mul e1 e2) sub = e_mul (e_var_subst e1 sub) (e_var_subst e2 sub).
Proof.
  induction sub as [ | (?&?) ]; intros; simpl; auto.
  now rewrite IHsub.
Qed.

Lemma subst_eq: forall e1 e2 sub,
    e_var_subst (e_eq e1 e2) sub = e_eq (e_var_subst e1 sub) (e_var_subst e2 sub).
Proof.
  induction sub as [ | (?&?) ]; intros; simpl; auto.
  now rewrite IHsub.
Qed.

Lemma subst_lt: forall e1 e2 sub,
    e_var_subst (e_lt e1 e2) sub = e_lt (e_var_subst e1 sub) (e_var_subst e2 sub).
Proof.
  induction sub as [ | (?&?) ]; intros; simpl; auto.
  now rewrite IHsub.
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
    intros; simp fresh_vars_e in *;
    (* the binary operations *)
    try (inv H; split;
         [eapply IHe0_1; eauto | eapply IHe0_2; eauto]);
    (* the other easy ones*)
    try easy.
  - intro.
    inv H0.
    + apply H.
    now left.
    + inv H1.
  - induction e_list.
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
    intros; simp fresh_vars_e in *;
    (* the binary operations *)
    try (inv H; split;
         [eapply IHe0_1; eauto | eapply IHe0_2; eauto]);
    (* the other easy ones*)
    try easy.
  - intro.
    apply H.
    right.
    assumption.
  - induction e_list.
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
  - rewrite subst_neg.
    simp fresh_vars_e in *.
  - rewrite subst_not.
    simp fresh_vars_e in *.
  - rewrite subst_add.
    simp fresh_vars_e in *.
    destruct H0, H.
    split.
    + apply IHe0_1; auto.
    + apply IHe0_2; auto.
  - rewrite subst_mul.
    simp fresh_vars_e in *.
    destruct H0, H.
    split.
    + apply IHe0_1; auto.
    + apply IHe0_2; auto.
  - rewrite subst_eq.
    simp fresh_vars_e in *.
    destruct H0, H.
    split.
    + apply IHe0_1; auto.
    + apply IHe0_2; auto.
  - rewrite subst_lt.
    simp fresh_vars_e in *.
    destruct H0, H.
    split.
    + apply IHe0_1; auto.
    + apply IHe0_2; auto.
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

#[export] Instance t_eq_dec : EqDecision t.
Proof.
  unfold EqDecision, Decision.
  decide equality; auto with ott_coq_equality.
Defined.
#[export] Hint Resolve t_eq_dec : ott_coq_equality.

Section e_rec.
  Variables
    (P_e : e -> Set)
    (P_list_e : list e -> Set).

  Hypothesis
    (H_e_t : forall (t5:t), P_e (e_t t5))
    (H_e_var : forall (x5:x), P_e (e_var x5))
    (H_e_neg : forall (e5:e), P_e e5 -> P_e (e_neg e5))
    (H_e_not : forall (e5:e), P_e e5 -> P_e (e_not e5))
    (H_e_add : forall (e1:e), P_e e1 -> forall (e2:e), P_e e2 -> P_e (e_add e1 e2))
    (H_e_mul : forall (e1:e), P_e e1 -> forall (e2:e), P_e e2 -> P_e (e_mul e1 e2))
    (H_e_eq : forall (e1:e), P_e e1 -> forall (e2:e), P_e e2 -> P_e (e_eq e1 e2))
    (H_e_lt : forall (e1:e), P_e e1 -> forall (e2:e), P_e e2 -> P_e (e_lt e1 e2))
    (H_e_fn_call : forall (e_list:list e), P_list_e e_list -> forall (fc5:fc), P_e (e_fn_call fc5 e_list))
    (H_list_e_nil : P_list_e nil)
    (H_list_e_cons : forall (e0:e), P_e e0 -> forall (e_l:list e), P_list_e e_l -> P_list_e (cons e0 e_l)).

  Fixpoint e_ott_rec (n:e) : P_e n :=
    match n as x return P_e x with
    | (e_t t5) => H_e_t t5
    | (e_var x5) => H_e_var x5
    | (e_neg e5) => H_e_neg e5 (e_ott_rec e5)
    | (e_not e5) => H_e_not e5 (e_ott_rec e5)
    | (e_add e1 e2) => H_e_add e1 (e_ott_rec e1) e2 (e_ott_rec e2)
    | (e_mul e1 e2) => H_e_mul e1 (e_ott_rec e1) e2 (e_ott_rec e2)
    | (e_eq e1 e2) => H_e_eq e1 (e_ott_rec e1) e2 (e_ott_rec e2)
    | (e_lt e1 e2) => H_e_lt e1 (e_ott_rec e1) e2 (e_ott_rec e2)
    | (e_fn_call fn5 e_list) => H_e_fn_call e_list (((fix e_list_ott_rec (e_l:list e) : P_list_e e_l := match e_l as x return P_list_e x with nil => H_list_e_nil | cons e1 xl => H_list_e_cons e1(e_ott_rec e1)xl (e_list_ott_rec xl) end)) e_list) fn5
    end.
End e_rec.

#[export] Instance e_eq_dec : EqDecision e.
Proof.
  unfold EqDecision, Decision.
  induction x using e_ott_rec with
    (P_list_e := fun e_list => forall e_list', {e_list = e_list'} + {e_list <> e_list'});
    intros; try (destruct y; auto).
  - is_eq t0 t5; auto.
    right.
    inv 1.
  - is_eq x5 x0; auto.
    right.
    inv 1.
  - destruct (IHx y); subst; auto.
    right; inv 1.
  - destruct (IHx y); subst; auto.
    right; inv 1.
  - destruct (IHx1 y1), (IHx2 y2); subst; auto.
    + right; inv 1.
    + right; inv 1.
    + right; inv 1.
  - destruct (IHx1 y1), (IHx2 y2); subst; auto.
    + right; inv 1.
    + right; inv 1.
    + right; inv 1.
  - destruct (IHx1 y1), (IHx2 y2); subst; auto.
    + right; inv 1.
    + right; inv 1.
    + right; inv 1.
  - destruct (IHx1 y1), (IHx2 y2); subst; auto.
    + right; inv 1.
    + right; inv 1.
    + right; inv 1.
  - is_eq fc5 fc0; auto.
    + destruct (IHx l); subst; auto.
      right; inv 1.
    + right; inv 1.
  - destruct e_list'; auto.
  - destruct e_list'; auto.
    destruct (IHx e); subst.
    + destruct (IHx0 e_list'); subst; auto.
      right; inv 1.
    + right; inv 1.
Defined.
#[export] Hint Resolve e_eq_dec : ott_coq_equality.

#[export] Instance rhs_eq_dec : EqDecision rhs.
Proof.
  unfold EqDecision, Decision.
  decide equality; auto with ott_coq_equality.
  - apply e_eq_dec.
  - apply list_eq_dec; apply e_eq_dec.
Qed.
#[export] Hint Resolve rhs_eq_dec : ott_coq_equality.

#[export] Instance stmt_eq_dec : EqDecision stmt.
Proof.
  unfold EqDecision, Decision.
  decide equality; auto with ott_coq_equality.
  - apply rhs_eq_dec.
  - apply e_eq_dec.
  - apply e_eq_dec.
  - apply e_eq_dec.
Qed.

#[export] Instance task_eq_dec: EqDecision task.
Proof.
  unfold EqDecision, Decision.
  decide equality; auto with ott_coq_equality.
  - by destruct (decide (s5 = s0)); [left|right].
  - apply stmt_eq_dec.
Defined.

#[export] Instance countable_task: Countable task.
(* is there some automation for this? *)
Admitted.

(* this substitution and subsequent well-typing is not currently used *)
(* I thought I might use it, and then didn't, but may be useful later? *)
Equations e_subst_s : s -> e -> e := {
    e_subst_s _ (e_t t) := e_t t;
    e_subst_s σ (e_var x_) := match σ !! x_ with | Some t => (e_t t) | None => (e_var x_) end ;
    e_subst_s σ (e_neg e0) := e_neg (e_subst_s σ e0);
    e_subst_s σ (e_not e0) := e_not (e_subst_s σ e0);
    e_subst_s σ (e_add e1 e2) := e_add (e_subst_s σ e1) (e_subst_s σ e2);
    e_subst_s σ (e_mul e1 e2) := e_mul (e_subst_s σ e1) (e_subst_s σ e2);
    e_subst_s σ (e_eq e1 e2) := e_eq (e_subst_s σ e1) (e_subst_s σ e2);
    e_subst_s σ (e_lt e1 e2) := e_lt (e_subst_s σ e1) (e_subst_s σ e2);
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

(* just like our vdash, this is the opposite way from other well-typing relations *)
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

(** Operations for typing and some lemmas about them *)
Equations typ_es: G -> list e -> list T -> Prop := {
    typ_es _ [] [] := True ;
    typ_es Γ (e::es) (T::Ts) := typ_e Γ e T /\ typ_es Γ es Ts ;
    typ_es _ _ _ := False
  }.

Definition add_G (Γ:G) (Tx:T*x): G := <[Tx.2:=ctxv_T Tx.1]> Γ.
Definition extend_G (Γ:G) (l:list (T*x)): G := foldr (flip add_G) Γ l.

Lemma subG_add: forall (G0 G1: G) y T_,
  G0 ⊆ G1 ->
  G0 !! y = None ->
  G0 ⊆ (insert y T_ G1).
Proof. intros; by apply insert_subseteq_r. Qed.

Lemma subG_add_2: forall (G0 G1: G) y T_,
  subseteq G0 G1 ->
  G0 !! y = Some T_ ->
  subseteq G0 (insert y T_ G1).
Proof.
  intros.
  replace G0 with (<[y:=T_]> G0) by now apply insert_id.
  now apply insert_mono.
Qed.

Lemma extend_subG: forall Γ1 Γ2 l,
    Γ1 ⊆ Γ2 -> extend_G Γ1 l ⊆ extend_G Γ2 l.
Proof.
  induction l; intros; auto.
  destruct a; simpl.
  apply insert_mono.
  now apply IHl.
Qed.

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

Lemma addG_subG: forall Γ1 Γ2 Tx,
    add_G Γ1 Tx ⊆ Γ2 ->
    Tx.2 ∉ dom Γ1 ->
    Γ1 ⊆ Γ2.
Proof.
  unfold add_G.
  intros.
  epose proof map_subseteq_spec _ _ as (? & _).
  pose proof H as H'.
  eapply H1 with (i:=Tx.2) in H; last eapply lookup_insert.
  eapply subG_add_2 in H; eauto.
  transitivity (<[Tx.2:=ctxv_T Tx.1]> Γ1); auto.
  apply subG_add; auto.
  now apply not_elem_of_dom.
Qed.

Lemma extend_domain: forall Γ x l,
    x ∉ dom Γ ->
    Forall (λ '(_, x0), x0 <> x) l ->
    x ∉ dom (extend_G Γ l).
Proof.
  induction l; intros; auto.
  destruct a; simpl in *.
  inv H0.
  pose proof IHl H H4.
  apply not_elem_of_dom.
  setoid_rewrite lookup_insert_ne; auto.
  now apply not_elem_of_dom.
Qed.

Lemma extend_subG_2: forall Γ1 Γ2 l,
    extend_G Γ1 l ⊆ Γ2 ->
    Forall (λ '(_, x), x ∉ dom Γ2) l ->
    Γ1 ⊆ Γ2.
Proof.
  induction l; intros; auto.
  destruct a; simpl in *.
  inv H0.
  apply addG_subG in H; auto.
  apply extend_domain; auto.
  - eapply lookup_weaken with (i:=x) in H; last apply lookup_insert.
    apply not_elem_of_dom in H3.
    setoid_rewrite H3 in H.
    inv H.
  - apply Forall_forall.
    intros (?&?) ? ?.
    eapply Forall_forall in H4; eauto.
    simpl in *; subst.
    eapply lookup_weaken with (i:=x) in H; last apply lookup_insert.
    apply not_elem_of_dom in H3.
    setoid_rewrite H3 in H.
    inv H.
Qed.

(* Tactics for subject reduction proof(s)*)
Ltac lookup_cases H i j :=
  is_eq i j; [setoid_rewrite lookup_insert in H; inv H
              | setoid_rewrite lookup_insert_ne in H; auto].

