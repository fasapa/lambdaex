(********************************************************************************
* Formalization of ES calculi            				        *
*									        *
* Flavio L. C. de Moura & Daniel L. Ventura & Washington R. Segundo, 2014	*
* Flavio L. C. de Moura & Lucas de Moura Amaral, 2017                           *
********************************************************************************)

Set Implicit Arguments.
Require Import Metatheory LambdaES_Defs LambdaES_Infra Lambda_Ex.
Require Import Rewriting Equation_C.
Require Export Morphisms.

(** Grammar of labelled pre-terms. Labelled terms extend the ordinary
 terms with a new constructor for marked explicit substitutions. *)

Inductive lab_term : pterm -> Prop :=
  | lab_term_var : forall x,
      lab_term (pterm_fvar x)
  | lab_term_app : forall t1 t2,
      lab_term t1 ->
      lab_term t2 ->
      lab_term (pterm_app t1 t2)
  | lab_term_abs : forall L t1,
      (forall x, x \notin L -> lab_term (t1 ^ x)) ->
      lab_term (pterm_abs t1)
  | lab_term_sub : forall L t1 t2,
     (forall x, x \notin L -> lab_term (t1 ^ x)) ->
      lab_term t2 -> lab_term (t1[t2])
  | lab_term_sub' : forall L t1 t2,
     (forall x, x \notin L -> lab_term (t1 ^ x)) ->
      (term t2) -> (SN lex t2) ->
      lab_term (t1 [[ t2 ]]).

(** Every term is also a labelled term because the grammar with labels
extends the term grammar. *)
Lemma term_is_lab_term: forall t, term t -> lab_term t.
Proof.
  intros t Ht. apply term_size_induction.
  - intro x. apply lab_term_var.
  - intros t1 Hbody Hind.
    apply lab_term_abs with (fv t1).
    intros x Hfv. apply Hind.
    + assumption.
    + trivial.
    + apply body_to_term; assumption.
  - intros t1 t2 Ht1 Hlab1 Ht2 Hlab2.
    apply lab_term_app; assumption.
  - intros t1 t3 Ht3 Hlab3 Hb1 Hind.
    apply lab_term_sub with (fv t1).
    + intros x Hfvt1. apply Hind.
      * assumption.
      * trivial.
      * apply body_to_term; assumption.
    + assumption.
  - assumption.
Qed.

Definition lab_body (t : pterm) :=
           exists L, forall x, x \notin L -> lab_term (t ^ x).

Lemma body_is_lab_body : forall t, body t -> lab_body t.
Proof.
 intros. case H; clear H; intros L H; exists L.
 intros. apply term_is_lab_term. apply H; trivial.
Qed.

(** Alternative definition for local closure *)

(** Local closure for labelled terms. *)
Fixpoint lc_at' (k:nat) (t:pterm) : Prop :=
  match t with
  | pterm_bvar i    => i < k
  | pterm_fvar x    => True
  | pterm_app t1 t2 => lc_at' k t1 /\ lc_at' k t2
  | pterm_abs t1    => lc_at' (S k) t1
  | pterm_sub t1 t2 => (lc_at' (S k) t1) /\ lc_at' k t2
  | pterm_sub' t1 t2 => (lc_at k t2) /\ (SN lex t2) /\ (lc_at' (S k) t1)
  end.

Definition term'' t := lc_at' 0 t.

Definition body'' t := lc_at' 1 t.

(** Labelled equations extends eqc. Note that the equations defined form labelled substitutions are not used alone. *)
Inductive lab_eqc  : pterm -> pterm -> Prop :=
| lab_eqc_def : forall t u v, lab_term u -> lab_term v -> lab_eqc (t[u][v]) ((& t)[v][u])
| lab_eqc_rx1 : forall t u v,
                  lab_term u -> term v -> lab_eqc (t[u][[v]]) ((& t)[[v]][u])
| lab_eqc_rx2 : forall t u v,
                  term u -> lab_term v -> lab_eqc (t[[u]][v]) ((& t)[v][[u]])
| lab_eqc_rx3 : forall t u v,
                  term u -> term v -> lab_eqc (t[[u]][[v]]) ((& t)[[v]][[u]]).

(** Correctness of the above definition. *)
(* forall u,0 notin fi(u) <-> lab_term u *)

Lemma eqc_is_lab_eqc: forall t u, eqc t u -> lab_eqc t u.
Proof.
  introv Heqc. induction Heqc.
  apply lab_eqc_def.
  - apply term_is_lab_term; assumption.
  - apply term_is_lab_term; assumption.
Qed.

Lemma eqc_ctx_is_lab_eqc_ctx: forall t u, t =c u -> ES_contextual_closure lab_eqc t u.
Proof.
  introv Heqc. induction Heqc.
  - apply ES_redex. apply eqc_is_lab_eqc; assumption.
  - apply ES_app_left; assumption.
  - apply ES_app_right; assumption.
  - apply ES_abs_in with L; assumption.
  - apply ES_subst_left with L; assumption.
  - apply ES_subst_right; assumption.
Qed.

Lemma eqc_ctx_trans_is_lab_eqc_ctx_trans: forall t u, t =c+ u -> trans_closure (ES_contextual_closure lab_eqc) t u.
Proof.
  introv Heqc. induction Heqc.
  - apply one_step_reduction. apply eqc_ctx_is_lab_eqc_ctx; assumption.
  - apply transitive_reduction with u.
    + apply eqc_ctx_is_lab_eqc_ctx; assumption.
    + assumption.
Qed.

Lemma lab_eqc_sym : forall t u, lab_eqc t u -> lab_eqc u t.
Proof.
  introv Heqc. destruct Heqc.
  - replace ((t [u]) [v]) with (((& (& t)) [u]) [v]).
    apply lab_eqc_def; assumption. rewrite bswap_idemp; trivial.
  - replace ((t [u]) [[v]]) with (((& (& t)) [u]) [[v]]).
    apply lab_eqc_rx2; assumption. rewrite bswap_idemp; trivial.
  - replace ((t [[u]]) [v]) with (((& (& t)) [[u]]) [v]).
    apply lab_eqc_rx1; assumption. rewrite bswap_idemp; trivial.
  - replace ((t [[u]]) [[v]]) with (((& (& t)) [[u]]) [[v]]).
    apply lab_eqc_rx3; assumption. rewrite bswap_idemp; trivial.
Qed.

(** lab_eqC: Reflexive-transitive of the contextual closure of lab_eqc *)
Definition lab_eqC (t: pterm) (u : pterm) :=  star_closure (ESlab_contextual_closure lab_eqc) t u .
Notation "t =~e u" := (lab_eqC t u) (at level 66).

(** =~e is an equivalence relation *)
Lemma lab_eqC_rf : forall t, t =~e t.
Proof.
  intro t. apply reflexive_reduction.
Qed.

(*
Lemma lab_eqc_preserves_SN_lex: forall t t', SN lex t -> lab_eqc t t' -> SN lex t'.
Proof.
  introv HSN Heqc. induction Heqc.
  induction H1. assumption.
  inversion H0.
  inversion H2.
  unfold SN.
  exists x.
  apply SN_intro.
  intros t' H4.
  apply H3.
  assert  (lab_eqc ((t [u]) [[v]]) (((& t) [[v]]) [u])).
  apply lab_eqc_rx1; assumption.
  Admitted.
*)

Lemma lab_ctx_eqc_sym : forall t u, (ESlab_contextual_closure lab_eqc t u) -> ESlab_contextual_closure lab_eqc u t.
Proof.
  introv H. induction H.
  - apply ESlab_redex. apply lab_eqc_sym. assumption.
  - apply ESlab_app_left; trivial.
  - apply ESlab_app_right; trivial.
  - apply ESlab_abs_in with L; trivial.
  - apply ESlab_subst_left with L; trivial.
  - apply ESlab_subst_right; trivial.
  - apply ESlab_lsubst_left with L; assumption.
  - apply ESlab_lsubst_right; trivial.
Qed.

Lemma lab_eqC_sym : forall t u, t =~e u -> u =~e t.
Proof.
  introv H. unfold lab_eqC in *. induction H.
  - apply lab_eqC_rf.
  - induction H.
    + apply star_trans_reduction.
      apply one_step_reduction.
      apply lab_ctx_eqc_sym; assumption.
    +  apply lab_ctx_eqc_sym in H.
       apply star_transitive_closure' with u; assumption.
Qed.

Lemma lab_eqC_trans : forall t u v, t =~e u -> u =~e v -> t =~e v.
Proof.
 introv Htu Huv.
 apply star_closure_composition with u; trivial.
Qed.

Instance lab_eqC_eq : Equivalence lab_eqC.
Proof.
 split; intros_all.
 apply lab_eqC_rf.
 apply lab_eqC_sym; trivial.
 apply lab_eqC_trans with y; trivial.
Qed.

Lemma eqc_ctx_is_lab_eqC: forall t u, t =e u -> t =~e u.
Proof.
  introv Heqc. induction Heqc.
  - apply lab_eqC_rf.
  - destruct H.
    + apply eqc_ctx_is_lab_eqc_ctx in H.
      unfold lab_eqC. apply star_trans_reduction.
      apply one_step_reduction. apply ES_cc_is_ESlab_cc in H; assumption.
    + unfold lab_eqC. apply star_trans_reduction.
      apply transitive_reduction with u.
      * apply eqc_ctx_is_lab_eqc_ctx in H.
        apply ES_cc_is_ESlab_cc in H; assumption.
      * apply eqc_ctx_trans_is_lab_eqc_ctx_trans in H0.
        apply ES_cc_trans_is_ESlab_cc_trans in H0; assumption.
Qed.

  (*
Lemma lab_eqc_trans : forall t u v, lab_eqc t u -> lab_eqc u v -> lab_eqc t v.
Proof.
  intros t u v Htu Huv.
  destruct Huv.
  assumption.
  inversion Htu.
  apply lab_eqc_rx1; assumption.
  rewrite bswap_idemp; trivial.
  apply lab_eqc_rf.
  inversion Htu.
  apply lab_eqc_rx2; assumption.
  rewrite bswap_idemp; trivial.
  apply lab_eqc_rf.
  inversion Htu.
  apply lab_eqc_rx3; assumption.
  rewrite bswap_idemp; trivial.
  apply lab_eqc_rf.
Qed.
*)

(** The extended reduction system. This system is used to propagate
terminating labelled substitutions. *)
Inductive lab_sys_x : pterm -> pterm -> Prop :=
| lab_reg_rule_var : forall t, lab_sys_x (pterm_bvar 0 [[t]]) t
| lab_reg_rule_gc : forall t u, lab_term t -> lab_sys_x (t[[u]]) t
| lab_reg_rule_app : forall t1 t2 u,
  lab_sys_x ((pterm_app t1 t2)[[u]]) (pterm_app (t1[[u]]) (t2[[u]]))
| lab_reg_rule_lamb : forall t u,
  lab_sys_x ((pterm_abs t)[[u]]) (pterm_abs ((& t)[[u]]))
| lab_reg_rule_comp : forall t u v, has_free_index 0 u ->
  lab_sys_x (t[u][[v]]) (((& t)[[v]])[u[[v]]]).
Notation "t ->_lab_x u" := (lab_sys_x t u) (at level 59, left associativity).

(** Internal reductions: lab_x plus lex inside labelled substitutions *)
Inductive lab_x_i: pterm -> pterm -> Prop :=
| xi_from_bx_in_les: forall t u u', u -->lex u' ->
                       lab_x_i (t [[ u ]]) (t [[ u' ]])
| xi_from_x: forall t t', t ->_lab_x t' -> lab_x_i t t'.

(** Reduction on labelled terms: lex plus lab_x *)
Inductive lab_sys_lx: pterm -> pterm -> Prop :=
| lab_B_lx : forall t u, t ->_B u -> lab_sys_lx t u
| lab_sys_x_lx : forall t u, t ->_x u -> lab_sys_lx t u
| lab_sys_x_lab_lx : forall t u, t ->_lab_x u -> lab_sys_lx t u.

Lemma Bx_is_lab_lx: forall t u,  sys_Bx t u -> lab_sys_lx t u.
Proof.
  introv HBx. destruct HBx.
  - apply lab_B_lx; assumption.
  - apply lab_sys_x_lx; assumption.
Qed.

Lemma ESLab_Bx_is_lab_lx: forall t u,  ESlab_contextual_closure sys_Bx t u ->  ESlab_contextual_closure lab_sys_lx t u.
Proof.
  introv HES. induction HES.
  - apply ESlab_redex. apply Bx_is_lab_lx in H; assumption.
  - apply ESlab_app_left; assumption.
  - apply ESlab_app_right; assumption.
  - apply ESlab_abs_in with L; assumption.
  - apply ESlab_subst_left with L; assumption.
  - apply ESlab_subst_right; assumption.
  - apply ESlab_lsubst_left with L; assumption.
  - apply ESlab_lsubst_right; assumption.
Qed.

(* ********************************************************************** *)
(** pterm lists  properties *)

(* Fixpoint cr_lc_at_list (n : nat) (l : list pterm) {struct l} : Prop := *)
(*  match l with *)
(*  | nil => True *)
(*  | t::lu =>  lc_at' n t /\ (cr_lc_at_list (S n) lu)  *)
(*  end. *)

(* Lemma lc_at_mult_sub : forall n t lu, lc_at' n (t//[lu]) <-> (lc_at' (n + length lu) t /\ cr_lc_at_list n lu). *)
(* Proof. *)
(*  intros. generalize n; clear n. induction lu; simpl.  *)
(*  split. intro. assert (Q : n + 0 = n); try omega. rewrite Q. split; trivial. *)
(*  intro. assert (Q : n + 0 = n); try omega. rewrite Q in H. apply H. *)
(*  intro n. replace (n + S (length lu)) with ((S n) + length lu). split. *)
(*  intro H. destruct H. split.  *)
(*  apply IHlu; trivial. split; trivial. apply IHlu; trivial. *)
(*  intro H. destruct H. destruct H0. split; trivial. apply IHlu. split; trivial. *)
(*  omega. *)
(* Qed. *)

(** Reduction modulo lab_eqC *)
Definition red_ctx_mod_lab_eqC (R: pterm -> pterm -> Prop) (t: pterm) (u : pterm) :=
           exists t' u', (t =~e t')/\(ESlab_contextual_closure R t' u')/\(u' =~e u).

(** External reduction context (reductions everywhere except inside labelled substitutions) modulo lab_eqC *)
Definition ext_lab_ee_ctx_red (R: pterm -> pterm -> Prop) (t: pterm) (u : pterm) :=
    exists t' u', (t =~e t')/\(ext_lab_contextual_closure R t' u')/\(u' =~e u).

(** Reduction lab_sys_x modulo lab_eqC *)
Definition lab_ex := red_ctx_mod_lab_eqC lab_sys_x.
Notation "t -->[ex] u" := (lab_ex t u) (at level 59, left associativity).

Definition lab_lex := red_ctx_mod_lab_eqC lab_sys_lx.
Notation "t -->[lex] u" := (lab_lex t u) (at level 59, left associativity).

Definition lab_x_i_eq := red_ctx_mod_lab_eqC lab_x_i.
Notation "t -->[lx_i] u" := (lab_x_i_eq t u) (at level 59, left associativity).

Definition lab_x_e_eq := ext_lab_ee_ctx_red sys_Bx.
Notation "t -->[lx_e] u" := (lab_x_e_eq t u) (at level 59, left associativity).

Definition red_lab_wregular (R : pterm -> pterm -> Prop) :=
  forall t t',  R t t' -> lab_term t -> lab_term t'.

Instance rw_eqC_sub' : Proper (eqC ==> eqC ==> eqC) pterm_sub'.
Proof.
  intros_all. apply star_closure_composition with (y [[x0]]).
  - inversion H; subst.
    + reflexivity.
    + apply star_trans_reduction. inversion H1; subst.
      apply one_step_reduction. pick_fresh z.
      (* apply ES_lsubst_left with (fv x \u fv y \u fv x0 \u fv y0). *)
  (*     introv Hfv. apply eqc_ctx_open; assumption. *)
  (*     assert (x =c+ y). *)
  (*     { apply transitive_reduction with u; assumption. } *)
  (*     pick_fresh z. *)
  (*     apply eqc_trans_sub_left with (fv x \u fv y \u fv x0 \u fv y0 \u fv u). *)
  (*     introv Hfv. apply eqc_trans_open; assumption. *)
  (* - induction H0. *)
  (*   + reflexivity. *)
  (*   + apply star_trans_reduction. induction H0. *)
  (*     * apply one_step_reduction. *)
  (*       apply ES_subst_right; assumption. *)
  (*     * apply transitive_reduction with (y[u]). *)
  (*       ** apply ES_subst_right; assumption. *)
  (*       ** assumption. *)
Admitted.                       (* Fabrício *)
(*
Definition red_lab_regular' (R : pterm -> pterm -> Prop) :=
  forall t t',  R t t' -> (lab_term t <-> lab_term t').
 *)

(** Unlabelled reduction is in the corresponding labelled reduction. *)
Lemma sys_Bx_is_lab_sys_lx: forall t t', t -->lex t' -> t -->[lex] t'.
Proof.
  introv Hlex. induction Hlex.
  destruct H as [ x' [Hee [Hes Hee' ] ] ].
  unfold lab_lex. unfold red_ctx_mod_lab_eqC.
  exists x x'. split.
  - apply eqc_ctx_is_lab_eqC; assumption.
  - split.
    + apply ES_cc_is_ESlab_cc in Hes.
      apply ESLab_Bx_is_lab_lx in Hes; assumption.
    + apply eqc_ctx_is_lab_eqC; assumption.
Qed.

Lemma open_lab_term : forall t x k, lab_term t -> ({k ~> pterm_fvar x}t) = t.
Proof.
 intros t x k H. generalize k; clear k.
 induction H; intros; simpl; trivial.
 rewrite IHlab_term1; rewrite IHlab_term2; trivial.
 case var_fresh with (L := L \u (fv t1) \u fv ({Datatypes.S k ~> pterm_fvar x}t1)). intros z Hz.
 apply notin_union in Hz. destruct Hz. apply notin_union in H1. destruct H1.
 assert (Q : {Datatypes.S k ~> pterm_fvar x}t1 ^ z = t1 ^ z). apply H0; trivial.
 unfold open in Q. rewrite subst_com in Q; try omega; trivial.
 apply open_var_inj in Q; trivial. rewrite Q; trivial.
 rewrite IHlab_term.
 case var_fresh with (L := L \u (fv t1) \u fv ({Datatypes.S k ~> pterm_fvar x}t1)). intros z Hz.
 apply notin_union in Hz. destruct Hz. apply notin_union in H2. destruct H2.
 assert (Q : {Datatypes.S k ~> pterm_fvar x}t1 ^ z = t1 ^ z). apply H0; trivial.
 unfold open in Q. rewrite subst_com in Q; try omega; trivial.
 apply open_var_inj in Q; trivial. rewrite Q; trivial.
 rewrite <- open_rec_term with (t := t2); trivial.
 case var_fresh with (L := L \u (fv t1) \u fv ({Datatypes.S k ~> pterm_fvar x}t1)). intros z Hz.
 apply notin_union in Hz. destruct Hz. apply notin_union in H3. destruct H3.
 assert (Q : {Datatypes.S k ~> pterm_fvar x}t1 ^ z = t1 ^ z).
 apply H0; trivial.
 unfold open in Q. rewrite subst_com in Q; try omega; trivial.
 apply open_var_inj in Q; trivial.
 rewrite Q; trivial.
Qed.

Lemma SN_open: forall t x k, SN lex t -> SN lex ({k ~> (pterm_fvar x)} t).
Proof.
    Admitted.

Lemma SN_open_rename: forall t x y k, SN lex ({k ~> (pterm_fvar x)} t) -> SN lex ({k ~> (pterm_fvar y)} t).
Proof.
    Admitted.

Lemma lc_at'_open_rec_rename: forall t x y m n, lc_at' m (open_rec n (pterm_fvar x) t) -> lc_at' m (open_rec n (pterm_fvar y) t).
Proof.
  induction t. simpl. introv H. case_nat. constructor. assumption.
  simpl. intros; trivial. simpl. introv H. destruct H.
  apply (IHt1 x y) in H. apply (IHt2 x y) in H0.
  split; assumption. simpl.
  introv H. apply IHt with x. assumption. simpl.
  introv H. destruct H. split. apply IHt1 with x; assumption. apply IHt2 with x; assumption.
  introv H. destruct H. split. Admitted.
  (* apply lc_at_open_rec_rename with x; auto.  *)
  (*   destruct H0. split. apply SN_open_rename with (x := x); auto. *)
  (*   apply IHt1 with x; assumption. *)
  (* Qed.   *)

Corollary lab_term_open_rename: forall t x y, lab_term (t^x) -> lab_term (t^y).
Proof.
  introv H. Admitted.
  (*  apply lab_term_eq_term'' in H. apply lab_term_eq_term''. *)
  (*   apply lc_at'_open_rec_rename with x. assumption. *)
  (* Qed. *)

Lemma lab_sys_x_i_e: forall t t0 t1 t', (t =~e t0) -> lab_sys_lx t0 t1 -> (t1 =~e t') -> (t -->[lx_i] t' \/ t -->[lx_e] t').
Proof.
    introv Hee Hred Hee'. induction Hred.
    - right. exists t0 u. split*. split*.
      + apply ext_lab_redex. apply B_lx; assumption.
    - right. exists t0 u. split*. split*.
      apply ext_lab_redex. apply sys_x_lx; assumption.
    - inversion H.
      + subst. right. (* rewrite Hee. *)
      (*   exists (pterm_bvar 0 [u]) u. split*. split. *)
      (* + *)
      (* + *)
      (* + *)
      (* + *)

      (*   * apply ext_lab_redex. apply sys_x_lx. apply reg_rule_var. *)
      (*   * assumption. *)
      (* + right. inversion Hee. *)
        (*   * Admitted. *)
Admitted.       (* Fabrício *)
(* rewrite Hee. *)
(*       + *)
(*       + *)
(*       + *)
(*       + *)
(*     -        *)
(*       constructor 1. constructor 1. auto. auto.  *)
(*     constructor 2. exists t u. split*. split. constructor 1. constructor 2. auto. auto.  *)
(*     constructor 1. exists t u. split*. split. constructor 1. auto. constructor 2. auto. auto. *)
(* Qed. *)

Lemma lab_open_close_var : forall (x : var) (t : pterm), lab_term t -> t = close t x ^ x.
Proof.
  introv W. unfold close, open. generalize 0.
  induction W; intros k; simpls; f_equal*.
  case_var*. simpl. case_nat*.

  let L := gather_vars in match goal with |- _ = ?t =>
    destruct (var_fresh (L \u fv t)) as [y Fr] end.
  apply* (@open_var_inj y).
  apply notin_union in Fr. destruct Fr.
  apply notin_union in H1. destruct H1. auto.
  apply notin_union in Fr. destruct Fr. auto.
  unfolds open. rewrite* close_var_rec_open. VSD.fsetdec.
  (*Focus 3. fail.*)
  let L := gather_vars in match goal with |- _ = ?t =>
    destruct (var_fresh (L \u fv t)) as [y Fr] end.
  apply* (@open_var_inj y).
  auto. auto.
  (*rewrite* close_var_rec_open.  VSD.fsetdec.*)
  unfolds open. rewrite* close_var_rec_open. VSD.fsetdec.
  let L := gather_vars in match goal with |- _ = ?t =>
    destruct (var_fresh (L \u fv t)) as [y Fr] end.
  apply* (@open_var_inj y).
  auto. auto.
  unfolds open. rewrite* close_var_rec_open. VSD.fsetdec.
  let L := gather_vars in match goal with |- _ = ?t =>
    destruct (var_fresh (L \u fv t)) as [y Fr] end.
  apply* (@open_var_inj y).
  auto. auto.
  unfolds open. Admitted.
  (* rewrite <- open_close_var_gen with (x := x) (k := k); auto. *)
(* Qed. *)
(* Check if needed.
Lemma close_var_spec : forall t x, term t ->
  exists u, t = u ^ x /\ body u /\ x \notin (fv u).
Proof.
    intros.
    exists (close t x).
    rewrite <- open_close_var; auto.
    split*. split*.
    apply close_var_body; auto.
    apply close_fresh; auto.
    Qed.

Lemma close_var_lab_body : forall x t,  lab_term t -> lab_body (close t x).
Proof.
  introv W. exists {{x}}. intros y Fr.
  unfold open, close. generalize 0. gen y.
  induction W; intros y Fr k; simpls.
  case_var; simpl. case_nat*.
  auto*.
  constructor 1.
  constructor 1.
  apply* lab_term_app.
  apply IHW1; auto.
  apply IHW2; auto.
  apply_fresh* lab_term_abs.
    unfolds open. rewrite* close_var_rec_open. VSD.fsetdec.
  apply_fresh* lab_term_sub. unfolds open. rewrite* close_var_rec_open.  VSD.fsetdec.
  apply_fresh* lab_term_sub'. unfolds open. rewrite* close_var_rec_open.  VSD.fsetdec.
Admitted.
 *)

(* Lemma ee_presv_ie: forall t t' u u', t =EE u -> u' =EE t' -> ((u -->[lx_i] u' \/ u -->[lx_e] u') -> (t -->[lx_i] t' \/ t -->[lx_e] t')). *)
(* Proof. *)
(*     intros. *)

(*     destruct H1.  destruct H1.  destruct H1.  destruct H1. destruct H2. *)
(*     left. *)
(*     exists x x0. *)
(*     split*. *)
(*     apply star_closure_composition with u; auto. *)
(*     split*. *)
(*     apply star_closure_composition with u'; auto. *)

(*     destruct H1.  destruct H1.  destruct H1.  destruct H2. *)
(*     right. *)
(*     exists x x0. *)
(*     split*. *)
(*     apply star_ctx_eqcc_sym in H. *)
(*     apply star_ctx_eqcc_sym in H. *)
(*     apply star_closure_composition with u; auto. *)
(*     split*. *)
(*     apply star_closure_composition with u'; auto. *)
(* Qed. *)
(* Fabrício *)

Lemma lab_ex_impl_i_e: forall t t', t -->[lex] t' -> (t -->[lx_i] t' \/ t -->[lx_e] t').
Proof.
  introv Hred. destruct Hred as [t0 [t1 [Hee [Hes Hee'] ] ] ]. gen t t'.
  induction Hes. (* Induction on the contextual closure of lab_sys_lx. *)
  - (* lab_sys_lx is applied at the root of the term. *)
    induction H. (* Application of Bx \cup lab_x at the root of the term. *)
    + (* Application of the rule B. *)
      introv Hee Hee'. right. unfold lab_x_e_eq. exists t u. split.
      * assumption.
      * split.
        apply ext_lab_redex. apply B_lx; assumption.
        assumption.
    + (* Application of rules x. *)
      introv Hee Hee'. right. exists t u. split.
      * assumption.
      * split.
         apply ext_lab_redex. apply sys_x_lx; assumption.
         assumption.
    + (* Application of rules lab_x. *)
      introv Hee Hee'. left. exists t u. split.
      * assumption.
      * split.
         apply ESlab_redex. apply xi_from_x; assumption.
         assumption.
  - admit.
  (* - (* lab_sys_lx is applied to the left of an application. *) *)
    (* introv Hee Hee'. *)
    (*       (* apply IHHes. *) *)

    (* apply lab_sys_x_i_e with (t0:=t) (t1:=t'). auto.  *)
  (* apply EE_lab_term with t0; auto*. *)
  (*   - *)
  (*   - *)
  (*   - *)
  (*   - *)
  (*   - *)
  (*   - *)
  (*   - *)
    (* app_left *)
  -(*  apply EE_presv_ie with (u := (pterm_app t u)) (u' := (pterm_app t' u)); auto. *)
(*     assert  (t-->[lx_i]t' \/ t-->[lx_e]t'). *)
(*     apply IHlab_contextual_closure; auto. constructor 1; auto. *)
(*     pose proof (EE_lab_term H0 H3); auto. inversion H4; subst; auto. *)
(*     constructor 1; auto. *)
(*     destruct H4. *)
(*     left. apply EE_ext_clos_app_left. *)
(*     pose proof (EE_lab_term H0 H3); auto.  auto. *)
(*     right. apply EE_ext_clos_app_left. *)
(*     pose proof (EE_lab_term H0 H3); auto.  auto. *)

(*     (* app_right *) *)
(*     apply EE_presv_ie with (u := (pterm_app t u)) (u' := (pterm_app t u')); auto. *)
(*     assert  (u-->[lx_i]u' \/ u-->[lx_e]u'). *)
(*     apply IHlab_contextual_closure; auto. constructor 1; auto. *)
(*     pose proof (EE_lab_term H0 H3); auto. inversion H4; subst; auto. *)
(*     constructor 1; auto. *)
(*     destruct H4. *)
(*     left. apply EE_ext_clos_app_right. *)
(*     pose proof (EE_lab_term H0 H3); auto.  auto. *)
(*     right. apply EE_ext_clos_app_right. *)
(*     pose proof (EE_lab_term H0 H3); auto.  auto. *)

(*     (* abs *) *)
(*     apply EE_presv_ie with (u := pterm_abs t) (u' := pterm_abs t'); auto. *)
(*     pose proof (EE_lab_term H1 H3); auto. inversion H4; subst; auto. *)
(*     pick_fresh z. *)
(*     assert  (t^z-->[lx_i]t'^z \/ t^z-->[lx_e]t'^z). *)
(*     apply H0 with z; auto. constructor 1; auto. *)
(*     constructor 1; auto. *)
(*     apply notin_union in Fr; destruct Fr. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     destruct H5. *)
(*     left. apply EE_ext_clos_abs with L. exact red_rename_lab_xi. *)
(*     exact red_lab_regular'_lab_xi. *)
(*     apply EE_lab_term with t0; auto. *)


(*     intros. *)
(*     pose proof red_rename_lab_xi_eq. apply H14 with z; auto. *)
(*     right. apply EE_ext_clos_abs with L. exact red_rename_sys_Bx. exact red_lab_regular'_sys_Bx. *)
(*     apply EE_lab_term with t0; auto. *)
(*     intros. pose proof red_rename_lab_xe_eq. *)
(*     unfold red_rename in H14. *)
(*     apply H14 with z; auto. *)

(*     (* outer sub *) *)
(*     apply EE_presv_ie with (u := t[u]) (u' := t'[u]); auto. *)
(*     pose proof (EE_lab_term H3 H4); auto. inversion H5; subst; auto. *)
(*     pick_fresh z. *)
(*     assert  (t^z-->[lx_i]t'^z \/ t^z-->[lx_e]t'^z). *)
(*     apply H1 with z; auto. constructor 1; auto. constructor 1; auto. *)
(*     apply notin_union in Fr; destruct Fr. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     destruct H6. *)
(*     left. apply EE_ext_clos_outer_sub with L; auto. *)
(*     exact red_rename_lab_xi. exact red_lab_regular'_lab_xi. *)
(*     intros. *)
(*     pose proof red_rename_lab_xi_eq.  apply H17 with z; auto. *)
(*     right. apply EE_ext_clos_outer_sub with L; auto. *)
(*     exact red_rename_sys_Bx. exact red_lab_regular'_sys_Bx. *)
(*     intros. pose proof red_rename_lab_xe_eq. apply H17 with z; auto. *)

(*     (* inner sub *) *)
(*     apply EE_presv_ie with (u := t[u]) (u' := t[u']); auto. *)
(*     assert (u' =EE u'). constructor 1; auto. *)
(*     assert (u =EE u). constructor 1; auto. *)
(*     apply EE_lab_term in H3. inversion H3; subst. *)
(*     pose proof (IHlab_contextual_closure u' H4 u H9 H5). *)
(*     destruct H6. *)
(*     left. apply EE_ext_clos_inner_sub; auto. *)
(*     right. apply EE_ext_clos_inner_sub; auto. *)
(*     auto. *)

(*     (* outer lsub *) *)
(*     apply EE_presv_ie with (u := t[[u]]) (u' := t'[[u]]); auto. *)
(*     pose proof (EE_lab_term H3 H4); auto. inversion H5; subst; auto. *)
(*     pick_fresh z. *)
(*     assert  (t^z-->[lx_i]t'^z \/ t^z-->[lx_e]t'^z). *)
(*     apply H1 with z; auto. constructor 1; auto. constructor 1; auto. *)
(*     apply notin_union in Fr; destruct Fr. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     destruct H6. *)
(*     left. apply EE_ext_clos_outer_lsub with L. *)
(*     apply EE_lab_term with t0; auto. *)
(*     exact red_rename_lab_xi. exact red_lab_regular'_lab_xi. *)
(*     intros. *)
(*     pose proof red_rename_lab_xi_eq.  apply H18 with z; auto. *)
(*     right. apply EE_ext_clos_outer_lsub with L. *)
(*     apply EE_lab_term with t0; auto. *)
(*     exact red_rename_sys_Bx. exact red_lab_regular'_sys_Bx. *)
(*     intros. pose proof red_rename_lab_xe_eq. apply H18 with z; auto. *)



(*     (* inner lsub *) *)
(*     left. exists (t [[u]]) (t [[u']]). split. auto. *)
(*     split*. *)
(*     apply EE_lab_term with t0 (t [[u]]) in H5. *)
(*     inversion H3; subst. *)
(*     apply lab_sys_lx_term_is_sys_Bx with u u' in H0; auto. *)
(*     (*inversion H5; subst.*) *)
(*     constructor 1.  constructor 1. auto. auto. *)
(*     constructor 1.  constructor 1. auto. *)
(*     apply lab_sys_lx_term_is_sys_Bx with u u' in H0; auto. *)
(*     auto. *)
Admitted.
(* Qed. *)

Lemma lab_ie_impl_ex: forall t t', (t -->[lx_i] t' \/ t -->[lx_e] t') -> t -->[lex] t'.
Proof. (* Admitted. *)
Admitted.
    (* intros. destruct H; destruct H; destruct H; destruct H; destruct H0; generalize dependent t; generalize dependent t'; induction H0; intros. *)

    (* (*[> ------------------  Interna <]*) *)
    (* (*[> Base <]*) *)

    (* exists t s. *)
    (* split*. split*. *)
    (* inversion H; subst. *)
    (* inversion H3; subst. constructor 8; auto. exists L; auto. *)
    (* inversion H4; subst. *)
    (* constructor 1; auto.  constructor 2; subst. auto. *)
    (* constructor 1; auto. constructor 3; auto. *)

    (* (* app_left *) *)
    (* apply EE_presv_lab_lex with (u := (pterm_app t u)) (u' := (pterm_app t' u)); auto. *)
    (* apply EE_clos_app_left. *)
(*     pose proof (EE_lab_term H0 H3); auto.  *)
(*     apply IHext_lab_contextual_closure; auto. constructor 1; auto.  *)
(*     pose proof (EE_lab_term H0 H3); auto. inversion H4; subst; auto.  *)
(*     constructor 1; auto. *)

(*     (* app_right *) *)
(*     apply EE_presv_lab_lex with (u := (pterm_app t u)) (u' := (pterm_app t u')); auto. *)
(*     apply EE_clos_app_right.  pose proof (EE_lab_term H0 H3); auto.  *)
(*     apply IHext_lab_contextual_closure; auto. constructor 1; auto.  *)
(*     pose proof (EE_lab_term H0 H3); auto. inversion H4; subst; auto.  *)
(*     constructor 1; auto. *)

(*     (* abs *) *)
(*     apply EE_presv_lab_lex with (u := pterm_abs t) (u' := pterm_abs t'); auto. *)
(*     pose proof (EE_lab_term H1 H3); auto. inversion H4; subst; auto.  *)
(*     pick_fresh z. *)
(*     assert  (t^z-->[lex]t'^z). *)
(*     apply H0 with z; auto. constructor 1; auto. constructor 1; auto.  *)
(*     apply notin_union in Fr; destruct Fr. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply EE_clos_abs with L. *)
(*     apply EE_lab_term with t0; auto. *)
(*     intros. pose proof red_rename_lab_lex.  *)
(*     intros. apply red_rename_lab_lex with z; auto. *)

(*     (* outer sub *) *)
(*     apply EE_presv_lab_lex with (u := t[u]) (u' := t'[u]); auto. *)
(*     pose proof (EE_lab_term H3 H4); auto. inversion H5; subst; auto.  *)
(*     pick_fresh z. *)
(*     assert  (t^z-->[lex]t'^z). *)
(*     apply H1 with z; auto. constructor 1; auto. constructor 1; auto.  *)
(*     apply notin_union in Fr; destruct Fr. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply EE_clos_outer_sub with L; auto. *)
(*     intros. apply red_rename_lab_lex with z; auto. *)

(*     (* inner sub *) *)
(*     apply EE_presv_lab_lex with (u := t[u]) (u' := t[u']); auto. *)
(*     assert (u' =EE u'). constructor 1; auto. *)
(*     assert (u =EE u). constructor 1; auto. *)
(*     apply EE_lab_term in H3. inversion H3; subst. *)
(*     pose proof (IHext_lab_contextual_closure u' H4 u H9 H5). *)
(*     apply EE_clos_inner_sub; auto. *)
(*     auto. *)


(*     (* outer lsub *) *)
(*     apply EE_presv_lab_lex with (u := t[[u]]) (u' := t'[[u]]); auto. *)
(*     pose proof (EE_lab_term H3 H4); auto. inversion H5; subst; auto.  *)
(*     pick_fresh z. *)
(*     assert  (t^z-->[lex]t'^z). *)
(*     apply H1 with z; auto. constructor 1; auto. constructor 1; auto.  *)
(*     apply notin_union in Fr; destruct Fr. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply EE_clos_outer_lsub with L; auto. *)
(*     intros. apply red_rename_lab_lex with z; auto. *)

(*     (*[> -------------------------------------------------------  Externa <]*) *)
(*     (*[> Base <]*) *)
(*     exists (t) (s).  split*. split*.   *)
(*     inversion H; subst.  *)
(*     constructor 1.  constructor 1; auto.   *)
(*     constructor 1.  constructor 2; auto.   *)

(*     (* app_left *) *)
(*     apply EE_presv_lab_lex with (u := (pterm_app t u)) (u' := (pterm_app t' u)); auto. *)
(*     apply EE_clos_app_left.  *)
(*     pose proof (EE_lab_term H0 H3); auto.  *)
(*     apply IHext_lab_contextual_closure; auto. constructor 1; auto.  *)
(*     pose proof (EE_lab_term H0 H3); auto. inversion H4; subst; auto.  *)
(*     constructor 1; auto. *)

(*     (* app_right *) *)
(*     apply EE_presv_lab_lex with (u := (pterm_app t u)) (u' := (pterm_app t u')); auto. *)
(*     apply EE_clos_app_right.  *)
(*     pose proof (EE_lab_term H0 H3); auto.  *)
(*     apply IHext_lab_contextual_closure; auto. constructor 1; auto.  *)
(*     pose proof (EE_lab_term H0 H3); auto. inversion H4; subst; auto.  *)
(*     constructor 1; auto. *)

(*     (* abs *) *)
(*     apply EE_presv_lab_lex with (u := pterm_abs t) (u' := pterm_abs t'); auto. *)
(*     pose proof (EE_lab_term H1 H3); auto. inversion H4; subst; auto.  *)
(*     pick_fresh z. *)
(*     assert  (t^z-->[lex]t'^z). *)
(*     apply H0 with z; auto. constructor 1; auto. constructor 1; auto.  *)
(*     apply notin_union in Fr; destruct Fr. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply EE_clos_abs with L. *)
(*     apply EE_lab_term with t0; auto. *)
(*     intros. pose proof red_rename_lab_lex.  *)
(*     intros. apply red_rename_lab_lex with z; auto. *)

(*     (* outer sub *) *)
(*     apply EE_presv_lab_lex with (u := t[u]) (u' := t'[u]); auto. *)
(*     pose proof (EE_lab_term H3 H4); auto. inversion H5; subst; auto.  *)
(*     pick_fresh z. *)
(*     assert  (t^z-->[lex]t'^z). *)
(*     apply H1 with z; auto. constructor 1; auto. constructor 1; auto.  *)
(*     apply notin_union in Fr; destruct Fr. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply EE_clos_outer_sub with L; auto. *)
(*     intros. apply red_rename_lab_lex with z; auto. *)

(*     (* inner sub *) *)
(*     apply EE_presv_lab_lex with (u := t[u]) (u' := t[u']); auto. *)
(*     assert (u' =EE u'). constructor 1; auto. *)
(*     assert (u =EE u). constructor 1; auto. *)
(*     apply EE_lab_term in H3. inversion H3; subst. *)
(*     pose proof (IHext_lab_contextual_closure u' H4 u H9 H5). *)
(*     apply EE_clos_inner_sub; auto. *)
(*     auto. *)


(*     (* outer lsub *) *)
(*     apply EE_presv_lab_lex with (u := t[[u]]) (u' := t'[[u]]); auto. *)
(*     pose proof (EE_lab_term H3 H4); auto. inversion H5; subst; auto.  *)
(*     pick_fresh z. *)
(*     assert  (t^z-->[lex]t'^z). *)
(*     apply H1 with z; auto. constructor 1; auto. constructor 1; auto.  *)
(*     apply notin_union in Fr; destruct Fr. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply notin_union in H7; destruct H7. *)
(*     apply EE_clos_outer_lsub with L; auto. *)
(*     intros. apply red_rename_lab_lex with z; auto. *)
(* Qed. *)

Theorem lab_ex_eq_i_e: forall t t', lab_term t -> (t -->[lex] t' <-> (t -->[lx_i] t' \/ t -->[lx_e] t')).
Proof.
    split.
    intros; apply lab_ex_impl_i_e; auto.
    intros; apply lab_ie_impl_ex; auto.
Qed.

(** Parei aqui (Flávio) *)

(* Lemma swap_lab_term : forall x y S t, x \in S -> y \in S -> *)
(*                       lab_term S t -> lab_term S ([(x,y)]t). *)
(* Proof. *)
(*  intros x y S t Hx Hy H. induction H; simpl. *)
(*  case (x0 == x); case (x0 == y); intros; apply lab_term_var. *)
(*  apply lab_term_app; [apply IHlab_term1; trivial | apply IHlab_term2; trivial]. *)
(*  apply lab_term_abs with (L := L \u {{x}} \u {{y}}). intros z Hz.  *)
(*  apply notin_union in Hz. destruct Hz. apply notin_union in H1. destruct H1. *)
(*  apply notin_singleton in H2. apply notin_singleton in H3.  *)
(*  rewrite open_swap; trivial. apply H0; trivial; apply in_union; left; trivial. *)
(*  apply lab_term_sub with (L := L \u {{x}} \u {{y}});  *)
(*  try apply  IHlab_term; trivial; intros z Hz.  *)
(*  apply notin_union in Hz. destruct Hz. apply notin_union in H2. destruct H2. *)
(*  apply notin_singleton in H3. apply notin_singleton in H4.  *)
(*  rewrite open_swap; trivial. apply H0; trivial; apply in_union; left; trivial. *)
(*  apply lab_term_sub' with (L := L \u {{x}} \u {{y}}); trivial. intros z Hz.  *)
(*  apply notin_union in Hz. destruct Hz. apply notin_union in H4. destruct H4. *)
(*  apply notin_singleton in H5. apply notin_singleton in H6.  *)
(*  rewrite open_swap; trivial. apply H0; trivial; apply in_union; left; trivial. *)
(*  apply swap_term; trivial. apply lex_SN_swap; trivial. *)
(*  apply swap_fvar; trivial. *)
(* Qed. *)

(* Lemma swap_lab_term' : forall x y S t, x \in S -> y \in S -> *)
(*                                        x \notin fv t -> y \notin fv t -> *)
(*                                        lab_term S (t ^ x) -> lab_term S (t ^ y). *)
(* Proof. *)
(*  intros. replace (t^y) with ([(x,y)](t^x)). apply swap_lab_term; trivial. *)
(*  unfold open. rewrite open_swap_comm. rewrite swap_var_l. *)
(*  rewrite swap_fresh; trivial. *)
(* Qed. *)

(* Lemma swap_lab_body : forall x y S t, x \in S -> y \in S -> *)
(*                       lab_body S t -> lab_body S ([(x,y)]t). *)
(* Proof. *)
(*  intros. unfold lab_body in *|-*. case H1; clear H1; intros L H1. *)
(*  exists (L \u {{x}} \u {{y}}). intros z Hz. *)
(*  apply notin_union in Hz. destruct Hz. apply notin_union in H2. destruct H2. *)
(*  apply notin_singleton in H3. apply notin_singleton in H4. rewrite open_swap; trivial. *)
(*  apply swap_lab_term. apply in_union. left; trivial. apply in_union. left; trivial. *)
(*  apply H1; trivial. *)
(* Qed. *)

(* Lemma bswap_rec_open : forall x k t, bswap_rec (S k) (t ^ x) = (bswap_rec (S k) t) ^ x.  *)
(* Proof. *)
(*  intros. *)
(*  case var_fresh with (L := fv t \u {{x}}). intros y Fry. *)
(*  case var_fresh with (L := fv t \u {{x}} \u {{y}}). intros z Frz. *)
(*  apply notin_union in Fry. destruct Fry. apply notin_singleton in H0. *)
(*  apply notin_union in Frz. destruct Frz. apply notin_union in H1.  *)
(*  destruct H1. apply notin_singleton in H2. apply notin_singleton in H3. *)
(*  rewrite <- bswap_eq_openclose with (x := y) (y := z). unfold open.  *)
(*  rewrite subst_com with (i := S k) (j := 0); try omega; trivial. *)
(*  rewrite subst_com with (i := S (S k)) (j := 0) ; try omega; trivial.  *)
(*  rewrite <- openclose_com; try omega; trivial. *)
(*  rewrite <- openclose_com; try omega; trivial. *)
(*  rewrite bswap_eq_openclose with (x := y) (y := z); trivial. *)
(*  apply notin_union. split; trivial. apply notin_singleton; trivial.  *)
(*  intro; apply H0; rewrite H4; trivial. intro; apply H3; rewrite H4; trivial. *)
(*  unfold open. rewrite fv_open_; trivial. apply notin_union. *)
(*  split. unfold open. rewrite fv_open_; trivial. apply notin_singleton; trivial. *)
(* Qed. *)


(* (** Open a labeled locally closed term is the identity *) *)
(* Lemma open_rec_lab_term : forall S t u,  lab_term S t -> forall k, t = {k ~> u}t. *)
(* Proof. *)
(*   induction 1; intros; simpl; fequals*; unfolds open ; *)
(*   case var_fresh with (L := L); intros x Fr;  *)
(*   try apply* (@open_rec_term_core t1 0 (pterm_fvar x)); try omega; *)
(*   try apply H0; trivial. apply open_rec_term; trivial. *)
(* Qed.   *)

(* Lemma red_regular_lab_x : forall t t', lab_sys_x t t' -> (exists S, lab_term S t /\ lab_term S t').    *)
(* Proof. *)
(*  intros t t' H. induction H; exists S. *)
(*  inversion H. split; trivial. apply term_to_lab_term; trivial.  *)
(*  split; trivial. *)
(*  split. inversion H0. inversion H. apply lab_term_sub' with (L := L \u x); trivial.  *)
(*  intros z Fr; apply notin_union in Fr;  destruct Fr. *)
(*  unfold open. simpl. apply lab_term_app. apply H7; trivial. apply H3; trivial. *)
(*  inversion H0. inversion H. apply lab_term_app. *)
(*  apply lab_term_sub' with (L := x); trivial. apply lab_term_sub' with (L := L); trivial.  *)
(*  split; trivial.  inversion H. clear H H0 H1 t1 t2.  *)
(*  apply lab_term_abs with (L := L \u (fv t)); intros x Hx. *)
(*  apply notin_union in Hx. destruct Hx. *)
(*  assert (Q : lab_term (S \u {{x}}) (pterm_abs t ^ x)). apply H2; trivial. clear H2 H L. *)
(*  unfold open in *|-*. simpl. rewrite <- open_rec_term with (t := u); trivial. *)
(*  inversion Q. clear Q H t1. *)
(*  apply lab_term_sub' with (L := L \u (fv t)); trivial. intros y Hy. unfold open in *|-*. *)
(*  apply notin_union in Hy. destruct Hy. *)
(*  assert (Q : lab_term (S \u {{x}} \u {{y}}) ({0 ~> pterm_fvar y}({1 ~> pterm_fvar x}t))).  *)
(*    apply H1; trivial. clear H1 H L.  *)
(*  rewrite <- open_bswap; trivial. rewrite subst_com in Q; try omega; trivial. *)
(*  rewrite swap_eq_open; trivial. apply swap_lab_term; trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  apply subset_trans with (F := S); trivial. *)
(*  apply subset_union_weak_l. *)
(*  split; trivial. inversion H. clear H H1 H2 t1 t2. *)
(*  apply lab_term_sub with (L := L \u (fv t)). intros x Hx. *)
(*  apply notin_union in Hx. destruct Hx. *)
(*  assert (Q : lab_term (S \u {{x}}) ((t [u]) ^ x)). apply H3; trivial. clear H3 H L. *)
(*  unfold open in *|-*. simpl in *|-*. rewrite <- open_rec_term with (t := v); trivial. *)
(*  inversion Q. clear Q H H2 t1 t2. *)
(*  apply lab_term_sub' with (L := L \u (fv t)); trivial. intros y Hy. unfold open in *|-*. *)
(*  apply notin_union in Hy. destruct Hy. *)
(*  assert (Q : lab_term (S \u {{x}} \u {{y}}) ({0 ~> pterm_fvar y}({1 ~> pterm_fvar x}t))).  *)
(*    apply H3; trivial. clear H3 H L.  *)
(*  rewrite <- open_bswap; trivial. rewrite subst_com in Q; try omega; trivial. *)
(*  rewrite swap_eq_open; trivial. apply swap_lab_term; trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  apply subset_trans with (F := S); trivial. *)
(*  apply subset_union_weak_l. *)
(*  apply lab_term_sub' with (L := L); trivial; intros x Hx. *)
(*  assert (Q : lab_term (S \u {{x}}) ((t [u]) ^ x)). apply H3; trivial. clear H3. *)
(*  unfold open in Q. simpl in Q.  inversion Q; trivial. *)
(* Qed. *)

(* Lemma red_regular_lab_Bx : forall t t', lab_sys_Bx t t' -> (exists S, lab_term S t /\ lab_term S t'). *)
(* Proof. *)
(*  intros t t' H. induction H. destruct H; exists S. inversion H. *)
(*  split; [apply lab_term_app; trivial | apply lab_term_sub' with (L := x); trivial].  *)
(*  apply lab_term_abs with (L := x); trivial. apply term_to_lab_term; trivial. *)
(*  apply red_regular_lab_x; trivial. *)
(* Qed. *)

(* Lemma red_regular'_lab_eqc : forall t t', lab_eqc t t' -> (exists S, lab_term S t <-> lab_term S t'). *)
(* Proof. *)
(*  intros t t' H. induction H. exists {}. split; intros; trivial. *)
(*  exists S. split; intros. *)
(*  inversion H1. clear H1 H2 H3 t1 t2. *)
(*  apply lab_term_sub with (L := L \u (fv t)); trivial. intros x Hx. unfold open in *|-*. *)
(*  apply notin_union in Hx. destruct Hx. *)
(*  assert (Q : lab_term (S \u {{x}}) ((t [u]) ^ x)). apply H4; trivial. clear H4 H1 L. *)
(*  inversion Q. clear Q H0 H1 H3 t1 t2. simpl. rewrite <- open_rec_term with (t := v); trivial. *)
(*  apply lab_term_sub' with (L := L \u (fv t)); trivial. intros y Hy. unfold open in *|-*. *)
(*  apply notin_union in Hy. destruct Hy. *)
(*  assert (Q : lab_term (S \u {{x}} \u {{y}}) ({0 ~> pterm_fvar y}({1 ~> pterm_fvar x}t))).  *)
(*    apply H4; trivial. clear H4 H0 L.  *)
(*  rewrite <- open_bswap; trivial. rewrite subst_com in Q; try omega; trivial. *)
(*  rewrite swap_eq_open; trivial. apply swap_lab_term; trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  apply subset_trans with (F := S); trivial. *)
(*  apply subset_union_weak_l.  *)
(*  inversion H1. clear H1 H2 H3 t1 t2. *)
(*  apply lab_term_sub' with (L := L \u (fv t)); trivial. intros x Hx. unfold open in *|-*. *)
(*  apply notin_union in Hx. destruct Hx. *)
(*  assert (Q : lab_term (S \u {{x}}) ((& t [[v]]) ^ x)). apply H4; trivial. clear H4 H1 L. *)
(*  unfold open in Q. simpl in Q. rewrite <- open_rec_term with (t := v) in Q; trivial. *)
(*  inversion Q. clear Q H1 H3 H5 H6 t1 t2. simpl. rewrite open_lab_term with (t := u) (S := S); trivial. *)
(*  apply lab_term_sub with (L := L \u (fv t)); trivial. intros y Hy. unfold open in *|-*. *)
(*  apply notin_union in Hy. destruct Hy. *)
(*  assert (Q : lab_term (S \u {{x}} \u {{y}}) ({0 ~> pterm_fvar y}({1 ~> pterm_fvar x}&t))).  *)
(*    apply H4; trivial. clear H4 H1 L.  *)
(*  rewrite <- open_bswap in Q; trivial. rewrite subst_com; try omega; trivial. *)
(*  rewrite swap_eq_open; trivial. apply swap_lab_term; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply lab_term_subset with (S := S); trivial. apply subset_union_weak_l. *)
(*  case var_fresh with (L := L). intros x Hx. *)
(*  assert (Q :  lab_term (S \u {{x}}) (({1 ~> pterm_fvar x}(& t)[[v]]))). *)
(*    unfold open in H4. simpl in H4.  *)
(*    rewrite open_rec_term with (t := v) (k := 0) (u := pterm_fvar x); trivial. *)
(*    apply H4; trivial. *)
(*  clear H4 Hx L. inversion Q; trivial. *)
(*  case var_fresh with (L := L \u fv v). intros x Hx. apply notin_union in Hx. destruct Hx. *)
(*  assert (Q :  lab_term (S \u {{x}}) (({1 ~> pterm_fvar x}(& t)[[v]]))). *)
(*    unfold open in H4. simpl in H4.  *)
(*    rewrite open_rec_term with (t := v) (k := 0) (u := pterm_fvar x); trivial. *)
(*    apply H4; trivial. *)
(*  clear H4 H1 L. inversion Q. clear Q H H0 H1 H3 H4 H5 H6 H7 u L t1 t2.    *)
(*  unfold VarSet.Subset in H8. setoid_rewrite in_union in H8. *)
(*  intros y Hy.  assert (Q : y \in S \/ y \in {{x}}). apply H8; trivial. clear H8. *)
(*  destruct Q; trivial. apply in_singleton in H. rewrite H in Hy. contradiction. *)
(*  exists {}. split; intros. *)
(*  inversion H1. clear H1 H2 H3 t1 t2. *)
(*  apply lab_term_sub' with (L := L \u (fv t)); trivial. intros x Hx. unfold open in *|-*. *)
(*  apply notin_union in Hx. destruct Hx. *)
(*  assert (Q : lab_term ({} \u {{x}}) (t [[u]] ^ x)). apply H4; trivial. clear H4 H1 L. *)
(*  unfold open in Q. simpl in Q. rewrite <- open_rec_term with (t := u) in Q; trivial. *)
(*  inversion Q. clear Q H1 H3 H5 H8 t1 t2. simpl. rewrite <- open_rec_term with (t := v); trivial. *)
(*  apply lab_term_sub' with (L := L \u (fv t)); trivial. intros y Hy. unfold open in *|-*. *)
(*  apply notin_union in Hy. destruct Hy. *)
(*  assert (Q : lab_term ({} \u {{x}} \u {{y}}) ({0 ~> pterm_fvar y}({1 ~> pterm_fvar x}t))).  *)
(*    apply H4; trivial. clear H4 H1 L.  *)
(*  rewrite <- open_bswap; trivial. rewrite subst_com in Q; try omega; trivial. *)
(*  rewrite swap_eq_open; trivial. apply swap_lab_term; trivial. *)
(*  apply in_union. left. left. trivial.  *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  apply subset_trans with (F := {}); trivial. apply subset_union_weak_l. *)
(*  case var_fresh with (L := L). intros x Hx. *)
(*  assert (Q :  lab_term ({} \u {{x}}) (({1 ~> pterm_fvar x}t)[[u]])). *)
(*    unfold open in H4. simpl in H4.  *)
(*    rewrite open_rec_term with (t := u) (k := 0) (u := pterm_fvar x); trivial. *)
(*    apply H4; trivial. *)
(*  clear H4 Hx L. inversion Q; trivial.  *)
(*  case var_fresh with (L := L \u fv u). intros x Hx. apply notin_union in Hx. destruct Hx. *)
(*  assert (Q :  lab_term ({} \u {{x}}) (({1 ~> pterm_fvar x}t)[[u]])). *)
(*    unfold open in H4. simpl in H4.  *)
(*    rewrite open_rec_term with (t := u) (k := 0) (u := pterm_fvar x); trivial. *)
(*    apply H4; trivial. *)
(*  clear H4 H1 L. inversion Q. clear Q H H0 H1 H3 H4 H5 H6 H7 H8 H9 L t1 t2.    *)
(*  unfold VarSet.Subset in H10. setoid_rewrite in_union in H10. *)
(*  intros y Hy.  assert (Q : y \in {} \/ y \in {{x}}). apply H10; trivial. clear H10. *)
(*  destruct Q; trivial. apply in_singleton in H. rewrite H in Hy. contradiction. *)
(*  inversion H1. clear H1 H2 H3 t1 t2. *)
(*  apply lab_term_sub' with (L := L \u (fv t)); trivial. intros x Hx. unfold open in *|-*. *)
(*  apply notin_union in Hx. destruct Hx. *)
(*  assert (Q : lab_term ({} \u {{x}}) ((& t)[[v]] ^ x)). apply H4; trivial. clear H4 H1 L. *)
(*  unfold open in Q. simpl in Q. rewrite <- open_rec_term with (t := v) in Q; trivial. *)
(*  inversion Q. clear Q H1 H3 H5 H8 t1 t2. simpl. rewrite <- open_rec_term with (t := u); trivial. *)
(*  apply lab_term_sub' with (L := L \u (fv t)); trivial. intros y Hy. unfold open in *|-*. *)
(*  apply notin_union in Hy. destruct Hy. *)
(*  assert (Q : lab_term ({} \u {{x}} \u {{y}}) ({0 ~> pterm_fvar y}({1 ~> pterm_fvar x}(& t)))).  *)
(*    apply H4; trivial. clear H4 H1 L.  *)
(*  rewrite <- open_bswap in Q; trivial. rewrite subst_com; try omega; trivial. *)
(*  rewrite swap_eq_open; trivial. apply swap_lab_term; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply subset_trans with (F := {}); trivial. apply subset_union_weak_l. *)
(*  case var_fresh with (L := L). intros x Hx. *)
(*  assert (Q :  lab_term ({} \u {{x}}) (({1 ~> pterm_fvar x}(& t))[[v]])). *)
(*    unfold open in H4. simpl in H4.  *)
(*    rewrite open_rec_term with (t := v) (k := 0) (u := pterm_fvar x); trivial. *)
(*    apply H4; trivial. *)
(*  clear H4 Hx L. inversion Q; trivial.  *)
(*  case var_fresh with (L := L \u fv v). intros x Hx. apply notin_union in Hx. destruct Hx. *)
(*  assert (Q :  lab_term ({} \u {{x}}) (({1 ~> pterm_fvar x}(&t))[[v]])). *)
(*    unfold open in H4. simpl in H4.  *)
(*    rewrite open_rec_term with (t := v) (k := 0) (u := pterm_fvar x); trivial. *)
(*    apply H4; trivial. *)
(*  clear H4 H1 L. inversion Q. clear Q H H0 H1 H3 H4 H5 H6 H7 H8 H9 L t1 t2.    *)
(*  unfold VarSet.Subset in H10. setoid_rewrite in_union in H10. *)
(*  intros y Hy.  assert (Q : y \in {} \/ y \in {{x}}). apply H10; trivial. clear H10. *)
(*  destruct Q; trivial. apply in_singleton in H. rewrite H in Hy. contradiction. *)
(* Qed. *)

(* Lemma red_swap_Lab_sys_x : red_swap lab_sys_x. *)
(* Proof.  *)
(*  intros_all. induction H; simpl. *)
(*  (* lab_reg_rule_var *) *)
(*  apply lab_reg_rule_var with (S := S \u {{x}} \u {{y}}). *)
(*  apply lab_term_sub' with (L := {}); inversion H; clear H H0 H1 t1 t2.  *)
(*  intros z Hz. unfold open. simpl. apply lab_term_var.  *)
(*  apply swap_term; trivial. apply lex_SN_swap; trivial. *)
(*  apply fv_subset_swap; trivial. *)
(*  (* lab_reg_rule_gc *) *)
(*  apply lab_reg_rule_gc with (S := S \u {{x}} \u {{y}}); simpl. *)
(*  apply swap_lab_term.  *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  apply lab_term_subset with (S := S); trivial. *)
(*  apply subset_trans with (F := S \u {{x}}); apply subset_union_weak_l. *)
(*  inversion H0. clear H0 H1 H2 t1 t2. apply lab_term_sub' with (L := L \u {{x}} \u {{y}}). *)
(*  intros z Hz. apply notin_union in Hz. destruct Hz. apply notin_union in H0. destruct H0. *)
(*  apply notin_singleton in H1. apply notin_singleton in H2. rewrite open_swap; trivial. *)
(*  apply swap_lab_term. apply in_union. left. apply in_union. left. apply in_union. right. *)
(*  apply in_singleton; trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply lab_term_subset with (S := S \u {{z}}).  *)
(*  rewrite union_comm with (E := S \u {{x}} \u {{y}}) (F := {{z}}).  *)
(*  rewrite union_assoc. rewrite union_assoc. rewrite union_comm with (E := {{z}}). *)
(*  rewrite <- union_assoc. apply subset_union_weak_l. apply H3; trivial. *)
(*  apply swap_term; trivial. apply lex_SN_swap; trivial. apply swap_fvar. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial.  *)
(*  apply subset_trans with (F := S); trivial. rewrite <- union_assoc. *)
(*  apply subset_union_weak_l. *)
(*  (* lab_reg_rule_app *) *)
(*  apply lab_reg_rule_app with (S := S \u {{x}} \u {{y}}). apply swap_lab_body. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  apply lab_body_subset with (S := S); trivial. rewrite <- union_assoc. apply subset_union_weak_l.   *)
(*  inversion H0. clear H0 H1 H2 t0 t3. *)
(*  apply lab_term_sub' with (L := L \u {{x}} \u {{y}}). intros z Hz. *)
(*  apply notin_union in Hz. destruct Hz. apply notin_union in H0. destruct H0. *)
(*  apply notin_singleton in H1. apply notin_singleton in H2. rewrite open_swap; trivial. *)
(*  apply swap_lab_term. apply in_union. left. apply in_union. left. apply in_union. right. *)
(*  apply in_singleton; trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply lab_term_subset with (S := S \u {{z}}).  *)
(*  rewrite union_comm with (E := S \u {{x}} \u {{y}}) (F := {{z}}).  *)
(*  rewrite union_assoc. rewrite union_assoc. rewrite union_comm with (E := {{z}}). *)
(*  rewrite <- union_assoc. apply subset_union_weak_l. apply H3; trivial. *)
(*  apply swap_term; trivial. apply lex_SN_swap; trivial. apply swap_fvar. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial.  *)
(*  apply subset_trans with (F := S); trivial. rewrite <- union_assoc. *)
(*  apply subset_union_weak_l. *)
(*  (* lab_reg_rule_lamb *) *)
(*  inversion H. clear H H0 H1 t1 t2. unfold bswap. rewrite bswap_swap_comm. *)
(*  apply lab_reg_rule_lamb with (S := S \u {{x}} \u {{y}}). *)
(*  apply lab_term_sub' with (L := L \u {{x}} \u {{y}}). intros z Hz. *)
(*  apply notin_union in Hz. destruct Hz. apply notin_union in H. destruct H. *)
(*  apply notin_singleton in H0. apply notin_singleton in H1. unfold open. simpl. *)
(*  assert (Q :  lab_term (S \u {{z}}) (pterm_abs t ^ z)). apply H2; trivial. *)
(*  clear H2 H L. inversion Q. clear Q H t1.  *)
(*  apply lab_term_abs with (L := L \u {{x}} \u {{y}} \u {{z}}). intros w Hw. *)
(*  apply notin_union in Hw. destruct Hw. apply notin_union in H. destruct H. *)
(*  apply notin_union in H. destruct H.  apply notin_singleton in H6.  *)
(*  apply notin_singleton in H7. apply notin_singleton in H8. unfold open.  *)
(*  rewrite <- swap_var_id with (x := x) (y := y) (z := z); trivial. *)
(*  rewrite <- swap_var_id with (x := x) (y := y) (z := w); trivial. *)
(*  rewrite <- open_swap_comm. rewrite <- open_swap_comm. apply swap_lab_term.   *)
(*  apply in_union. left. apply in_union. left.  *)
(*  apply in_union. left. apply in_union. right. apply in_singleton. trivial. *)
(*  apply in_union. left. apply in_union. left.  *)
(*  apply in_union. right. apply in_singleton. trivial. *)
(*  apply lab_term_subset with (S := S \u {{z}} \u {{w}}).  *)
(*  rewrite <- union_assoc with (E :=  S \u {{x}} \u {{y}}). *)
(*  rewrite union_comm with (F := {{z}} \u {{w}}).   *)
(*  rewrite union_assoc with (E := {{z}} \u {{w}}). *)
(*  rewrite union_assoc with (E := {{z}} \u {{w}}). *)
(*  rewrite union_comm with (F := S). rewrite union_assoc.  *)
(*  rewrite <-  union_assoc with (E :=  S \u {{z}} \u {{w}}). *)
(*  apply subset_union_weak_l. apply H2; trivial.  *)
(*  apply swap_term; trivial. apply lex_SN_swap; trivial. apply swap_fvar.  *)
(*  apply in_union. left. apply in_union. right. apply in_singleton. trivial. *)
(*  apply in_union. right. apply in_singleton. trivial. *)
(*  apply subset_trans with (F := S); trivial. rewrite <- union_assoc. *)
(*  apply subset_union_weak_l.   *)
(*  (* lab_reg_rule_comp *) *)
(*  unfold bswap. rewrite bswap_swap_comm.  *)
(*  apply lab_reg_rule_comp with (S := S \u {{x}} \u {{y}}). *)
(*  inversion H. clear H H1 H2 t1 t2. *)
(*  apply lab_term_sub' with (L := L \u {{x}} \u {{y}}). intros z Hz. *)
(*  apply notin_union in Hz. destruct Hz. apply notin_union in H. destruct H. *)
(*  apply notin_singleton in H1. apply notin_singleton in H2. unfold open. simpl. *)
(*  assert (Q :  lab_term (S \u {{z}}) ((t[u]) ^ z)). apply H3; trivial. *)
(*  clear H3 H L. inversion Q. clear Q H H3 t1 t2.  *)
(*  apply lab_term_sub with (L := L \u {{x}} \u {{y}} \u {{z}}). intros w Hw. *)
(*  apply notin_union in Hw. destruct Hw. apply notin_union in H. destruct H. *)
(*  apply notin_union in H. destruct H.  apply notin_singleton in H3.  *)
(*  apply notin_singleton in H9. apply notin_singleton in H10. unfold open.  *)
(*  rewrite <- swap_var_id with (x := x) (y := y) (z := z); trivial. *)
(*  rewrite <- swap_var_id with (x := x) (y := y) (z := w); trivial. *)
(*  rewrite <- open_swap_comm. rewrite <- open_swap_comm. apply swap_lab_term.   *)
(*  apply in_union. left. apply in_union. left.  *)
(*  apply in_union. left. apply in_union. right. apply in_singleton. trivial. *)
(*  apply in_union. left. apply in_union. left.  *)
(*  apply in_union. right. apply in_singleton. trivial. *)
(*  apply lab_term_subset with (S := S \u {{z}} \u {{w}}).  *)
(*  rewrite <- union_assoc with (E :=  S \u {{x}} \u {{y}}). *)
(*  rewrite union_comm with (F := {{z}} \u {{w}}).   *)
(*  rewrite union_assoc with (E := {{z}} \u {{w}}). *)
(*  rewrite union_assoc with (E := {{z}} \u {{w}}). *)
(*  rewrite union_comm with (F := S). rewrite union_assoc.  *)
(*  rewrite <-  union_assoc with (E :=  S \u {{z}} \u {{w}}). *)
(*  apply subset_union_weak_l. apply H7; trivial.  *)
(*  rewrite <- swap_var_id with (x := x) (y := y) (z := z); trivial. *)
(*  rewrite <- open_swap_comm. apply swap_lab_term. *)
(*  apply in_union. left. apply in_union. left. apply in_union. right. apply in_singleton. trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton. trivial. *)
(*  apply lab_term_subset with (S := S \u {{z}}); trivial. *)
(*  rewrite union_comm with (E := S \u {{x}} \u {{y}}) (F := {{z}}).  *)
(*  rewrite union_assoc. rewrite union_assoc. rewrite union_comm with (E := {{z}}). *)
(*  rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  apply swap_term; trivial. apply lex_SN_swap; trivial. apply swap_fvar.  *)
(*  apply in_union. left. apply in_union. right. apply in_singleton. trivial. *)
(*  apply in_union. right. apply in_singleton. trivial. *)
(*  apply subset_trans with (F := S); trivial. rewrite <- union_assoc. apply subset_union_weak_l.   *)
(*  intro H'. apply H0. apply swap_term with (x := x) (y := y) in H'. *)
(*  rewrite swap_inv in H'; trivial. *)
(* Qed. *)

(* Lemma red_swap_Lab_sys_Bx : red_swap lab_sys_Bx. *)
(* Proof.  *)
(*  intros_all. destruct H; simpl. destruct H; simpl. *)
(*  apply lab_B_lx. apply lab_reg_rule_b with (S := S \u {{x}} \u {{y}}). apply swap_lab_body.  *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial.  *)
(*  apply lab_body_subset with (S := S); trivial. rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  apply swap_term; trivial. apply swap_fvar.  *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial.  *)
(*  apply in_union. right. apply in_singleton; trivial.  *)
(*  apply subset_trans with (F := S); trivial. rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  apply lex_SN_swap; trivial. *)
(*  apply lab_sys_x_lx. apply red_swap_Lab_sys_x; trivial. *)
(* Qed. *)

(* Lemma red_swap_lab_eqc : red_swap lab_eqc. *)
(* Proof.  *)
(*  intros_all. destruct H; unfold bswap; simpl; try rewrite bswap_swap_comm. *)
(*  apply lab_eqc_rf. apply lab_eqc_rx1 with (S := S \u {{x}} \u {{y}}). apply swap_lab_term.  *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  apply lab_term_subset with (S := S); trivial. rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  apply swap_term; trivial. *)
(*  apply lab_eqc_rx2; apply swap_term; trivial. *)
(* Qed. *)

(* Lemma ctx_lab_regular : forall R, red_lab_regular R -> red_lab_regular (lab_contextual_closure R). *)
(* Proof. *)
(*  intros_all. induction H0. apply H; trivial. *)
(*  case IHlab_contextual_closure; clear IHlab_contextual_closure; intros S' H2. *)
(*  exists (S \u S'). destruct H2. split; apply lab_term_app; trivial.  *)
(*  apply lab_term_subset with (S := S'); trivial. apply subset_union_weak_r. *)
(*  apply lab_term_subset with (S := S); trivial. apply subset_union_weak_l. *)
(*  apply lab_term_subset with (S := S'); trivial. apply subset_union_weak_r. *)
(*  apply lab_term_subset with (S := S); trivial. apply subset_union_weak_l. *)
(*  case IHlab_contextual_closure; clear IHlab_contextual_closure; intros S' H2. *)
(*  exists (S \u S'). destruct H2. split; apply lab_term_app; trivial.  *)
(*  apply lab_term_subset with (S := S); trivial. apply subset_union_weak_l. *)
(*  apply lab_term_subset with (S := S'); trivial. apply subset_union_weak_r. *)
(*  apply lab_term_subset with (S := S); trivial. apply subset_union_weak_l. *)
(*  apply lab_term_subset with (S := S'); trivial. apply subset_union_weak_r. *)
(*  pick_fresh x. apply notin_union in Fr. destruct Fr. apply notin_union in H2. destruct H2. *)
(*  assert (Q:  exist S, lab_term S (t ^ x) /\ lab_term S (t' ^ x)). apply H1; trivial. *)
(*  clear H0 H1 H2 L. case Q; clear Q. intros S Q. destruct Q. exists (S \u {{x}}). *)
(*  split; apply lab_term_abs with (L := (fv t) \u (fv t')); intros y Hy; *)
(*  apply notin_union in Hy; destruct Hy.  *)
(*  apply lab_term_subset with (S' := S \u {{x}} \u {{y}}) in H0.  *)
(*  apply swap_lab_term' with (x := x); trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  apply lab_term_subset with (S' := S \u {{x}} \u {{y}}) in H1.  *)
(*  apply swap_lab_term' with (x := x); trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr. *)
(*  apply notin_union in Fr. destruct Fr. apply notin_union in H3. destruct H3. *)
(*  assert (Q:  exist S, lab_term S (t ^ x) /\ lab_term S (t' ^ x)). apply H2; trivial. *)
(*  clear H1 H2 H3 L. case Q; clear Q. intros S' Q. destruct Q. exists (S' \u S \u {{x}}). *)
(*  split; apply lab_term_sub with (L := (fv t) \u (fv t')); try intros y Hy; *)
(*  try apply notin_union in Hy; try destruct Hy.  *)
(*  apply lab_term_subset with (S' := S' \u S \u {{x}} \u {{y}}) in H1.  *)
(*  apply swap_lab_term' with (x := x); trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  rewrite <- union_assoc.  rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  apply lab_term_subset with (S := S); trivial. rewrite union_comm with (E := S'). *)
(*  rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  apply lab_term_subset with (S' := S' \u S \u {{x}} \u {{y}}) in H2.  *)
(*  apply swap_lab_term' with (x := x); trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  rewrite <- union_assoc.  rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  apply lab_term_subset with (S := S); trivial. rewrite union_comm with (E := S'). *)
(*  rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  case IHlab_contextual_closure; clear IHlab_contextual_closure; intros S' H2. *)
(*  exists (S \u S'). destruct H2. inversion H0. clear H0. *)
(*  split; apply lab_term_sub with (L := x); try intros y Hy. *)
(*  apply lab_term_subset with (S := S \u {{y}}). rewrite <- union_assoc. *)
(*  rewrite union_comm with (E := S'). rewrite union_assoc. apply subset_union_weak_l. *)
(*  apply H4; trivial. apply lab_term_subset with (S := S'); trivial. apply subset_union_weak_r. *)
(*  apply lab_term_subset with (S := S \u {{y}}). rewrite <- union_assoc. *)
(*  rewrite union_comm with (E := S'). rewrite union_assoc. apply subset_union_weak_l. *)
(*  apply H4; trivial. apply lab_term_subset with (S := S'); trivial. apply subset_union_weak_r. *)
(*  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr. *)
(*  apply notin_union in Fr. destruct Fr. apply notin_union in H4. destruct H4. *)
(*  assert (Q:  exist S, lab_term S (t ^ x) /\ lab_term S (t' ^ x)). apply H3; trivial. *)
(*  clear H2 H3 H4 L. case Q; clear Q. intros S Q. destruct Q. exists (S \u (fv u) \u {{x}}). *)
(*  split; apply lab_term_sub' with (L := (fv t) \u (fv t')); trivial.  *)
(*  intros y Hy. apply notin_union in Hy. destruct Hy. *)
(*  apply lab_term_subset with (S' := S \u (fv u) \u {{x}} \u {{y}}) in H2.  *)
(*  apply swap_lab_term' with (x := x); trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  rewrite <- union_assoc.  rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  rewrite union_comm with (E := S). rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  intros y Hy. apply notin_union in Hy. destruct Hy. *)
(*  apply lab_term_subset with (S' := S \u (fv u) \u {{x}} \u {{y}}) in H3.  *)
(*  apply swap_lab_term' with (x := x); trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  rewrite <- union_assoc.  rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  rewrite union_comm with (E := S). rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  exists S. inversion H0. clear H0. generalize H3. intro H5. apply ctx_sys_Bex_regular in H5.  *)
(*  destruct H5. split; apply lab_term_sub' with (L := x); trivial. *)
(*  case H1; clear H1; intros n H1. inversion H1; clear H1. case (H6 u'); trivial; clear H6. *)
(*  intros k H1. exists k. apply H1. intros a H6. unfold VarSet.Subset in H2. apply H2. *)
(*  apply basic_prop1 with (t' := u'); trivial. right; trivial. *)
(* Qed. *)

(*
Lemma ctx_lab_regular' : forall R, red_lab_regular' R ->
                                    red_lab_regular' (lab_contextual_closure R).
Proof.
 intros R H. unfold red_lab_regular' in *|-*. intros t t' H'. induction H'.
 case (H t s); trivial.  intros S H1. exists S; trivial.
 case IHH'; clear IHH'; intros S' H1. exists (S \u S'). split.
 intro H2. inversion H2. clear H2 H3 H4 t1 t2. apply lab_term_app.

case IHH'2; clear IHH'2; intros S' H2.
 exists (S \u S'). split; intro H3. inversion H3. clear H0 H3 H4 t1 t2.
 apply lab_term_app. destruct H1. apply lab_term_subset with (S := S).

 apply lab_term_subset with (S := S).
 apply lab_term_subset with (S := S'); try apply H2; trivial].

 skip. skip. skip. skip.
 Admitted.
 *)
