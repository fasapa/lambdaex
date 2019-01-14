Require Import Arith Metatheory.
Require Import LibTactics LambdaES_Defs Rewriting.
Require Import LambdaES_FV LambdaES_Infra LambdaES_Tac.
Require Export Morphisms.

Instance iff_eq : Equivalence iff.
Proof.
 split; intros_all.
 split; trivial.
 split; apply H.
 split. intro H1. apply H0. apply H; trivial.
 intro H1. apply H. apply H0; trivial.
Qed.

Inductive eqc : pterm -> pterm -> Prop :=
| eqc_def: forall t u v, term u -> term v -> eqc (t[u][v]) ((& t)[v][u]).

Lemma eqc_sym : forall t u, eqc t u -> eqc u t.
Proof.
 intros_all. inversion H; subst; clear H.
 replace t0 with (&(& t0)) at 2.
 apply eqc_def; assumption. apply bswap_idemp.
Qed.

Lemma eqc_bvar_term  : forall x t, eqc (pterm_bvar x) t -> pterm_bvar x = t.
Proof.
  introv H; inversion H.
Qed.

Lemma eqc_fvar_term  : forall x t, eqc (pterm_fvar x) t -> pterm_fvar x = t.
Proof.
  introv H; inversion H.
Qed.

Lemma eqc_app_term :  forall t u v, eqc (pterm_app u v) t -> pterm_app u v = t.
Proof.
   intros t u v H; inversion H.
Qed.

Lemma eqc_abs_term :  forall t t', eqc (pterm_abs t) t' -> pterm_abs t = t' .
Proof.
   intros t t' H; inversion H.
Qed.

Lemma eqc_wregular: red_wregular eqc.
Proof.
  unfold red_wregular. intros_all.
  apply term_to_term' in H.
  apply term'_to_term. unfold term' in *.
  induction H0. simpl in *. destruct H as [ [ Ht Hu ] Hv]. split.
  - split.
    + apply lc_at_bswap; [auto | assumption].
    + apply lc_at_weaken_ind with 0; [assumption | auto].
  - apply term_to_term' in H0. assumption.
Qed.

Lemma red_out_eqc : red_out eqc.
Proof.
  introv Hterm Heqc. destruct Heqc; simpl.
  assert (Heqc:([x ~> u](& t)) = & ([x ~> u]t)).
  { rewrite (subst_bswap_rec 0). reflexivity.
  rewrite <- term_eq_term'; trivial. }
  rewrite Heqc. apply eqc_def.
  apply subst_term; assumption.
  apply subst_term; assumption.
Qed.

Lemma red_rename_eqc : red_rename eqc.
Proof.
 intros_all.
 rewrite* (@subst_intro x t).
 rewrite* (@subst_intro x t').
 apply red_out_eqc; trivial.
Qed.

Lemma eqc_open: forall n t u v, eqc t u -> eqc ({n ~> v}t) ({n ~> v}u).
Proof.
  intros_all. gen n v. induction H.
  intros n v'. unfold bswap. simpl. rewrite <- bswap_open_rec.
  change (bswap_rec 0 ({(S (S n)) ~> v'}t)) with (& ({(S(S n)) ~> v'}t)).
  assert (Hun: {n ~> v'}u = u).
  { rewrite <- open_rec_term; [ reflexivity | assumption ]. }
  assert (HuSn: {(S n) ~> v'}u = u).
  { rewrite <- open_rec_term; [ reflexivity | assumption ]. }
  assert (Hvn: {n ~> v'}v = v).
  { rewrite <- open_rec_term; [ reflexivity | assumption ]. }
  assert (HvSn: {(S n) ~> v'}v = v).
  { rewrite <- open_rec_term; [ reflexivity | assumption ]. }
  rewrite Hun. rewrite HuSn. rewrite Hvn. rewrite HvSn.
  apply eqc_def. auto. auto. auto. auto.
Qed.

(** =c: the contextual closure of eqc. *)
Definition eqc_ctx (t u: pterm) := ES_contextual_closure eqc t u.
Notation "t =c u" := (eqc_ctx t u) (at level 66).

(** Compatibility of =c with the structure of terms. *)
Lemma ESctx_eqc_bvar  : forall x t, (pterm_bvar x) =c t -> pterm_bvar x = t.
Proof.
  intros x t H. inversion H. inversion H0; trivial.
Qed.

Lemma ESctx_eqc_fvar : forall x t, (pterm_fvar x) =c t -> pterm_fvar x = t.
Proof.
  intros x t H. inversion H. inversion H0; trivial.
Qed.

Lemma ESctx_eqc_sym : forall t u, t =c u -> u =c t.
Proof.
  introv H. induction H. apply ES_redex. apply eqc_sym; assumption.
  apply ES_app_left; assumption.
  apply ES_app_right; assumption.
  apply ES_abs_in with L; assumption.
  apply ES_subst_left with L; assumption.
  apply ES_subst_right; assumption.
Qed.

Lemma ESctx_eqc_app_term :  forall t u v, (pterm_app u v) =c t -> exists u' v', t = pterm_app u' v'.
Proof.
  introv H. inversion H; subst.
  - inversion H0.
  - exists t' v. reflexivity.
  - exists u u'. reflexivity.
Qed.

Lemma ESctx_eqc_app_one_step :  forall t u v, (pterm_app u v) =c t -> exists u' v', t = pterm_app u' v' /\ (u =c u' \/ v =c v').
Proof.
  introv H. remember (pterm_app u v) as t'. induction H.
  - rewrite Heqt' in H. inversion H.
  - inversion Heqt'; subst.
    exists t' v. split.
    + reflexivity.
    + left. assumption.
  - inversion Heqt'; subst.
    exists u u'. split.
    + reflexivity.
    + right. assumption.
  - inversion Heqt'.
  - inversion Heqt'.
  - inversion Heqt'.
Qed.

Lemma eqc_ctx_open: forall x t u, t =c u -> t^x =c u^x.
Proof.
  intros x t u Heqc. unfold open. generalize 0. gen x. induction Heqc.
  - intros x n. apply ES_redex. apply eqc_open; assumption.
  - intros x n. simpl. apply ES_app_left. apply IHHeqc.
  - intros x n. simpl. apply ES_app_right. apply IHHeqc.
  - intros x n. simpl. apply ES_abs_in with L.
    introv HL. unfold open. rewrite subst_com.
    change ({0 ~> pterm_fvar x0}t) with (t ^ x0).
    rewrite subst_com. apply H0; assumption. auto.
    apply term_var. apply term_var. auto. apply term_var. apply term_var.
  - intros x n. simpl. apply ES_subst_left with L.
    introv HL. unfold open. rewrite subst_com.
    change ({0 ~> pterm_fvar x0}t) with (t ^ x0).
    rewrite subst_com. apply H0; assumption. auto.
    apply term_var. apply term_var. auto. apply term_var. apply term_var.
  - intros x n. simpl. apply ES_subst_right. apply IHHeqc.
Qed.

(*
Lemma ESctx_eqc_app_term :  forall t1 t2 t, (pterm_app t1 t2) =c t -> exists u1 u2, t = (pterm_app u1 u2) /\ ((t1 =c u1 /\ t2 = u2) \/ (t1 = u1 /\ t2 =c u2)).
Proof.
  introv H. remember (pterm_app t1 t2) as t'. induction H.
  - subst. inversion H.
  - exists t' u. split.
    Admitted.
*)

(** Verificar necessidade deste lema.
Lemma ESctx_eqc_abs_term :  forall t t', (pterm_abs t) =c t' ->
                       exists u, exists L, pterm_abs u = t' /\ (forall x, x \notin L -> (u ^ x) =c (t ^ x)).
Proof.
   intros t t' H. inversion H; subst.
   exists t {}. split; trivial.
   apply eqc_abs_term in H0; assumption.
   intros x H'. apply ES_redex. reflexivity.
   exists t'0 L. split; trivial. intros.
   apply ESctx_eqc_sym. apply H1; assumption.
Qed. *)

(** Verificar necessidade deste lema.
Lemma ESctx_eqc_sub_term :  forall t u v, (t[u]) =c v -> exists t', exists u', v = (t'[u']).
Proof.
  intros t u v H. inversion H; subst.
  apply eqc_sub_term in H0.
  destruct H0. subst.
  exists t u; trivial.
  destruct H0. destruct H0. destruct H0. destruct H1. destruct H2. subst.
  exists (& x [u]) x0; trivial.
  exists t' u; trivial.
  exists t u'; reflexivity.
Qed. *)

Lemma red_out_eqc_ctx : red_out eqc_ctx.
Proof.
  intros_all. unfold eqc_ctx in *. induction H0.
  - apply ES_redex. apply red_out_eqc. assumption. assumption.
  - simpl. apply ES_app_left. assumption.
  - simpl. apply ES_app_right. assumption.
  - simpl. apply ES_abs_in with ({{x}} \u L).
    intros. apply notin_union in H2. destruct H2 as [H2 H2'].
    apply notin_singleton in H2. repeat rewrite subst_open_var.
    apply H1. assumption. assumption. assumption. assumption. assumption.
  - simpl. apply ES_subst_left with ({{x}} \u L).
    intros. apply notin_union in H2. destruct H2 as [H2 H2'].
    apply notin_singleton in H2. repeat rewrite subst_open_var.
    apply H1; assumption. assumption. assumption.
    assumption. assumption.
  - simpl. apply ES_subst_right. apply IHES_contextual_closure.
Qed.

Lemma red_rename_eqc_ctx: red_rename eqc_ctx.
Proof.
  intros_all.
  rewrite* (@subst_intro x t).
  rewrite* (@subst_intro x t').
  apply red_out_eqc_ctx.
  apply term_var. assumption.
Qed.

Lemma red_wregular_eqc_ctx: red_wregular eqc_ctx.
Proof.
  unfold eqc_ctx. apply red_wregular_ctx.
  apply eqc_wregular.
Qed.

(** =c+: the transitive closure of =c. *)
Definition eqc_trans (t u: pterm) := trans_closure eqc_ctx t u.
Notation "t =c+ u" := (eqc_trans t u) (at level 66).

Lemma red_wregular_eqc_trans: red_wregular eqc_trans.
Proof.
  intros_all. induction H0.
  - generalize H0. apply red_wregular_eqc_ctx. assumption.
  - apply IHtrans_closure. generalize H0.
    apply red_wregular_ctx. apply eqc_wregular. assumption.
Qed.

Lemma ESctx_eqc_trans_app_term :  forall t u v, (pterm_app u v) =c+ t -> exists u' v', t = pterm_app u' v'.
Proof.
  introv H. remember (pterm_app u v) as t'.
  generalize dependent u. generalize dependent v. induction H.
  - introv H'. subst. inversion H.
    + inversion H0.
    + subst. exists t' v. reflexivity.
    + subst. exists u0 u'. reflexivity.
  - introv H'. subst. apply ESctx_eqc_app_term in H.
    destruct H. destruct H. apply IHtrans_closure in H. assumption.
Qed.

Lemma red_out_eqc_trans : red_out eqc_trans.
Proof.
  intros_all. unfold eqc_trans in *. induction H0.
  - apply one_step_reduction. apply red_out_eqc_ctx; assumption.
  - apply (red_out_eqc_ctx x u) in H0.
    apply transitive_reduction with ([x ~> u]u0); assumption. assumption.
Qed.
(*
Lemma red_rename_eqc_trans: red_rename eqc_trans.
Proof.
  intros_all.
  rewrite* (@subst_intro x t).
  rewrite* (@subst_intro x t').
  apply red_out_eqc_trans.
  apply term_var. assumption.
Qed.
*)
Lemma eqc_trans_bvar : forall x t, (pterm_bvar x) =c+ t -> pterm_bvar x = t.
Proof.
  introv H. remember (pterm_bvar x) as t0. induction H.
  - subst. apply ESctx_eqc_bvar; assumption.
  - subst. apply eq_trans with u.
    apply ESctx_eqc_bvar in H. assumption.
    apply IHtrans_closure. apply ESctx_eqc_bvar in H.
    symmetry. assumption.
Qed.

Lemma eqc_trans_fvar : forall x t, (pterm_fvar x) =c+ t -> pterm_fvar x = t.
Proof.
  introv H. remember (pterm_fvar x) as t0. induction H.
  - subst. apply ESctx_eqc_fvar; assumption.
  - subst. apply eq_trans with u. subst. apply ESctx_eqc_fvar; assumption.
    apply IHtrans_closure. apply ESctx_eqc_fvar in H.
    symmetry. assumption.
Qed.

Lemma close_rec_fresh: forall x t k, x \notin fv(close_rec k x t).
Proof.
  intros x t. gen x. induction t.
  intros x k. simpl. apply notin_empty.
  intros x k. simpl. case_var*. simpl.
  apply notin_empty. simpl. apply notin_singleton. auto.
  intros x k. simpl. apply notin_union. split.
  apply IHt1; assumption. apply IHt2; assumption.
  intros x k. simpls. apply IHt.
  intros x k. simpls. apply notin_union; split.
  apply IHt1. apply IHt2. intros x k. simpls.
  apply notin_union; split. apply IHt1. apply IHt2.
Qed.

Corollary close_fresh: forall x t, x \notin fv(close t x).
Proof.
  intros x t. unfold close.
  apply close_rec_fresh.
Qed.

Lemma close_spec: forall t x, term t -> exists u, t = u^x /\ body u /\ x \notin fv u.
Proof.
  intros t x H. exists (close t x).
  splits 3. apply open_close_var; assumption.
  apply close_var_body. assumption.
  apply close_fresh.
Qed.

Lemma eqc_trans_open: forall x t u, t =c+ u -> t^x =c+ u^x.
Proof.
  Admitted.

Lemma eqc_trans_abs : forall t t' L, (forall x, x \notin L -> t^x =c+ t'^x) -> pterm_abs t =c+ pterm_abs t'.
Proof. Admitted.
(*   introv H. pick_fresh x. forwards~ Red: (H x). *)
(*   asserts Ht1: (term (pterm_abs t')). *)
(*   apply_fresh term_abs as y. *)
(*   asserts Ht': (term (t' ^ x)). *)
(*   apply red_regular_trans in Red. apply Red. *)
(*   apply red_regular_eqc_ctx. *)
(*   apply term_open_rename with x; assumption. *)
(*   gen_eq u:(t^x). gen_eq v:(t'^x). clear H. *)
(*   gen t t' x L. induction Red; intros; subst.  *)
(*   apply one_step_reduction. apply ES_abs_in with L. *)
(*   intros_all. apply* (red_rename_eqc_ctx x); simpls*.   *)
(*   destruct~ (@close_spec u x). *)
(*   apply red_regular_eqc_trans in Red2. apply Red2. *)
(*   destruct H. subst.  *)
(*   apply transitive_reduction with (pterm_abs x0). *)
(*   apply IHRed1 with x L. *)
(*   apply term_abs with (fv x0). intros_all. *)
(*   destruct H0. apply body_to_term; assumption. *)
(*   apply notin_union. split. apply notin_union in Fr. *)
(*   destruct Fr. assumption. destruct H0. assumption. *)
(*   reflexivity. reflexivity. *)
(*   apply IHRed2 with x L. assumption.  *)
(*   apply notin_union. split. *)
(*   apply notin_union. split. *)
(*   apply  notin_union in Fr. destruct Fr. *)
(*   apply  notin_union in H. destruct H. *)
(*   assumption. destruct H0. assumption. *)
(*   apply  notin_union in Fr. destruct Fr. *)
(*   assumption. reflexivity. reflexivity. *)
(* Qed. *)

Lemma eqc_trans_sub_left : forall t t' u L, (forall x, x \notin L -> t^x =c+ t'^x) -> (t[u]) =c+ (t'[u]).
Proof. Admitted.

Lemma eqc_trans_sub_right : forall t u u', u =c+ u' -> (t[u]) =c+ (t[u']).
Proof. Admitted.

Lemma eqc_trans_sym: forall t u, t =c+ u -> u =c+ t.
Proof.
  intros_all. induction H.
  - apply one_step_reduction.
    apply ESctx_eqc_sym; assumption.
  - inversion IHtrans_closure; subst.
    + apply ESctx_eqc_sym in H.
      apply transitive_reduction with u.
      assumption. apply one_step_reduction.
      assumption.
    + apply ESctx_eqc_sym in H.
      apply ESctx_eqc_sym in H1.
      assert (u =c+ t).
      { apply one_step_reduction; assumption. }
      apply transitive_closure_composition with u; assumption.
Qed.

Lemma eqc_trans_subst_out: forall t t' x u, t =c+ t' -> ([x ~> u]t) =c+ ([x ~> u]t').
Proof.
  Admitted.

(** =e: the reflexive-transitive closure of =c. *)
Definition eqC (t : pterm) (u : pterm) := star_closure eqc_ctx t u.
Notation "t =e u" := (eqC t u) (at level 66).

(** =e is an equivalence relation *)

Lemma eqC_rf : forall t, t =e t.
Proof.
 intros_all. apply reflexive_reduction.
Qed.

Lemma eqC_sym : forall t u, t =e u -> u =e t.
Proof.
 intros t u H. induction H.
 - apply eqC_rf.
 - apply star_trans_reduction. apply eqc_trans_sym; assumption.
Qed.

Lemma eqC_trans : forall t u v, t =e u -> u =e v -> t =e v.
Proof.
 introv H H'. apply star_closure_composition with u; trivial.
Qed.

Instance eqC_eq : Equivalence eqC.
Proof.
 split; intros_all. apply eqC_rf.
 apply eqC_sym; trivial.
 apply eqC_trans with y; trivial.
Qed.

Lemma red_out_eqC : red_out eqC.
Proof.
  intros_all. gen x u. induction H0.
  - introv Hterm. apply reflexive_reduction.
  - introv Hterm. apply star_trans_reduction.
    apply red_out_eqc_trans; assumption.
Qed.

Lemma red_rename_eqC : red_rename eqC.
Proof.
 intros_all.
 rewrite* (@subst_intro x t).
 rewrite* (@subst_intro x t').
 apply red_out_eqC; trivial.
Qed.

Lemma red_wregular_eqC : red_wregular eqC.
Proof.
  intros_all. induction H0.
  - assumption.
  - gen H0. apply red_wregular_eqc_trans. assumption.
Qed.

(** Verificar necessidade deste lema.
Lemma eqc_sub_term :  forall t u t0, (t[u]) =e t0 ->
(t[u] = t0 \/ exists t', exists v, term u /\ term v /\ t'[v] = t /\ (& t')[u][v] = t0) .
Proof.
   intros t u t0 H. inversion H; subst.
   left; trivial. right. exists t1 u0.
   split; trivial. split; trivial. split; trivial.
Qed. *)

Lemma eqC_bvar_term  : forall x t, pterm_bvar x =e t -> pterm_bvar x = t.
Proof.
  introv H. remember (pterm_bvar x) as t0.
  inversion H; subst. reflexivity.
  apply eqc_trans_bvar; assumption.
Qed.

Lemma eqC_fvar_term  : forall x t, pterm_fvar x =e t -> pterm_fvar x = t.
Proof.
  introv H. remember (pterm_fvar x) as t0.
  inversion H; subst. reflexivity.
  apply eqc_trans_fvar; trivial.
Qed.

Lemma eqC_app_term :  forall t u v, pterm_app u v =e t -> exists u' v', t = pterm_app u' v'.
Proof.
  introv H. remember (pterm_app u v) as t'.
  generalize dependent u. generalize dependent v. induction H.
  - introv H. subst. exists u v. reflexivity.
  - introv H'. subst. inversion H; clear H.
    + subst. apply ESctx_eqc_app_term in H0. assumption.
    + subst. apply ESctx_eqc_app_term in H0. destruct H0.
      destruct H. subst. apply ESctx_eqc_trans_app_term in H1. assumption.
Qed.

Lemma eqC_subst_in: forall t x u u', u =e u' -> ([x ~> u]t) =e ([x ~> u']t).
Proof.
  Admitted.

(*
Lemma eqC_abs_term :  forall t t', pterm_abs t =e t' ->
                      exists u, exists L, pterm_abs u = t' /\ (forall x, x \notin L -> (u ^ x) =e (t ^ x)).
Proof.
   intros t t' H. gen_eq t0 : (pterm_abs t). generalize t; clear t. induction H.
   intros t' H'. rewrite H' in H. apply pctx_eqc_abs_term in H.
   case H; clear H; intros u0 H. case H; clear H; intros L H. destruct H.
   exists u0 L. split; trivial. intros x Fr. apply one_step_reduction. apply H0; trivial.
   intros t0 H'. rewrite H' in H. apply pctx_eqc_abs_term in H.
   case H; clear H; intros u0 H. case H; clear H; intros L H. destruct H.
   case (IHtrans_closure u0). rewrite H; trivial. intros t1 H2.
   case H2; clear H2; intros L' H2. destruct H2. exists t1 (L \u L').
   split; trivial. intros x Fr. apply notin_union in Fr. destruct Fr.
   rewrite (H3 x); trivial. apply one_step_reduction. apply H1; trivial.
Qed.

Lemma eqC_sub_term :  forall t u t0, t[u] =e t0 -> exists t', exists u', t'[u'] = t0 .
Proof.
   intros t u v H. gen_eq t0 : (t [u]). generalize t u; clear t u. induction H.
   intros t' u' H'. rewrite H' in H. apply pctx_eqc_sub_term in H; trivial.
   intros t' u' H'. rewrite H' in H. apply pctx_eqc_sub_term in H.
   case H; clear H; intros t0 H. case H; clear H; intros u0 H.
   case (IHtrans_closure t0 u0). rewrite H; trivial. intros t1 H1.
   case H1; clear H1; intros u1 H1. exists t1 u1; trivial.
Qed.

Lemma eqC_redex : forall t u v, ~(has_free_index 0 u) -> ~(has_free_index 0 v) -> (t[u][v]) =e ((& t)[v][u]) .
Proof.
  intros t u v Tt Tu Tv. apply star_trans_reduction.
  apply one_step_reduction. apply ES_redex. apply eqc_def; assumption.
Qed.
*)
Definition red_ctx_mod_eqC (R: pterm -> pterm -> Prop) (t: pterm) (u : pterm) :=
           exists t', exists u', (t =e t') /\ (ES_contextual_closure R t' u') /\ (u' =e u).

(* ********************************************************************** *)
(** =e Properties *)
(** Not true because indexes inside substitution need to be updated.

Lemma lc_at_eqc : forall n t u, eqc t u -> (lc_at n t <-> lc_at n u).
Proof.
  introv Heqc. gen n. induction Heqc.
  intro n. split.
  - intro Hlc_at. inversion Hlc_at; subst; clear Hlc_at.
    inversion H1; subst; clear H1. simpl. split.
    + split.
      * apply lc_at_bswap. apply lt_n_S. apply lt_0_Sn. assumption.
      * apply lc_at_weaken_ind with n.
        ** assumption.
        ** apply le_n_Sn.
    + apply lc_at_weaken_ind with
    + Hlc_at. inversion Hlc_at; subst; clear Hlc_at.
 inversion H1; subst; clear H1. simpl.

    inversion H1; subst; clear H1. split.
    + split.
      * apply lc_at_bswap. apply lt_n_S. apply lt_0_Sn. assumption.
      * apply lc_at_weaken_ind with n. assumption. auto.
    +

    intro H2. destruct H2. destruct H2. split. split.
 unfold bswap. apply lc_at_bswap. apply lt_n_S.
 apply lt_0_Sn. assumption. apply term_to_term' in H1.
 apply lc_at_weaken; assumption. apply term_to_term' in H0.
 apply lc_at_weaken; assumption. intro H2. destruct H2.
 destruct H2. split. split. apply lc_at_weaken_ind with 2.
 assumption. apply lt_n_S. apply lt_0_Sn.
 apply lc_at_weaken_ind with n. assumption.
 apply le_n_Sn. apply term_to_term' in H1.
 apply lc_at_weaken_ind with 0. assumption. apply le_0_n.
Qed.
*)
Lemma lc_at_ES_ctx_eqc : forall n t u, t =c u  -> (lc_at n t <-> lc_at n u).
Proof.
  (* introv H. generalize dependent n. induction H. *)
  (* - intro n. apply lc_at_eqc. assumption. *)
  (* - split; intro H'. *)
  (*   + inversion H'; subst. constructor. *)
  (*     rewrite <- IHES_contextual_closure. assumption. assumption. *)
  (*   + inversion H'; subst. constructor. rewrite IHES_contextual_closure. *)
  (*     assumption. assumption. *)
  (* - split; intro H'. *)
  (*   + inversion H'; subst. constructor. assumption. *)
  (*     rewrite <- IHES_contextual_closure. assumption. *)
  (*   + inversion H'; subst. constructor. assumption. *)
  (*     rewrite IHES_contextual_closure. assumption. *)
  (* - simpl. simpl in *. case var_fresh with L. intros. *)
  (*   rewrite <- lc_at_open' with (u := pterm_fvar x) (k := 0). *)
  (*   symmetry. rewrite <- lc_at_open' with (u := pterm_fvar x) (k := 0). *)
  (*   unfold open in *. symmetry. auto. intuition eauto.  intuition eauto. *)
  (*   apply neq_0_lt.  trivial. intuition eauto. apply neq_0_lt. trivial. *)
  (* - split; simpl; intros H'. case var_fresh with L. intros x H1. *)
  (*   split; destruct H'; auto. *)
  (*   rewrite <- lc_at_open' with (u := pterm_fvar x) (k := 0); auto. *)
  (*   unfold open in *. rewrite <- H0. *)
  (*   rewrite lc_at_open' with (u := pterm_fvar x) (k := 0). assumption. *)
  (*   auto. apply lt_0_Sn. assumption. apply lt_0_Sn. split. *)
  (*   case var_fresh with (L := L). introv H1. *)
  (*   destruct H'. rewrite <- lc_at_open' with (u := pterm_fvar x) (k := 0). *)
  (*   unfold open in *. rewrite H0. rewrite lc_at_open' with (u := pterm_fvar x) (k := 0). *)
  (*   assumption. auto. apply lt_0_Sn. assumption. auto. *)
  (*   apply lt_0_Sn. destruct H'. assumption. *)
  (* - intro n. split. *)
  (*   + intro H'. simpl. inversion H'. split. *)
  (*     * assumption. *)
  (*     * apply IHES_contextual_closure. assumption. *)
  (*   + intro H'. simpl. inversion H'. split. *)
  (*     * assumption. *)
  (*     * apply IHES_contextual_closure; assumption. *)
  (* Qed. *)
  Admitted.

Lemma lc_at_ES_ctx_eqc_trans : forall n t t', t =c+ t' -> (lc_at n t <-> lc_at n t').
Proof.
  introv H. generalize dependent n. induction H.
  - intro n. apply lc_at_ES_ctx_eqc. assumption.
  - intro n. apply (lc_at_ES_ctx_eqc n) in H.
    apply iff_trans with (lc_at n u). assumption.
    apply IHtrans_closure.
Qed.

Lemma lc_at_eqC : forall n t t', t =e t' -> (lc_at n t <-> lc_at n t').
Proof.
  introv H. generalize dependent n. induction H.
  - reflexivity.
  - intro n. apply lc_at_ES_ctx_eqc_trans. assumption.
Qed.

(*
Lemma eqc_fv : forall x t t', eqc t t' -> ((x \in fv t) <-> (x \in fv t')).
Proof.
  introv H. induction H. simpl. unfold bswap.
  rewrite fv_bswap_rec. rewrite <- union_assoc.
    assert (H'': fv v \u fv u [=] fv u \u fv v).
    { apply union_comm. } rewrite <- H''.
    rewrite union_assoc. split.
  - intro H'; assumption.
  - intro H'; assumption.
Qed.

Lemma ESctx_eqc_fv : forall x t t',  t =c t' -> ((x \in fv t) <-> (x \in fv t')).
Proof.
  introv H. generalize dependent x. induction H.
  - intro x. apply eqc_fv; assumption.
  - simpl. split.
    + intro H'. apply in_union in H'. destruct H'. apply in_union.
      left. rewrite <- IHES_contextual_closure; assumption.
      apply in_union. right; assumption.
    + intro H'. apply in_union in H'. destruct H'. apply in_union.
      left. rewrite IHES_contextual_closure; assumption.
      apply in_union; right; assumption.
  - simpl. split.
    + intro H'. apply in_union in H'. destruct H'.
      apply in_union. left; assumption.
      apply in_union. right. rewrite <- IHES_contextual_closure; assumption.
    + intro H'. apply in_union in H'. destruct H'.
      apply in_union. left; assumption.
      apply in_union. right. rewrite IHES_contextual_closure; assumption.
  - simpl. pick_fresh y. apply notin_union in Fr. destruct Fr. apply notin_union in H1.
    destruct H1. split.
    + intro H4.
      assert (Q: (x \in fv (t ^ y) <-> x \in fv t)).
      { apply fv_open_. intuition eauto. subst. apply H3; assumption. }
      assert (S: (x \in fv (t' ^ y) <-> x \in fv t')).
      { apply fv_open_. intuition eauto. subst. apply H3; assumption. }
      apply S. apply H0. assumption. apply Q; assumption.
    + intro H4.
      assert (Q: (x \in fv (t ^ y) <-> x \in fv t)).
      { apply fv_open_. intuition eauto. subst. apply H2; assumption. }
      assert (S: (x \in fv (t' ^ y) <-> x \in fv t')).
      { apply fv_open_. intuition eauto. subst. apply H2; assumption. }
      apply Q. apply H0. assumption. apply S; assumption.
  - simpl. pick_fresh y. apply notin_union in Fr. destruct Fr. apply notin_union in H1.
    destruct H1. apply notin_union in H1. destruct H1. split.
    + intro H5. apply in_union in H5. destruct H5. apply in_union. left.
      assert (Q: (x \in fv (t ^ y) <-> x \in fv t)).
      { apply fv_open_. intuition eauto. subst. apply H4; assumption. }
      assert (S: (x \in fv (t' ^ y) <-> x \in fv t')).
      { apply fv_open_. intuition eauto. subst. apply H4; assumption. }
      apply S. apply H0. assumption. apply Q. assumption.
      apply in_union. right; assumption.
    + intro H5. apply in_union in H5. destruct H5. apply in_union. left.
      assert (Q: (x \in fv (t ^ y) <-> x \in fv t)).
      { apply fv_open_. intuition eauto. subst. apply H3; assumption. }
      assert (S: (x \in fv (t' ^ y) <-> x \in fv t')).
      { apply fv_open_. intuition eauto. subst. apply H3; assumption. }
      apply Q. apply H0. assumption. apply S. assumption.
      apply in_union. right; assumption.
  - split.
    + introv H'. simpl in *. apply in_union in H'. destruct H'.
      apply in_union; left; assumption.
      apply in_union. right. apply IHES_contextual_closure. assumption.
    + intro H'. simpl in *. apply in_union in H'. destruct H'.
       apply in_union; left; assumption.
       apply in_union. right. apply IHES_contextual_closure; assumption.
Qed.

Lemma eqC_fv_trans : forall x t t', t =c+ t' -> ((x \in fv t) <-> (x \in fv t')).
Proof.
  introv H. generalize dependent x. induction H.
  - intro x. apply ESctx_eqc_fv; assumption.
  - intro x. apply (ESctx_eqc_fv x) in H.
    apply iff_trans with (x \in fv u). assumption.
    apply IHtrans_closure.
Qed.

Lemma eqC_fv : forall x t t', t =e t' -> ((x \in fv t) <-> (x \in fv t')).
Proof.
 introv H. generalize dependent x. induction H.
 - reflexivity.
 - intro x. apply eqC_fv_trans; assumption.
Qed.

*)
Lemma red_regular'_eqc : red_regular' eqc.
Proof.
  (* unfold red_regular'. intros t0 t1 H'. rewrite term_eq_term'. *)
  (* rewrite term_eq_term'. unfold term'. apply lc_at_eqc; trivial. *)
  (* Qed. *)
Admitted.
(*
Lemma pctx_eqc_fv : forall x t u, (p_contextual_closure eqc) t u  -> (x \in (fv t) <-> x \in (fv u)).
Proof.
 intros x t u H. induction H. induction H.
 split; trivial. simpl. split.
 intro H1. apply in_union in H1. case H1; clear H1.
 intro H1. apply in_union in H1. case H1; clear H1.
 intro H1. apply in_union. left. apply in_union.
 left. unfold bswap. rewrite fv_bswap_rec; trivial.
 intro H1. apply in_union. right. trivial.
 intro H1. apply in_union. left. apply in_union. right. trivial.
 intro H1. apply in_union in H1. case H1; clear H1.
 intro H1. apply in_union in H1. case H1; clear H1.
 intro H1. apply in_union. left. apply in_union.
 left. unfold bswap in H1. rewrite fv_bswap_rec in H1; trivial.
 intro H1. apply in_union. right. trivial.
 intro H1. apply in_union. left. apply in_union. right; trivial.
 simpl. split.
 intro H1. apply in_union in H1. case H1; clear H1.
 intro H1. apply in_union. left. apply IHp_contextual_closure1; trivial.
 intro H1. apply in_union. right; trivial. apply IHp_contextual_closure2; trivial.
 intro H1. apply in_union in H1. case H1; clear H1.
 intro H1. apply in_union. left. apply IHp_contextual_closure1; trivial.
 intro H1. apply in_union. right; trivial. apply IHp_contextual_closure2; trivial.
 simpl. pick_fresh z. apply notin_union in Fr. case Fr; clear Fr.
 intros H1 H2. apply notin_union in H1. case H1; clear H1. intros H1 H3.
 apply notin_union in H1. case H1; clear H1. intros H1 H4.
 apply notin_singleton in H4.
 assert (Q: (x \in fv (t ^ z) <-> x \in fv t)).
   unfold open. apply fv_open_. intro.
   apply H4. apply symmetry; trivial.
 assert (Q': (x \in fv (t' ^ z) <-> x \in fv t')).
   unfold open. apply fv_open_. intro.
   apply H4. apply symmetry; trivial.
 split.
 intro H5. apply Q'. apply H0; trivial. apply Q; trivial.
 intro H5. apply Q.  apply H0; trivial. apply Q'; trivial.
 simpl. pick_fresh z. apply notin_union in Fr. case Fr; clear Fr.
 intros H2 H3. apply notin_union in H2. case H2; clear H2.
 intros H2 H4. apply notin_union in H2. case H2; clear H2.
 intros H2 H5. apply notin_union in H2. case H2; clear H2.
 intros H2 H6. apply notin_union in H2. case H2; clear H2.
 intros H2 H7. apply notin_singleton in H7.
 assert (Q: (x \in fv (t ^ z) <-> x \in fv t)).
   unfold open. apply fv_open_. intro.
   apply H7. apply symmetry; trivial.
 assert (Q': (x \in fv (t' ^ z) <-> x \in fv t')).
   unfold open. apply fv_open_. intro.
   apply H7. apply symmetry; trivial.
 split.
 intro H8. apply in_union in H8. apply in_union. case H8; clear H8; intro H8.
 left. apply Q'. apply H0; trivial. apply Q; trivial.
 right. apply IHp_contextual_closure; trivial.
 intro H8. apply in_union in H8. apply in_union. case H8; clear H8; intro H8.
 left. apply Q. apply H0; trivial. apply Q'; trivial.
 right. apply IHp_contextual_closure; trivial.
Qed.
 *)

Lemma red_wregular_mod_eqC : forall R, red_wregular R ->
                        red_wregular (red_ctx_mod_eqC R).
Proof.
 introv H. unfold red_wregular. introv H0 H1.
 unfold red_ctx_mod_eqC in H1. destruct H1 as [x [x' [He [Hes He'] ] ] ].
 generalize He'; clear He'.
 apply red_wregular_eqC.
 generalize Hes; clear Hes.
 apply red_wregular_ctx. assumption.
 generalize He; clear He.
 apply red_wregular_eqC; assumption.
Qed.

(*
Lemma red_out_pctx_eqc : red_out (p_contextual_closure eqc).
Proof.
 apply red_out_pctx. apply red_out_eqc.
Qed.


Lemma red_out_pctx_eqc' : forall x t u u', term t -> term u ->
                        p_contextual_closure eqc u u' ->
                        p_contextual_closure eqc ([x ~> u]t) ([x ~> u']t).
Proof.
 intros x t u u' Tt Tu H.
 apply term_size_induction with (t := t); trivial; simpl.
 intro z. case (z == x). intro; trivial. intro. apply p_redex. apply eqc_rf.
 intros t1 B Ht1. apply p_abs_in with (L := {{x}} \u (fv t1)).
 intros z Fr. apply notin_union in Fr. destruct Fr.
 apply notin_singleton in H0.
 rewrite subst_open_var; trivial.
 rewrite subst_open_var; trivial.
 apply Ht1; trivial. apply body_to_term; trivial.
 apply (lc_at_pctx_eqc 0) in H.
 rewrite <- term_eq_term' in H.
 rewrite <- term_eq_term' in H. apply H; trivial.
 intros t1 t2 Tt1 Ht1 Tt2 Ht2. apply p_app; trivial.
 intros t1 t2 Tt2 Ht2 B Ht1.
 apply p_subst with (L := {{x}} \u (fv t1)); trivial.
 intros z Fr. apply notin_union in Fr. destruct Fr.
 apply notin_singleton in H0.
 rewrite subst_open_var; trivial.
 rewrite subst_open_var; trivial.
 apply Ht1; trivial. apply body_to_term; trivial.
 apply (lc_at_pctx_eqc 0) in H.
 rewrite <- term_eq_term' in H.
 rewrite <- term_eq_term' in H.
 apply H; trivial.
Qed.

Lemma pctx_eqc_open : forall n t t' u, term u -> p_contextual_closure eqc t t' ->
                     p_contextual_closure eqc ({n ~> u}t) ({n ~> u}t').
Proof.
  intros n t t' u Tu H. generalize n; clear n.
  induction H. destruct H. intro n. apply p_redex. apply eqc_rf.
  intro n. unfold open. simpl.
  replace ({S (S n) ~> u}(& t)) with (& ({S (S n) ~> u}t)).
  replace ({S n ~> u}v) with v. replace ({n ~> u}v) with v.
  replace ({S n ~> u}u0) with u0. replace ({n ~> u}u0) with u0.
  apply p_redex. apply eqc_rx; trivial.
  rewrite open_lc_at; trivial.
  apply lc_at_weaken_ind with (k1 := 0); try omega.
  rewrite <- term_eq_term'; trivial.
  rewrite open_lc_at; trivial.
  apply lc_at_weaken_ind with (k1 := 0); try omega.
  rewrite <- term_eq_term'; trivial.
  rewrite open_lc_at; trivial.
  apply lc_at_weaken_ind with (k1 := 0); try omega.
  rewrite <- term_eq_term'; trivial.
  rewrite open_lc_at; trivial.
  apply lc_at_weaken_ind with (k1 := 0); try omega.
  rewrite <- term_eq_term'; trivial.
  unfold bswap. rewrite <- bswap_open_rec; try omega; trivial.
  apply lc_at_weaken_ind with (k1 := 0); try omega.
  rewrite <- term_eq_term'; trivial.
  simpl; intro n. apply p_app; trivial.
  simpl; intro n. apply p_abs_in with (L := (fv u) \u L).
  intros x H2. apply notin_union in H2. case H2; clear H2.
  intros H2 H3. unfold open in *|-*.
  replace ({0 ~> pterm_fvar x}({S n ~> u}t))
  with ({S n ~> u}({0 ~> pterm_fvar x}t)).
  replace ({0 ~> pterm_fvar x}({S n ~> u}t'))
  with ({S n ~> u}({0 ~> pterm_fvar x}t')).
  apply H0; trivial.
  rewrite subst_com; trivial. omega.
  rewrite subst_com; trivial. omega.
  simpl; intro n. apply p_subst with (L := (fv u) \u L); trivial.
  intros x H2. apply notin_union in H2. case H2; clear H2.
  intros H2 H3. unfold open in *|-*.
  replace ({0 ~> pterm_fvar x}({S n ~> u}t))
  with ({S n ~> u}({0 ~> pterm_fvar x}t)).
  replace ({0 ~> pterm_fvar x}({S n ~> u}t'))
  with ({S n ~> u}({0 ~> pterm_fvar x}t')).
  apply H0; trivial.
  rewrite subst_com; trivial. omega.
  rewrite subst_com; trivial. omega.
Qed.


Lemma eqC_open : forall n t t' u, term u -> t =e t'-> (open_rec n u t) =e (open_rec n u t').
Proof.
 intros n t t' u Tu H. induction H.
 apply one_step_reduction. apply pctx_eqc_open; trivial.
 apply transitive_reduction with (u := ({n ~> u}u0)); trivial.
 apply pctx_eqc_open; trivial.
Qed.

Lemma eqC_open_var : forall (x:var) t1 t2 u, x \notin (fv t1) ->
	x \notin (fv t2) -> term u -> (t1 ^ x =e t2 ^ x) -> ((t1^^u) =e (t2^^u)).
Proof.
  intros x t1 t2 u H1 H2 T H3.
  assert (Q : subst x u (t1 ^ x) =e subst x u (t2 ^ x)).
   apply red_out_eqC; trivial.
  rewrite subst_intro with (x := x); trivial.
  rewrite subst_intro with (x := x) (t := t2); trivial.
Qed.

(** Compatibility of =c+ with the structure of terms. *)
Lemma eqc_trans_app_l: forall t t' u, term u -> t =c+ t' -> (pterm_app t u) =c+ (pterm_app t' u).
Proof.
  intros t t' u H1 H2.
  induction H2.
  apply one_step_reduction.
  apply ES_app_left; assumption.

  apply transitive_reduction with (pterm_app u0 u).
  apply ES_app_left; assumption. assumption.
Qed.

Lemma eqc_trans_app_r: forall t u u', term t -> u =c+ u' -> (pterm_app t u) =c+ (pterm_app t u').
Proof.
  intros t u u' H1 H2.
  induction H2.
  apply one_step_reduction.
  apply ES_app_right; assumption.
  apply transitive_reduction with (pterm_app t u).
  apply ES_app_right; assumption. assumption.
Qed.

Lemma eqc_trans_abs: forall t t' L, (forall x, x \notin L -> t^x =c+ t'^x) -> (pterm_abs t) =c+ (pterm_abs t').
Proof.
  introv H.
  pick_fresh z. apply notin_union in Fr. destruct Fr.
  apply notin_union in H0. destruct H0.
  assert (t^z =c+ t'^z). apply H; assumption.
  inversion H3; subst.
  apply one_step_reduction. apply ES_abs_in with L.
  introv H'. apply red_rename

Lemma eqc_trans_sub: forall t t' u L, term u -> (forall x, x \notin L -> t^x =c+ t'^x) -> (pterm_sub t u) =c+ (pterm_sub t' u).
  Proof. Admitted.


(** Compatibility of =e with the structure of pre-terms. *)

Lemma eqC_app_l: forall t t' u, term u -> t =e t' -> (pterm_app t u) =e (pterm_app t' u).
Proof.
  introv H1 H2.
  induction H2. reflexivity.
  apply star_trans_reduction. apply eqc_trans_app_l; assumption.
Qed.

Lemma eqC_app_r: forall t u u', term t -> u =e u' -> (pterm_app t u) =e (pterm_app t u').
Proof.
  introv H1 H2.
  induction H2. reflexivity.
  apply star_trans_reduction. apply eqc_trans_app_r; assumption.
Qed.

Lemma eqC_abs: forall t t' L, (forall x, x \notin L -> t^x =e t'^x) -> (pterm_abs t) =e (pterm_abs t').
Proof. Admitted.

Lemma eqC_sub: forall t t' u L, term u -> (forall x, x \notin L -> t^x =e t'^x) -> (pterm_sub t u) =e (pterm_sub t' u).
  Proof. Admitted.
*)

(* ********************************************************************** *)
(** =e Rewriting *)

Instance rw_eqC_app : Proper (eqC ==> eqC ==> eqC) pterm_app.
Proof.
    intros_all. apply star_closure_composition with (pterm_app y x0).
    - induction H.
      + reflexivity.
      + constructor. induction H.
        * constructor. constructor 2. assumption.
        * constructor 2 with (pterm_app u x0).
          constructor 2. assumption. assumption.
    - induction H0.
      + reflexivity.
      + induction H0.
        * constructor. constructor. constructor 3.
          assumption.
        * assert ((pterm_app y t) =c (pterm_app y u)).
          { apply ES_app_right. assumption. }
          apply (one_step_reduction eqc_ctx (pterm_app y t) (pterm_app y u)) in H2.
          apply star_transitive_closure_composition_1 with (pterm_app y u); assumption.
Qed.

Instance rw_eqC_abs : Proper (eqC ==> eqC) pterm_abs.
Proof.
  intros t t' Heq. induction Heq.
  - apply eqC_rf.
  - inversion H; subst; clear H.
    + unfold eqC. apply star_trans_reduction.
      apply one_step_reduction. pick_fresh y.
      apply notin_union in Fr.
      destruct Fr as [Hfv_t Hfv_u].
      apply ES_abs_in with (fv t \u fv u).
      introv Hfv. apply notin_union in Hfv.
      destruct Hfv as [Hfv_t' Hfv_u'].
      apply eqc_ctx_open; assumption.
    + apply star_trans_reduction.
      assert (t =c+ u).
      { apply transitive_reduction with u0; assumption. }
      pick_fresh x. apply notin_union in Fr.
      destruct Fr as [Fr Hfv_u0]. apply notin_union in Fr.
      destruct Fr as [Hfv_t Hfv_u].
      apply eqc_trans_abs with (fv t \u fv u).
      introv Hfv. apply notin_union in Hfv.
      destruct Hfv as [Hfv_t' Hfv_u'].
      apply eqc_trans_open; assumption.
Qed.

Instance rw_eqC_sub : Proper (eqC ==> eqC ==> eqC) pterm_sub.
Proof.
  intros_all. apply star_closure_composition with (y[x0]).
  - inversion H; subst.
    + reflexivity.
    + apply star_trans_reduction. inversion H1; subst.
      apply one_step_reduction. pick_fresh z.
      apply ES_subst_left with (fv x \u fv y \u fv x0 \u fv y0).
      introv Hfv. apply eqc_ctx_open; assumption.
      assert (x =c+ y).
      { apply transitive_reduction with u; assumption. }
      pick_fresh z.
      apply eqc_trans_sub_left with (fv x \u fv y \u fv x0 \u fv y0 \u fv u).
      introv Hfv. apply eqc_trans_open; assumption.
  - induction H0.
    + reflexivity.
    + apply star_trans_reduction. induction H0.
      * apply one_step_reduction.
        apply ES_subst_right; assumption.
     (*  * apply transitive_reduction with (y[u]). *)
(*         ** apply ES_subst_right; assumption. *)
(*         ** assumption. *)
(* Qed. *)
Admitted.                       (* Fabrício *)

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

Instance eqC_subst_out : forall x u, Proper (eqC ==> eqC) (subst x u).
Proof.
  intros x u v v' Hv. gen u x. induction Hv.
  - intros u x. apply eqC_rf.
  - intros u' x. apply star_trans_reduction.
    apply eqc_trans_subst_out; assumption.
Qed.

Instance eqC_subst : forall x, Proper (eqC ==> eqC ==> eqC) (subst x).
Proof.
  (* intros x v v' Hv u u' Hu. rewrite Hu. clear u Hu. *)
  (* gen u' x. induction Hv. *)
  (* - intros u x. apply eqC_rf. *)
  (* - intros u' x. gen u' x t u H. induction u'. *)
  (*   + introv Heqc. reflexivity. *)
  (*   + introv Heqc. simpl. case_var. *)
  (*     * apply star_trans_reduction; assumption. *)
  (*     * reflexivity. *)
  (*   + introv Heqc. simpl. *)
  (*     assert (Heq1: [x ~> t]u'1 =e [x ~> u]u'1). *)
  (*     { apply IHu'1; assumption. } *)
  (*     assert (Heq2: [x ~> t]u'2 =e [x ~> u]u'2). *)
  (*     { apply IHu'2; assumption. } *)
  (*     rewrite Heq1. rewrite Heq2. reflexivity. *)
  (*   +  introv Heqc. simpl. *)
  (*      assert (H: [x ~> t]u' =e [x ~> u]u'). *)
  (*      { apply IHu'; assumption. } *)
  (*      rewrite H. reflexivity. *)
  (*   + introv Heqc. simpl. *)
  (*      assert (Heq1: [x ~> t]u'1 =e [x ~> u]u'1). *)
  (*      { apply IHu'1; assumption. } *)
  (*      assert (Heq2: [x ~> t]u'2 =e [x ~> u]u'2). *)
  (*      { apply IHu'2; assumption. } *)
  (*      rewrite Heq1. rewrite Heq2. reflexivity. *)
  (*   + introv Heqc. simpl. *)
  (*      assert (Heq1: [x ~> t]u'1 =e [x ~> u]u'1). *)
  (*      { apply IHu'1; assumption. } *)
  (*      assert (Heq2: [x ~> t]u'2 =e [x ~> u]u'2). *)
  (*      { apply IHu'2; assumption. } *)
  (*      rewrite Heq1. rewrite Heq2. reflexivity. *)
(* Qed. *) Admitted.

(*
Instance rw_eqC_red : forall R, Proper (eqC ==> eqC ==> iff) (red_ctx_mod_eqC R).
Proof.
  intros_all. split.
  - intro HR. unfold red_ctx_mod_eqC in *.
    destruct HR as [x' [y' [He [Hes He'] ] ] ].
    exists x' y'. split.
    + rewrite <- H; assumption.
    + split.
      * assumption.
      * rewrite He'; assumption.
  - intro HR. unfold red_ctx_mod_eqC in *.
    destruct HR as [x' [y' [He [Hes He'] ] ] ].
    exists x' y'. split.
    + rewrite H; assumption.
    + split.
      * assumption.
      * rewrite He'. symmetry; assumption.
Qed.

Instance rw_eqC_trs : forall R, Proper (eqC ==> eqC ==> iff) (trans_closure (red_ctx_mod_eqC R)).
Proof.
    intros_all. split.
    - intro Htrans.
      inversion Htrans; subst; clear Htrans.
      apply one_step_reduction.
      destruct H1. destruct H1 as [x2 [He [Hes He'] ] ].
      exists x1 x2. split.
      + rewrite <- H; assumption.
      + split.
        * assumption.
        * rewrite He'; assumption.
      +
    -
          split; auto. rewrite <- H0; auto.
    constructor 2 with u. rewrite <- H; auto.
    apply transitive_star_derivation' in H2.
    destruct H2.
    constructor 1.
    destruct H2. destruct H2.  destruct H2. destruct H3.
    unfold red_ctx_mod_eqC. exists x1 x2.
    split; auto. split; auto. rewrite H4; auto.
    destruct H2. destruct H2. destruct H3. destruct H3.
    apply transitive_star_derivation'.
    right. exists x1. split; auto. exists x2. split; auto.
    destruct H4. destruct H4.  destruct H4. destruct H5.
    exists x3 x4. split; auto. split; auto. rewrite H6; auto.

    intro H'.
    inversion H'; subst.
    apply one_step_reduction.
    destruct H1. destruct H1.  destruct H1. destruct H2.
    exists x1 x2.
    split. rewrite H; auto.
    split; auto. rewrite H0; auto.
    constructor 2 with u. rewrite H; auto.
    apply transitive_star_derivation' in H2.
    destruct H2.
    constructor 1.
    destruct H2. destruct H2.  destruct H2. destruct H3.
    unfold red_ctx_mod_eqC. exists x1 x2.
    split; auto. split; auto. rewrite H4; auto. symmetry; auto.
    destruct H2. destruct H2. destruct H3. destruct H3.
    apply transitive_star_derivation'.
    right. exists x1. split; auto. exists x2. split; auto.
    destruct H4. destruct H4.  destruct H4. destruct H5.
    exists x3 x4. split; auto. split; auto. rewrite H6; auto. symmetry; auto.
Qed.

Instance rw_eqC_lc_at : forall n, Proper (eqC ==> iff) (lc_at n).
Proof.
 intros_all. apply lc_at_eqC; trivial.
Qed.

Instance rw_eqC_body : Proper (eqC ==> iff) body.
Proof.
 intros_all. rewrite body_eq_body'. rewrite body_eq_body'.
 unfold body'. rewrite H. reflexivity.
Qed.

Instance rw_eqC_term : Proper (eqC ==> iff) term.
Proof.
 intros_all. rewrite term_eq_term'. rewrite term_eq_term'.
 unfold term'. rewrite H. reflexivity.
Qed.

Instance rw_eqC_fv : Proper (eqC ==> VarSet.Equal) fv.
Proof.
 intros_all. apply eqC_fv; trivial.
Qed.

Instance rw_eqC_subst_right : forall t, Proper (eqC ++> eqC) (pterm_sub t).
Proof.
 intros_all. generalize dependent t. induction H.
 - reflexivity.
 - constructor 2. induction H.
   + constructor 1; auto. constructor 6. assumption.
   + assert ((t0 [t]) =c (t0 [u])).
     { apply ES_subst_right. assumption. }
     apply transitive_reduction with (t0 [u]); assumption.
Qed.

Instance SN_ind_mod_eqC : forall n R, Proper (eqC ==> iff) (SN_ind n (red_ctx_mod_eqC R)).
Proof.
 intros_all. split. intro H'.
 apply SN_intro. intros z H''. inversion H'.
 case (H0 z). rewrite H; trivial. intros k H1. destruct H1.
 exists k; split; try omega; trivial. intro H'.
 apply SN_intro. intros z H''. inversion H'.
 case (H0 z). rewrite <- H; trivial. intros k H1. destruct H1.
 exists k; split; try omega; trivial.
Qed.

Instance NF_mod_eqC : forall R, Proper (eqC ==> iff) (NF (red_ctx_mod_eqC R)).
Proof.
 intros_all. split; intro H'.
 intros t0 H0. rewrite <- H in H0.
 apply (H' t0); trivial.
 intros t0 H0. rewrite H in H0.
 apply (H' t0); trivial.
Qed.
 *)

Lemma red_all_eqC : forall x t t' (u u' : pterm), t =e t' -> u =e u' -> ([x ~> u]t) =e ([x ~> u']t').
Proof.
  introv Heq1 Heq2. rewrite Heq1. rewrite Heq2. apply eqC_rf.
Qed.
(*
Lemma red_rename_pctx_eqc : red_rename (p_contextual_closure eqc).
Proof.
 intros_all.
 rewrite* (@subst_intro x t).
 rewrite* (@subst_intro x t').
 apply red_out_pctx_eqc; trivial.
Qed.
 *)

Lemma red_out_mod_eqC : forall R, red_wregular R -> red_out R ->
                    red_out (red_ctx_mod_eqC R).
Proof.
 intros R H1 H2. unfold red_out. intros x t t' u T H3.
 unfold red_ctx_mod_eqC in *|-*.
 case H3; clear H3; intros t0 H3.
 case H3; clear H3; intros u0 H3.
 case H3; clear H3; intros H3 H4.
 case H4; clear H4; intros H4 H5.
 assert (Q: red_wregular (ES_contextual_closure R)).
   apply red_wregular_ctx; trivial.
 assert (Q': red_out (ES_contextual_closure R)).
   apply red_out_ctx; trivial.
 exists ([x ~> t]t0) ([x ~> t]u0). split.
 apply red_out_eqC; try reflexivity; trivial.
 split. apply Q'; trivial.
 apply red_out_eqC; try reflexivity; trivial.
Qed.

(*
Lemma red_not_fv_mod_eqC : forall R, red_not_fv R -> red_not_fv (red_ctx_mod_eqC R).
Proof.
 intros. apply red_not_fv_ctx in H.
 unfold red_not_fv in *|-*. intros.
 unfold red_ctx_mod_eqC in H0.
 case H0; clear H0; intros t0 H0.
 case H0; clear H0; intros t1 H0.
 case H0; clear H0; intros H2 H3.
 case H3; clear H3; intros H3 H4.
 apply (H x) in H3.
 apply (eqC_fv x) in H4. intro H5.
 assert (Q : x \in fv t1).
           apply H4; trivial.
 contradiction.
 apply (eqC_fv x) in H2.
 intro H5. assert (Q : x \in fv t).
           apply H2; trivial.
 contradiction.
Qed.
*)

Lemma red_fv_mod_eqC : forall R, red_fv R -> red_fv (red_ctx_mod_eqC R).
Proof.
(*  intros. apply red_fv_ctx in H. *)
(*  unfold red_fv in *|-*. intros. *)
(*  unfold red_ctx_mod_eqC in H0. *)
(*  case H0; clear H0; intros t0 H0. *)
(*  case H0; clear H0; intros t1 H0. *)
(*  case H0; clear H0; intros H2 H3. *)
(*  case H3; clear H3; intros H3 H4. *)
(*  apply (eqC_fv x) in H2. apply H2. *)
(*  apply H with (t' := t1); trivial. *)
(*  apply (eqC_fv x) in H4. *)
(*  apply H4; trivial. *)
  (* Qed. *)
Admitted.


(* ********************************************************************** *)
(*
Lemma ctx_to_mod_eqC : forall R t t', contextual_closure R t t' -> red_ctx_mod_eqC R t t'.
Proof.
 intros R t t' H.
 exists t t'. split.
 reflexivity. split; trivial.
 reflexivity.
Qed.

Lemma eqC_abs_in_close : forall x L t t', eqC t t' -> x \notin L ->
                                     eqC (pterm_abs (close t x)) (pterm_abs (close t' x)).
Proof. Admitted.
  introv H Fr. induction H.
  - apply eqC_rf. apply term_abs with L.
    introv H0. apply term_open_rename with x.
    rewrite <- open_close_var; assumption.
  - apply star_trans_reduction.
    destruct H.
    + apply one_step_reduction.
      unfold eqc_ctx in *. inversion H. clear H. subst.
      * apply ES_redex. subst. apply eqc_def.
      *
      *
      *
      *
      *
      apply eqc_abs_in_close.
    +
    apply trs_pctx_abs_in_close with (L := L); trivial.
 apply red_regular'_eqc. apply red_out_eqc.
Qed.

Lemma eqC_subst_left_close : forall x L t t' u,  term t ->
                              eqC t t' -> x \notin L ->
                              eqC ((close t x)[u]) ((close t' x)[u]).
Proof.
  introv Hterm Heqc Fr. gen x L u Hterm. induction Heqc.
  - introv HL Hterm. reflexivity.
  - introv HL Hterm.
    apply trs_pctx_subst_close with (L := L); trivial.
 apply red_regular'_eqc. apply red_out_eqc.
 intros. apply eqc_rf. apply one_step_reduction. apply p_redex. apply eqc_rf.
Qed.

Lemma eqC_abs_in : forall L t t', body t ->
                              (forall x, x \notin L -> eqC (t^x) (t'^x)) ->
                              eqC (pterm_abs t) (pterm_abs t').
Proof.
 intros L t t' B H.
 apply trs_pctx_abs_in with (L := L); trivial.
 apply red_regular'_eqc. apply red_out_eqc.
Qed.

Lemma eqC_subst_left : forall L t t' u, body t ->  term u ->
                              (forall x, x \notin L -> eqC (t^x) (t'^x)) ->
                              eqC (t[u]) (t'[u]).
Proof.
 intros L t t' u B T H.
 apply trs_pctx_subst with (L := L); trivial.
 apply red_regular'_eqc. apply red_out_eqc.
 intros. apply eqc_rf. apply one_step_reduction. apply p_redex. apply eqc_rf.
Qed.
 *)

Lemma mod_eqC_app_left : forall R t t' u, red_ctx_mod_eqC R t t' ->
                         red_ctx_mod_eqC R (pterm_app t u) (pterm_app t' u).
Proof.
(*   introv H. case H; clear H. intros t0 H. *)
(*   case H; clear H; intros t1 H. *)
(*   destruct H as [Heqc [Hes Heqc'] ]. *)
(*   exists (pterm_app t0 u) (pterm_app t1 u). split. *)
(*   - rewrite Heqc. reflexivity. *)
(*   - split. *)
(*     + apply ES_app_left; trivial. *)
(*     + rewrite Heqc'; reflexivity. *)
  (* Qed. *)
  Admitted.

Lemma trs_mod_eqC_app_left : forall R t t' u, trans_closure (red_ctx_mod_eqC R) t t' ->
                         trans_closure (red_ctx_mod_eqC R) (pterm_app t u) (pterm_app t' u).
Proof.
 introv H. induction H.
 - apply one_step_reduction. apply  mod_eqC_app_left; trivial.
 - apply transitive_reduction with (pterm_app u0 u); trivial.
   apply  mod_eqC_app_left; trivial.
Qed.

Lemma str_mod_eqC_app_left : forall R t t' u, star_closure (red_ctx_mod_eqC R) t t' ->
                         star_closure (red_ctx_mod_eqC R) (pterm_app t u) (pterm_app t' u).
Proof.
 introv H. induction H.
 - apply reflexive_reduction.
 - apply  star_trans_reduction.
 apply trs_mod_eqC_app_left; trivial.
Qed.

Lemma mod_eqC_app_right : forall R t t' u, red_ctx_mod_eqC R t t' ->
                         red_ctx_mod_eqC R (pterm_app u t) (pterm_app u t').
Proof.
(*  introv H. case H; clear H; intros t0 H. case H; clear H; intros t1 H. *)
(*  destruct H as [Heqc [Hes Heqc'] ]. *)
(*  exists (pterm_app u t0) (pterm_app u t1). split. *)
(*  - rewrite Heqc; reflexivity. *)
(*  - split. *)
(*    + apply ES_app_right; trivial. *)
(*    + rewrite Heqc'; reflexivity. *)
  (* Qed. *)
Admitted.

Lemma trs_mod_eqC_app_right : forall R t u u', trans_closure (red_ctx_mod_eqC R) u u' ->
                         trans_closure (red_ctx_mod_eqC R) (pterm_app t u) (pterm_app t u').
Proof.
 introv H. induction H.
 - apply one_step_reduction. apply  mod_eqC_app_right; trivial.
 - apply transitive_reduction with (pterm_app t u); trivial.
   apply  mod_eqC_app_right; trivial.
Qed.

Lemma str_mod_eqC_app_right : forall R t u u', star_closure (red_ctx_mod_eqC R) u u' ->
                         star_closure (red_ctx_mod_eqC R) (pterm_app t u) (pterm_app t u').
Proof.
 introv H. induction H.
 - apply reflexive_reduction.
 - apply  star_trans_reduction.
   apply trs_mod_eqC_app_right; trivial.
Qed.

Lemma mod_eqC_subst_right : forall R t u u', red_ctx_mod_eqC R u u' ->
                         red_ctx_mod_eqC R (pterm_sub t u) (pterm_sub t u').
Proof.
(*  introv H. case H; clear H; intros u0 H. case H; clear H; intros u1 H. *)
(*  destruct H as [Heqc [ Hes Heqc'] ]. exists (t[u0]) (t[u1]). split. *)
(*  - rewrite Heqc. reflexivity. *)
(*  - split. *)
(*    + apply ES_subst_right; trivial. *)
(*    + rewrite Heqc'; reflexivity. *)
(* Qed. *)
Admitted.
  
Lemma trs_mod_eqC_subst_right : forall R t u u', trans_closure (red_ctx_mod_eqC R) u u' ->
                         trans_closure (red_ctx_mod_eqC R) (t[u]) (t[u']).
Proof.
 introv H. induction H.
 - apply one_step_reduction. apply  mod_eqC_subst_right; trivial.
 - apply transitive_reduction with (t[u]); trivial.
   apply  mod_eqC_subst_right; trivial.
Qed.

Lemma str_mod_eqC_subst_right : forall R t u u', star_closure (red_ctx_mod_eqC R) u u' ->
                         star_closure (red_ctx_mod_eqC R) (t[u]) (t[u']).
Proof.
 introv H. induction H.
 - apply reflexive_reduction.
 - apply  star_trans_reduction.
   apply trs_mod_eqC_subst_right; trivial.
Qed.
(*
Lemma mod_eqC_abs_in_close : forall x R L t t', red_wregular R -> red_out R ->
                              red_ctx_mod_eqC R t t' -> x \notin L ->
                              red_ctx_mod_eqC R (pterm_abs (close t x)) (pterm_abs (close t' x)).
Proof.
  introv Reg Out H Fr. case H; clear H; intros t0 H.
  case H; clear H; intros t1 H.
  destruct H as [ Heqc [Hes Heqc'] ].
  exists (pterm_abs (close t0 x)) (pterm_abs (close t1 x)). split.
  - apply eqC_abs_in_close with L; trivial.
  - apply red_wregular_ctx in Reg. apply Reg in Hes. split. Admitted.
   (* + apply ctx_abs_in_close with L; trivial. *)
(*  apply eqC_abs_in_close with (L := L); trivial.  *)
(*  apply red_regular_ctx in Reg. apply Reg in H0. apply H0. *)
(* Qed. *)

Lemma mod_eqC_abs_in : forall R L t t', red_wregular R -> red_out R ->
                      (forall x, x \notin L -> red_ctx_mod_eqC R (t ^ x) (t' ^ x)) ->
                       red_ctx_mod_eqC R (pterm_abs t) (pterm_abs t').
Proof.
 introv Reg Out H.  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr.
 apply notin_union in Fr. destruct Fr as [Fr Hfv_t']. apply notin_union in Fr.
 destruct Fr as [HL Hfv_t].
 assert (Q: red_ctx_mod_eqC R (t ^ x) (t' ^ x)).
 { apply H; trivial. }
 clear H. gen_eq t2 : (t ^ x). gen_eq t3 : (t' ^ x).
 intros Ht2 Ht3. replace t with (close t2 x).
 replace t' with (close t3 x). clear Ht2 Ht3.
 apply mod_eqC_abs_in_close with (L := L); trivial.
 rewrite Ht2. rewrite <- close_open_term; trivial.
 rewrite Ht3. rewrite <- close_open_term; trivial.
Qed.

Lemma trs_mod_eqC_abs_in : forall R L t t', red_wregular R -> red_out R ->
                      (forall x, x \notin L -> trans_closure (red_ctx_mod_eqC R) (t ^ x) (t' ^ x)) ->
                       trans_closure (red_ctx_mod_eqC R) (pterm_abs t) (pterm_abs t').
Proof.
  introv H0 H1 H2.  case var_fresh with (L := L \u (fv t) \u (fv t')).
  intros x Fr. apply notin_union in Fr. destruct Fr as [Fr Hfv_t'].
  apply notin_union in Fr. destruct Fr as [HL Hfv_t].
  assert (Q: trans_closure (red_ctx_mod_eqC R) (t ^ x) (t' ^ x)).
  { apply H2; trivial. }
  clear H2. gen_eq t0 : (t ^ x). gen_eq t1 : (t' ^ x). intros Ht1 Ht0.
  replace t with (close t0 x). replace t' with (close t1 x).
  clear Ht0 Ht1. induction Q. apply one_step_reduction.
  apply mod_eqC_abs_in_close with (L := L); trivial.
  apply transitive_reduction with (u := pterm_abs (close u x)); trivial.
  apply mod_eqC_abs_in_close with (L := L); trivial.
  rewrite Ht1. rewrite <- close_open_term; trivial.
  rewrite Ht0. rewrite <- close_open_term; trivial.
Qed.

Lemma str_mod_eqC_abs_in : forall R L t t', red_wregular R -> red_out R ->
                      (forall x, x \notin L -> star_closure (red_ctx_mod_eqC R) (t ^ x) (t' ^ x)) ->
                       star_closure (red_ctx_mod_eqC R) (pterm_abs t) (pterm_abs t').
Proof.
  introv H0 H1 H2.  case var_fresh with (L := L \u (fv t) \u (fv t')).
  intros x Fr. apply notin_union in Fr. destruct Fr as [Fr Fr'].
  apply notin_union in Fr. destruct Fr as [Fr Fr''].
  assert (Q: star_closure (red_ctx_mod_eqC R) (t ^ x) (t' ^ x)).
  { apply H2; trivial. }
  clear H2. gen_eq t0 : (t ^ x). gen_eq t1 : (t' ^ x). intros Ht1 Ht0.
 replace t with (close t0 x). replace t' with (close t1 x).
 clear Ht0 Ht1. destruct Q. apply reflexive_reduction. Admitted.
(*  apply term_abs with L. intros x' H'. apply term_open_rename with x. *)
(*  rewrite <- open_close_var; assumption. *)
(*  apply star_trans_reduction. destruct H. *)
(*  apply one_step_reduction. unfold red_ctx_mod_eqC in *. *)


(*  apply mod_eqC_abs_in_close with (L := L); trivial. *)
(*  apply transitive_reduction with (u := pterm_abs (close u x)); trivial. *)
(*  apply mod_eqC_abs_in_close with (L := L); trivial.  *)
(*  rewrite Ht1. rewrite <- close_open_term; trivial.  *)
(*  rewrite Ht0. rewrite <- close_open_term; trivial. *)
(* Qed. *)

Lemma mod_eqC_subst_left_close : forall x R L t t' u, red_wregular R -> red_out R ->
                              red_ctx_mod_eqC R t t' -> x \notin L ->
                              red_ctx_mod_eqC R ((close t x)[u]) ((close t' x)[u]).
Proof.
  introv Reg Out H Fr. case H; clear H; intros t0 H.
  case H; clear H; intros t1 H.
  destruct H as [Heqc [Hes Heqc'] ].
  exists ((close t0 x)[u]) ((close t1 x)[u]). split.
  - apply eqC_subst_left_close with (L := L); trivial. rewrite H.
 apply red_regular_ctx in Reg. apply Reg in H0. apply H0. split.
 apply ctx_subst_left_close with (L := L); trivial.
 apply eqC_subst_left_close with (L := L); trivial.
 apply red_regular_ctx in Reg. apply Reg in H0. apply H0.
Qed.

Lemma mod_eqC_subst_left : forall R L t t' u, red_regular R -> red_out R -> term u ->
                      (forall x, x \notin L -> red_ctx_mod_eqC R (t ^ x) (t' ^ x)) ->
                       red_ctx_mod_eqC R (t[u]) (t'[u]).
Proof.
 intros R L t t' u Reg Out T H.  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr.
 apply notin_union in Fr. destruct Fr. apply notin_union in H0. destruct H0.
 assert (Q: red_ctx_mod_eqC R (t ^ x) (t' ^ x)). apply H; trivial. clear H.
 gen_eq t2 : (t ^ x). gen_eq t3 : (t' ^ x). intros Ht2 Ht3.
 replace t with (close t2 x). replace t' with (close t3 x). clear Ht2 Ht3.
 apply mod_eqC_subst_left_close with (L := L); trivial.
 rewrite Ht2. rewrite <- close_open_term; trivial.
 rewrite Ht3. rewrite <- close_open_term; trivial.
Qed.


Lemma trs_mod_eqC_subst_left : forall R L t t' u, red_regular R -> red_out R -> term u ->
                              (forall x, x \notin L -> trans_closure (red_ctx_mod_eqC R) (t ^ x) (t' ^ x)) ->
                              trans_closure (red_ctx_mod_eqC R) (t[u]) (t'[u]).
Proof.
 intros R L t t' u H0 H1 T H2.  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr.
 apply notin_union in Fr. destruct Fr. apply notin_union in H. destruct H.
 assert (Q: trans_closure (red_ctx_mod_eqC R) (t ^ x) (t' ^ x)). apply H2; trivial. clear H2.
 gen_eq t0 : (t ^ x). gen_eq t1 : (t' ^ x). intros Ht1 Ht0.
 replace t with (close t0 x). replace t' with (close t1 x).
 clear Ht0 Ht1. induction Q.
 apply one_step_reduction. apply mod_eqC_subst_left_close with (L := L); trivial.
 apply transitive_reduction with (u := (close u0 x)[u]); trivial.
 apply mod_eqC_subst_left_close with (L := L); trivial.
 rewrite Ht1. rewrite <- close_open_term; trivial.
 rewrite Ht0. rewrite <- close_open_term; trivial.
Qed.


Lemma str_mod_eqC_subst_left : forall R L t t' u, red_regular R -> red_out R -> term u ->
                      (forall x, x \notin L -> star_closure (red_ctx_mod_eqC R) (t ^ x) (t' ^ x)) ->
                       star_closure (red_ctx_mod_eqC R) (t[u]) (t'[u]).
Proof.
 intros R L t t' u H0 H1 T H2.  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr.
 apply notin_union in Fr. destruct Fr. apply notin_union in H. destruct H.
 assert (Q: star_closure (red_ctx_mod_eqC R) (t ^ x) (t' ^ x)). apply H2; trivial. clear H2.
 gen_eq t0 : (t ^ x). gen_eq t1 : (t' ^ x). intros Ht1 Ht0.
 replace t with (close t0 x). replace t' with (close t1 x).
 clear Ht0 Ht1. destruct Q. apply reflexive_reduction.
 apply star_trans_reduction. induction H2.
 apply one_step_reduction. apply mod_eqC_subst_left_close with (L := L); trivial.
 apply transitive_reduction with (u := (close u0 x)[u]); trivial.
 apply mod_eqC_subst_left_close with (L := L); trivial.
 rewrite Ht1. rewrite <- close_open_term; trivial.
 rewrite Ht0. rewrite <- close_open_term; trivial.
Qed.
*)

(*** about NF and SN modulo =e ***)
(*
Lemma eqC_SN_app : forall n R t u, red_regular R -> term t -> term u ->
                   SN_ind n (red_ctx_mod_eqC R) (pterm_app t u) ->
                   SN_ind n (red_ctx_mod_eqC R) t /\ SN_ind n (red_ctx_mod_eqC R) u.
Proof.
 intros n R t u Reg.
 generalize t u; clear t u.
 induction n.  intros. split; rewrite <- NF_eq_SN0 in *|-*; unfold NF in *|-*.
 intros t' H'. apply (H1 (pterm_app t' u)). apply mod_eqC_app_left; trivial.
 intros u' H'. apply (H1 (pterm_app t u')). apply mod_eqC_app_right; trivial.
 intros t u Tt Tu H. destruct H. split.
 apply SN_intro. intros t' H'. exists n. split; try omega.
 apply IHn with (t := t') (u := u); trivial. apply red_regular_eqC in Reg.
 apply Reg in H'. apply H'. case (H (pterm_app t' u)). apply mod_eqC_app_left; trivial.
 intros k H''. apply WSN with (k := k). omega. apply H''.
 apply SN_intro. intros u' H'. exists n. split; try omega.
 apply IHn with (t := t) (u := u'); trivial. apply red_regular_eqC in Reg.
 apply Reg in H'. apply H'. case (H (pterm_app t u')). apply mod_eqC_app_right; trivial.
 intros k H''. apply WSN with (k := k). omega. apply H''.
Qed.


Lemma eqC_SN_abs : forall x n R t, red_regular R -> red_out R ->
               SN_ind n (red_ctx_mod_eqC R) (pterm_abs t) ->
               x \notin (fv t) -> SN_ind n (red_ctx_mod_eqC R) (t ^ x).
Proof.
 intros x n R t Reg Out.
 generalize t; clear t.
 generalize Out. intro Out'. apply red_out_mod_eqC in Out; trivial.
 generalize Reg. intro Reg'. apply red_regular_eqC in Reg.
 apply red_out_to_rename in Out.
 induction n. intros.
 apply SN0_to_NF in H.
 apply NF_to_SN0; unfold NF in *|-*.
 intros t' H'. gen_eq t0 : (close t' x). intro H1.
 replace t' with (t0 ^ x) in H'.
 assert (Q: red_ctx_mod_eqC R (pterm_abs t) (pterm_abs t0)).
    apply mod_eqC_abs_in with (L := {{x}}); trivial. intros z H2.
    apply notin_singleton in H2. apply Out with (x := x); trivial.
    rewrite H1. apply fv_close'.
 apply False_ind. apply (H (pterm_abs t0)); trivial.
 rewrite H1. rewrite open_close_var with (x := x).
 reflexivity. apply Reg in H'. apply H'.
 intros. destruct H. apply SN_intro.
 intros. exists n. split; try omega.
 gen_eq t0 : (close t' x). intro H2.
 replace t' with (t0 ^ x). replace t' with (t0 ^ x) in H1.
 apply IHn; trivial. case (H (pterm_abs t0)); trivial.
 apply  mod_eqC_abs_in with (L := {{x}}); trivial.
 intros z H3. apply notin_singleton in H3.
 apply Out with (x := x); trivial.
 rewrite H2. apply fv_close'.
 intros k H3. apply WSN with (k := k); try omega.
 apply H3. rewrite H2. apply fv_close'.
 rewrite H2. rewrite open_close_var with (x := x).
 reflexivity. apply Reg in H1. apply H1.
 rewrite H2. rewrite open_close_var with (x := x).
 reflexivity. apply Reg in H1. apply H1.
Qed.


Lemma eqC_SN_sub : forall x n R t u, red_regular R -> red_out R ->
               body t -> term u -> x \notin (fv t) ->
               SN_ind n (red_ctx_mod_eqC R) (t[u]) ->
               SN_ind n (red_ctx_mod_eqC R) (t ^ x) /\
               SN_ind n (red_ctx_mod_eqC R) u.
Proof.
 intros x n R t u Reg Out B T.
 generalize t u B T; clear t u B T.
 generalize Out. intro Out'. apply red_out_mod_eqC in Out; trivial.
 generalize Reg. intro Reg'. apply red_regular_eqC in Reg.
 apply red_out_to_rename in Out.
 induction n. intros. rewrite <- NF_eq_SN0 in *|-*; unfold NF in *|-*.
 split. intros t' H'. gen_eq t0 : (close t' x). intro H1.
 replace t' with (t0 ^ x) in H'.
 assert (Q: red_ctx_mod_eqC R (t[u]) (t0[u])).
    apply mod_eqC_subst_left with (L := {{x}}); trivial. intros z H2.
    apply notin_singleton in H2. apply Out with (x := x); trivial.
    rewrite H1. apply fv_close'.
 apply (H0 (t0[u])); trivial.
 rewrite H1. rewrite open_close_var with (x := x).
 reflexivity. apply Reg in H'. apply H'.
 rewrite <- NF_eq_SN0 in *|-*; unfold NF in *|-*. intros u' H'.
 apply (H0 (t[u'])). apply mod_eqC_subst_right; trivial.
 intros. split. destruct H0. apply SN_intro.
 intros. exists n. split; try omega.
 gen_eq t0 : (close t' x). intro H2.
 replace t' with (t0 ^ x). replace t' with (t0 ^ x) in H1.
 apply IHn with (u := u); trivial.
 rewrite body_eq_body'. unfold body'.
 apply Reg in H1. destruct H1.
 rewrite term_eq_term' in H3. unfold term' in H3. unfold open in H3.
 rewrite lc_at_open with (u := pterm_fvar x); trivial.
 rewrite H2. apply fv_close'. case (H0 (t0[u])); trivial.
 apply mod_eqC_subst_left with (L := {{x}}); trivial.
 intros z H3. apply notin_singleton in H3.
 apply Out with (x := x); trivial.
 rewrite H2. apply fv_close'. intros k H3. destruct H3.
 apply WSN with (k := k); try omega; trivial.
 rewrite H2. rewrite open_close_var with (x := x).
 reflexivity. apply Reg in H1. apply H1.
 rewrite H2. rewrite open_close_var with (x := x).
 reflexivity. apply Reg in H1. apply H1.
 apply SN_intro. intros u' H'. exists n; split; try omega.
 apply (IHn t u'); trivial. apply Reg in H'. apply H'.
 destruct H0. case (H0 (t[u'])). apply mod_eqC_subst_right; trivial.
 intros k H1. destruct H1.
 apply WSN with (k := k); try omega; trivial.
Qed.


Lemma eqC_SN_app_list : forall n R t lu, red_regular R -> term t -> term %% lu ->
                   SN_ind n (red_ctx_mod_eqC R) (t // lu) ->
                   SN_ind n (red_ctx_mod_eqC R) t /\ SN_ind n (red_ctx_mod_eqC R) %% lu.
Proof.
 intros n R t lu Reg. generalize n t; clear n t.
 induction lu; simpl. intros n t T H0 H. split; trivial.
 intros n t T H0 H. destruct H0. apply eqC_SN_app in H; trivial. destruct H.
 assert (Q : SN_ind n (red_ctx_mod_eqC R) t /\ SN_ind n (red_ctx_mod_eqC R) %% lu).
  apply IHlu; trivial.
 clear IHlu. destruct Q. split; trivial. split; trivial.
 rewrite term_mult_app. split; trivial.
Qed.

Lemma red_h_mult_app : forall R t t' lu, term %% lu -> (red_ctx_mod_eqC R) t t' -> (red_ctx_mod_eqC R) (t // lu) (t' // lu).
Proof.
 intros R t t' lu Tlu H. induction lu; simpl in *|-*; trivial.
 destruct Tlu. apply mod_eqC_app_left; trivial.
 apply IHlu; trivial.
Qed.

Lemma red_t_mult_app : forall R t lu lu', term t -> term %% lu -> R_list (red_ctx_mod_eqC R) lu lu' -> (red_ctx_mod_eqC R) (t // lu) (t // lu').
Proof.
 intros R t lu lu' Tt Tlu H. unfold R_list in H.
 case H; clear H; intros t0 H.
 case H; clear H; intros t1 H.
 case H; clear H; intros l0 H.
 case H; clear H; intros l1 H.
 destruct H. destruct H0.
 rewrite H. rewrite H0. rewrite H in Tlu.
 clear H H0. induction l0; simpl. destruct l1; simpl.
 apply mod_eqC_app_right; trivial.
 apply mod_eqC_app_right; trivial.
 simpl in Tlu. rewrite term_distribute_over_application.
 rewrite term_mult_app. destruct Tlu. destruct H0.
 split; trivial. split; trivial.
 simpl in Tlu. destruct Tlu.
 apply mod_eqC_app_left; trivial.
 apply IHl0; trivial.
Qed.
*)
(**** eqC and eqC' equivalence ***)
(*
Inductive eqC'  : pterm -> pterm -> Prop :=
  | eqC'_refl: forall u, eqC' u u
  | eqC'_trans: forall t u v, eqC' t u -> eqC' u v -> eqC' t v
  | eqC'_redex: forall t u v,
    term u -> term v -> eqC' (t[u][v]) ((& t)[v][u])
  | eqC'_app : forall t t' u u', eqC' t t' -> eqC' u u' ->
    eqC' (pterm_app t u) (pterm_app t' u')
  | eqC'_abs : forall t t' L,
   (forall x, x \notin L -> eqC' (t ^ x) (t' ^ x)) ->
    eqC' (pterm_abs t) (pterm_abs t')
  | eqC'_sub : forall t t' u u' L,
   (forall x, x \notin L -> eqC' (t ^ x) (t' ^ x)) -> eqC' u u' ->
    eqC' (t[u]) (t'[u']).

 Notation "t =e' u" := (eqC' t u) (at level 66).

 Lemma eqC'_sym : forall t u, t =e' u -> u =e' t.
 Proof.
  intros t u H.
  induction H.
  apply eqC'_refl.
  apply eqC'_trans with (u := u); trivial.
  replace (t[u]) with ((& (& t))[u]). apply eqC'_redex; trivial.
  unfold bswap. rewrite bswap_rec_id. reflexivity.
  apply eqC'_app; trivial.
  apply eqC'_abs with (L := L); trivial.
  apply eqC'_sub with (L := L); trivial.
 Qed.

 Instance eqC'_eq : Equivalence eqC'.
 Proof.
   split.
   unfold Reflexive. apply eqC'_refl.
   unfold Symmetric. apply eqC'_sym.
   unfold Transitive. apply eqC'_trans.
 Qed.

Lemma term_eqC' : forall t t', t =e' t' -> (term t <-> term t').
Proof.
 intros t t' H. induction H.
 split; trivial. split. intro.
 apply IHeqC'2. apply IHeqC'1; trivial. intro.
 apply IHeqC'1. apply IHeqC'2; trivial. split.
 intro H'. apply body_to_subs; trivial.
 apply body'_to_body. apply term_to_term' in H'.
 unfold body'. unfold term' in H'. simpl in *|-*.
 split. apply lc_at_bswap. omega. apply H'.
 apply lc_at_weaken_ind with (k1 := 0); try omega.
 apply H'. intro H'. apply body_to_subs; trivial.
 apply body'_to_body. apply term_to_term' in H'.
 unfold body'. unfold term' in H'. simpl in *|-*.
 split. replace t with (& (& t)).
 apply lc_at_bswap. omega. apply H'. apply bswap_rec_id.
 apply lc_at_weaken_ind with (k1 := 0); try omega.
 apply H'. split. intro H'.
 apply term_distribute_over_application.
 apply term_distribute_over_application in H'.
 split. apply IHeqC'1; apply H'. apply IHeqC'2; apply H'.
 intro H'. apply term_distribute_over_application.
 apply term_distribute_over_application in H'.
 split. apply IHeqC'1; apply H'. apply IHeqC'2; apply H'.
 split. intro H'. apply body_to_term_abs.
 apply term_abs_to_body in H'. unfold body in *|-*.
 case H'. clear H'. intros L' H'. exists (L \u L').
 intros x H''. apply notin_union in H''. apply H0.
 apply H''. apply H'. apply H''.
 intro H'. apply body_to_term_abs.
 apply term_abs_to_body in H'. unfold body in *|-*.
 case H'. clear H'. intros L' H'. exists (L \u L').
 intros x H''. apply notin_union in H''. apply H0.
 apply H''. apply H'. apply H''. split. intro H'.
 generalize H'. intro H''. apply term_sub_to_body in H'.
 apply term_sub_to_term in H''. apply body_to_subs.
 unfold body in *|-*. case H'. clear H'. intros L' H'.
 exists (L \u L'). intros x H'''. apply notin_union in H'''.
 apply H0. apply H'''. apply H'. apply H'''. apply IHeqC'; trivial.
 intro H'. generalize H'. intro H''. apply term_sub_to_body in H'.
 apply term_sub_to_term in H''. apply body_to_subs.
 unfold body in *|-*. case H'. clear H'. intros L' H'.
 exists (L \u L'). intros x H'''. apply notin_union in H'''.
 apply H0. apply H'''. apply H'. apply H'''. apply IHeqC'; trivial.
Qed.

Instance rw_eqC'_term : Proper (eqC' ==> iff) term.
Proof.
 intros_all. apply term_eqC'; assumption.
Qed.

Lemma eqC_eq_eqC': forall t t', term t -> (t =e t' <-> t =e' t').
Proof.
 intros t t' T. split.
 assert (Q : forall u v, term u -> p_contextual_closure eqc u v -> u =e' v).
   clear T t t'. intros t t' T H. induction H. destruct H.
   reflexivity. rewrite eqC'_redex; trivial. reflexivity.
   apply term_distribute_over_application in T. destruct T.
   apply eqC'_app.
   apply IHp_contextual_closure1; trivial.
   apply IHp_contextual_closure2; trivial.
   apply eqC'_abs with (L := L). intros. apply H0; trivial.
   apply body_open_term; trivial. apply term_abs_to_body; trivial.
   apply subs_to_body in T; destruct T.
   apply eqC'_sub with (L := L). intros. apply H0; trivial.
   apply body_open_term; trivial. apply IHp_contextual_closure; trivial.
 intro H. induction H. apply Q; trivial.
 apply eqC'_trans with (u := u). apply Q; trivial.
 apply IHtrans_closure. apply (lc_at_pctx_eqc 0) in H.
 rewrite term_eq_term'. apply H. rewrite <- term_eq_term'; trivial.
 intro H. induction H. reflexivity.
 apply transitive_closure_composition with (u := u).
 apply IHeqC'1; trivial. apply IHeqC'2. rewrite <- H; trivial.
 rewrite eqC_redex; trivial. reflexivity.
 apply term_distribute_over_application in T. destruct T.
 rewrite IHeqC'1; trivial. rewrite IHeqC'2; trivial. reflexivity.
 apply eqC_abs_in with (L := L). apply term_abs_to_body; trivial.
 intros x H1. apply H0; trivial. apply body_open_term; trivial.
 apply term_abs_to_body; trivial. apply subs_to_body in T; destruct T.
 rewrite IHeqC'; trivial. apply eqC_subst_left with (L := L); trivial.
 rewrite <- H1; trivial. intros x H4. apply H0; trivial.
 apply body_open_term; trivial.
Qed.


(* ********************************************************************** *)
(** =e' Rewriting *)

Lemma eqC'_fv : forall x t t',
     (eqC' t t') -> ((x \in fv t) <-> (x \in fv t')).
Proof.
 intros x t t' H. induction H.
 split; trivial.
 split.
 intro H'. apply IHeqC'2. apply IHeqC'1; trivial.
 intro H'. apply IHeqC'1. apply IHeqC'2; trivial.
 simpl. split.
 intro H2. apply in_union in H2. case H2; clear H2.
 intro H2. apply in_union in H2. case H2; clear H2.
 intro H2. apply in_union. left. apply in_union.
 left. unfold bswap. rewrite fv_bswap_rec; trivial.
 intro H2. apply in_union. right; trivial.
 intro H2. apply in_union. left. apply in_union. right; trivial.
 intro H2. apply in_union in H2. case H2; clear H2.
 intro H2. apply in_union in H2. case H2; clear H2.
 intro H2. apply in_union. left. apply in_union.
 left. unfold bswap in H2. rewrite fv_bswap_rec in H2; trivial.
 intro H2. apply in_union. right; trivial.
 intro H2. apply in_union. left; apply in_union. right; trivial.
 simpl. split.
 intro H1. apply in_union in H1. case H1; clear H1.
 intro H1. apply in_union. left. apply IHeqC'1; trivial.
 intro H1. apply in_union. right; trivial. apply IHeqC'2; trivial.
 intro H1. apply in_union in H1. case H1; clear H1.
 intro H1. apply in_union. left. apply IHeqC'1; trivial.
 intro H1. apply in_union. right; trivial. apply IHeqC'2; trivial.
 simpl. pick_fresh z. apply notin_union in Fr. case Fr; clear Fr.
 intros H1 H2. apply notin_union in H1. case H1; clear H1. intros H1 H3.
 apply notin_union in H1. case H1; clear H1. intros H1 H4.
 apply notin_singleton in H4.
 assert (Q: (x \in fv (t ^ z) <-> x \in fv t)).
   unfold open. apply fv_open_. intro.
   apply H4. apply symmetry; trivial.
 assert (Q': (x \in fv (t' ^ z) <-> x \in fv t')).
   unfold open. apply fv_open_. intro.
   apply H4. apply symmetry; trivial.
 split.
 intro H5. apply Q'. apply H0; trivial. apply Q; trivial.
 intro H5. apply Q. apply H0; trivial. apply Q'; trivial.
 simpl. pick_fresh z. apply notin_union in Fr. case Fr; clear Fr.
 intros H2 H3. apply notin_union in H2. case H2; clear H2. intros H2 H4.
 apply notin_union in H2. case H2; clear H2. intros H2 H5.
 apply notin_union in H2. case H2; clear H2. intros H2 H6.
 apply notin_union in H2. case H2; clear H2. intros H2 H7.
 apply notin_singleton in H7.
 assert (Q: (x \in fv (t ^ z) <-> x \in fv t)).
   unfold open. apply fv_open_. intro.
   apply H7. apply symmetry; trivial.
 assert (Q': (x \in fv (t' ^ z) <-> x \in fv t')).
   unfold open. apply fv_open_. intro.
   apply H7. apply symmetry; trivial.
 split.
 intro H8. apply in_union in H8. case H8; clear H8.
 intro H8. apply in_union. left.
 apply Q'. apply H0; trivial. apply Q; trivial.
 intro H8. apply in_union. right; trivial. apply IHeqC'; trivial.
 intro H8. apply in_union in H8. case H8; clear H8.
 intro H8. apply in_union. left.
 apply Q. apply H0; trivial. apply Q'; trivial.
 intro H8. apply in_union. right; trivial. apply IHeqC'; trivial.
Qed.

Instance rw_eqC'_fv : Proper (eqC' ==> VarSet.Equal) fv.
Proof.
 intros_all. apply eqC'_fv; trivial.
Qed.

Definition Cofinite_q (L : VarSet.t) (R : pterm -> pterm -> Prop) (t t' : pterm)  :=
 forall x, x \notin L -> R (t ^ x) (t' ^ x) .

Definition term_R (R : pterm -> pterm -> Prop) (t t' : pterm) :=
  term t /\ R t t'.

Instance rw_eqC'_app : Proper (eqC' ++> eqC' ++> eqC') pterm_app.
Proof.
 intros_all.
 apply eqC'_app; trivial.
Qed.

Lemma eq_app_l: forall t t' u, t =e t' -> pterm_app t u =e pterm_app t' u.
Proof.
  intros t t' u eq.
  rewrite eq.
  reflexivity.
Qed.

Lemma eq_app_r: forall t u u', u =e u' -> pterm_app t u =e pterm_app t u'.
Proof.
  intros t t' u eq.
  rewrite eq.
  reflexivity.
Qed.

Instance rw_eqC'_abs : forall L, Proper (Cofinite_q L eqC' ++> eqC') pterm_abs.
Proof.
 intros_all. unfold Cofinite_q in H.
 apply eqC'_abs with (L := L); trivial.
Qed.

Instance rw_eqC'_sub : forall L, Proper (Cofinite_q L eqC' ++> eqC' ++> eqC') pterm_sub.
Proof.
 intros_all. unfold Cofinite_q in H.
 apply eqC'_sub with (L := L); trivial.
Qed.

Lemma eqC'_open : forall n t t' u, term u ->
t =e' t'-> (open_rec n u t) =e' (open_rec n u t').
Proof.
 intros n t t' u H.
 intro H'. generalize n; clear n.
 induction H'. reflexivity.
 intro n. rewrite IHH'1; trivial.
 intro n. unfold open. simpl.
 rewrite open_lc_at with (t := u0).
 rewrite open_lc_at with (t := u0).
 rewrite open_lc_at with (t := v).
 rewrite open_lc_at with (t := v).
 replace ({S (S n) ~> u}(& t)) with (& ({S (S n) ~> u}t)).
 apply eqC'_redex; trivial.
 apply bswap_open_rec. omega.
 apply term_to_term'; trivial.
 apply lc_at_weaken_ind with (k1 := 0);
 try omega. apply term_to_term'; trivial.
 apply lc_at_weaken_ind with (k1 := 0);
 try omega. apply term_to_term'; trivial.
 apply lc_at_weaken_ind with (k1 := 0);
 try omega. apply term_to_term'; trivial.
 apply lc_at_weaken_ind with (k1 := 0);
 try omega. apply term_to_term'; trivial.
 simpl; intro n. rewrite IHH'1; rewrite IHH'2.
 reflexivity.
 simpl; intro n. apply eqC'_abs with (L := (fv u) \u L).
 intros x H2. apply notin_union in H2. case H2; clear H2.
 intros H2 H3. unfold open in *|-*.
 replace ({0 ~> pterm_fvar x}({S n ~> u}t))
 with ({S n ~> u}({0 ~> pterm_fvar x}t)).
 replace ({0 ~> pterm_fvar x}({S n ~> u}t'))
 with ({S n ~> u}({0 ~> pterm_fvar x}t')).
 apply H1; trivial.
 rewrite subst_com; trivial. omega.
 rewrite subst_com; trivial. omega.
 simpl; intro n. apply eqC'_sub with (L := (fv u) \u L).
 intros x H2. apply notin_union in H2. case H2; clear H2.
 intros H2 H3. unfold open in *|-*.
 replace ({0 ~> pterm_fvar x}({S n ~> u}t))
 with ({S n ~> u}({0 ~> pterm_fvar x}t)).
 replace ({0 ~> pterm_fvar x}({S n ~> u}t'))
 with ({S n ~> u}({0 ~> pterm_fvar x}t')).
 apply H1; trivial.
 rewrite subst_com; trivial. omega.
 rewrite subst_com; trivial. omega.
 apply IHH'.
Qed.

Instance rw_eqC'_abs' : Proper (eqC' ++> eqC') pterm_abs.
Proof.
 intros_all. apply eqC'_abs with (L := {}).
 intros x' H'. apply eqC'_open; trivial.
Qed.

Instance rw_eqC'_sub' : Proper (eqC' ++> eqC' ++> eqC') pterm_sub.
Proof.
 intros_all. apply eqC'_sub with (L := {}); trivial.
 intros x' H'. apply eqC'_open; trivial.
Qed.

Lemma eq_abs: forall t t', t =e' t' -> pterm_abs t =e' pterm_abs t'.
Proof.
  intros t t' eq.
  rewrite eq.
  reflexivity.
Qed.

Lemma eq_subs: forall t t' u, t =e' t' -> pterm_sub t u =e' pterm_sub t' u.
Proof.
  intros t t' u eq.
  rewrite eq.
  reflexivity.
Qed.
*)