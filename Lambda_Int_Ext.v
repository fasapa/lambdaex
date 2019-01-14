Set Implicit Arguments.

Require Import Metatheory LambdaES_Defs LambdaESLab_Defs LambdaES_Infra LambdaES_FV.
Require Import Rewriting.
Require Import Equation_C Lambda Lambda_Ex.


Inductive ext_lab_contextual_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
| lab_redex : forall t s, Red t s -> ext_lab_contextual_closure Red t s
| lab_app_left : forall t t' u, lab_term u -> ext_lab_contextual_closure Red t t' -> 
	  		        ext_lab_contextual_closure Red (pterm_app t u) (pterm_app t' u)
| lab_app_right : forall t u u', lab_term t -> ext_lab_contextual_closure Red u u' -> 
	  		         ext_lab_contextual_closure Red (pterm_app t u) (pterm_app t u')
| lab_abs_in : forall t t' L, (forall x, x \notin L -> ext_lab_contextual_closure Red (t^x) (t'^x)) 
                              -> ext_lab_contextual_closure Red (pterm_abs t) (pterm_abs t')
| lab_subst_left : forall t t' u L, lab_term u -> 
	  	                    (forall x, x \notin L -> ext_lab_contextual_closure Red (t^x) (t'^x)) -> 
	                            ext_lab_contextual_closure Red  (t[u]) (t'[u])
| lab_subst_right : forall t u u', lab_body t -> ext_lab_contextual_closure Red u u' -> 
	  	                   ext_lab_contextual_closure Red  (t[u]) (t[u']) 
| lab_subst'_ext : forall t t' u L, term u -> (*SN Red u ->*)
	  	                    (forall x, x \notin L -> ext_lab_contextual_closure Red (t^x) (t'^x)) -> 
	                            ext_lab_contextual_closure Red  (t[[u]]) (t'[[u]])
.

Inductive lab_x_i: pterm -> pterm -> Prop :=
| xi_from_bx_in_les: forall t1 t2 t2', 
                       lab_term (t1 [[ t2 ]]) ->
                       (sys_Bx t2 t2') ->
                       lab_x_i (t1 [[ t2 ]]) (t1 [[ t2' ]])
| xi_from_x : forall t t', 
                lab_term t ->
                lab_sys_x t t' -> 
                lab_x_i t t'. 

Definition lab_EE_ctx_red (R: pterm -> pterm -> Prop) (t: pterm) (u : pterm) := 
        exists t' u', (t =EE t')/\(lab_contextual_closure R t' u')/\(u' =EE u).

Definition ext_lab_EE_ctx_red (R: pterm -> pterm -> Prop) (t: pterm) (u : pterm) := 
    exists t' u', (t =EE t')/\(ext_lab_contextual_closure R t' u')/\(u' =EE u).


Definition lab_x_i_eq := ext_lab_EE_ctx_red lab_x_i.

Definition lab_x_e_eq := ext_lab_EE_ctx_red sys_Bx.

Notation "t -->[lx_i] u" := (lab_x_i_eq t u) (at level 59, left associativity).
Notation "t -->[lx_e] u" := (lab_x_e_eq t u) (at level 59, left associativity).

(* -------------- *)

Lemma term_ee_is_eqc: forall t t', term t -> t =ee t' -> eqc t t'.
Proof.
    intros.
    destruct H0. auto.
    destruct H0; inversion H; subst.
    pick_fresh x.
    apply notin_union in Fr. destruct Fr.
    apply notin_union in H2. destruct H2.
    apply notin_union in H2. destruct H2.
    pose proof H4 x H2.
    inversion H8.
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
  introv H. destruct H. split. apply lc_at_open_rec_rename with x; auto. 
  destruct H0. split. apply SN_open_rename with (x := x); auto.
  apply IHt1 with x; assumption.
Qed.  

Corollary lab_term_open_rename: forall t x y, lab_term (t^x) -> lab_term (t^y).  
Proof.
  introv H. apply lab_term_eq_term'' in H. apply lab_term_eq_term''.
  apply lc_at'_open_rec_rename with x. assumption.
Qed.


Lemma lab_sys_x_i_e: forall t t' x x', lab_term t -> (x =EE t) -> (t' =EE x') -> lab_sys_lx t t' -> (x -->[lx_i] x' \/ x -->[lx_e] x').
Proof.
    intros.
    induction H2.  
    constructor 2. exists t u. split*. split. constructor 1. constructor 1. auto. auto. 
    constructor 2. exists t u. split*. split. constructor 1. constructor 2. auto. auto. 
    constructor 1. exists t u. split*. split. constructor 1. auto. constructor 2. auto. auto. auto.
Qed.

(*Lemma eqcc_lab_term: forall t t', lab_term t -> t =ee t' -> lab_term t'.*)
(*Proof.*)
    (*intros. induction H0. inversion H0; subst. *)
    (*apply term''_to_lab_term.*)
    (*apply lab_term_to_term'' in H. unfold term'' in *. simpl.*)
    (*simpl in H. destruct H. destruct H. split. split. *)
    (*apply lc_at'_bswap_rec; auto.*)
    (*apply lc_at'_weaken; auto.*)
    (*admit. admit. admit. *)

    (*inversion H0; subst.*)
    (*apply term''_to_lab_term.*)
    (*apply lab_term_to_term'' in H. unfold term'' in *. simpl.*)
    (*simpl in H. destruct H. destruct H3. destruct H4. *)
    (*split. split. apply lc_at_weaken_ind with 0. auto. auto. *)
    (*split*.  admit. admit. *)

    (*inversion H0; subst.*)
    (*apply term''_to_lab_term.*)
    (*apply lab_term_to_term'' in H. unfold term'' in *. simpl.*)
    (*simpl in H. destruct H. destruct H. destruct H4. *)
    (*split. apply term_to_term' in H5; unfold term' in *; auto. *)
    (*split*. split. admit.*)
    (*admit. *)


    (*inversion H0; subst.*)
    (*apply term''_to_lab_term.*)
    (*apply lab_term_to_term'' in H. unfold term'' in *. simpl.*)
    (*simpl in H. destruct H. destruct H3. destruct H4. destruct H6. *)
    (*split. apply term_to_term' in H5; unfold term' in *; auto. *)
    (*split*. split. apply lc_at_weaken_ind with 0. auto. auto. *)
    (*split*.*)
    (*admit. *)
(*Qed.*)

Lemma ctx_eqcc_sym: forall t u, simpl_lab_contextual_closure eqcc t u -> simpl_lab_contextual_closure eqcc u t.
Proof.
    intros. induction H. 
    destruct H. 
    apply eqc_sym in H. constructor; constructor 1; auto.
    apply lab_eqc_sym in H. constructor; constructor 2; auto.
    constructor 2; auto.
    constructor 3; auto.
    constructor 4 with L; auto.
    constructor 5 with L; auto.
    constructor 6; auto.
    constructor 7 with L; auto.
    constructor 8; auto.
    destruct H1.
    apply red_regular'_eqc in H1. apply H1; auto.
    inversion H1; subst; inversion H0; subst.
    pick_fresh z.
    apply notin_union in Fr; destruct Fr.
    apply notin_union in H4; destruct H4.
    apply notin_union in H4; destruct H4.
    apply notin_union in H4; destruct H4.
    pose proof (H6 z H4).
    inversion H11.

    destruct H1. 
    apply eqc_sym in H1. constructor 1; auto.
    apply lab_eqc_sym in H1. constructor 2; auto.
Qed.

Lemma star_ctx_eqcc_sym: forall t u, t =EE u -> u =EE t.
Proof.
    intros. induction H. constructor. induction H.
    constructor 2; constructor 1. apply ctx_eqcc_sym; auto.
    apply star_closure_composition with u; auto.

    (* Qed. *)
Admitted.

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
  unfolds open.
(*   rewrite <- open_close_var_gen with (x := x) (k := k); auto. *)
  (* Qed. *)
Admitted.

Lemma term_EE_open: forall t t' x, lab_term t' -> (t ^ x) =EE t' -> exists u, t' = u ^ x.
Proof.
    intros.
    exists (close t' x).
    rewrite <- lab_open_close_var; auto.
    Qed.

Lemma term_EE_open_fv: forall t t' x, lab_term t' -> x \notin fv(t) -> (t ^ x) =EE t' -> exists u, t' = u ^ x /\ x \notin fv(u).
Proof.
    intros.
    apply term_EE_open in H1; auto.
    destruct H1. exists (close t' x). 
    split. rewrite <- lab_open_close_var; auto.
    apply close_fresh.
Qed.

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

Lemma lab_close_var_spec : forall t x, lab_term t -> 
  exists u, t = u ^ x /\ lab_body u /\ x \notin (fv u).
Proof.
    intros.
    exists (close t x).
    rewrite <- lab_open_close_var; auto.
    split*. split*.
    apply close_var_lab_body; auto.
    apply close_fresh; auto.
Qed.


(* ----------------------------------------------------- RED REGULAR *)

Lemma red_lab_regular'_simpl_lab_ctx: forall R, red_lab_regular' R -> red_lab_regular' (simpl_lab_contextual_closure R).
Proof.
    Admitted.

Lemma red_lab_regular'_ext_lab_ctx: forall R, red_lab_regular' R -> red_lab_regular' (ext_lab_contextual_closure R).
Proof.
    intros. unfold red_lab_regular' in *.
    intros. induction H0. apply H; auto.
    split; constructor; auto.
    inversion H2; subst; auto.
    apply IHext_lab_contextual_closure in H5; auto.
    inversion H2; subst; auto.
    apply IHext_lab_contextual_closure in H5; auto.


    split; constructor; auto.
    inversion H2; subst; auto.
    apply IHext_lab_contextual_closure in H6; auto.
    inversion H2; subst; auto.
    apply IHext_lab_contextual_closure in H6; auto.

    split; intros. 
    inversion H2; subst.
    constructor 3 with (L0 \u L); intros.
    rewrite <- H1; auto. 
    inversion H2; subst.
    constructor 3 with (L0 \u L); intros.
    rewrite H1; auto. 


    split; intros. 
    inversion H3; subst.
    constructor 4 with (L0 \u L); intros; auto.
    rewrite <- H2; auto. 
    inversion H3; subst.
    constructor 4 with (L0 \u L); intros; auto.
    rewrite -> H2; auto. 


    split; intros. 
    inversion H2; subst.
    constructor 4 with L; auto. rewrite <- IHext_lab_contextual_closure; auto.
    inversion H2; subst.
    constructor 4 with L; auto. rewrite -> IHext_lab_contextual_closure; auto.


    split; intros. 
    inversion H3; subst.
    constructor 5 with (L0 \u L); intros; auto.
    rewrite <- H2; auto. 
    inversion H3; subst.
    constructor 5 with (L0 \u L); intros; auto.
    rewrite -> H2; auto. 
Qed.

Lemma red_lab_regular'_star: forall R, red_lab_regular' R -> red_lab_regular' (star_closure R).
Proof.
    unfold red_lab_regular' in *.
    intros.
    induction H0.
    reflexivity.
    induction H0. auto.
    (* rewrite IHtrans_closure; auto. *)
    (* Qed. *)
Admitted.
    
Lemma red_lab_regular'_trans: forall R, red_lab_regular' R -> red_lab_regular' (trans_closure R).
Proof.
    intros. unfold red_lab_regular' in *; intros.  induction H0.  apply H; auto.
    (* destruct IHtrans_closure1. destruct IHtrans_closure2. split; auto. *)
    (* Qed. *)
Admitted.

Lemma red_lab_regular'_lab_eqc: red_lab_regular' lab_eqc.
Proof.
  unfold red_lab_regular'. intros_all. 
  induction H; split; intros H1; inversion H1; subst.

  (* <-- *)

  (* 1 *)
  constructor 4 with L. intros. unfold open in *.
  pose proof (H4 x H2).
  apply lab_term_eq_term''.  apply lab_term_eq_term'' in H3.
  pose proof H3. apply lc_rec_open_var_rec' in H7. simpl in H7. destruct H7.
  simpl. rewrite <- lab_term_eq_term''. constructor 5 with L.
  intros. unfold open. rewrite lab_term_eq_term''. 
  apply lc_at_open_var_rec'.  apply lc_at_open_var_rec'. apply lc_at'_bswap_rec; auto.
  rewrite term_eq_term'. apply lc_at_open_var_rec. rewrite term_eq_term' in H0. 
  apply lc_at_weaken; auto. apply SN_open; auto. auto.

  (* 2 *)
  constructor 5 with L. intros. unfold open in *.
  pose proof (H4 x H2).
  apply lab_term_eq_term''.  apply lab_term_eq_term'' in H3.
  pose proof H3 as H7. 
  apply lc_rec_open_var_rec' in H7.  simpl in H7. destruct H7. destruct H7.
  simpl. rewrite <- lab_term_eq_term''. constructor 4 with L.
  intros. unfold open. rewrite lab_term_eq_term''. 
  apply lc_at_open_var_rec'.  apply lc_at_open_var_rec'. 
  apply bswap_rec_lc_at' with (k := 0); auto.
  rewrite lab_term_eq_term''. apply lc_at_open_var_rec'. rewrite lab_term_eq_term'' in H5. 
  apply lc_at'_weaken; auto. auto. 

  pick_fresh z. 
  apply notin_union in Fr. destruct Fr.
  apply notin_union in H2; destruct H2.
  apply notin_union in H2; destruct H2.
  pose proof (H4 z H2).
  rewrite lab_term_eq_term'' in H8. apply lc_rec_open_var_rec' in H8. simpl in H8.
  destruct H8.  destruct H9. auto.


  (* 3 *)
  pick_fresh z. 
  apply notin_union in Fr. destruct Fr.
  apply notin_union in H2; destruct H2.
  apply notin_union in H2; destruct H2.
  pose proof (H4 z H2).
  rewrite lab_term_eq_term'' in H8. apply lc_rec_open_var_rec' in H8. simpl in H8.
  destruct H8.  destruct H9.

  constructor 5 with L; auto. intros.
  rewrite lab_term_eq_term''. apply lc_at_open_var_rec'. simpl. split.
  apply lc_at'_bswap_rec; auto. 
  rewrite lab_term_eq_term'' in H0. apply lc_at'_weaken; auto.

  (* --> *)
  (* 1 *)
  pick_fresh z. 
  apply notin_union in Fr. destruct Fr.
  apply notin_union in H2; destruct H2.
  apply notin_union in H2; destruct H2.
  pose proof (H4 z H2).
  rewrite lab_term_eq_term'' in H9. apply lc_rec_open_var_rec' in H9. simpl in H9.
  destruct H9. 

  constructor 4 with L; auto; intros.
  rewrite lab_term_eq_term''. apply lc_at_open_var_rec'. simpl. split.
  rewrite term_eq_term' in H5. apply lc_at_weaken; auto.
  split*.
  apply bswap_rec_lc_at' with 0; auto. 

  (* 2 *)
  pick_fresh z. 
  apply notin_union in Fr. destruct Fr.
  apply notin_union in H2; destruct H2.
  apply notin_union in H2; destruct H2.
  pose proof (H4 z H2).
  rewrite lab_term_eq_term'' in H9. apply lc_rec_open_var_rec' in H9. simpl in H9.
  destruct H9.  destruct H10.

  constructor 5 with L; auto; intros.
  rewrite lab_term_eq_term''. apply lc_at_open_var_rec'. simpl. split.
  rewrite term_eq_term' in H5. apply lc_at_weaken; auto.
  split*.
  apply lc_at'_bswap_rec; auto. 

  (* 3 *)
  pick_fresh z. 
  apply notin_union in Fr. destruct Fr.
  apply notin_union in H2; destruct H2.
  apply notin_union in H2; destruct H2.
  pose proof (H4 z H2).
  rewrite lab_term_eq_term'' in H9. apply lc_rec_open_var_rec' in H9. simpl in H9.
  destruct H9.  destruct H10.

  constructor 5 with L; auto; intros.
  rewrite lab_term_eq_term''. apply lc_at_open_var_rec'. simpl. split.
  rewrite term_eq_term' in H5. apply lc_at_weaken; auto.
  split*.
  apply bswap_rec_lc_at' with (k := 0); auto. 

Qed.


Lemma red_regular'_eqcc: red_regular' eqcc.
Proof.
    Admitted.

Lemma red_lab_regular'_eqcc: red_lab_regular' eqcc.
Proof.
    Admitted.

Lemma red_lab_regular'_ctx_eqcc: red_lab_regular' (simpl_lab_contextual_closure eqcc).
Proof.
    intros. unfold red_lab_regular' in *.
    intros. induction H. apply red_lab_regular'_eqcc; auto.
    split; constructor; auto.
    inversion H1; subst; auto.
    apply IHsimpl_lab_contextual_closure in H4; auto.
    inversion H1; subst; auto.
    apply IHsimpl_lab_contextual_closure in H4; auto.


    split; constructor; auto.
    inversion H1; subst; auto.
    apply IHsimpl_lab_contextual_closure in H5; auto.
    inversion H1; subst; auto.
    apply IHsimpl_lab_contextual_closure in H5; auto.

    split; intros. 
    inversion H1; subst.
    constructor 3 with (L0 \u L); intros.
    rewrite <- H0; auto. 
    inversion H1; subst.
    constructor 3 with (L0 \u L); intros.
    rewrite H0; auto. 


    split; intros. 
    inversion H2; subst.
    constructor 4 with (L0 \u L); intros; auto.
    rewrite <- H1; auto. 
    inversion H2; subst.
    constructor 4 with (L0 \u L); intros; auto.
    rewrite -> H1; auto. 


    split; intros. 
    inversion H1; subst.
    constructor 4 with L; auto. rewrite <- IHsimpl_lab_contextual_closure; auto.
    inversion H1; subst.
    constructor 4 with L; auto. rewrite -> IHsimpl_lab_contextual_closure; auto.


    split; intros. 
    inversion H2; subst.
    constructor 5 with (L0 \u L); intros; auto.
    rewrite <- H1; auto. 
    inversion H2; subst.
    constructor 5 with (L0 \u L); intros; auto.
    rewrite -> H1; auto. 


    split; intros. 
    inversion H2; subst.
    constructor 5 with (L); intros; auto.
    pose proof (red_regular'_eqcc H1); auto. 
    rewrite <- H3; auto.
    inversion H7.
    exists x.
    inversion H3.
    constructor. intros.

    apply H4.  apply term_ee_is_eqc in H1.
    destruct H8.  destruct H8.  destruct H8.  destruct H9.
    pose proof ES_redex eqc u u' H1. 
    pose proof one_step_reduction (ES_contextual_closure eqc) u u' H11. 
    pose proof star_trans_reduction (ES_contextual_closure eqc) u u' H12. 
    pose proof star_closure_composition (ES_contextual_closure eqc) u u' x0 H13 H8.
    exists x0 x1. auto. 

    auto.

    inversion H2; subst.
    constructor 5 with (L); intros; auto.
    inversion H7.
    exists x.
    inversion H3.
    constructor. intros.

    apply H4.  apply term_ee_is_eqc in H1; auto.
    destruct H8.  destruct H8.  destruct H8.  destruct H9.
    pose proof ES_redex eqc u u' H1. 
    pose proof one_step_reduction (ES_contextual_closure eqc) u u' H11. 
    pose proof star_trans_reduction (ES_contextual_closure eqc) u u' H12. 
    apply eqC_sym in H13.
    pose proof star_closure_composition (ES_contextual_closure eqc) u' u x0 H13 H8.
    exists x0 x1. auto. 

    Qed.

Lemma red_lab_regular'_EE: red_lab_regular' (star_ctx_eqcc).
Proof.
    unfold red_lab_regular' in *.
    intros.
    induction H.
    reflexivity.
    induction H. apply red_lab_regular'_ctx_eqcc; auto.
    (* rewrite IHtrans_closure1; auto. *)
    (* Qed. *)
Admitted.

Lemma red_lab_regular'_lab_xi: red_lab_regular' lab_x_i.
Proof.
    Admitted.

Lemma red_lab_regular'_lab_sys_lx: red_lab_regular' lab_sys_lx.
Proof.
    Admitted.

Lemma red_lab_regular'_ctx_lab_sys_lx: red_lab_regular' (lab_contextual_closure lab_sys_lx).
Proof.
    Admitted.

Lemma red_lab_regular'_sys_Bx: red_lab_regular' sys_Bx.
Proof.
    Admitted.

(* ----------------------------------------------------- RED RENAME *)

Lemma red_rename_lab_ctx: forall R, red_rename R -> red_rename (lab_contextual_closure R).
Proof.
    Admitted.

Lemma red_rename_simpl_lab_ctx: forall R, red_rename R -> red_rename (simpl_lab_contextual_closure R).
Proof.
    Admitted.

Lemma red_rename_ext_lab_ctx: forall R, red_rename R -> red_rename (ext_lab_contextual_closure R).
Proof.
    Admitted.

Lemma red_rename_trans: forall R, red_rename R -> red_rename (trans_closure R).
Proof.
    Admitted.

Lemma red_rename_lab_eqc: red_rename lab_eqc.
Proof.
    Admitted.

Lemma red_rename_eqcc: red_rename eqcc.
Proof.
   unfold red_rename.
   intros.
   induction H1. 
   pose proof red_rename_eqc.  unfold red_rename in H2.
   constructor 1.
   apply H2 with x; auto.
   right. apply red_rename_lab_eqc with x; auto.
Qed.


Lemma red_rename_EE: red_rename star_ctx_eqcc.
Proof.
    (*unfold red_rename. intros. *)
    (*remember (t ^ x) as u.  remember (t' ^ x) as u'.*)
    (*induction H1; subst.*)
    (*apply open_var_inj in Hequ'.*)
    (*rewrite Hequ'; auto. constructor 1; auto. auto. auto.*)
    (*remember (t ^ x) as u.  remember (t' ^ x) as u'.*)
    (*generalize dependent t.*)
    (*generalize dependent t'.*)
    (*induction H1; intros; subst.*)
    (*pose proof (red_rename_simpl_lab_ctx red_rename_eqcc).*)
    (*constructor 2. constructor 1.*)
    (*apply (H2 x); auto.*)
    (*assert (lab_term u). admit.*)
    (*pose proof (@lab_close_var_spec u x H1).*)
    (*destruct H2 as [ u0 [ H3 [ H4 H5 ] ] ].*)
    (*apply star_closure_composition with (u0 ^ y).*)
    (*apply IHtrans_closure1; auto. *)
    (*apply IHtrans_closure2; auto. *)
    Admitted.



Lemma red_rename_lab_xi: red_rename lab_x_i.
Proof.
    Admitted.

Lemma red_rename_lab_xi_eq: red_rename lab_x_i_eq.
Proof.
    Admitted.

Lemma red_rename_lab_xe_eq: red_rename lab_x_e_eq.
Proof.
    Admitted.


Lemma red_rename_sys_Bx: red_rename sys_Bx.
Proof.
    Admitted.

Lemma red_rename_lab_sys_lx: red_rename lab_sys_lx.
Proof.
    Admitted.


Lemma red_rename_ctx_lab_sys_lx: red_rename (lab_contextual_closure lab_sys_lx).
Proof.
    Admitted.

Lemma red_rename_lab_lex: red_rename lab_lex.
Proof.
    Admitted.

(* ---------------------- *)

Lemma EE_lab_term : forall t t', lab_term t -> t =EE t' -> lab_term t'.
Proof.
    intros. apply red_lab_regular'_EE in H0. destruct H0; auto.

    Qed.

(* ------------------------------------------------------- star_lab clos *)

Lemma star_lab_closure_app_left: forall R t t' u, lab_term u -> star_closure (simpl_lab_contextual_closure R) t t' -> star_closure (simpl_lab_contextual_closure R) (pterm_app t u) (pterm_app t' u).
Proof.
    intros.
    induction H0.
    constructor.
    constructor 2.
    induction H0.
    constructor. constructor 2; auto.
    constructor 2 with (pterm_app u0 u); auto. 
    (* Qed. *)
Admitted.

Lemma star_lab_closure_app_right: forall R t t' u, lab_term u -> star_closure (simpl_lab_contextual_closure R) t t' -> star_closure (simpl_lab_contextual_closure R) (pterm_app u t) (pterm_app u t').
Proof.
    intros.
    induction H0.
    constructor.
    constructor 2.
    induction H0.
    constructor. constructor 3; auto.
    constructor 2 with (pterm_app u u0); auto.
    (* Qed. *)
Admitted.


Lemma trans_lab_closure_abs: forall R t t' L, lab_term (pterm_abs t) -> red_lab_regular' R -> red_rename R -> (forall y : VarSet.elt, y \notin L -> trans_closure (simpl_lab_contextual_closure R) (t ^ y) (t' ^ y)) -> trans_closure (simpl_lab_contextual_closure R) (pterm_abs t) (pterm_abs t').
Proof.
    intros R t t' L term_abs reg. intros.
    inversion term_abs; subst.
    pick_fresh z.
    apply notin_union in Fr. destruct Fr.
    apply notin_union in H1. destruct H1.
    apply notin_union in H1. destruct H1.
    pose proof (H0 z H1). clear H0.
    remember (t ^ z) as u.  remember (t' ^ z) as u'.
    generalize dependent t. generalize dependent t'.
    induction H6; intros; subst.
    constructor 1. constructor 4 with L. intros. 
    apply red_rename_simpl_lab_ctx in H. unfold red_rename in H. apply H with z; auto.
    assert (lab_term u). 
    apply red_lab_regular'_simpl_lab_ctx in reg.
    apply red_lab_regular'_trans in reg.
(*     apply reg in H6_. *)
(*     pose proof (H2 z H5). *)
(*     apply H6_; auto. *)

(*     pose proof (lab_close_var_spec z H0). *)
(*     destruct H6 as [u0 [eq1 [H7 H8] ] ]. subst. *)
(*     constructor 2 with (pterm_abs u0). *)
(*     apply IHtrans_closure1; auto. *)
(*     apply IHtrans_closure2; auto. *)
(*     inversion H7; subst. *)
(*     constructor 3 with x; auto. *)
(*     intros. *)
(*     apply lab_term_open_rename with z; auto. *)
    (* Qed. *)
Admitted.

Lemma star_lab_closure_abs: forall R t t' L, (forall y : VarSet.elt, y \notin L -> star_closure (simpl_lab_contextual_closure R) (t ^ y) (t' ^ y)) -> red_rename R -> lab_term (pterm_abs t) -> red_lab_regular' R -> star_closure (simpl_lab_contextual_closure R) (pterm_abs t) (pterm_abs t').
Proof.
    intros.
    pick_fresh z.
    apply notin_union in Fr. destruct Fr.
    apply notin_union in H3. destruct H3.
    pose proof (H z H3).
    remember (t ^ z) as u.  remember (t' ^ z) as u'.
    generalize dependent t. generalize dependent t'.
    induction H6; intros; subst.
    apply open_var_inj in Hequ; subst; auto. constructor 1; auto. 
    constructor 2. apply trans_lab_closure_abs with L; auto. intros.
    apply red_rename_trans with z; auto. apply red_rename_simpl_lab_ctx; auto.
Qed.


Lemma trans_lab_closure_outer_sub: forall R t t' v L, lab_term (t[v]) -> red_lab_regular' R -> red_rename R -> (forall y : VarSet.elt, y \notin L -> trans_closure (simpl_lab_contextual_closure R) (t ^ y) (t' ^ y)) -> trans_closure (simpl_lab_contextual_closure R) (t[v]) (t'[v]).
Proof.
    intros R t t' v L lab_term_tv reg. intros.
    inversion lab_term_tv; subst.
    pick_fresh z.
    apply notin_union in Fr. destruct Fr.
    apply notin_union in H1. destruct H1.
    apply notin_union in H1. destruct H1.
    apply notin_union in H1. destruct H1.
    pose proof (H0 z H1). clear H0.
    remember (t ^ z) as u.  remember (t' ^ z) as u'.
    generalize dependent t. generalize dependent t'.
    induction H8; intros; subst.
    constructor 1. constructor 5 with L; auto. intros. 
    apply red_rename_simpl_lab_ctx in H. unfold red_rename in H. apply H with z; auto.
    assert (lab_term u). 


    apply red_lab_regular'_simpl_lab_ctx in reg.
    apply red_lab_regular'_trans in reg.
(*     apply reg in H8_. *)
(*     pose proof (H3 z H7). *)
(*     apply H8_; auto. *)

(*     pose proof (lab_close_var_spec z H0). *)
(*     destruct H8 as [u0 [eq1 [H9 H10] ] ]. subst. *)
(*     constructor 2 with (u0[v]). *)
(*     apply IHtrans_closure1; auto. *)
(*     apply IHtrans_closure2; auto. *)
(*     inversion H9; subst. *)
(*     constructor 4 with x; auto. *)
(*     intros. *)
(*     apply lab_term_open_rename with z; auto. *)
    (* Qed. *)
Admitted.

Lemma star_lab_closure_outer_sub: forall R t t' v L, lab_term (t[v]) -> red_lab_regular' R -> (forall y : VarSet.elt, y \notin L -> star_closure (simpl_lab_contextual_closure R) (t ^ y) (t' ^ y)) -> red_rename R -> star_closure (simpl_lab_contextual_closure R) (t[v]) (t'[v]).
Proof.
    intros R t t' v L lab_term_tv reg. intros.
    inversion lab_term_tv; subst.
    pick_fresh z.
    apply notin_union in Fr. destruct Fr.
    apply notin_union in H1. destruct H1.
    apply notin_union in H1. destruct H1.
    apply notin_union in H1. destruct H1.
    pose proof (H z H1).
    remember (t ^ z) as u.  remember (t' ^ z) as u'.
    generalize dependent t. generalize dependent t'.
    induction H8; intros; subst.
    apply open_var_inj in Hequ; subst; auto. constructor 1; auto. 
    constructor 2. apply trans_lab_closure_outer_sub with L; auto. intros.
    apply red_rename_trans with z; auto. apply red_rename_simpl_lab_ctx; auto.
Qed.

Lemma star_lab_closure_inner_sub: forall R t u u', lab_body t -> star_closure (simpl_lab_contextual_closure R) u u' -> star_closure (simpl_lab_contextual_closure R) (t[u]) (t[u']).
Proof.
    intros.
    induction H0.
    constructor.
    constructor 2.
    induction H0.
    constructor. constructor 6; auto.
(*     constructor 2 with (t[u]); auto.  *)
    (* Qed. *)
Admitted.

Lemma trans_lab_closure_outer_lsub: forall R t t' v L, lab_term (t[[v]]) -> red_lab_regular' R -> red_rename R -> (forall y : VarSet.elt, y \notin L -> trans_closure (simpl_lab_contextual_closure R) (t ^ y) (t' ^ y)) -> trans_closure (simpl_lab_contextual_closure R) (t[[v]]) (t'[[v]]).
Proof.
    intros R t t' v L lab_term_tv reg. intros.
    inversion lab_term_tv; subst.
    pick_fresh z.

    apply notin_union in Fr. destruct Fr.
    apply notin_union in H1. destruct H1.
    apply notin_union in H1. destruct H1.
    apply notin_union in H1. destruct H1.
    pose proof (H0 z H1). clear H0.
    remember (t ^ z) as u.  remember (t' ^ z) as u'.
    generalize dependent t. generalize dependent t'.
    induction H9; intros; subst.
    constructor 1. constructor 7 with L; auto. intros. 
    apply red_rename_simpl_lab_ctx in H. unfold red_rename in H. apply H with z; auto.
    assert (lab_term u). 

    apply red_lab_regular'_simpl_lab_ctx in reg.
    apply red_lab_regular'_trans in reg.
(*     apply reg in H9_. *)
(*     pose proof (H3 z H8). *)
(*     apply H9_; auto. *)

(*     pose proof (lab_close_var_spec z H0). *)
(*     destruct H9 as [u0 [eq1 [H9 H10] ] ]. subst. *)
(*     constructor 2 with (u0[[v]]). *)
(*     apply IHtrans_closure1; auto. *)
(*     apply IHtrans_closure2; auto. *)

(*     inversion H9; subst. *)
(*     constructor 5 with x; auto. *)
(*     intros. *)
(*     apply lab_term_open_rename with z; auto. *)

(* Qed. *)
Admitted.

Lemma star_lab_closure_outer_lsub: forall R t t' v L, lab_term (t[[v]]) -> red_lab_regular' R -> (forall y : VarSet.elt, y \notin L -> star_closure (simpl_lab_contextual_closure R) (t ^ y) (t' ^ y)) -> red_rename R -> star_closure (simpl_lab_contextual_closure R) (t[[v]]) (t'[[v]]).
Proof.
    intros R t t' v L lab_term_tv reg. intros.
    inversion lab_term_tv; subst.
    pick_fresh z.
    apply notin_union in Fr. destruct Fr.
    apply notin_union in H1. destruct H1.
    apply notin_union in H1. destruct H1.
    apply notin_union in H1. destruct H1.
    pose proof (H z H1).
    remember (t ^ z) as u.  remember (t' ^ z) as u'.
    generalize dependent t. generalize dependent t'.
    induction H9; intros; subst.
    apply open_var_inj in Hequ; subst; auto. constructor 1; auto. 
    constructor 2. apply trans_lab_closure_outer_lsub with L; auto. intros.
    apply red_rename_trans with z; auto. apply red_rename_simpl_lab_ctx; auto.
Qed.

(* -------------------------------------------------------------  EE clos *)

Lemma EE_clos_app_left: forall R t t' u, lab_term u -> ((lab_EE_ctx_red R) t t') -> ((lab_EE_ctx_red R) (pterm_app t u) (pterm_app t' u)).
Proof.
    intros.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H1.
    exists (pterm_app x u) (pterm_app x0 u).
    split. apply star_lab_closure_app_left; auto.
    split*. constructor 2; auto.
    apply star_lab_closure_app_left; auto.

Qed.

Lemma EE_clos_app_right: forall R t t' u, lab_term u -> ((lab_EE_ctx_red R) t t') -> ((lab_EE_ctx_red R) (pterm_app u t) (pterm_app u t')).
Proof.
    intros.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H1.
    exists (pterm_app u x) (pterm_app u x0).
    split. apply star_lab_closure_app_right; auto.
    split*. constructor 3; auto.
    apply star_lab_closure_app_right; auto.

Qed.

Lemma EE_clos_abs: forall x x0 L, (lab_term (pterm_abs x0)) -> (forall y : VarSet.elt, y \notin L -> lab_lex (x0 ^ y) (x ^ y)) -> lab_lex (pterm_abs x0) (pterm_abs x).
Proof.
    intros x x0 L lab_term_abs H.
    inversion lab_term_abs; subst.
    pose proof H1 as trm. clear H1.
    pick_fresh z.
    apply notin_union in Fr. destruct Fr.
    apply notin_union in H0. destruct H0.
    apply notin_union in H0. destruct H0.
    pose proof (H z H0).
    destruct H4.  destruct H4.  destruct H4.  destruct H5.
    pose proof H4;  apply (term_EE_open_fv ) in H4; auto.
    pose proof H6;  apply star_ctx_eqcc_sym in H6;  apply (term_EE_open_fv ) in H6; auto.
    destruct H4 as [ x3 [ eq  z_fv_x3  ] ]; subst. 
    destruct H6 as [ x1 [ eq  z_fv_x1  ] ]; subst. 
    exists (pterm_abs x3) (pterm_abs x1).
    split. apply star_lab_closure_abs with (L := L); auto.
    intros. apply red_rename_EE with z; auto.
    exact red_rename_eqcc.
    exact red_lab_regular'_eqcc.
    split. constructor 4 with (L \u fv(x3) \u fv(x1)). intros.
    (*apply red_rename_lab_ctx in rename_R.*)
    apply notin_union in H4. destruct H4.
    apply notin_union in H4. destruct H4.
    pose proof red_rename_ctx_lab_sys_lx.
    unfold red_rename in H9. apply H10 with z; auto.

    apply star_lab_closure_abs with L.
    intros.  apply red_rename_EE with z; auto. exact red_rename_eqcc.
    apply red_lab_regular'_ctx_lab_sys_lx in H5.
    constructor 3 with L; intros.
    apply lab_term_open_rename with z.
    rewrite <- H5. apply EE_lab_term with (x0 ^ z).
    apply trm; auto. auto.
    exact red_lab_regular'_eqcc.
    apply red_lab_regular'_ctx_lab_sys_lx in H5.
    apply H5.  apply EE_lab_term with (x0 ^ z); auto.
    apply EE_lab_term with (x0 ^ z); auto.
    
Qed.

Lemma EE_clos_outer_sub: forall t t' u L, lab_term (t[u]) -> (forall y : VarSet.elt, y \notin L -> lab_lex (t ^ y) (t' ^ y)) -> lab_lex (t[u]) (t'[u]).
Proof.
    intros x x0 u L lab_term_tu H.
    inversion lab_term_tu; subst.
    pick_fresh z.
    apply notin_union in Fr. destruct Fr.
    apply notin_union in H0. destruct H0.
    apply notin_union in H0; destruct H0.
    apply notin_union in H0; destruct H0.
    pose proof (H z H0).
    destruct H7.  destruct H7.  destruct H7.  destruct H8.
    pose proof H7;  apply (term_EE_open_fv ) in H7; auto.
    pose proof H9;  apply star_ctx_eqcc_sym in H9;  apply (term_EE_open_fv ) in H9; auto.
    destruct H7 as [ x3 [ eq  z_fv_x3  ] ]; subst. 
    destruct H9 as [ x1 [ eq  z_fv_x1  ] ]; subst. 
    exists (x3[u]) (x1[u]).
    split. 

    apply star_lab_closure_outer_sub with (L := L); auto.
    exact red_lab_regular'_eqcc.
    intros. apply red_rename_EE with z; auto.
    exact red_rename_eqcc.

    split. constructor 5 with (L \u fv(x3) \u fv(x1)); auto. intros.
    apply notin_union in H7. destruct H7.
    apply notin_union in H7. destruct H7.
    pose proof red_rename_ctx_lab_sys_lx.
    unfold red_rename in H13. apply H13 with z; auto.

    apply star_lab_closure_outer_sub with (L := L); auto.
    apply red_lab_regular'_ctx_lab_sys_lx in H8.
    constructor 4 with L; intros; auto.
    apply lab_term_open_rename with z; auto.
    rewrite <- H8.
    apply EE_lab_term with (x ^ z); auto.

    exact red_lab_regular'_eqcc.
    intros. apply red_rename_EE with z; auto. 
    exact red_rename_eqcc.


    apply red_lab_regular'_ctx_lab_sys_lx in H8.
    rewrite <- H8. apply EE_lab_term with (x ^ z).
    apply H2; auto. auto.
    apply EE_lab_term with (x ^ z).
    apply H2; auto. auto.
Qed.

Lemma EE_clos_inner_sub: forall R t u u', lab_body t -> (lab_EE_ctx_red R) (u) (u') -> (lab_EE_ctx_red R) (t[u]) (t[u']).
Proof.
    intros.
    destruct H0.  destruct H0.  destruct H0.  destruct H1.
    exists (t[x]) (t[x0]).
    split. 
    apply star_lab_closure_inner_sub; auto.
    split*. constructor 6; auto.
    apply star_lab_closure_inner_sub; auto.
Qed.

Lemma EE_clos_outer_lsub: forall t t' u L, lab_term (t[[u]]) -> (forall y : VarSet.elt, y \notin L -> lab_lex (t ^ y) (t' ^ y)) -> lab_lex (t[[u]]) (t'[[u]]).
Proof.
    intros x x0 u L term_tu H.
    inversion term_tu; subst.
    pick_fresh z.
    apply notin_union in Fr. destruct Fr.
    apply notin_union in H0. destruct H0.
    apply notin_union in H0; destruct H0.
    apply notin_union in H0; destruct H0.
    pose proof (H z H0).
    destruct H8.  destruct H8.  destruct H8.  destruct H9.
    pose proof H8;  apply (term_EE_open_fv ) in H8; auto.
    pose proof H10;  apply star_ctx_eqcc_sym in H10;  apply (term_EE_open_fv ) in H10; auto.
    destruct H8 as [ x3 [ eq  z_fv_x3  ] ]; subst. 
    destruct H10 as [ x1 [ eq  z_fv_x1  ] ]; subst. 
    exists (x3[[u]]) (x1[[u]]).
    split. 

    apply star_lab_closure_outer_lsub with (L := L); auto.
    exact red_lab_regular'_eqcc.
    intros. apply red_rename_EE with z; auto.
    exact red_rename_eqcc.

    split. constructor 7 with (L \u fv(x3) \u fv(x1)); auto. intros.
    apply notin_union in H8. destruct H8.
    apply notin_union in H8. destruct H8.
    pose proof red_rename_ctx_lab_sys_lx.
    unfold red_rename in H14. apply H14 with z; auto.

    apply star_lab_closure_outer_lsub with (L := L); auto.
    apply red_lab_regular'_ctx_lab_sys_lx in H9.
    constructor 5 with L; intros; auto.
    apply lab_term_open_rename with z; auto.
    rewrite <- H9.
    apply EE_lab_term with (x ^ z); auto.
    exact red_lab_regular'_eqcc.
    intros. apply red_rename_EE with z; auto.
    exact red_rename_eqcc.

    apply red_lab_regular'_ctx_lab_sys_lx in H9.
    rewrite <- H9. apply EE_lab_term with (x ^ z).
    apply H2; auto. auto.
    apply EE_lab_term with (x ^ z).
    apply H2; auto. auto.
Qed.


(* -------------------------------------------------------------  EE ext_clos *)

Lemma EE_ext_clos_app_left: forall R t t' u, lab_term u -> ((ext_lab_EE_ctx_red R) t t') -> ((ext_lab_EE_ctx_red R) (pterm_app t u) (pterm_app t' u)).
Proof.
    intros.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H1.
    exists (pterm_app x u) (pterm_app x0 u).
    split. apply star_lab_closure_app_left; auto.
    split*. constructor 2; auto.
    apply star_lab_closure_app_left; auto.

Qed.

Lemma EE_ext_clos_app_right: forall R t t' u, lab_term u -> ((ext_lab_EE_ctx_red R) t t') -> ((ext_lab_EE_ctx_red R) (pterm_app u t) (pterm_app u t')).
Proof.
    intros.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H1.
    exists (pterm_app u x) (pterm_app u x0).
    split. apply star_lab_closure_app_right; auto.
    split*. constructor 3; auto.
    apply star_lab_closure_app_right; auto.

Qed.

Lemma EE_ext_clos_abs: forall R x x0 L, red_rename R -> red_lab_regular' R -> lab_term (pterm_abs x0) -> (forall y : VarSet.elt, y \notin L -> (ext_lab_EE_ctx_red R) (x0 ^ y) (x ^ y)) -> (ext_lab_EE_ctx_red R) (pterm_abs x0) (pterm_abs x).
Proof.
    intros R x x0 L rename_R reg_R term_abs H.
    inversion term_abs; subst.

    pick_fresh z.
    apply notin_union in Fr. destruct Fr.
    apply notin_union in H0. destruct H0.
    apply notin_union in H0. destruct H0.
    pose proof (H z H0).
    destruct H5.  destruct H5.  destruct H5.  destruct H6.
    pose proof H5;  apply (term_EE_open_fv ) in H5; auto.
    pose proof H7;  apply star_ctx_eqcc_sym in H7;  apply (term_EE_open_fv ) in H7; auto.
    destruct H5 as [ x3 [ eq  z_fv_x3  ] ]; subst. 
    destruct H7 as [ x1 [ eq  z_fv_x1  ] ]; subst. 
    exists (pterm_abs x3) (pterm_abs x1).
    split. apply star_lab_closure_abs with (L := L); auto.
    intros. apply red_rename_EE with z; auto.
    exact red_rename_eqcc. exact red_lab_regular'_eqcc.
    split. constructor 4 with (L \u fv(x3) \u fv(x1)). intros.
    apply red_rename_ext_lab_ctx in rename_R.
    apply notin_union in H5. destruct H5.
    apply notin_union in H5. destruct H5.
    unfold red_rename in rename_R. apply rename_R with z; auto.

    apply star_lab_closure_abs with L.
    intros.  apply red_rename_EE with z; auto. exact red_rename_eqcc.

    apply red_lab_regular'_ext_lab_ctx in reg_R.
    unfold red_lab_regular' in reg_R. apply reg_R in H6. 
    constructor 3 with L. intros.
    apply lab_term_open_rename with z.
    rewrite <- H6. apply EE_lab_term with (x0 ^ z).
    apply H1; auto. auto.
    exact red_lab_regular'_eqcc.
    apply red_lab_regular'_ext_lab_ctx in reg_R.
    apply reg_R in H6.
    rewrite <- H6. apply EE_lab_term with (x0 ^ z).
    apply H1; auto. auto.

    apply EE_lab_term with (x0 ^ z); auto.
Qed.

Lemma EE_ext_clos_outer_sub: forall R t t' u L, lab_term (t[u]) -> red_rename R -> red_lab_regular' R -> (forall y : VarSet.elt, y \notin L -> (ext_lab_EE_ctx_red R) (t ^ y) (t' ^ y)) -> (ext_lab_EE_ctx_red R) (t[u]) (t'[u]).
Proof.
    intros R x x0 u L lab_term_tu rename_R reg_R H.
    inversion lab_term_tu; subst.

    pick_fresh z.
    apply notin_union in Fr. destruct Fr.
    apply notin_union in H0. destruct H0.
    apply notin_union in H0; destruct H0.
    apply notin_union in H0; destruct H0.
    pose proof (H z H0).
    destruct H7.  destruct H7.  destruct H7.  destruct H8.
    pose proof H7;  apply (term_EE_open_fv ) in H7; auto.
    pose proof H9;  apply star_ctx_eqcc_sym in H9;  apply (term_EE_open_fv ) in H9; auto.
    destruct H7 as [ x3 [ eq  z_fv_x3  ] ]; subst. 
    destruct H9 as [ x1 [ eq  z_fv_x1  ] ]; subst. 
    exists (x3[u]) (x1[u]).
    split. 

    apply star_lab_closure_outer_sub with (L := L); auto.
    intros. exact red_lab_regular'_eqcc. 
    intros.  apply red_rename_EE with z; auto. exact red_rename_eqcc.

    split. constructor 5 with (L \u fv(x3) \u fv(x1)); auto. intros.
    apply red_rename_ext_lab_ctx in rename_R.
    apply notin_union in H7. destruct H7.
    apply notin_union in H7. destruct H7.
    unfold red_rename in rename_R. apply rename_R with z; auto.

    apply star_lab_closure_outer_sub with (L := L); auto.
    constructor 4 with L; auto.
    intros. apply lab_term_open_rename with z.
    apply red_lab_regular'_ext_lab_ctx in reg_R.
    apply reg_R in H8.

    rewrite <- H8. apply EE_lab_term with (x ^ z).
    apply H2; auto. auto. exact red_lab_regular'_eqcc.

    intros. apply red_rename_EE with z; auto. exact red_rename_eqcc.


    apply red_lab_regular'_ext_lab_ctx in reg_R.
    unfold red_lab_regular' in reg_R. apply reg_R in H8. 
    rewrite <- H8. apply EE_lab_term with (x ^ z).
    apply H2; auto. auto.

    apply EE_lab_term with (x ^ z).
    apply H2; auto. auto.
Qed.

Lemma EE_ext_clos_inner_sub: forall R t u u', lab_body t -> (ext_lab_EE_ctx_red R) (u) (u') -> (ext_lab_EE_ctx_red R) (t[u]) (t[u']).
Proof.
    intros.
    destruct H0.  destruct H0.  destruct H0.  destruct H1.
    exists (t[x]) (t[x0]).
    split. 
    apply star_lab_closure_inner_sub; auto.
    split*. constructor 6; auto.
    apply star_lab_closure_inner_sub; auto.
Qed.

Lemma EE_ext_clos_outer_lsub: forall R t t' u L, lab_term (t[[u]]) -> (*SN R u ->*) red_rename R -> red_lab_regular' R -> (forall y : VarSet.elt, y \notin L -> (ext_lab_EE_ctx_red R) (t ^ y) (t' ^ y)) -> (ext_lab_EE_ctx_red R) (t[[u]]) (t'[[u]]).
Proof.
    intros R x x0 u L lab_term_tu rename_R reg_R H.
    inversion lab_term_tu; subst.
    pick_fresh z.
    apply notin_union in Fr. destruct Fr.
    apply notin_union in H0. destruct H0.
    apply notin_union in H0; destruct H0.
    apply notin_union in H0; destruct H0.
    pose proof (H z H0).
    destruct H8.  destruct H8.  destruct H8.  destruct H9.
    pose proof H8;  apply (term_EE_open_fv ) in H8; auto.
    pose proof H10;  apply star_ctx_eqcc_sym in H10;  apply (term_EE_open_fv ) in H10; auto.
    destruct H8 as [ x3 [ eq  z_fv_x3  ] ]; subst. 
    destruct H10 as [ x1 [ eq  z_fv_x1  ] ]; subst. 
    exists (x3[[u]]) (x1[[u]]).
    split. 

    apply star_lab_closure_outer_lsub with (L := L); auto.
    intros. exact red_lab_regular'_eqcc.
    intros. apply red_rename_EE with z; auto.
    exact red_rename_eqcc.

    split. constructor 7 with (L \u fv(x3) \u fv(x1)); auto. intros.
    apply red_rename_ext_lab_ctx in rename_R.
    apply notin_union in H8. destruct H8.
    apply notin_union in H8. destruct H8.
    unfold red_rename in rename_R. apply rename_R with z; auto.

    apply star_lab_closure_outer_lsub with (L := L); auto.
    constructor 5 with L; auto.
    intros. apply lab_term_open_rename with z.
    apply red_lab_regular'_ext_lab_ctx in reg_R.
    apply reg_R in H9.
    rewrite <- H9. apply EE_lab_term with (x ^ z).
    apply H2; auto. auto. exact red_lab_regular'_eqcc.

    intros. apply red_rename_EE with z; auto. exact red_rename_eqcc.

    apply red_lab_regular'_ext_lab_ctx in reg_R.
    apply reg_R in H9.
    rewrite <- H9. apply EE_lab_term with (x ^ z).
    apply H2; auto. auto. 

    apply EE_lab_term with (x ^ z).
    apply H2; auto. auto. 
Qed.

(* ------------------- *)



Lemma lab_sys_lx_term_is_sys_Bx : forall t t', term t -> lab_sys_lx t t' -> sys_Bx t t'.
Proof.
    intros.
    induction H0.
    constructor; auto.
    constructor 2; auto.
    inversion H0; subst; inversion H.
    Qed.


(* ------------------------------------------------------------  EE presv reductions *)

Lemma EE_presv_ie: forall t t' u u', t =EE u -> u' =EE t' -> ((u -->[lx_i] u' \/ u -->[lx_e] u') -> (t -->[lx_i] t' \/ t -->[lx_e] t')).
Proof.
    intros.

    destruct H1.  destruct H1.  destruct H1.  destruct H1. destruct H2.
    left.  
    exists x x0.
    split*.
    apply star_closure_composition with u; auto.
    split*.
    apply star_closure_composition with u'; auto.

    destruct H1.  destruct H1.  destruct H1.  destruct H2.
    right.  
    exists x x0.
    split*.
    apply star_ctx_eqcc_sym in H.
    apply star_ctx_eqcc_sym in H.
    apply star_closure_composition with u; auto.
    split*.
    apply star_closure_composition with u'; auto.
Qed.

Lemma EE_presv_lab_lex: forall t t' u u', t =EE u -> u' =EE t' -> ((u -->[lex] u') -> (t -->[lex] t')).
Proof.
    intros.
    destruct H1.
    destruct H1.
    destruct H1.
    destruct H2.
    exists x x0.
    split. apply star_closure_composition with u; auto.
    split*. apply star_closure_composition with u'; auto.
Qed.

(* ------------------------------------------------------------- IE <-> LEX (um passo) *)

Lemma lab_ex_impl_i_e: forall t t', lab_term t -> t -->[lex] t' -> (t -->[lx_i] t' \/ t -->[lx_e] t').
Proof.
    intros.
    destruct H0.  destruct H0. destruct H0.  destruct H1.
    generalize dependent t.
    generalize dependent t'.
    induction H1; intros.

    (* Base *)
    apply lab_sys_x_i_e with t s; auto. apply EE_lab_term with t0; auto*.

    (* app_left *)
    apply EE_presv_ie with (u := (pterm_app t u)) (u' := (pterm_app t' u)); auto.
    assert  (t-->[lx_i]t' \/ t-->[lx_e]t').
    apply IHlab_contextual_closure; auto. constructor 1; auto. 
    pose proof (EE_lab_term H0 H3); auto. inversion H4; subst; auto.
    constructor 1; auto.
    destruct H4. 
    left. apply EE_ext_clos_app_left. 
    pose proof (EE_lab_term H0 H3); auto.  auto.
    right. apply EE_ext_clos_app_left. 
    pose proof (EE_lab_term H0 H3); auto.  auto.

    (* app_right *)
    apply EE_presv_ie with (u := (pterm_app t u)) (u' := (pterm_app t u')); auto.
    assert  (u-->[lx_i]u' \/ u-->[lx_e]u').
    apply IHlab_contextual_closure; auto. constructor 1; auto. 
    pose proof (EE_lab_term H0 H3); auto. inversion H4; subst; auto.
    constructor 1; auto.
    destruct H4. 
    left. apply EE_ext_clos_app_right. 
    pose proof (EE_lab_term H0 H3); auto.  auto.
    right. apply EE_ext_clos_app_right. 
    pose proof (EE_lab_term H0 H3); auto.  auto.

    (* abs *)
    apply EE_presv_ie with (u := pterm_abs t) (u' := pterm_abs t'); auto.
    pose proof (EE_lab_term H1 H3); auto. inversion H4; subst; auto. 
    pick_fresh z.
    assert  (t^z-->[lx_i]t'^z \/ t^z-->[lx_e]t'^z).
    apply H0 with z; auto. constructor 1; auto. 
    constructor 1; auto. 
    apply notin_union in Fr; destruct Fr.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    destruct H5.
    left. apply EE_ext_clos_abs with L. exact red_rename_lab_xi. 
    exact red_lab_regular'_lab_xi.
    apply EE_lab_term with t0; auto.


    intros. 
    pose proof red_rename_lab_xi_eq. apply H14 with z; auto.
    right. apply EE_ext_clos_abs with L. exact red_rename_sys_Bx. exact red_lab_regular'_sys_Bx.
    apply EE_lab_term with t0; auto.
    intros. pose proof red_rename_lab_xe_eq.
    unfold red_rename in H14.
    apply H14 with z; auto.

    (* outer sub *)
    apply EE_presv_ie with (u := t[u]) (u' := t'[u]); auto.
    pose proof (EE_lab_term H3 H4); auto. inversion H5; subst; auto. 
    pick_fresh z.
    assert  (t^z-->[lx_i]t'^z \/ t^z-->[lx_e]t'^z).
    apply H1 with z; auto. constructor 1; auto. constructor 1; auto. 
    apply notin_union in Fr; destruct Fr.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    destruct H6.
    left. apply EE_ext_clos_outer_sub with L; auto.
    exact red_rename_lab_xi. exact red_lab_regular'_lab_xi.
    intros.
    pose proof red_rename_lab_xi_eq.  apply H17 with z; auto.
    right. apply EE_ext_clos_outer_sub with L; auto.
    exact red_rename_sys_Bx. exact red_lab_regular'_sys_Bx.
    intros. pose proof red_rename_lab_xe_eq. apply H17 with z; auto.

    (* inner sub *)
    apply EE_presv_ie with (u := t[u]) (u' := t[u']); auto.
    assert (u' =EE u'). constructor 1; auto.
    assert (u =EE u). constructor 1; auto.
    apply EE_lab_term in H3. inversion H3; subst.
    pose proof (IHlab_contextual_closure u' H4 u H9 H5).
    destruct H6. 
    left. apply EE_ext_clos_inner_sub; auto.
    right. apply EE_ext_clos_inner_sub; auto.
    auto.

    (* outer lsub *)
    apply EE_presv_ie with (u := t[[u]]) (u' := t'[[u]]); auto.
    pose proof (EE_lab_term H3 H4); auto. inversion H5; subst; auto. 
    pick_fresh z.
    assert  (t^z-->[lx_i]t'^z \/ t^z-->[lx_e]t'^z).
    apply H1 with z; auto. constructor 1; auto. constructor 1; auto. 
    apply notin_union in Fr; destruct Fr.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    destruct H6.
    left. apply EE_ext_clos_outer_lsub with L.
    apply EE_lab_term with t0; auto.
    exact red_rename_lab_xi. exact red_lab_regular'_lab_xi.
    intros.
    pose proof red_rename_lab_xi_eq.  apply H18 with z; auto.
    right. apply EE_ext_clos_outer_lsub with L.
    apply EE_lab_term with t0; auto.
    exact red_rename_sys_Bx. exact red_lab_regular'_sys_Bx.
    intros. pose proof red_rename_lab_xe_eq. apply H18 with z; auto.



    (* inner lsub *)
    left. exists (t [[u]]) (t [[u']]). split. auto.
    split*. 
    apply EE_lab_term with t0 (t [[u]]) in H5.
    inversion H3; subst.
    apply lab_sys_lx_term_is_sys_Bx with u u' in H0; auto.
    (*inversion H5; subst.*)
    constructor 1.  constructor 1. auto. auto.
    constructor 1.  constructor 1. auto. 
    apply lab_sys_lx_term_is_sys_Bx with u u' in H0; auto.
    auto.

Qed.

Lemma lab_ie_impl_ex: forall t t', lab_term t -> (t -->[lx_i] t' \/ t -->[lx_e] t') -> t -->[lex] t'.
Proof.
    intros. destruct H0; destruct H0; destruct H0; destruct H0; destruct H1; generalize dependent t; generalize dependent t'; induction H1; intros.

    (*[> ------------------  Interna <]*)
    (*[> Base <]*)

    exists t s.
    split*. split*. 
    inversion H; subst. 
    inversion H3; subst. constructor 8; auto. exists L; auto.
    inversion H4; subst.
    constructor 1; auto.  constructor 2; subst. auto. 
    constructor 1; auto. constructor 3; auto.

    (* app_left *)
    apply EE_presv_lab_lex with (u := (pterm_app t u)) (u' := (pterm_app t' u)); auto.
    apply EE_clos_app_left. 
    pose proof (EE_lab_term H0 H3); auto. 
    apply IHext_lab_contextual_closure; auto. constructor 1; auto. 
    pose proof (EE_lab_term H0 H3); auto. inversion H4; subst; auto. 
    constructor 1; auto.

    (* app_right *)
    apply EE_presv_lab_lex with (u := (pterm_app t u)) (u' := (pterm_app t u')); auto.
    apply EE_clos_app_right.  pose proof (EE_lab_term H0 H3); auto. 
    apply IHext_lab_contextual_closure; auto. constructor 1; auto. 
    pose proof (EE_lab_term H0 H3); auto. inversion H4; subst; auto. 
    constructor 1; auto.

    (* abs *)
    apply EE_presv_lab_lex with (u := pterm_abs t) (u' := pterm_abs t'); auto.
    pose proof (EE_lab_term H1 H3); auto. inversion H4; subst; auto. 
    pick_fresh z.
    assert  (t^z-->[lex]t'^z).
    apply H0 with z; auto. constructor 1; auto. constructor 1; auto. 
    apply notin_union in Fr; destruct Fr.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply EE_clos_abs with L.
    apply EE_lab_term with t0; auto.
    intros. pose proof red_rename_lab_lex. 
    intros. apply red_rename_lab_lex with z; auto.

    (* outer sub *)
    apply EE_presv_lab_lex with (u := t[u]) (u' := t'[u]); auto.
    pose proof (EE_lab_term H3 H4); auto. inversion H5; subst; auto. 
    pick_fresh z.
    assert  (t^z-->[lex]t'^z).
    apply H1 with z; auto. constructor 1; auto. constructor 1; auto. 
    apply notin_union in Fr; destruct Fr.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply EE_clos_outer_sub with L; auto.
    intros. apply red_rename_lab_lex with z; auto.

    (* inner sub *)
    apply EE_presv_lab_lex with (u := t[u]) (u' := t[u']); auto.
    assert (u' =EE u'). constructor 1; auto.
    assert (u =EE u). constructor 1; auto.
    apply EE_lab_term in H3. inversion H3; subst.
    pose proof (IHext_lab_contextual_closure u' H4 u H9 H5).
    apply EE_clos_inner_sub; auto.
    auto.


    (* outer lsub *)
    apply EE_presv_lab_lex with (u := t[[u]]) (u' := t'[[u]]); auto.
    pose proof (EE_lab_term H3 H4); auto. inversion H5; subst; auto. 
    pick_fresh z.
    assert  (t^z-->[lex]t'^z).
    apply H1 with z; auto. constructor 1; auto. constructor 1; auto. 
    apply notin_union in Fr; destruct Fr.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply EE_clos_outer_lsub with L; auto.
    intros. apply red_rename_lab_lex with z; auto.

    (*[> -------------------------------------------------------  Externa <]*)
    (*[> Base <]*)
    exists (t) (s).  split*. split*.  
    inversion H; subst. 
    constructor 1.  constructor 1; auto.  
    constructor 1.  constructor 2; auto.  

    (* app_left *)
    apply EE_presv_lab_lex with (u := (pterm_app t u)) (u' := (pterm_app t' u)); auto.
    apply EE_clos_app_left. 
    pose proof (EE_lab_term H0 H3); auto. 
    apply IHext_lab_contextual_closure; auto. constructor 1; auto. 
    pose proof (EE_lab_term H0 H3); auto. inversion H4; subst; auto. 
    constructor 1; auto.

    (* app_right *)
    apply EE_presv_lab_lex with (u := (pterm_app t u)) (u' := (pterm_app t u')); auto.
    apply EE_clos_app_right. 
    pose proof (EE_lab_term H0 H3); auto. 
    apply IHext_lab_contextual_closure; auto. constructor 1; auto. 
    pose proof (EE_lab_term H0 H3); auto. inversion H4; subst; auto. 
    constructor 1; auto.

    (* abs *)
    apply EE_presv_lab_lex with (u := pterm_abs t) (u' := pterm_abs t'); auto.
    pose proof (EE_lab_term H1 H3); auto. inversion H4; subst; auto. 
    pick_fresh z.
    assert  (t^z-->[lex]t'^z).
    apply H0 with z; auto. constructor 1; auto. constructor 1; auto. 
    apply notin_union in Fr; destruct Fr.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply EE_clos_abs with L.
    apply EE_lab_term with t0; auto.
    intros. pose proof red_rename_lab_lex. 
    intros. apply red_rename_lab_lex with z; auto.

    (* outer sub *)
    apply EE_presv_lab_lex with (u := t[u]) (u' := t'[u]); auto.
    pose proof (EE_lab_term H3 H4); auto. inversion H5; subst; auto. 
    pick_fresh z.
    assert  (t^z-->[lex]t'^z).
    apply H1 with z; auto. constructor 1; auto. constructor 1; auto. 
    apply notin_union in Fr; destruct Fr.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply EE_clos_outer_sub with L; auto.
    intros. apply red_rename_lab_lex with z; auto.

    (* inner sub *)
    apply EE_presv_lab_lex with (u := t[u]) (u' := t[u']); auto.
    assert (u' =EE u'). constructor 1; auto.
    assert (u =EE u). constructor 1; auto.
    apply EE_lab_term in H3. inversion H3; subst.
    pose proof (IHext_lab_contextual_closure u' H4 u H9 H5).
    apply EE_clos_inner_sub; auto.
    auto.


    (* outer lsub *)
    apply EE_presv_lab_lex with (u := t[[u]]) (u' := t'[[u]]); auto.
    pose proof (EE_lab_term H3 H4); auto. inversion H5; subst; auto. 
    pick_fresh z.
    assert  (t^z-->[lex]t'^z).
    apply H1 with z; auto. constructor 1; auto. constructor 1; auto. 
    apply notin_union in Fr; destruct Fr.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply EE_clos_outer_lsub with L; auto.
    intros. apply red_rename_lab_lex with z; auto.
Qed.

Theorem lab_ex_eq_i_e: forall t t', lab_term t -> (t -->[lex] t' <-> (t -->[lx_i] t' \/ t -->[lx_e] t')).
Proof.
    split.
    intros; apply lab_ex_impl_i_e; auto.
    intros; apply lab_ie_impl_ex; auto.
Qed.

