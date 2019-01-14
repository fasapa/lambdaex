Set Implicit Arguments.
Require Import Arith Metatheory Lambda_Ex Lambda.
Require Import Rewriting LambdaES_Infra.
Require Import LambdaES_Defs.

Require NormalizationTheory. Module NT := NormalizationTheory.

(* LambdaES_Def *)



Inductive SN_ind (n : nat) (R : pterm -> pterm -> Prop) (t : pterm) : Prop :=
 | SN_intro : (forall t', R t t' -> exists k, k < n /\ SN_ind k R t') -> SN_ind n R t.

Lemma SN_ind_Succ : forall R t n, SN_ind n R t -> SN_ind (S n) R t.
Proof.
 intros. constructor. intros t' Ht. inversion H. 
 specialize H0 with t'. apply H0 in Ht. inversion Ht. 
 destruct H1 as [H1 H2]. exists x. split.
 - omega.
 - assumption. 
Qed.

Definition SN (R : pterm -> pterm -> Prop) (t : pterm) := 
                                             exists n, SN_ind n R t.

Lemma SN_Red : forall R t u, SN R t -> R t u -> SN R u.
Proof.
 intros R t u Ht Hr. inversion Ht. inversion H. apply H0 in Hr. 
 inversion Hr. destruct H1 as [H1 H2]. exists x0. assumption.
Qed.



(* =================================================================

   Relacoes entre SN e NT.SN: falta provar se SN e patriarcal: 
   necessidade de garantir um numero finito de redutos a partir 
   de um termo t em lex, para do MAX entre os n' de cada t' 
   obtermos um n para t.

====================================================================
Lemma SNisPat : NT.patriarchal lex (SN lex).
Proof.
 unfold NT.patriarchal. intros.
 
Theorem SNindP {R: pterm -> pterm -> Prop} {P: pterm -> Prop}
: (forall t, (forall t', R t t' -> P t') -> SN R t -> P t)
  -> (forall t, SN R t -> P t).
Proof.
 intros HI t Ht. apply HI.

Lemma SNequivNTSN : forall t, SN lex t <-> NT.SN lex t.
Proof.
 split; intros H.
 - apply NT.toSN. inversion H as [x H1]. intros y Ht. induction Ht. 
   + inversion H0. apply H0 in Ht. inversion Ht. 
     inversion H2. inversion H3.
   + apply IHx.  
===================================================================*)

Definition NF (R : pterm -> pterm -> Prop) (t : pterm) := 
                                                 forall t', ~ R t t'.

Inductive SNalt (R : pterm -> pterm -> Prop) (t : pterm) : Prop :=
| SN_nf : NF R t -> SNalt R t
| SN_acc : (forall t', R t t' -> SNalt R t') -> SNalt R t.

Lemma SNaltPat {R : pterm -> pterm -> Prop} : NT.patriarchal R (SNalt R).
Proof.
  unfold NT.patriarchal. intros x H. apply SN_acc. assumption.
Qed.

Lemma SNaltStab : forall R t u, SNalt R t -> R t u -> SNalt R u.
Proof.
 intros R t u Ht Hr. inversion Ht. 
 - apply H in Hr. inversion Hr.
 - specialize H with u. apply H in Hr. assumption.
Qed.

Theorem SNindP {R: pterm -> pterm -> Prop} {P: pterm -> Prop}
: (forall t, (forall t', R t t' -> P t') -> SNalt R t -> P t)
  -> (forall t, SNalt R t -> P t).
Proof.
  intros IH t Ht. 
  (*
  assert (Hpat: NT.patriarchal R (fun x => SNalt R x -> P x)).
  { unfold NT.patriarchal.
    intros.
    apply IH.
    - intros.
      apply H.
      + assumption.      
      + apply SNaltStab with x; assumption.
    - assumption.
  } *)
  induction Ht.
  - apply IH. 
   + intros. apply H in H0. inversion H0.
   + constructor; assumption.
  - apply IH.  
   + assumption.
   + apply SN_acc. assumption.
Qed.

Theorem SNaltEquivNTSN {R: pterm -> pterm -> Prop}: forall t, SNalt R t <-> NT.SN R t.
Proof.
 split; intro H. 
 - inversion H.
  + apply NT.toSN. intros. apply H0 in H1. inversion H1.
  + eapply SNindP. 
   * intros. apply NT.SNpatriarchal. apply H1.
   * assumption.
 - eapply NT.SNind.
   + intros. apply SNaltPat. apply H0.
  + assumption.
Qed.

Lemma SNalt_app : forall t t', SNalt lex (pterm_app t t') -> SNalt lex t /\ SNalt lex t'. Admitted.

(* Inductive headApp : pterm -> Prop :=  *)
 
(*   | hvar : forall x, headApp (pterm_fvar x) *)

(*   | happ : forall t u,  *)
    
(*                          headApp t -> Lterm u -> *)
(* (*-------------------------------------------------------------------------*) *)
(*                          headApp (pterm_app t u) *)

(* . *)

(* Inductive HNF_Beta : pterm -> Prop := *)
  
(*   | hnfB_headApp : forall t, headApp t -> HNF_Beta t *)

(*   | hnfB_abs : forall L t, *)

(*                       (forall x, x \notin L -> HNF_Beta (t ^ x))->  *)
(* (*-------------------------------------------------------------------------*) *)
(*                                HNF_Beta (pterm_abs t) *)
(* . *)

(* Inductive nfbApp : pterm -> Prop :=  *)

(*   | nfb_var : forall x, nfbApp (pterm_fvar x) *)

(*   | nfb_app : forall t u,  *)
    
(*                        nfbApp t -> Lterm u -> NF Beta u -> *)
(* (*-------------------------------------------------------------------------*) *)
(*                            nfbApp (pterm_app t u) *)

(* . *)

(* Inductive NF_Beta : pterm -> Prop := *)
  
(*   | nfB_nfbApp : forall t, nfbApp t -> NF_Beta t *)

(*   | nfB_abs : forall L t, *)

(*                       (forall x, x \notin L -> NF_Beta (t ^ x))->  *)
(* (*-------------------------------------------------------------------------*) *)
(*                                NF_Beta (pterm_abs t) *)
(* . *)

Lemma NFB_app : forall u v, NF Beta (pterm_app u v) -> NF Beta u /\ NF Beta v.
Proof.
 intros. split; unfold NF; unfold not; intros.
 - assert ( pterm_app u v -->Beta pterm_app t' v).
   { apply L_app_left. assumption. }
   apply H in H1. assumption.
 - assert ( pterm_app u v -->Beta pterm_app u t').
   { apply L_app_right. assumption. }
   apply H in H1. assumption.
Qed.

(* Lemma NF_Beta_NF : forall t, Lterm t -> (NF Beta t <-> NF_Beta t). *)
(* Proof. *)
(*  split; intro H'.  *)
(*  - induction H. *)
(*   + do 2 constructor. *)
(*   + constructor. apply NFB_app in H'; destruct H' as [H1 H2]. apply nfb_app. *)


(* (*=================================================================================*) *)

(* (* Lambda *) *)

(* (* Lemma L_SN_app : forall n R t u, L_red_regular R ->  Lterm t -> Lterm u ->  *) *)
(* (*                SN_ind n (L_contextual_closure R) (pterm_app t u) -> *) *)
(* (*                SN_ind n (L_contextual_closure R) t /\ SN_ind n (L_contextual_closure R) u. *) *)
(* (*  Proof. *) *)
(* (*  intros n R t u Reg.  *) *)
(* (*  generalize t u; clear t u.   *) *)
(* (*  induction n.  intros. split; rewrite <- NF_eq_SN0 in *|-*; unfold NF in *|-*.  *) *)
(* (*  intros t' H'. apply (H1 (pterm_app t' u)). apply L_app_left; trivial. *) *)
(* (*  intros u' H'. apply (H1 (pterm_app t u')). apply L_app_right; trivial. *) *)
(* (*  intros t u Tt Tu H. destruct H. split.  *) *)
(* (*  apply SN_intro. intros t' H'. exists n. split; try omega.  *) *)
(* (*  apply IHn with (t := t') (u := u); trivial. apply red_regular_Lctx in Reg. *) *)
(* (*  apply Reg in H'. apply H'. case (H (pterm_app t' u)). apply L_app_left; trivial.  *) *)
(* (*  intros k H''. apply WSN with (k := k). omega. apply H''. *) *)
(* (*  apply SN_intro. intros u' H'. exists n. split; try omega.  *) *)
(* (*  apply IHn with (t := t) (u := u'); trivial. apply red_regular_Lctx in Reg. *) *)
(* (*  apply Reg in H'. apply H'. case (H (pterm_app t u')). apply L_app_right; trivial.  *) *)
(* (*  intros k H''. apply WSN with (k := k). omega. apply H''. *) *)
(* (* Qed.  *) *)


(* (* Lemma L_SN_abs : forall x n R t, L_red_regular R -> L_red_out R ->  *) *)
(* (*                SN_ind n (L_contextual_closure R) (pterm_abs t) -> *) *)
(* (*                x \notin (fv t) -> SN_ind n (L_contextual_closure R) (t ^ x). *) *)
(* (* Proof. *) *)
(* (*  intros x n R t Reg Out. *) *)
(* (*  generalize t; clear t. *) *)
(* (*  apply red_regular_Lctx in Reg.  *) *)
(* (*  apply red_out_Lctx in Out.  *) *)
(* (*  apply L_red_out_to_rename in Out. *) *)
(* (*  induction n. intros.  *) *)
(* (*  apply SN0_to_NF in H.  *) *)
(* (*  apply NF_to_SN0; unfold NF in *|-*. *) *)
(* (*  intros t' H'. gen_eq t0 : (close t' x). intro H1. *) *)
(* (*  replace t' with (t0 ^ x) in H'. *) *)
(* (*  assert (Q: L_contextual_closure R (pterm_abs t) (pterm_abs t0)). *) *)
(* (*     apply L_abs_in with (L := {{x}}). intros z H2.  *) *)
(* (*     apply notin_singleton in H2. apply Out with (x := x); trivial. *) *)
(* (*     rewrite H1. apply fv_close'. *) *)
(* (*  assert (Q': ~ L_contextual_closure R (pterm_abs t) (pterm_abs t0)). *) *)
(* (*     apply H. *) *)
(* (*  contradiction. rewrite H1. rewrite open_close_var with (x := x). *) *)
(* (*  reflexivity. apply Reg in H'. apply Lterm_is_term. apply H'. *) *)
(* (*  intros. destruct H. apply SN_intro. *) *)
(* (*  intros. exists n. split; try omega. *) *)
(* (*  gen_eq t0 : (close t' x). intro H2. *) *)
(* (*  replace t' with (t0 ^ x). replace t' with (t0 ^ x) in H1. *) *)
(* (*  apply IHn; trivial. case (H (pterm_abs t0)); trivial. *) *)
(* (*  apply L_abs_in with (L := {{x}}). *) *)
(* (*  intros z H3. apply notin_singleton in H3.  *) *)
(* (*  apply Out with (x := x); trivial. *) *)
(* (*  rewrite H2. apply fv_close'. *) *)
(* (*  intros k H3. apply WSN with (k := k); try omega. *) *)
(* (*  apply H3. rewrite H2. apply fv_close'. *) *)
(* (*  rewrite H2. rewrite open_close_var with (x := x). *) *)
(* (*  reflexivity. apply Lterm_is_term. apply Reg in H1. apply H1. *) *)
(* (*  rewrite H2. rewrite open_close_var with (x := x). *) *)
(* (*  reflexivity. apply Lterm_is_term. apply Reg in H1. apply H1.  *) *)
(* (* Qed. *) *)


(* (* Lemma L_SN_mult_app : forall n R t l, L_red_regular R ->  Lterm t -> Lterm %% l ->  *) *)
(* (*                SN_ind n (L_contextual_closure R) (t // l) -> *) *)
(* (*                SN_ind n (L_contextual_closure R) t /\ SN_ind n (L_contextual_closure R) %% l. *) *)
(* (* Proof. *) *)
(* (*  intros n R t l Reg. generalize n t; clear n t. *) *)
(* (*  induction l; simpl. intros n t T H0 H. split; trivial. *) *)
(* (*  intros n t T H0 H. destruct H0. apply L_SN_app in H; trivial. destruct H. *) *)
(* (*  assert (Q : SN_ind n (L_contextual_closure R) t /\ SN_ind n (L_contextual_closure R) %% l).  *) *)
(* (*   apply IHl; trivial. *) *)
(* (*  clear IHl. destruct Q. split; trivial. split; trivial. *) *)
(* (*  rewrite Lterm_mult_app. split; trivial.  *) *)
(* (* Qed.  *) *)

(* Lemma Lctx_red_h_mult_app : forall R t t' lu, Lterm %% lu -> (L_contextual_closure R) t t' -> (L_contextual_closure R) (t // lu) (t' // lu). *)
(* Proof. *)
(*  intros R t t' lu Tlu H. induction lu; simpl in *|-*; trivial. *)
(*  destruct Tlu. apply L_app_left; trivial. *)
(*  apply IHlu; trivial. *)
(* Qed.  *)

(* (* Lemma Lctx_red_t_mult_app : forall R t lu lu', Lterm t -> Lterm %% lu -> R_list (L_contextual_closure R) lu lu' -> (L_contextual_closure R) (t // lu) (t // lu'). *) *)
(* (* Proof. *) *)
(* (*  intros R t lu lu' Tt Tlu H. unfold R_list in H. *) *)
(* (*  case H; clear H; intros t0 H. *) *)
(* (*  case H; clear H; intros t1 H. *) *)
(* (*  case H; clear H; intros l0 H. *) *)
(* (*  case H; clear H; intros l1 H. *) *)
(* (*  destruct H. destruct H0.  *) *)
(* (*  rewrite H. rewrite H0. rewrite H in Tlu.  *) *)
(* (*  clear H H0. induction l0; simpl. destruct l1; simpl.  *) *)
(* (*  apply L_app_right; trivial. *) *)
(* (*  apply L_app_right; trivial.  *) *)
(* (*  simpl in Tlu. apply Lterm_app. rewrite Lterm_mult_app.  *) *)
(* (*  destruct Tlu. destruct H0. *) *)
(* (*  split; trivial. apply Tlu. *) *)
(* (*  simpl in Tlu. destruct Tlu.  *) *)
(* (*  apply L_app_left; trivial. *) *)
(* (*  apply IHl0; trivial.  *) *)
(* (* Qed. *) *)


(* (** Inductive Characterisation of NF Beta **) *)

(* (* Lemma NF_ind_eq_Beta : forall t, Lterm t -> (NF_ind Beta t <-> NF Beta t). *) *)
(* (* Proof. *) *)
(* (*  intros. split.  *) *)
(* (*  intro H'. induction H'. *) *)
(* (*  induction l; simpl in *|-*. *) *)
(* (*  intros t H2. inversion H2. inversion H3. *) *)
(* (*  intros t H2. inversion H2. inversion H3. *) *)
(* (*  case eqdec_nil with (l := l). intro. rewrite H11 in H6. simpl in H6. *) *)
(* (*  generalize H6. discriminate. *) *)
(* (*  intro H11. case  m_app_eq_app with (t := (pterm_fvar x)) (lu := l); trivial. *) *)
(* (*  intros t2 H12. case H12; clear H12; intros t3 H12.  *) *)
(* (*  generalize H6. rewrite H12. discriminate. *) *)
(* (*  unfold NF in IHl. apply IHl with (t' := t'). inversion H. trivial. *) *)
(* (*  intros u' H'. apply H0. right; trivial. *) *)
(* (*  intros u' H8 Tu' t1.  apply H1; trivial. right; trivial. trivial. *) *)
(* (*  unfold NF in H1. apply H1 with (u := a) (t' := u'). *) *)
(* (*  left; trivial. inversion H; trivial. trivial. *) *)
(* (*  intros t' H2. inversion H2. inversion H3. inversion H. *) *)
(* (*  unfold NF in H1. case var_fresh with (L := L \u L0 \u L1). *) *)
(* (*  intros x Fr. apply notin_union in Fr. destruct Fr. apply notin_union in H8; destruct H8. *) *)
(* (*  apply H1 with (x := x) (t' := t'0 ^x); trivial.  *) *)
(* (*  apply H7; trivial. apply H4; trivial.  *) *)
(* (*  assert (Reg : L_red_regular rule_beta). apply L_beta_regular. *) *)
(* (*  assert (Out : L_red_out rule_beta). apply L_beta_red_out. *) *)
(* (*  apply Lterm_size_induction3 with (t := t); trivial; intros. *) *)
(* (*  apply NF_ind_app; intros. *) *)
(* (*  apply H0; trivial. rewrite NF_eq_SN0 in H1|-*. apply L_SN_mult_app in H1; trivial. *) *)
(* (*  destruct H1. rewrite <- P_list_eq with (P := SN_ind 0 (L_contextual_closure rule_beta)) in H3. *) *)
(* (*  apply H3; trivial.  rewrite <- P_list_eq with (P := Lterm). intros.  *) *)
(* (*  apply H0; trivial. case eqdec_nil with (l := l); intro. *) *)
(* (*  rewrite H4 in *|-*. simpl in *|-*. unfold Lbody in H1. *) *)
(* (*  case H1; clear H1; intros L H1. apply NF_ind_abs with (L := fv t1 \u L). *) *)
(* (*  intros x Fr. apply notin_union in Fr. destruct Fr. apply H2; trivial. *) *)
(* (*  apply H1; trivial. rewrite NF_eq_SN0 in H3. apply L_SN_abs with (x := x) in H3; trivial. *) *)
(* (*  rewrite <- NF_eq_SN0 in H3. trivial.  *) *)
(* (*  apply False_ind. case not_nil_append with (l := l); trivial. *) *)
(* (*  intros t0 H5. case H5; clear H5; intros l' H5.  rewrite H5 in H3. *) *)
(* (*  rewrite <- mult_app_append in H3. unfold NF in H3. apply (H3 ((t1 ^^ t0) // l')). *) *)
(* (*  apply Lctx_red_h_mult_app. rewrite <- P_list_eq with (P := Lterm). intros. *) *)
(* (*  apply H0. rewrite H5. apply in_or_app. left; trivial. *) *)
(* (*  apply L_redex. apply reg_rule_beta; trivial. unfold body. unfold Lbody in H1. *) *)
(* (*  case H1; clear H1; intros L H1. apply H0. rewrite H5. *) *)
(* (*  apply in_or_app. right. simpl. left; trivial. *) *)
(* (* Qed. *) *)

(* (** Inductive Characterisation of NF Beta **) *)

(* (* Lemma NF_ind_eq_Beta : forall t, Lterm t -> (NF_ind Beta t <-> NF Beta t). *) *)
(* (* Proof. *) *)
(* (*  intros. split.  *) *)
(* (*  intro H'. induction H'. *) *)
(* (*  induction l; simpl in *|-*. *) *)
(* (*  intros t H2. inversion H2. inversion H3. *) *)
(* (*  intros t H2. inversion H2. inversion H3. *) *)
(* (*  case eqdec_nil with (l := l). intro. rewrite H11 in H6. simpl in H6. *) *)
(* (*  generalize H6. discriminate. *) *)
(* (*  intro H11. case  m_app_eq_app with (t := (pterm_fvar x)) (lu := l); trivial. *) *)
(* (*  intros t2 H12. case H12; clear H12; intros t3 H12.  *) *)
(* (*  generalize H6. rewrite H12. discriminate. *) *)
(* (*  unfold NF in IHl. apply IHl with (t' := t'). inversion H. trivial. *) *)
(* (*  intros u' H'. apply H0. right; trivial. *) *)
(* (*  intros u' H8 Tu' t1.  apply H1; trivial. right; trivial. trivial. *) *)
(* (*  unfold NF in H1. apply H1 with (u := a) (t' := u'). *) *)
(* (*  left; trivial. inversion H; trivial. trivial. *) *)
(* (*  intros t' H2. inversion H2. inversion H3. inversion H. *) *)
(* (*  unfold NF in H1. case var_fresh with (L := L \u L0 \u L1). *) *)
(* (*  intros x Fr. apply notin_union in Fr. destruct Fr. apply notin_union in H8; destruct H8. *) *)
(* (*  apply H1 with (x := x) (t' := t'0 ^x); trivial.  *) *)
(* (*  apply H7; trivial. apply H4; trivial.  *) *)
(* (*  assert (Reg : L_red_regular rule_beta). apply L_beta_regular. *) *)
(* (*  assert (Out : L_red_out rule_beta). apply L_beta_red_out. *) *)
(* (*  apply Lterm_size_induction3 with (t := t); trivial; intros. *) *)
(* (*  apply NF_ind_app; intros. *) *)
(* (*  apply H0; trivial. rewrite NF_eq_SN0 in H1|-*. apply L_SN_mult_app in H1; trivial. *) *)
(* (*  destruct H1. rewrite <- P_list_eq with (P := SN_ind 0 (L_contextual_closure rule_beta)) in H3. *) *)
(* (*  apply H3; trivial.  rewrite <- P_list_eq with (P := Lterm). intros.  *) *)
(* (*  apply H0; trivial. case eqdec_nil with (l := l); intro. *) *)
(* (*  rewrite H4 in *|-*. simpl in *|-*. unfold Lbody in H1. *) *)
(* (*  case H1; clear H1; intros L H1. apply NF_ind_abs with (L := fv t1 \u L). *) *)
(* (*  intros x Fr. apply notin_union in Fr. destruct Fr. apply H2; trivial. *) *)
(* (*  apply H1; trivial. rewrite NF_eq_SN0 in H3. apply L_SN_abs with (x := x) in H3; trivial. *) *)
(* (*  rewrite <- NF_eq_SN0 in H3. trivial.  *) *)
(* (*  apply False_ind. case not_nil_append with (l := l); trivial. *) *)
(* (*  intros t0 H5. case H5; clear H5; intros l' H5.  rewrite H5 in H3. *) *)
(* (*  rewrite <- mult_app_append in H3. unfold NF in H3. apply (H3 ((t1 ^^ t0) // l')). *) *)
(* (*  apply Lctx_red_h_mult_app. rewrite <- P_list_eq with (P := Lterm). intros. *) *)
(* (*  apply H0. rewrite H5. apply in_or_app. left; trivial. *) *)
(* (*  apply L_redex. apply reg_rule_beta; trivial. unfold body. unfold Lbody in H1. *) *)
(* (*  case H1; clear H1; intros L H1. apply H0. rewrite H5. *) *)
(* (*  apply in_or_app. right. simpl. left; trivial. *) *)
(* (* Qed. *) *)

(* (** Inductive Characterisation of SN Beta **) *)

(*  Inductive SN_Beta : pterm -> Prop := *)


(*   | sn_beta_var : forall (x : var) (lu : list pterm), *)

(*                       (forall u, (In u lu) -> SN_Beta u) -> *)
(* (*-------------------------------------------------------------------------*) *)
(*                          SN_Beta ((pterm_fvar x) // lu) *)


(*   | sn_beta_abs : forall L (u : pterm), *)

(*                       (forall x, x \notin L -> SN_Beta (u ^ x))->  *)
(* (*-------------------------------------------------------------------------*) *)
(*                              SN_Beta (pterm_abs u) *)

 
(*   | sn_beta_meta_sub : forall  (t u : pterm) (lv : list pterm), *)

(*                           SN_Beta u -> SN_Beta ((t ^^ u) // lv) -> *)
(* (*-------------------------------------------------------------------------*) *)
(*                     SN_Beta ((pterm_app (pterm_abs t)  u) // lv) *)
(* .   *)

(* Theorem SN_Beta_prop : forall t, Lterm t -> SN Beta t -> SN_Beta t. *)
(* Proof. *)
(*  intros t T.  *)

(*  intro H. case H; clear H; intros n H.  *)
(*  generalize t T H; clear T t H. induction n; intros. *)
(* (*  rewrite <- NF_eq_SN0 in H. rewrite <- NF_ind_eq_Beta in H; trivial. *) *)
(* (*  induction H. apply sn_beta_var; intros. *) *)
(* (*  apply H0; trivial. rewrite Lterm_mult_app in T. destruct T. *) *)
(* (*  rewrite <- P_list_eq in H3. apply H3; trivial. *) *)
(* (*  inversion T; clear T. apply sn_beta_abs with (L := L \u L0); intros. *) *)
(* (*  apply notin_union in H3. destruct H3. apply H0; trivial. apply H2; trivial. *) *)
(* (*  assert (Reg : L_red_regular rule_beta); try apply L_beta_regular. *) *)
(* (*  assert (Out : L_red_out rule_beta); try apply  L_beta_red_out. *) *)
(* (*  generalize H; clear H. apply Lterm_size_induction3 with (t := t); intros; trivial.  *) *)
(* (*  apply sn_beta_var; intros. *) *)
(* (*  assert (Q : SN_ind (S n) Beta  %% l).  *) *)
(* (*     apply L_SN_mult_app in H0; trivial. apply H0.  *) *)
(* (*     rewrite <- P_list_eq with (P := Lterm).       *) *)
(* (*     intros u' H2. apply H; trivial.   *) *)
(* (*  apply H; trivial. rewrite <- P_list_eq with (P := SN_ind (S n) Beta) in Q. *) *)
(* (*  apply Q; trivial.  *) *)
(* (*  case eqdec_nil with (l := l).  *) *)
(* (*  intro H3. rewrite H3 in *|-*. simpl in *|-*. clear H H3. *) *)
(* (*  inversion H0; clear H0. *) *)
(* (*  apply sn_beta_abs  with (L := fv t1 \u x). intros y Fr. *) *)
(* (*  apply notin_union in Fr. destruct Fr. *) *)
(* (*  apply H1; trivial. apply H; trivial. apply L_SN_abs; trivial. *) *)
(* (*  intro H3. case not_nil_append with (l := l); trivial. *) *)
(* (*  intros a Hl. case Hl; clear Hl. intros l' Hl. *) *)
(* (*  rewrite Hl in *|-*. rewrite <- mult_app_append in *|-*. *) *)
(* (*  clear H3 Hl.  *) *)
(* (*  assert (Tl : Lterm a /\ Lterm %% l'). *) *)
(* (*    split. apply H. apply in_or_app. right.  *) *)
(* (*    simpl; left; trivial. *) *)
(* (*    apply P_list_eq with (P := Lterm). *) *)
(* (*    intros u Hu. apply H. apply in_or_app. left. *) *)
(* (*    trivial.   *) *)
(* (*  destruct Tl. apply sn_beta_meta_sub. apply H. *) *)
(* (*  apply in_or_app. simpl. right. left; trivial. *) *)
(* (*  apply L_SN_mult_app in H2; trivial. destruct H2. apply L_SN_app in H2; trivial. *) *)
(* (*  destruct H2; trivial. *) *)
(* (*  inversion H0. apply Lterm_abs with (L := x); intros.  *) *)
(* (*  apply H6; trivial.  apply Lterm_app. inversion H0. apply Lterm_abs with (L := x); intros.  *) *)
(* (*  apply H5; trivial. trivial. apply IHn. rewrite  Lterm_mult_app. split; trivial. *) *)
(* (*  apply Lbody_open_term; trivial. *) *)
(* (*  apply SN_one_step with (t := pterm_app (pterm_abs t1) a // l'); trivial. *) *)
(* (*  apply Lctx_red_h_mult_app; trivial. apply L_redex. apply reg_rule_beta. *) *)
(* (*  unfold Lbody in H0. case H0; clear H0; intros L H0. exists L. intros. *) *)
(* (*  apply H0; trivial. trivial. *) *)
(* (* Qed. *) *)
(* Admitted. *)

(* (*=============================================================================*) *)

(* (* Lambda_Ex *) *)

(* (** The two definitions of SN are equivalent for lex. *) *)
(* Lemma SN_equivSN_alt: forall t, SN lex t <-> SN_alt lex t. *)
(* Proof. Admitted. *)


(* (* *)

(* (** NF lex Properties **) *)
(*  *)
(* Lemma NF_eqC : forall t t', t =e t' -> NF lex t -> NF lex t'. *)
(* Proof. *)
(*  intros t t'. intros. unfold NF in *|-*. *)
(*  intros t1 H1. rewrite <- H in H1. *)
(*  apply (H0 t1); trivial. *)
(* Qed. *)
(*  *)
(* Lemma NF_fvar : forall x, NF lex (pterm_fvar x). *)
(* Proof. *)
(*  intros x t H'. *)
(*  case H'; clear H'.  *)
(*  intros t0 H0. case H0; clear H0. *)
(*  intros t1 H1. destruct H1. destruct H0. *)
(*  assert (Q : pterm_fvar x = t0). *)
(*   clear H0 H1 t1. gen_eq t1 : (pterm_fvar x). *)
(*   intro H1. induction H. rewrite H1. rewrite H1 in H. *)
(*   inversion H; trivial. clear H H1 H2 H3 s t0. inversion H0; trivial. *)
(*   rewrite IHtrans_closure in H. rewrite H1. rewrite H1 in H. inversion H. *)
(*   inversion H2; trivial. rewrite H1 in H. symmetry. inversion H. inversion H2; trivial. *)
(*  rewrite <- Q in H0. inversion H0. inversion H2. inversion H5. inversion H5. *)
(* Qed. *)
(*  *)
(*  *)
(* Lemma NF_app_lex : forall t u v, NF lex u -> NF lex v -> (pterm_app u v -->lex t) ->  *)
(*                exists t', u =e pterm_abs t' /\ t =e (t'[v]). *)
(* Proof. *)
(*  intros t u v NFu NFv H. apply lex_app in H. case H; clear H; intro H. *)
(*  case H; clear H; intros t' H. exists t'; trivial. *)
(*  case H; clear H; intro H; case H; clear H; intros t' H; destruct H. *)
(*  assert (Q : ~ u -->lex t'). apply (NFu t'). contradiction. *)
(*  assert (Q : ~ v -->lex t'). apply (NFv t'). contradiction. *)
(* Qed. *)
(*  *)
(* Lemma NF_app_lex_eq : forall t u v, NF lex u -> NF lex v -> (pterm_app u v -->lex t) ->  *)
(*                exists t' t'' v', u = pterm_abs t' /\ t = (t''[v']). *)
(* Proof. *)
(*  intros t u v NFu NFv H. apply NF_app_lex in H; trivial. *)
(*  case H; clear H. intros t' H. destruct H. *)
(*  apply eqC_sym in H. apply eqC_abs_term in H. *)
(*  apply eqC_sym in H0. apply eqC_sub_term in H0. *)
(*  case H; clear H. intros t1 H. case H; clear H. intros L H. destruct H.  *)
(*  case H0; clear H0. intros t1' H0. case H0; clear H0. intros u' H0. *)
(*  exists t1 t1' u'. split. rewrite H. reflexivity. rewrite H0. reflexivity. *)
(* Qed. *)
(*  *)
(* Lemma NF_mult_app_var : forall x lt, NF lex %% lt -> NF lex ((pterm_fvar x) // lt). *)
(* Proof. *)
(*  intros x lt H.  *)
(*  induction lt; simpl in *|-*. apply NF_fvar. *)
(*  destruct H. assert (Q : NF lex (pterm_fvar x // lt)). apply IHlt; trivial. *)
(*  clear IHlt. unfold NF. intros t' H'. case eqdec_nil with (l := lt). intro H''. *)
(*  rewrite H'' in H'. simpl in H'. *)
(*  apply NF_app_lex_eq in H'; trivial. case H'; clear H'. intros t0 H'. *)
(*  case H'; clear H'. intros t0' H'. case H'; clear H'. intros v' H'. *)
(*  destruct H'. inversion H1. *)
(*  apply NF_fvar. intro H''. *)
(*  assert (Q' : exists t' u', (pterm_fvar x) // lt = pterm_app t' u'). *)
(*   apply m_app_eq_app; trivial. *)
(*  case Q'; clear Q'. intros u H1. case H1; clear H1. intros v H1. *)
(*  rewrite H1 in H'. apply NF_app_lex_eq in H'; trivial. *)
(*  case H'; clear H'. intros t0 H'. case H'; clear H'. intros t0' H'. *)
(*  case H'; clear H'. intros v' H'. *)
(*  destruct H'. inversion H2; trivial.  *)
(*  rewrite <- H1; trivial.  *)
(* Qed. *)
(*  *)
(*  *)
(*  *)
(* Lemma lex_abs_not_NF : forall l t, l <> nil -> term (pterm_abs t // l) -> ~ NF lex (pterm_abs t // l). *)
(* Proof. *)
(*  intros. induction l. intro H'. apply H; trivial. *)
(*  simpl in *|-*. case eqdec_nil with (l := l). intro H'. *)
(*  rewrite H' in *|-*. simpl in *|-*. intro H1. *)
(*  apply (H1 (t[a])). apply ctx_to_mod_eqC. apply redex.  *)
(*  apply B_lx. apply term_distribute_over_application in H0. *)
(*  destruct H0. apply term_abs_to_body in H0. apply reg_rule_b; trivial. *)
(*  intro H'. apply term_distribute_over_application in H0. destruct H0. *)
(*  assert (Q : ~ NF lex (pterm_abs t // l)). *)
(*    apply IHl; trivial. *)
(*  clear IHl H'. intro H'. apply Q. intros t' H2. *)
(*  apply (H' (pterm_app t' a)). apply left_app_lex; trivial. *)
(* Qed.  *)
(*  *)
(* Lemma lex_sub_not_NF : forall x t u, body t -> term u -> x \notin (fv t) -> *)
(*       ~ NF lex (t ^ x) -> ~ NF lex (t[u]). *)
(* Proof. *)
(*  intros. intro H3. apply H2. clear H2. *)
(*  intros t0 H2. gen_eq t1 : (close t0 x). intro H4. *)
(*  replace t0 with (t1 ^ x) in H2. apply (H3 (t1 [u])). *)
(*  apply left_subst_lex with (L:= (fv t) \u (fv t1)); trivial. *)
(*  intros z Fr. apply notin_union in Fr. destruct Fr. *)
(*  apply ctx_sys_lex_red_rename with (x := x); trivial. *)
(*  rewrite H4. apply fv_close'. rewrite H4. *)
(*  rewrite open_close_var with (x := x); trivial. *)
(*  apply ctx_sys_Bex_regular in H2. apply H2. *)
(* Qed.   *)
(*  *)
(* Lemma lex_sub_not_NF' : forall t u, body t -> term u -> ~ NF lex (t[u]). *)
(* Proof. *)
(*   intros. apply body_size_induction with (t := t); trivial; intros; intro H'.  *)
(*   apply (H' u). apply ctx_to_mod_eqC. apply redex. apply sys_x_lx. apply reg_rule_var; trivial. *)
(*   apply (H' (pterm_fvar x)). apply ctx_to_mod_eqC. apply redex. apply sys_x_lx. apply reg_rule_gc; trivial. *)
(*   apply (H' (pterm_abs ((& t1)[u]))). apply ctx_to_mod_eqC. apply redex. apply sys_x_lx. apply reg_rule_lamb; trivial. *)
(*   rewrite body_eq_body'; unfold body'. simpl; trivial. *)
(*   apply (H' (pterm_app (t1[u]) (t2[u]))). apply ctx_to_mod_eqC. apply redex. apply sys_x_lx. apply reg_rule_app; trivial; *)
(*   rewrite body_eq_body' in *|-*; unfold body' in *|-*; simpl in *|-*; apply H2. *)
(*   case var_fresh with (L := fv t3).  *)
(*   intros x Hx. case fv_in_or_notin with (t := t3 ^ x) (x := x); intros. *)
(*   apply (H' ((& t1)[u][ t3[ u ] ])). apply ctx_to_mod_eqC. apply redex. apply sys_x_lx. apply reg_rule_comp; trivial. *)
(*   rewrite body_eq_body' in *|-*; unfold body' in *|-*; simpl in *|-*; split; trivial. *)
(*   rewrite term_eq_term'. unfold term'. apply not_body_term_fvar with (x := x); trivial. *)
(*   rewrite body_eq_body' in H2. unfold body' in H2. trivial.  *)
(*   assert (T : term t3). *)
(*     rewrite term_eq_term'; simpl. unfold term'. *)
(*     rewrite body_eq_body' in *|-; unfold body' in *|-. *)
(*     apply body_term_fvar with (x := x); trivial. *)
(*   clear x Hx H2 H5. rewrite eqC_redex in H'; trivial. *)
(*   generalize H'. case var_fresh with (L := fv ((& t1)[u])). *)
(*   intros x Fr. apply lex_sub_not_NF with (x := x); trivial. *)
(*   rewrite body_eq_body'. unfold body'. simpl. *)
(*   split. apply lc_at_bswap; try omega; trivial. *)
(*   rewrite <- body_eq_body'. apply term_is_a_body; trivial. *)
(*   unfold open. unfold bswap. simpl.   *)
(*   replace (open_rec 0 (pterm_fvar x) u) with u. *)
(*   apply H4. *)
(*   simpl in Fr. apply notin_union in Fr. apply Fr. *)
(*   rewrite size_bswap_rec; trivial.  *)
(*   rewrite body_eq_body'. unfold body'. *)
(*   rewrite <- lc_at_open with (u := pterm_fvar x); trivial. *)
(*   apply lc_at_bswap; try omega; trivial. *)
(*   rewrite open_lc_at; trivial.  *)
(*   rewrite <- term_eq_term'; trivial. *)
(* Qed.   *)

(* (** SN lex Properties **) *)
(*  *)
(*  *)
(* Lemma SN_app_var : forall x t, SN lex t -> SN lex (pterm_app (pterm_fvar x) t). *)
(* Proof. *)
(*  intros x t H. case H; clear H. intros n H. exists n. generalize t H; clear t H. *)
(*  induction n. intros t H. rewrite <- NF_eq_SN0 in *|-*.  *)
(*  replace (pterm_app (pterm_fvar x) t) with ((pterm_fvar x) // (t :: nil)). *)
(*  apply NF_mult_app_var. simpl; split; trivial. simpl; trivial. *)
(*  intros t H. inversion H. apply SN_intro. intros u H'. *)
(*  apply lex_app_var in H'. case H'; clear H'; intros t' H'. *)
(*  destruct H'. case (H0 t'); clear H0; trivial. intros k H0.  *)
(*  destruct H0. exists n; split; try omega. rewrite H1. apply IHn. *)
(*  apply WSN with (k := k); try omega; trivial. *)
(* Qed. *)
(*  *)
(*  *)
(*  *)
(* Lemma SN_mult_app_var : forall x lt, term %% lt -> SN lex %% lt -> SN lex ((pterm_fvar x) // lt). *)
(* Proof. *)
(*  intros x lt T H. induction lt; simpl. exists 0. rewrite <- NF_eq_SN0. apply NF_fvar. *)
(*  simpl in *|-*. destruct T. destruct H. assert (H': SN lex (pterm_fvar x // lt)). apply IHlt; trivial. clear H2 IHlt. *)
(*  case H; clear H. intros n H. case H'; clear H'. intros n' H'. *)
(*  gen_eq k : (n + n'). intro Hk. exists k. generalize a lt n n'  H0 H1 H H' Hk. clear a lt n n' H0 H1 H H' Hk. *)
(*  induction k. intros.  *)
(*  assert (Qn : n = 0). symmetry in Hk. omega. *)
(*  assert (Qn': n' = 0). symmetry in Hk. omega. clear Hk. *)
(*  rewrite Qn in H. rewrite Qn' in H'. clear Qn Qn'. *)
(*  rewrite <- NF_eq_SN0 in *|-*.  *)
(*  replace (pterm_app (pterm_fvar x // lt) a) with ((pterm_fvar x) // (a :: lt)). *)
(*  apply NF_mult_app_var. simpl. split; trivial. clear a n n' H0 H. *)
(*  induction lt; simpl in *|-*; trivial. split. intros a' Ha'. *)
(*  apply (H' (pterm_app (pterm_fvar x // lt) a')). *)
(*  apply right_app_lex; trivial. rewrite term_mult_app. destruct H1. split; trivial. *)
(*  apply IHlt. apply H1. intros t' Ht'. apply (H' (pterm_app t' a)). *)
(*  apply left_app_lex; trivial. apply H1. simpl; trivial. *)
(*  intros. apply SN_intro. intros t' Ht'. inversion H. inversion H'. *)
(*  apply lex_app in Ht'. case Ht'; clear Ht'. intro Ht'. case Ht'; clear Ht'. intros u Ht'. destruct Ht'. *)
(*  case eqdec_nil with (l := lt). intro H6. rewrite H6 in H4. simpl in H4. apply eqC_fvar_term in H4. apply False_ind. *)
(*  generalize H4. discriminate. intro H6. case m_app_eq_app with (t := (pterm_fvar x)) (lu := lt); trivial. *)
(*  intros u0 H7. case H7; clear H7. intros v0 H7. rewrite H7 in H4. apply eqC_app_term in H4. *)
(*  case H4; clear H4. intros u' H4. case H4; clear H4. intros v' H4. destruct H4. apply False_ind. *)
(*  generalize H4. discriminate. *)
(*  intro H4. case H4; clear H4. intro H4. case H4; clear H4; intros u H4. destruct H4. *)
(*  case (H3 u); trivial; clear H3. intros k' H3. destruct H3. exists k. split; try omega. *)
(*  rewrite H4. apply lex_mult_app_var in H5. case H5; clear H5. intros lt' H5. destruct H5. rewrite H5. *)
(*  apply IHk with (n := n) (n' := n' - 1); trivial. apply lex_R_list_regular in H7. apply H7; trivial. *)
(*  apply WSN with (k := k'); try omega. rewrite <- H5; trivial. omega. *)
(*  intro H4. case H4; clear H4. intros a' H4. destruct H4. exists k; split; try omega. *)
(*  case (H2 a'); clear H2; trivial. intros k' H2. destruct H2. rewrite H4. *)
(*  apply IHk with (n := n - 1) (n' := n'); trivial. apply ctx_sys_Bex_regular in H5. apply H5. *)
(*  apply WSN with (k := k'); try omega; trivial. omega. *)
(* Qed. *)
(*  *)
(*  *)
(* Lemma lex_SN_abs : forall n L t, (forall x, x \notin L -> SN_ind n lex (t ^ x)) -> *)
(*                                  (SN_ind n lex (pterm_abs t)). *)
(* Proof. *)
(*  intros n L t. generalize t; clear t. induction n.  *)
(*  intros. rewrite <- NF_eq_SN0. setoid_rewrite <- NF_eq_SN0 in H. *)
(*  intros t' H'. apply lex_abs in H'. case H'; clear H'; intros L0 H'. case H'; clear H'; intros t0 H'. *)
(*  destruct H'. pick_fresh x. apply notin_union in Fr. destruct Fr. apply notin_union in H2. destruct H2. *)
(*  apply notin_union in H2. destruct H2. apply notin_union in H2. destruct H2. *)
(*  case H with (x := x) (t' := (t0 ^ x)); trivial. apply H1; trivial. *)
(*  intros t H. apply SN_intro. intros t' H'. exists n; split; try omega. *)
(*  apply lex_abs in H'. case H'; clear H'; intros L0 H'. case H'; clear H'; intros t0 H'. *)
(*  destruct H'. pick_fresh x. apply notin_union in Fr. destruct Fr. apply notin_union in H2. destruct H2. *)
(*  apply notin_union in H2. destruct H2. apply notin_union in H2. destruct H2.  apply notin_union in H2. destruct H2. *)
(*  rewrite H0. apply IHn. intros x' H8. destruct (H x'); trivial. case (H9 (t0 ^ x')). *)
(*  apply ctx_sys_lex_red_rename with (x := x); trivial. apply H1; trivial. *)
(*  intros k H10. destruct H10. apply WSN with (k := k); try omega; trivial. *)
(* Qed. *)
(*  *)
(*  *)
(* Lemma lex_SN_ind_rename : forall n x x' t, body t -> x' \notin ({{x}} \u (fv t)) -> SN_ind n lex (t ^ x) -> SN_ind n lex (t ^ x'). *)
(* Proof. *)
(*  intros n x x' t B Fr H. apply notin_union in Fr; destruct Fr. apply notin_singleton in H0. *)
(*  generalize t B H0 H1 H. clear t B H0 H1 H. induction n. *)
(*  intros t B H0 H1 H. rewrite <- NF_eq_SN0 in *|-*.  *)
(*  intros t' H'. gen_eq t0 : (close t' x'). intro H2.  *)
(*  replace t' with (t0 ^ x') in H'. apply (H (t0 ^x)). apply ctx_sys_lex_red_rename with (x := x'); trivial.  *)
(*  rewrite H2. apply fv_close'. rewrite H2. rewrite open_close_var with (x := x'). reflexivity. *)
(*  apply ctx_sys_Bex_regular in H'. apply H'. intros t B H0 H1 H. destruct H. *)
(*  apply SN_intro. intros t' H'. exists n; split; try omega. gen_eq t0 : (close t' x'). intro H2. *)
(*  generalize H'. intro T. apply ctx_sys_Bex_regular in T. destruct T. *)
(*  replace t' with (t0 ^ x') in H'. case (H (t0 ^ x)); clear H. apply ctx_sys_lex_red_rename with (x := x'); trivial. *)
(*  rewrite H2. apply fv_close'. intros k H. destruct H.  replace t' with (t0 ^ x'). apply (IHn t0); trivial. *)
(*  apply ctx_sys_Bex_regular in H'. destruct H'. rewrite term_eq_term' in H7. unfold term' in H7. unfold open in H7. *)
(*  rewrite body_eq_body'. unfold body'. rewrite lc_at_open with (u := pterm_fvar x'); trivial. *)
(*  rewrite H2. apply fv_close'. apply WSN with (k := k); try omega; trivial. *)
(*  rewrite H2; rewrite open_close_var with (x := x'); try reflexivity; trivial. *)
(*  rewrite H2; rewrite open_close_var with (x := x'); try reflexivity; trivial. *)
(* Qed. *)
(*  *)
(* Lemma lex_SN_rename :  forall x x' t, body t -> x' \notin ({{x}} \u (fv t)) -> SN lex (t ^ x) -> SN lex (t ^ x'). *)
(* Proof. *)
(*  intros. case H1; clear H1; intros n H1; exists n; apply lex_SN_ind_rename with (x := x); trivial. *)
(* Qed. *)
(*  *)
(* Lemma lex_SN_ind_swap : forall n x y t, SN_ind n lex t -> SN_ind n lex ([(x,y)]t). *)
(* Proof. *)
(*  intros. generalize t H. clear t H. induction n. *)
(*  intros. rewrite <- NF_eq_SN0 in *|-*. intros t' H'. *)
(*  apply (H ([(x,y)]t')). rewrite <- swap_inv with (t := t) (x := x) (y := y). *)
(*  apply ctx_sys_lex_red_swap; trivial. *)
(*  intros. inversion H. clear H. apply SN_intro. intros t' H'. *)
(*  rewrite <- swap_inv with (t := t') (x := x) (y := y). *)
(*  case (H0 ([(x, y)]t')). rewrite <- swap_inv with (t := t) (x := x) (y := y). *)
(*  apply ctx_sys_lex_red_swap; trivial.   *)
(*  intros k H. destruct H. exists n; split; try omega.  apply IHn; trivial. *)
(*  apply WSN with (k := k); try omega; trivial. *)
(* Qed. *)
(*  *)
(* Lemma lex_SN_swap : forall x y t, SN lex t -> SN lex ([(x,y)]t). *)
(* Proof. intros; case H; clear H; intros n H; exists n; apply lex_SN_ind_swap; trivial. Qed. *)
(*  *)
(* *) *)

(* (* LexSN *) *)

(* (** Inductive Characterisation of SN lex **) *)
(*  *)
(*  Inductive ISN : pterm -> Prop := *)
(*  *)
(*  *)
(*   | isn_var : forall (x : var) (lu : list pterm), *)
(*  *)
(*                      (forall u, (In u lu) -> ISN u) -> *)
(* (*-------------------------------------------------------------------------*) *)
(*                          ISN ((pterm_fvar x) // lu) *)
(*  *)
(*  *)
(*   | isn_NF : forall (u : pterm), *)
(*  *)
(*                                 NF lex u -> *)
(* (*-------------------------------------------------------------------------*) *)
(*                                   ISN u *)
(*  *)
(*  *)
(*   | isn_app : forall  (u v : pterm) (lu : list pterm), *)
(*  *)
(*                       ISN (u[v] // lu) -> *)
(* (*-------------------------------------------------------------------------*) *)
(*                       ISN ((pterm_app (pterm_abs u)  v) // lu) *)
(*  *)
(*  *)
(*   | isn_subs : forall  (u v : pterm) (lu : list pterm), *)
(*  *)
(*                   ISN ((u ^^ v) // lu) -> ISN v -> *)
(* (*-------------------------------------------------------------------------*) *)
(*                        ISN (u[v] // lu) *)
(*  *)
(*  *)
(*   | isn_abs : forall L (u : pterm), *)
(*  *)
(*                        (forall x, x \notin L -> ISN (u ^ x)) -> *)
(* (*-------------------------------------------------------------------------*) *)
(*                            ISN (pterm_abs u) . *)
(*  *)
(*  *)
(*  *)
(*  *)
(* Lemma ISN_prop : forall t, term t -> (ISN t <-> SN lex t). *)
(* Proof. *)
(* (*  intros t T. split. intro H. induction H. *) *)
(* (* (* -> *) *) *)
(* (*  (* isn_var *) *) *)
(* (*  rewrite term_mult_app in T. destruct T. clear H1. *) *)
(* (*  assert (Q : SN lex %% lu). *) *)
(* (*   clear H. induction lu; simpl in *|-*; trivial. *) *)
(* (*   destruct H2. split. apply H0; trivial. left. trivial. *) *)
(* (*   apply IHlu; trivial. intros u Hu Tu. *) *)
(* (*   apply H0; trivial. right; trivial. *) *)
(* (*  apply SN_mult_app_var; trivial. *) *)
(* (*  (* isn_NF *) *) *)
(* (*  exists 0. rewrite <- NF_eq_SN0; trivial. *) *)
(* (*  (* isn_app *) *) *)
(* (*  apply perpetuality with (t' := ((u [v]) // lu)); trivial. *) *)
(* (*  apply p_B. apply IHISN. rewrite term_mult_app in *|-*. *) *)
(* (*  destruct T. split; trivial. rewrite term_eq_term' in *|-*. *) *)
(* (*  unfold term' in *|-*. simpl in *|-*. trivial. *) *)
(* (*  (* isn_subs *) *) *)
(* (*  generalize T. intro T'. rewrite term_mult_app in T. destruct T. *) *)
(* (*  apply subs_to_body in H1. destruct H1. *) *)
(* (*  apply perpetuality with (t' := ((u ^^ v) // lu)); trivial. *) *)
(* (*  apply p_subst1; trivial. apply IHISN2; trivial. apply IHISN1; trivial. *) *)
(* (*  rewrite term_mult_app. split; trivial. *) *)
(* (*  apply body_open_term; trivial. *) *)
(* (*  (* isn_abs *) *) *)
(* (*  apply term_abs_to_body in T. *) *)
(* (*  case var_fresh with (L := L \u fv u). intros x Fr. *) *)
(* (*  apply notin_union in Fr. destruct Fr. *) *)
(* (*  case (H0 x); trivial. apply body_to_term; trivial. *) *)
(* (*  intros n H3. exists n. apply lex_SN_abs with (L := {{x}} \u (fv u)). *) *)
(* (*  intros x' Fr. apply lex_SN_ind_rename with (x := x); trivial. *) *)
(* (* (* <- *) *) *)
(* (*  intro H. unfold SN in H. case H; clear H; intros n H. *) *)
(* (*  generalize t T H; clear T t H. induction n; intros. *) *)
(* (*  apply isn_NF. apply SN0_to_NF. trivial. *) *)
(* (*  generalize H; clear H. *) *)
(* (*  assert (Reg : red_regular sys_Bx). *) *)
(* (*   apply  sys_Bx_regular. *) *)
(* (*  assert (Out : red_out sys_Bx). *) *)
(* (*   apply  sys_Bx_red_out. *) *)
(* (*  apply term_size_induction3 with (t := t); intros; trivial. *) *)
(* (*  (* var *) *) *)
(* (*  apply isn_var; intros. *) *)
(* (*  assert (Q : SN_ind (S n) lex  %% l). *) *)
(* (*     apply eqC_SN_app_list in H0; trivial. apply H0. *) *)
(* (*     rewrite <- P_list_eq with (P := term). *) *)
(* (*     intros u' H2. apply H; trivial. *) *)
(* (*  apply H; trivial. rewrite <- P_list_eq with (P := SN_ind (S n) lex) in Q. *) *)
(* (*  apply Q; trivial. *) *)
(* (*  (* abs *) *) *)
(* (*  case eqdec_nil with (l := l). *) *)
(* (*  intro H3. rewrite H3 in *|-*. simpl in *|-*. clear H H3. *) *)
(* (*  apply isn_abs with (L := fv t1). intros x Fr. *) *)
(* (*  apply H1; trivial. apply body_to_term; trivial. *) *)
(* (*  apply eqC_SN_abs; trivial. *) *)
(* (*  intro H3. case not_nil_append with (l := l); trivial. *) *)
(* (*  intros a Hl. case Hl; clear Hl. intros l' Hl. *) *)
(* (*  rewrite Hl in *|-*. rewrite <- mult_app_append in *|-*. *) *)
(* (*  clear H3 Hl. *) *)
(* (*  assert (Tl : term a /\ term %% l'). *) *)
(* (*    split. apply H. apply in_or_app. right. *) *)
(* (*    simpl; left; trivial. *) *)
(* (*    apply P_list_eq with (P := term). *) *)
(* (*    intros u Hu. apply H. apply in_or_app. left. *) *)
(* (*    trivial. *) *)
(* (*  clear H H1. destruct Tl. *) *)
(* (*  apply isn_app. apply IHn. *) *)
(* (*  rewrite term_mult_app. split; trivial. *) *)
(* (*  apply body_to_subs; trivial. *) *)
(* (*  apply SN_one_step with (t := pterm_app (pterm_abs t1) a // l'); trivial. *) *)
(* (*  apply left_m_app_lex; trivial. apply ctx_to_mod_eqC. apply redex. *) *)
(* (*  apply B_lx. apply reg_rule_b; trivial. *) *)
(* (*  (* subs *) *) *)
(* (*  assert (Tl : term %% l). *) *)
(* (*    apply P_list_eq with (P := term). *) *)
(* (*    intros u Hu. apply H; trivial. *) *)
(* (*  apply isn_subs. *) *)
(* (*  apply IHn. apply term_mult_app. split; trivial. *) *)
(* (*  apply body_open_term; trivial. *) *)
(* (*  case SN_trs with (n := S n) (R := lex) (t := (t1 [t3]) // l) (u := (t1 ^^ t3) // l); trivial. *) *)
(* (*  apply left_trans_m_app_lex; trivial. *) *)
(* (*  apply trs_ex_to_lex. apply full_comp; trivial. *) *)
(* (*  intros k Hk. destruct Hk. apply WSN with (k := k); try omega; trivial. *) *)
(* (*  apply eqC_SN_app_list in H4; trivial. destruct H4. *) *)
(* (*  case var_fresh with (L := (fv t1)). intros x Fr. *) *)
(* (*  apply eqC_SN_sub with (x := x) in H4; trivial. *) *)
(* (*  destruct H4.  apply H1; trivial. *) *)
(* (*  apply body_to_subs; trivial. *) *)
(* (* Qed. *) Admitted. *)
