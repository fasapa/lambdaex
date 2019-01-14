(********************************************************************************
* Formalization of labelled lambda ex calculus				        *		
*									        *
* Flavio L. C. de Moura & Daniel L. Ventura & Washington R. Segundo, 2014	*
*********************************************************************************)

Set Implicit Arguments.
Require Import Metatheory LambdaES_Defs LambdaES_Infra LambdaES_FV.
Require Import Rewriting.
Require Import Equation_C Lambda Lambda_Ex Arith Morphisms.

(*
(** Given a relation Red, constructs its contextual closure just over Lterms *)
Inductive L_contextual_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
  | L_redex : forall t s, Red t s -> L_contextual_closure Red t s
  | L_app_left : forall t t' u, Lterm u -> L_contextual_closure Red t t' -> 
	  		L_contextual_closure Red (pterm_app t u) (pterm_app t' u)
  | L_app_right : forall t u u', Lterm t -> L_contextual_closure Red u u' -> 
	  		L_contextual_closure Red (pterm_app t u) (pterm_app t u')
  | L_abs_in : forall t t' L, (forall x, x \notin L -> L_contextual_closure Red (t^x) (t'^x)) 
      -> L_contextual_closure Red (pterm_abs t) (pterm_abs t')
.

(** Given a relation Red, constructs its parallel contextual closure *)
Inductive p_contextual_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
  | p_redex : forall t s, Red t s -> p_contextual_closure Red t s
  | p_app : forall t t' u u', p_contextual_closure Red t t' -> p_contextual_closure Red u u' ->
	  		p_contextual_closure Red (pterm_app t u) (pterm_app t' u')
  | p_abs_in : forall t t' L, (forall x, x \notin L -> p_contextual_closure Red (t^x) (t'^x)) -> 
               p_contextual_closure Red (pterm_abs t) (pterm_abs t')
  | p_subst : forall t t' u u' L, (forall x, x \notin L -> p_contextual_closure Red (t^x) (t'^x)) -> 
              p_contextual_closure Red u u' -> 
	      p_contextual_closure Red  (pterm_sub t u) (pterm_sub t' u') .
*)

(** Step 1 *)



(** Grammar of labelled pre-terms. Labelled terms extend the ordinary
 terms with a new constructor for marked explicit substitutions. *)

Inductive lab_term : pterm -> Prop :=
  | lab_term_var : forall x,
      lab_term (pterm_fvar x)
  | lab_term_app : forall t1 t2,
      lab_term t1 -> lab_term t2 -> 
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

Definition lab_body (t : pterm) := 
           exists L, forall x, x \notin L -> lab_term (t ^ x).

(** Given a relation Red, constructs the contextual closure for labelled terms. *)

Inductive lab_contextual_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
  | lab_redex : forall t s, Red t s -> lab_contextual_closure Red t s
  | lab_app_left : forall t t' u, lab_term u -> lab_contextual_closure Red t t' -> 
	  		lab_contextual_closure Red (pterm_app t u) (pterm_app t' u)
  | lab_app_right : forall t u u', lab_term t -> lab_contextual_closure Red u u' -> 
	  		lab_contextual_closure Red (pterm_app t u) (pterm_app t u')
  | lab_abs_in : forall t t' L, (forall x, x \notin L -> lab_contextual_closure Red (t^x) (t'^x)) 
      -> lab_contextual_closure Red (pterm_abs t) (pterm_abs t')
  | lab_subst_left : forall t t' u L, lab_term u -> 
	  	(forall x, x \notin L -> lab_contextual_closure Red (t^x) (t'^x)) -> 
	        lab_contextual_closure Red  (t[u]) (t'[u])
  | lab_subst_right : forall t u u', lab_body t -> lab_contextual_closure Red u u' -> 
	  	lab_contextual_closure Red  (t[u]) (t[u']) 
  | lab_subst'_left : forall t t' u L, term u -> 
	  	(forall x, x \notin L -> lab_contextual_closure Red (t^x) (t'^x)) -> 
	        lab_contextual_closure Red  (t[[u]]) (t'[[u]])
  | lab_subst'_right : forall t u u', lab_body t -> term u ->  (SN lex u) -> Red u u' -> 
	  	lab_contextual_closure Red  (t[[u]]) (t[[u']]) 
.


(* No SN *)
Inductive simpl_lab_contextual_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
  | s_lab_redex : forall t s, Red t s -> simpl_lab_contextual_closure Red t s
  | s_lab_app_left : forall t t' u, lab_term u -> simpl_lab_contextual_closure Red t t' -> 
	  		simpl_lab_contextual_closure Red (pterm_app t u) (pterm_app t' u)
  | s_lab_app_right : forall t u u', lab_term t -> simpl_lab_contextual_closure Red u u' -> 
	  		simpl_lab_contextual_closure Red (pterm_app t u) (pterm_app t u')
  | s_lab_abs_in : forall t t' L, (forall x, x \notin L -> simpl_lab_contextual_closure Red (t^x) (t'^x)) 
      -> simpl_lab_contextual_closure Red (pterm_abs t) (pterm_abs t')
  | s_lab_subst_left : forall t t' u L, lab_term u -> 
	  	(forall x, x \notin L -> simpl_lab_contextual_closure Red (t^x) (t'^x)) -> 
	        simpl_lab_contextual_closure Red  (t[u]) (t'[u])
  | s_lab_subst_right : forall t u u', lab_body t -> simpl_lab_contextual_closure Red u u' -> 
	  	simpl_lab_contextual_closure Red  (t[u]) (t[u']) 
  | s_lab_subst'_left : forall t t' u L, term u -> 
	  	(forall x, x \notin L -> simpl_lab_contextual_closure Red (t^x) (t'^x)) -> 
	        simpl_lab_contextual_closure Red  (t[[u]]) (t'[[u]])
  | s_lab_subst'_right : forall t u u', lab_body t -> term u -> Red u u' -> 
	  	simpl_lab_contextual_closure Red  (t[[u]]) (t[[u']]) 
.

(* ====================================================================== *)
(** ** Alternative definition for local closure *)

(* ********************************************************************** *)
(** Local closure for marked terms. *)

Fixpoint lc_at' (k:nat) (t:pterm) {struct t} : Prop :=
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

(** Equivalence of [term and [term'] *)

Lemma term_impl_lab_term: forall t, term t -> lab_term t.
Proof.
    induction 1; try constructor; intuition eauto.
    constructor 3 with L. auto.
    constructor 4 with L; auto.

Qed.


Lemma lc_rec_open_var_rec' : forall x t k,
  lc_at' k (open_rec k x t) -> lc_at' (S k) t.
Proof.
  induction t; simpl; introv H; auto*.
  case_nat; simpls~.
  split.
  destruct H. apply lc_rec_open_var_rec with x. auto.
  split*.
  destruct H.
  destruct H0. admit. (* !!!!!!!!!!!!! *)
Qed.


Lemma lc_at'_weaken_ind : forall k1 k2 t,
  lc_at' k1 t -> k1 <= k2 -> lc_at' k2 t.
Proof. introv. gen k1 k2. induction t; simpl; introv T Lt; auto*.
       omega. apply (IHt (S k1) (S k2)); trivial; try omega.
       case T; clear T; intros Tt1 Tt2. split. 
       apply (IHt1 (S k1) (S k2)); trivial; try omega.
       apply (IHt2 k1 k2); trivial; try omega.
       destruct T as [ H1 [H2 H3] ].
       split*. 
       apply lc_at_weaken_ind with k1; auto.
       split*.
       apply IHt1 with (S k1); auto.
       apply le_n_S; auto.
Qed. 

Lemma lc_at'_weaken : forall k t,
  term'' t -> lc_at' k t.
Proof. introv H. apply~ (@lc_at'_weaken_ind 0). omega. Qed.

Lemma lab_term_to_term'' : forall t,
  lab_term t -> term'' t.
Proof.
  introv T. induction T; unfold term'; simple~.
  pick_fresh y. unfold term''. simpl. auto.
  split; pick_fresh x; simpl; auto. 
  unfold term''. simpl. pick_fresh x. apply lc_rec_open_var_rec' with (x := (pterm_fvar x)). apply H0. eauto. constructor. pick_fresh x. apply lc_rec_open_var_rec' with (x := (pterm_fvar x)). apply H0. eauto. auto. 
  constructor. apply term_to_term' in H1. auto. split*. unfold term'' in H0. pick_fresh x. apply lc_rec_open_var_rec' with (x := (pterm_fvar x)). eauto.
Qed.

Lemma lc_at_open_var_rec' : forall x t k,
  lc_at' (S k) t -> lc_at' k (open_rec k (pterm_fvar x) t).
Proof.
  induction t; simpl; introv H; auto*.
  case_nat; simpls~.
  unfold lt in *|-.
  apply le_lt_or_eq in H.
  case H.
  intro H1. apply lt_S_n in H1; trivial.
  intro H1. assert (n = k).
  auto. assert (k = n). auto.
  contradiction.
  split.
  destruct H. apply lc_at_open_var_rec. auto.
  split*.
  destruct H.
  destruct H0. admit. (* !!!!!!!!!!!!! *)
Qed. 


Lemma lc_at'_bswap_rec : forall n k t, S k < n -> lc_at' n t -> lc_at' n (bswap_rec k t).
Proof.
 intros n k t. 
 generalize n k; clear n k.
 induction t.
 (* bvar *)
 intros n' k H0 H1. simpl in H1.
 unfolds bswap_rec. 
 case (k === n). intro H2.
 rewrite H2. simpl. omega. intro H2.
 case (S k === n). intro H3. simpl. omega. intro H3. 
 simpl. trivial.
 (* fvar *)
 intros n k H0 H1. simpl in *|-*. trivial.
 (* app *)
 intros n k H0 H1. simpl in *|-*. destruct H1. split.
 apply IHt1; trivial. apply IHt2; trivial.
 (* abs *)
 intros n k H0 H1. simpl in *|-*.
 apply IHt; try omega; trivial.
 (* sub *)
 intros n k H0 H1. simpl in *|-*. destruct H1. split.
 apply IHt1; try omega; trivial. apply IHt2; trivial.
 (* sub' *)
 intros n k H0 H1. simpl in *|-*. destruct H1 as [ H2 [ H3 H4 ] ].
 split*. apply lc_at_bswap_rec; auto.
 split*. admit. (* !!!!! *)
 apply IHt1; auto. apply lt_n_S; auto.
Qed.

Lemma bswap_rec_lc_at' : forall n k t, S k < n -> lc_at' n (bswap_rec k t) -> lc_at' n t.
Proof.
    Admitted.
 


Lemma term''_to_lab_term : forall t,
  term'' t -> lab_term t.
Proof.
  introv. unfold term'.
  apply pterm_size_induction with (t := t).
  (* bvar *)
  simpl. intros. 
  assert (~ n < 0). auto with arith.
  contradiction.
  (* fvar *)
  simpl. intros.
  apply lab_term_var. 
  (* abs *)
  simpl. intros.
  apply lab_term_abs with (L := fv t1).
  intros x Fr.
  apply (H t1); trivial.
  unfold open. 
  apply lc_at_open_var_rec'; trivial.
  (* app *)
  intros t1 t2 IHt1 IHt2 H.
  simpl in H. apply lab_term_app.
  apply IHt1; apply H.
  apply IHt2; apply H.
  (* sub *)
  intros. simpl in H1.
  apply lab_term_sub with (L := fv t1).
  intros x Fr.
  apply (H0 t1); trivial.
  unfold open. 
  apply lc_at_open_var_rec'. apply H1.
  apply H.  apply H1. 
  (* sub' *)
  intros. 
  unfold term'' in H1. simpl in H1.
  pick_fresh x.
  constructor 5 with (fv t \u fv t1 \u fv t3). intros.
  destruct H1. destruct H3. apply H0. eauto. auto. unfold term''. 
  apply lc_at_open_var_rec'; auto. destruct H1. apply term'_to_term; auto. destruct H1. destruct* H2.
Qed.


Lemma lab_term_eq_term'' : forall t, lab_term t <-> term'' t.
Proof. intros. split. apply lab_term_to_term''. apply term''_to_lab_term. Qed.


Lemma lab_body_to_body'' : forall t,
  lab_body t -> body'' t.
Proof.
  introv [L H]. pick_fresh x. 
  applys (@lc_rec_open_var_rec' (pterm_fvar x)).
  apply lab_term_to_term''. apply~ H.
Qed.

Lemma body''_to_lab_body : forall t,
  body'' t -> lab_body t.
Proof.
  introv B. exists ({}:vars). introv F.
  apply term''_to_lab_term. apply~ lc_at_open_var_rec'.
Qed.

Lemma lab_body_eq_body'' : forall t, lab_body t <-> body'' t.
Proof. intros. split. apply lab_body_to_body''. apply body''_to_lab_body. Qed.


(** Labelled lambda ex calculus. There is just one B rule that works
both in the labelled and non-labelled calculus. *)

(** Labelled equations *)

Inductive lab_eqc  : pterm -> pterm -> Prop := 
(*| lab_eqc_rf: forall u, lab_eqc u u*)
| lab_eqc_rx1 : forall t u v, 
                  lab_term u -> term v -> lab_eqc (t[u][[v]]) ((& t)[[v]][u]) 
| lab_eqc_rx2 : forall t u v, 
                  term u -> lab_term v -> lab_eqc (t[[u]][v]) ((& t)[v][[u]]) 
| lab_eqc_rx3 : forall t u v, 
                  term u -> term v -> lab_eqc (t[[u]][[v]]) ((& t)[[v]][[u]]).
                          
Lemma lab_eqc_sym : forall t u, lab_eqc t u -> lab_eqc u t.
Proof.
  intros t u Heqc.
  destruct Heqc.
  (*apply lab_eqc_rf.*)
  replace ((t [u]) [[v]]) with (((& (& t)) [u]) [[v]]).
  apply lab_eqc_rx2; assumption.
  rewrite bswap_idemp; trivial.
  replace ((t [[u]]) [v]) with (((& (& t)) [[u]]) [v]).
  apply lab_eqc_rx1; assumption.
  rewrite bswap_idemp; trivial.  
  replace ((t [[u]]) [[v]]) with (((& (& t)) [[u]]) [[v]]).
  apply lab_eqc_rx3; assumption.
  rewrite bswap_idemp; trivial.
Qed.  

(*Lemma lab_eqc_trans : forall t u v, lab_eqc t u -> lab_eqc u v -> lab_eqc t v.*)
(*Proof.*)
  (*intros t u v Htu Huv.*)
  (*induction Huv.*)
  (*[>assumption.<]*)
  (*inversion Htu; subst.*)
  (*[>apply lab_eqc_rx1; assumption.<]*)
  (*rewrite bswap_idemp; trivial.*)
  (*apply lab_eqc_rf.*)
  (*inversion Htu.*)
  (*apply lab_eqc_rx2; assumption.*)
  (*rewrite bswap_idemp; trivial.*)
  (*apply lab_eqc_rf.*)
  (*inversion Htu.*)
  (*apply lab_eqc_rx3; assumption.*)
  (*rewrite bswap_idemp; trivial.*)
  (*apply lab_eqc_rf.*)
(*Qed.  *)

(*Instance lab_eqc_eq : Equivalence lab_eqc.*)
(*Proof.*)
 (*split; intros_all.*)
 (*apply lab_eqc_rf.*)
 (*apply lab_eqc_sym; trivial.*)
 (*generalize H H0. apply lab_eqc_trans.*)
(*Qed.*)

Definition lab_eqC (t: pterm) (u : pterm) :=  trans_closure (lab_contextual_closure lab_eqc) t u . 
Notation "t =~e u" := (lab_eqC t u) (at level 66).

(** =~e is an equivalence relation *)

(*Lemma lab_eqC_rf : forall t, t =~e t.*)
(*Proof.*)
 (*intro t. *)
 (*apply one_step_reduction.*)
 (*apply lab_redex. reflexivity.*)
(*Qed.*)

(*Lemma lab_eqc_preserves_SN_lex: forall t t', SN lex t -> lab_eqc t t' -> SN lex t'.
Proof.
  intros t t' H0 H1.
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
  Admitted.*)
   
(*Lemma lab_ctx_eqc_sym : forall t u, (lab_contextual_closure lab_eqc t u) -> lab_contextual_closure lab_eqc u t. *)
(*Proof.*)
  (*intros t u H. induction H.*)
  (*apply lab_redex. rewrite H. reflexivity.*)
  (*apply lab_app_left; trivial. *)
  (*apply lab_app_right; trivial.*)
  (*apply lab_abs_in with L; trivial.*)
  (*apply lab_subst_left with (L:=L); trivial.*)
  (*apply lab_subst_right; trivial.*)
  (*apply lab_subst'_left with L; assumption.*)
  (*apply lab_subst'_right; trivial. *)
  (*apply lab_eqc_sym; assumption.*)
(*Qed.*)

(*Lemma lab_eqC_sym : forall t u, t =~e u -> u =~e t.*)
(*Proof.*)
  (*intros t u H.*)
  (*unfold lab_eqC in *.*)
  (*induction H.*)
  (*apply one_step_reduction.*)
  (*apply lab_ctx_eqc_sym; assumption.*)
  (*apply lab_ctx_eqc_sym in H.*)
  (*apply (one_step_reduction (lab_contextual_closure lab_eqc)) in H.*)
  (*apply transitive_closure_composition with u; assumption.*)
(*Qed.  *)

Lemma lab_eqC_trans : forall t u v, t =~e u -> u =~e v -> t =~e v.
Proof.
 intros t u v H H'.
 apply transitive_closure_composition with (u := u); trivial.
Qed.

(*Instance lab_eqC_eq : Equivalence lab_eqC.*)
(*Proof.*)
 (*split; intros_all.*)
 (*apply lab_eqC_rf.*)
 (*apply lab_eqC_sym; trivial.*)
 (*apply lab_eqC_trans with y; trivial.*)
(*Qed.*)

Definition eqcc t t' := eqc t t' \/ lab_eqc t t'.
Notation "t =ee t'" := (eqcc t t') (at level 66).

Definition star_ctx_eqcc (t: pterm) (u : pterm) :=  star_closure (simpl_lab_contextual_closure eqcc) t u . 
Notation "t =EE u" := (star_ctx_eqcc t u) (at level 66).


(** TBD:regularity and contextual lemmas are missing. *)

(** Step 2 *)

(** The extended reduction system. This system is used to propagate
terminating labelled substitutions. *)

Inductive lab_sys_x : pterm -> pterm -> Prop :=
| lab_reg_rule_var : forall t, lab_term (pterm_bvar 0 [[t]]) -> lab_sys_x (pterm_bvar 0 [[t]]) t

| lab_reg_rule_gc : forall t u, lab_term t -> lab_term (t[[u]]) -> lab_sys_x (t[[u]]) t

| lab_reg_rule_app : forall t1 t2 u, lab_term (t1[[u]]) -> lab_term (t2[[u]]) ->
  lab_sys_x ((pterm_app t1 t2)[[u]]) (pterm_app (t1[[u]]) (t2[[u]]))

| lab_reg_rule_lamb : forall t u, lab_term ((pterm_abs t)[[u]]) -> 
  lab_sys_x ((pterm_abs t)[[u]]) (pterm_abs ((& t)[[u]]))

| lab_reg_rule_comp : forall t u v, lab_term ((t[u])[[v]]) -> ~ term u -> 
  lab_sys_x (t[u][[v]]) (((& t)[[v]])[u[[v]]]).
Notation "t ->_lab_x u" := (lab_sys_x t u) (at level 59, left associativity).

Inductive lab_sys_lx: pterm -> pterm -> Prop :=
| B_lx : forall t u, t ->_B u -> lab_sys_lx t u
| sys_x_lx : forall t u, t ->_x u -> lab_sys_lx t u
| sys_x_lab_lx : forall t u, t ->_lab_x u -> lab_sys_lx t u.

Definition red_ctx_mod_lab_eqC (R: pterm -> pterm -> Prop) (t: pterm) (u : pterm) := 
           exists t' u', (t =~e t')/\(ES_contextual_closure R t' u')/\(u' =~e u).

Definition lab_ex (t: pterm) (u : pterm) := 
    exists t' u', (t =~e t')/\(lab_contextual_closure lab_sys_x t' u')/\(u' =~e u).

Definition lab_lex (t: pterm) (u : pterm) := 
    exists t' u', (t =EE t')/\(lab_contextual_closure lab_sys_lx t' u')/\(u' =EE u).

Notation "t -->[ex] u" := (lab_ex t u) (at level 59, left associativity).
Notation "t -->[lex] u" := (lab_lex t u) (at level 59, left associativity).

Definition red_lab_regular (R : pterm -> pterm -> Prop) :=
  forall t t',  R t t' -> lab_term t /\ lab_term t'.

Definition red_lab_regular' (R : pterm -> pterm -> Prop) :=
  forall t t',  R t t' -> (lab_term t <-> lab_term t').

(** Unlabelled reduction is in the corresponding labelled reduction. *)
Lemma sys_Bx_is_lab_sys_lx: forall t t', t -->lex t' -> t -->[lex] t'.
Proof.
    Admitted.

  
(** Unlabelled of S-terms *)
Fixpoint U_lab (t : pterm) : pterm :=
  match t with
  | pterm_bvar i    => pterm_bvar i
  | pterm_fvar x    => pterm_fvar x
  | pterm_app t1 t2 => pterm_app (U_lab t1) (U_lab t2)
  | pterm_abs t1    => pterm_abs (U_lab t1)
  | pterm_sub t1 t2 => pterm_sub (U_lab t1) (U_lab t2)
  | pterm_sub' t1 t2 => pterm_sub (U_lab t1) t2
  end.




(* ********************************************************************** *)
(** pterm lists  properties *)

Fixpoint cr_lc_at_list (n : nat) (l : list pterm) {struct l} : Prop :=
 match l with
 | nil => True
 | t::lu =>  lc_at' n t /\ (cr_lc_at_list (S n) lu) 
 end.

Lemma lc_at_mult_sub : forall n t lu, lc_at' n (t//[lu]) <-> (lc_at' (n + length lu) t /\ cr_lc_at_list n lu).
Proof.
 intros. generalize n; clear n. induction lu; simpl. 
 split. intro. assert (Q : n + 0 = n); try omega. rewrite Q. split; trivial.
 intro. assert (Q : n + 0 = n); try omega. rewrite Q in H. apply H.
 intro n. replace (n + S (length lu)) with ((S n) + length lu). split.
 intro H. destruct H. split. 
 apply IHlu; trivial. split; trivial. apply IHlu; trivial.
 intro H. destruct H. destruct H0. split; trivial. apply IHlu. split; trivial.
 omega.
Qed.


(** Step 3 *)

(** Step 4 *)

