(*********************************************************************************
 * Formalization of ES calculi                                                   *
 * Brian Aydemir & Arthur Chargueraud, July 2007              	   	         *
 * Flavio L. C. de Moura & Daniel L. Ventura, 2012 & Washington R. Segundo, 2017 *
 *********************************************************************************)

Set Implicit Arguments.
Require Import Metatheory LambdaES_Defs LambdaES_Infra LambdaES_FV.
Require Import Rewriting.
Require Import Equation_C.

(** Lambda_ex calculus *)
Inductive rule_b : pterm -> pterm -> Prop :=
   reg_rule_b : forall (t u:pterm),  body t -> term u ->  
     rule_b (pterm_app(pterm_abs t) u) (t[u]).
Notation "t ->_B u" := (rule_b t u) (at level 66).

Inductive sys_x : pterm -> pterm -> Prop :=
| reg_rule_var : forall t, sys_x (pterm_bvar 0 [t]) t
| reg_rule_gc : forall t u, term t -> sys_x (t[u]) t
| reg_rule_app : forall t1 t2 u, 
  sys_x ((pterm_app t1 t2)[u]) (pterm_app (t1[u]) (t2[u]))
| reg_rule_lamb : forall t u, 
  sys_x ((pterm_abs t)[u]) (pterm_abs ((& t)[u]))
| reg_rule_comp : forall t u v, has_free_index 0 u ->
  sys_x (t[u][v]) (((& t)[v])[ u[ v ] ]).

Notation "t ->_x u" := (sys_x t u) (at level 59, left associativity).

Definition ex t u := red_ctx_mod_eqC sys_x t u.
Notation "t -->ex u" := (ex t u) (at level 66).

Definition ex_trs t u := trans_closure ex t u.
Notation "t -->ex+ u" := (ex_trs t u) (at level 66).

Definition ex_str t u := star_closure ex t u.
Notation "t -->ex* u" := (ex_str t u) (at level 66).

Inductive sys_Bx: pterm -> pterm -> Prop :=
| B_lx : forall t u, t ->_B u -> sys_Bx t u
| sys_x_lx : forall t u, t ->_x u -> sys_Bx t u.

Notation "t ->_Bx u" := (sys_Bx t u) (at level 59, left associativity).

Definition lex t u :=  red_ctx_mod_eqC sys_Bx t u.
Notation "t -->lex u" := (lex t u) (at level 66).

Definition lex_trs t u := trans_closure lex t u.
Notation "t -->lex+ u" := (lex_trs t u) (at level 66).

Definition lex_str t u := star_closure lex t u.
Notation "t -->lex* u" := (lex_str t u) (at level 66).

(** The two definitions of SN are equivalent for lex. *)
Lemma SN_equivSN_alt: forall t, SN lex t <-> SN_alt lex t.
Proof. Admitted.
    
(* ********************************************************************** *)
(** Properties of the sys_x  *)

Lemma sys_x_wregular : red_wregular sys_x.
Proof.
  intros_all. induction H0.
  - inversion H. assumption.
  - assumption.
  - inversion H; subst; clear H. 
    apply term_app.
    + apply term_sub with L. introv Hl.
      unfold open in *. simpl in H2.
      apply H2 in Hl. inversion Hl.
      assumption. assumption.
    + apply term_sub with L. introv Hl.
      unfold open in *. simpl in H2.
      apply H2 in Hl. inversion Hl.
      assumption. assumption.
  - apply term_to_term' in H.
    unfold term' in H.
    inversion H; subst; clear H. simpl in H0.
    assert (lc_at 2 (& t)).
    { apply lc_at_bswap. auto. assumption. }
    apply term'_to_term. unfold term'. simpl. split.
    + assumption.
    + apply lc_at_weaken_ind with 0; auto.
  - inversion H; subst; clear H. Admitted.
(*     apply term_sub. *)
(*     apply body_to_body' in H0. *)
(*     unfold body' in H0. simpl in H0. *)
(*     destruct H0 as [Ht Hu]. *)
(*     apply term'_to_term. unfold term'. *)
(*     simpl. split. *)
(*     + split. *)
(*       * apply lc_at_bswap; auto. *)
(*       * apply term_to_term' in H2. *)
(*         apply lc_at_weaken_ind with 0; auto. *)
(*     + split. *)
(*       * assumption. *)
(*       * apply term_to_term' in H2. *)
(*         assumption. *)
(* Qed. *)

Lemma ctx_sys_x_wregular : red_wregular (ES_contextual_closure sys_x).
Proof.
  apply red_wregular_ctx.
  apply sys_x_wregular.
Qed.

Lemma ctx_sys_ex_wregular : red_wregular ex.
Proof.
  unfold red_wregular. introv Hterm Hex.
  inversion Hex; subst; clear Hex.
  destruct H as [u [He [Hes He'] ] ].
  generalize He'; clear He'.
  apply red_wregular_eqC.
  generalize Hes; clear Hes.
  apply ctx_sys_x_wregular.
  generalize He; clear He.
  apply red_wregular_eqC.
  assumption.
Qed.

Lemma sys_Bx_wregular : red_wregular sys_Bx.
Proof.
 intros_all. inversion H0; subst; clear H0.
 - inversion H1; subst; clear H1.
   unfold body in H0. destruct H0 as [L H1].
   apply term_sub with L; assumption.
 - generalize H1; clear H1.
   apply sys_x_wregular; trivial.
Qed.

Lemma ctx_sys_Bx_wregular : red_wregular (ES_contextual_closure sys_Bx).
Proof.
  apply red_wregular_ctx.
  apply sys_Bx_wregular.
Qed.

Lemma ctx_sys_Bex_wregular : red_wregular lex.
Proof.
  unfold red_wregular. introv Hterm Hex.
  inversion Hex; subst; clear Hex.
  destruct H as [u [He [Hes He'] ] ].
  generalize He'; clear He'.
  apply red_wregular_eqC.
  generalize Hes; clear Hes.
  apply ctx_sys_Bx_wregular.
  generalize He; clear He.
  apply red_wregular_eqC.
  assumption.
Qed.

Lemma sys_x_red_out : red_out sys_x.
Proof. 
  intros_all. generalize dependent u.
  generalize dependent x. induction H0.
  - introv Hterm. simpl. constructor.
  - introv Hterm. simpl. constructor.
    apply subst_term; assumption.
  - introv Hterm. simpl. constructor.
  - introv Hterm. simpl.
    apply term_to_term' in Hterm.
    unfold bswap. rewrite subst_bswap_rec.
    constructor. assumption.
  - introv Hterm. simpl.
    unfold bswap. rewrite subst_bswap_rec.
    constructor. change ([x ~> u0]t [ [x ~> u0 ] u ] ) with ([x ~> u0 ] (t[u])). Admitted.
(*     apply body_to_body' in H. apply body'_to_body. unfold body' in *. *)
(*     apply lc_at_subst. assumption. *)
(*     apply term_to_term' in Hterm. *)
(*     apply lc_at_weaken_ind with 0; auto. *)
(*     intro H2. apply H0. apply subst_term' in H2; assumption. *)
(*     apply subst_term; assumption. *)
(*     apply term_to_term' in Hterm. assumption. *)
(* Qed. *)

Lemma sys_Bx_red_out : red_out sys_Bx.
Proof. 
 intros_all. destruct H0. induction H0.
 simpl. apply B_lx. apply reg_rule_b. apply body'_to_body;
 apply lc_at_subst; apply body_to_body'; trivial. 
 apply term_is_a_body; trivial.
 apply term'_to_term; apply lc_at_subst; apply term_to_term'; 
 trivial. apply sys_x_lx. apply sys_x_red_out; trivial.
Qed.
 
Lemma ctx_sys_x_red_out : red_out (ES_contextual_closure sys_x).
Proof. 
 apply red_out_ctx.
 apply sys_x_red_out.
Qed.

Lemma ctx_sys_Bx_red_out : red_out (ES_contextual_closure sys_Bx).
Proof. 
 apply red_out_ctx.
 apply sys_Bx_red_out.
Qed.

Lemma ctx_sys_ex_red_out : red_out ex.
Proof.
 apply red_out_mod_eqC.
 apply sys_x_wregular.
 apply sys_x_red_out.
Qed.

Lemma ctx_sys_lex_red_out : red_out lex.
Proof.
 apply red_out_mod_eqC.
 apply sys_Bx_wregular.
 apply sys_Bx_red_out.
Qed.

Lemma ctx_sys_x_red_rename : red_rename (ES_contextual_closure sys_x).
Proof.
 apply red_out_to_rename.
 apply ctx_sys_x_red_out.
Qed.

Lemma ctx_sys_Bx_red_rename : red_rename (ES_contextual_closure sys_Bx).
Proof.
 apply red_out_to_rename.
 apply ctx_sys_Bx_red_out.
Qed.

Lemma ctx_sys_ex_red_rename : red_rename ex.
Proof.
 apply red_out_to_rename.
 apply ctx_sys_ex_red_out.
Qed.

Lemma ctx_sys_lex_red_rename : red_rename lex.
Proof.
 apply red_out_to_rename.
 apply ctx_sys_lex_red_out.
Qed.

Lemma trs_ex_red_rename: red_rename (trans_closure ex).
Proof.
 apply red_out_to_rename.
 apply red_out_trs.
 apply ctx_sys_ex_red_out.
Qed.

Lemma trs_lex_red_rename: red_rename (trans_closure lex).
Proof.
 apply red_out_to_rename.
 apply red_out_trs.
 apply ctx_sys_lex_red_out.
Qed.


Lemma sys_x_not_fv : red_not_fv sys_x.
Proof.
 unfold red_not_fv. intros x t t' H. 
 induction H; simpl; intro H';  
 apply notin_union in H'; try apply notin_union;
 try apply H'; try split; try apply notin_union; try apply H'.
 case H'; clear H'; intros H2 H3. apply notin_union in H2. 
 split. apply H2. apply H3. split.
 case H'; clear H'; intros H2 H3. apply notin_union in H2.
 apply H2. apply H'. unfold bswap. rewrite fv_bswap_rec. apply H'.
 case H'; clear H'; intros H2 H3. apply notin_union in H2.
 split. unfold bswap. rewrite fv_bswap_rec. apply H2. apply H3.
 case H'; clear H'; intros H2 H3. apply notin_union in H2.
 split. apply H2. apply H3.
Qed.

Lemma sys_Bx_not_fv : red_not_fv sys_Bx.
Proof.
 unfold red_not_fv. intros x t t' H. 
 induction H; simpl. destruct H; simpl.
 intro H'. apply notin_union in H'. apply notin_union.
 assumption. apply sys_x_not_fv; trivial.
Qed.

Lemma sys_x_fv : red_fv sys_x.
Proof.
 unfold red_fv. intros x t t' H. 
 induction H; simpl. 
 intro H'. apply in_union; right; trivial.
 intro H'. apply in_union; left; trivial.
 intro H'; apply in_union in H'; case H'; clear H';
 intro H'; apply in_union in H'; case H'; clear H'; 
 intro H'; apply in_union.
 left; apply in_union; left; trivial. right; trivial.
 left; apply in_union; right; trivial. right; trivial.
 intro H'; apply in_union in H'; case H'; clear H';
 intro H'; apply in_union. left. unfold bswap in H'.
 rewrite fv_bswap_rec in H'; trivial. right; trivial.
 intro H'; apply in_union in H'; case H'; clear H';
 intro H'; apply in_union in H'; case H'; clear H'; 
 intro H'; apply in_union. unfold bswap in H'.
 rewrite fv_bswap_rec in H'. left; apply in_union.
 left; trivial. right; trivial. left; apply in_union.
 right; trivial. right; trivial.
Qed.

Lemma sys_Bx_fv : red_fv sys_Bx.
Proof.
 unfold red_fv. intros x t t' H. 
 destruct H. destruct H; simpl; trivial.
 apply sys_x_fv; trivial.
Qed. 

Lemma ctx_sys_x_red_swap : red_swap (ES_contextual_closure sys_x).
Proof.
 apply red_out_to_swap.
 apply ctx_sys_x_red_out.
Qed.

Lemma ctx_sys_Bx_red_swap : red_swap (ES_contextual_closure sys_Bx).
Proof.
 apply red_out_to_swap.
 apply ctx_sys_Bx_red_out.
Qed.

Lemma ctx_sys_ex_red_swap : red_swap ex.
Proof.
 apply red_out_to_swap.
 apply ctx_sys_ex_red_out.
Qed.

Lemma ctx_sys_lex_red_swap : red_swap lex.
Proof.
 apply red_out_to_swap.
 apply ctx_sys_lex_red_out.
Qed.

Lemma trs_ex_red_swap: red_swap (trans_closure ex).
Proof.
 apply red_out_to_swap.
 apply red_out_trs.
 apply ctx_sys_ex_red_out.
Qed.

Lemma trs_lex_red_swap: red_swap (trans_closure lex).
Proof.
 apply red_out_to_swap.
 apply red_out_trs.
 apply ctx_sys_lex_red_out.
Qed.

(***************************************************)

Lemma left_app_ex: forall t u v, term t  ->   
      u -->ex v -> pterm_app u t -->ex pterm_app v t.
Proof.
  intros; apply mod_eqC_app_left; trivial. 
Qed.

Lemma left_trans_app_ex: forall t u v,  term t  ->   
      u -->ex+ v -> pterm_app u t -->ex+ pterm_app v t.
Proof.
  intros; apply trs_mod_eqC_app_left; trivial. 
Qed.

Lemma left_star_app_ex: forall t u v,  term t  ->   
      u -->ex* v -> pterm_app u t -->ex* pterm_app v t.
Proof.
  intros; apply str_mod_eqC_app_left; trivial. 
Qed.
  
Lemma right_app_ex: forall t u v, term t  ->   
      u -->ex v -> pterm_app t u -->ex pterm_app t v.
Proof.
  intros; apply mod_eqC_app_right; trivial. 
Qed.

Lemma right_trans_app_ex: forall t u v,  term t  ->   
      u -->ex+ v -> pterm_app t u -->ex+ pterm_app t v.
Proof.
   intros; apply trs_mod_eqC_app_right; trivial. 
Qed.

Lemma right_star_app_ex: forall t u v,  term t  ->   
      u -->ex* v -> pterm_app t u -->ex* pterm_app t v.
Proof.
   intros; apply str_mod_eqC_app_right; trivial. 
Qed.
(*
Lemma in_abs_ex: forall L u v, (forall x, x \notin L -> (u ^ x) -->ex (v ^ x)) -> 
  ((pterm_abs u) -->ex (pterm_abs v)).
Proof.
 intros; apply mod_eqC_abs_in with (L := L); trivial. 
 apply sys_x_wregular.
 apply sys_x_red_out.
Qed.

Lemma in_trans_abs_ex: forall L u v,  (forall x, x \notin L -> (u ^ x) -->ex+ (v ^ x)) -> 
  ((pterm_abs u) -->ex+ (pterm_abs v)).
Proof.
 intros; apply trs_mod_eqC_abs_in with (L := L); trivial.
 apply sys_x_regular.
 apply sys_x_red_out.
Qed.
*)

Lemma in_star_abs_ex: forall L u v,  (forall x, x \notin L -> (u ^ x) -->ex* (v ^ x)) -> 
  ((pterm_abs u) -->ex* (pterm_abs v)).
Proof.
(*  intros; apply str_mod_eqC_abs_in with (L := L); trivial. *)
(*  apply sys_x_regular. *)
(*  apply sys_x_red_out. *)
  (* Qed. *)
Admitted.

(*
Lemma left_subst_ex: forall L t u v,  term t -> (forall x, x \notin L ->  (u ^ x) -->ex (v ^ x)) -> 
  (u[t]) -->ex (v[t]). 
Proof.
 intros; apply mod_eqC_subst_left with (L := L); trivial.
 apply sys_x_regular.
 apply sys_x_red_out.
Qed.

Lemma left_trans_subst_ex: forall L t u v,  term t -> (forall x, x \notin L ->  (u ^ x) -->ex+ (v ^ x)) -> 
  (u[t]) -->ex+ (v[t]).
Proof.
 intros; apply trs_mod_eqC_subst_left with (L := L); trivial.
 apply sys_x_regular.
 apply sys_x_red_out.
Qed.

Lemma left_star_subst_ex: forall L t u v,  term t -> (forall x, x \notin L ->  (u ^ x) -->ex* (v ^ x)) -> 
  (u[t]) -->ex* (v[t]).
Proof.
 intros; apply str_mod_eqC_subst_left with (L := L); trivial.
 apply sys_x_regular.
 apply sys_x_red_out.
Qed.

Lemma right_subst_ex: forall t u v,  body t -> 
      u -->ex v -> (t[u]) -->ex (t[v]). 
Proof.
 intros; apply mod_eqC_subst_right; trivial.
Qed.  

Lemma right_trans_subst_ex: forall t u v,  body t -> 
      u -->ex+ v -> (t[u]) -->ex+ (t[v]). 
Proof.
 intros; apply trs_mod_eqC_subst_right; trivial.
Qed.

Lemma right_star_subst_ex: forall t u v,  body t -> 
      u -->ex* v -> (t[u]) -->ex* (t[v]). 
Proof.
 intros; apply str_mod_eqC_subst_right; trivial.
Qed.


Lemma left_app_lex: forall t u v, term t  ->   
      u -->lex v -> pterm_app u t -->lex pterm_app v t.
Proof.
  intros; apply mod_eqC_app_left; trivial. 
Qed.

Lemma left_trans_app_lex: forall t u v,  term t  ->   
      u -->lex+ v -> pterm_app u t -->lex+ pterm_app v t.
Proof.
  intros; apply trs_mod_eqC_app_left; trivial. 
Qed.

Lemma left_star_app_lex: forall t u v,  term t  ->   
      u -->lex* v -> pterm_app u t -->lex* pterm_app v t.
Proof.
  intros; apply str_mod_eqC_app_left; trivial. 
Qed.
  
Lemma right_app_lex: forall t u v, term t  ->   
      u -->lex v -> pterm_app t u -->lex pterm_app t v.
Proof.
  intros; apply mod_eqC_app_right; trivial. 
Qed.

Lemma right_trans_app_lex: forall t u v,  term t  ->   
      u -->lex+ v -> pterm_app t u -->lex+ pterm_app t v.
Proof.
   intros; apply trs_mod_eqC_app_right; trivial. 
Qed.

Lemma right_star_app_lex: forall t u v,  term t  ->   
      u -->lex* v -> pterm_app t u -->lex* pterm_app t v.
Proof.
   intros; apply str_mod_eqC_app_right; trivial. 
Qed.

Lemma in_abs_lex: forall L u v, (forall x, x \notin L -> (u ^ x) -->lex (v ^ x)) -> 
  ((pterm_abs u) -->lex (pterm_abs v)).
Proof.
 intros; apply mod_eqC_abs_in with (L := L); trivial. 
 apply sys_Bx_regular.
 apply sys_Bx_red_out.
Qed.

Lemma in_trans_abs_lex: forall L u v,  (forall x, x \notin L -> (u ^ x) -->lex+ (v ^ x)) -> 
  ((pterm_abs u) -->lex+ (pterm_abs v)).
Proof.
 intros; apply trs_mod_eqC_abs_in with (L := L); trivial.
 apply sys_Bx_regular.
 apply sys_Bx_red_out.
Qed.

Lemma in_star_abs_lex: forall L u v,  (forall x, x \notin L -> (u ^ x) -->lex* (v ^ x)) -> 
  ((pterm_abs u) -->lex* (pterm_abs v)).
Proof.
 intros; apply str_mod_eqC_abs_in with (L := L); trivial.
 apply sys_Bx_regular.
 apply sys_Bx_red_out.
Qed.

Lemma left_subst_lex: forall L t u v,  term t -> (forall x, x \notin L ->  (u ^ x) -->lex (v ^ x)) -> 
  (u[t]) -->lex (v[t]). 
Proof.
 intros; apply mod_eqC_subst_left with (L := L); trivial.
 apply sys_Bx_regular.
 apply sys_Bx_red_out.
Qed.

Lemma left_trans_subst_lex: forall L t u v,  term t -> (forall x, x \notin L ->  (u ^ x) -->lex+ (v ^ x)) -> 
  (u[t]) -->lex+ (v[t]).
Proof.
 intros; apply trs_mod_eqC_subst_left with (L := L); trivial.
 apply sys_Bx_regular.
 apply sys_Bx_red_out.
Qed.

Lemma left_star_subst_lex: forall L t u v,  term t -> (forall x, x \notin L ->  (u ^ x) -->lex* (v ^ x)) -> 
  (u[t]) -->lex* (v[t]).
Proof.
 intros; apply str_mod_eqC_subst_left with (L := L); trivial.
 apply sys_Bx_regular.
 apply sys_Bx_red_out.
Qed.

Lemma right_subst_lex: forall t u v,  body t -> 
      u -->lex v -> (t[u]) -->lex (t[v]). 
Proof.
 intros; apply mod_eqC_subst_right; trivial.
Qed.  

Lemma right_trans_subst_lex: forall t u v,  body t -> 
      u -->lex+ v -> (t[u]) -->lex+ (t[v]). 
Proof.
 intros; apply trs_mod_eqC_subst_right; trivial.
Qed.

Lemma right_star_subst_lex: forall t u v,  body t -> 
      u -->lex* v -> (t[u]) -->lex* (t[v]). 
Proof.
 intros; apply str_mod_eqC_subst_right; trivial.
Qed.


Lemma ex_to_lex : forall t t', t -->ex t' -> t -->lex t'.
Proof.
 intros t t' H. 
 case H; clear H. intros t0 H.
 case H; clear H. intros u0 H.
 destruct H. case H0; clear H0. intros H0 H1.
 exists t0 u0. split; trivial. split; trivial.
 apply contextual_R1_R2 with (R1 := sys_x); trivial.
 intros t1 t2 H'. apply sys_x_lx; trivial.
Qed.


Lemma trs_ex_to_lex : forall t t', t -->ex+ t' -> t -->lex+ t'.
Proof.
  apply trans_R1_R2. apply ex_to_lex.
Qed.

Lemma str_ex_to_lex : forall t t', t -->ex* t' -> t -->lex* t'.
Proof.
  apply star_R1_R2. apply ex_to_lex.
Qed.


(*** About NF Lex and SN lex ****)

Lemma left_m_app_lex : forall t t' lu, (term %% lu) ->
                       t -->lex t' -> (t // lu) -->lex (t' // lu).
Proof.
 intros t t' lu T H. induction lu; simpl; trivial.
 simpl in T. destruct T. apply left_app_lex; trivial.
 apply IHlu; trivial.
Qed.

Lemma left_trans_m_app_lex : forall t t' lu, (term %% lu) ->
                             t -->lex+ t' -> (t // lu) -->lex+ (t' // lu).
Proof.
 intros t t' lu T H. induction lu; simpl; trivial.
 simpl in T. destruct T. apply left_trans_app_lex; trivial.
 apply IHlu; trivial.
Qed.


Lemma lex_app : forall t u v, pterm_app u v -->lex t -> 
                (exists t', u =e pterm_abs t' /\ t =e (t'[v])) \/
                (exists u', t =e pterm_app u' v /\  u -->lex u') \/ 
                (exists v', t =e pterm_app u v' /\  v -->lex v').
Proof.
 intros t u v H. case H; clear H; intros t0 H; case H; clear H; intros t1 H.
 destruct H; destruct H0. apply eqC_app_term in H. 
 case H; clear H; intros u0 H; case H; clear H; intros v0 H.
 destruct H; destruct H2. rewrite <- H in H0. clear H t0.
 inversion H0. inversion H. inversion H6.
 left. exists t3. split. rewrite H9. rewrite H2. reflexivity.
 rewrite <- H3. rewrite H12. rewrite H1. reflexivity.
 inversion H6. right. left. exists t'. split. rewrite <- H3. rewrite H6. rewrite H1. reflexivity.
 rewrite <- H2. apply ctx_to_mod_eqC; trivial.
 right. right. exists u'. split. rewrite <- H2. rewrite H6. rewrite H1. reflexivity.
 rewrite <- H3. apply ctx_to_mod_eqC; trivial.
Qed.

Lemma lex_abs : forall t u, pterm_abs t -->lex u ->
                (exists L t', u =e pterm_abs t' /\ (forall x, x \notin L -> (t ^ x) -->lex (t' ^ x))).
Proof.
 intros t u H. case H; clear H; intros t0 H; case H; clear H; intros t1 H. 
 destruct H; destruct H0. apply eqC_abs_term in H. 
 case H; clear H; intros u0 H; case H; clear H; intros L H.
 destruct H. rewrite <- H in H0. clear H t0.
 inversion H0. inversion H. inversion H5. inversion H5.
 exists (L0 \u L). exists t'. split. rewrite <- H1. rewrite H4. reflexivity.
 intros x H5. apply notin_union in H5. destruct H5. rewrite <- H2; trivial.
 apply ctx_to_mod_eqC. apply H3; trivial.
Qed.

Lemma lex_R_list_regular : forall lt lt', R_list lex lt lt' -> (term %% lt <-> term %% lt').
Proof.
 intros lt lt' H. unfold R_list in H. 
 case H; clear H; intros t H.
 case H; clear H; intros t' H.
 case H; clear H; intros l0 H.
 case H; clear H; intros l1 H.
 destruct H. destruct H0. 
 rewrite H. rewrite H0. clear H H0.
 induction l0; simpl. apply ctx_sys_Bex_regular in H1. split.
 intro H2. split. apply H1. apply H2.
 intro H2. split. apply H1. apply H2. split.
 intro H2. split. apply H2. apply IHl0. apply H2.
 intro H2. split. apply H2. apply IHl0. apply H2.
Qed.

(** NF lex Properties **)

Lemma NF_eqC : forall t t', t =e t' -> NF lex t -> NF lex t'.
Proof.
 intros t t'. intros. unfold NF in *|-*.
 intros t1 H1. rewrite <- H in H1.
 apply (H0 t1); trivial.
Qed.

Lemma NF_fvar : forall x, NF lex (pterm_fvar x).
Proof.
 intros x t H'.
 case H'; clear H'. 
 intros t0 H0. case H0; clear H0.
 intros t1 H1. destruct H1. destruct H0.
 assert (Q : pterm_fvar x = t0).
  clear H0 H1 t1. gen_eq t1 : (pterm_fvar x).
  intro H1. induction H. rewrite H1. rewrite H1 in H.
  inversion H; trivial. clear H H1 H2 H3 s t0. inversion H0; trivial.
  rewrite IHtrans_closure in H. rewrite H1. rewrite H1 in H. inversion H.
  inversion H2; trivial. rewrite H1 in H. symmetry. inversion H. inversion H2; trivial.
 rewrite <- Q in H0. inversion H0. inversion H2. inversion H5. inversion H5.
Qed.


Lemma NF_app_lex : forall t u v, NF lex u -> NF lex v -> (pterm_app u v -->lex t) -> 
               exists t', u =e pterm_abs t' /\ t =e (t'[v]).
Proof.
 intros t u v NFu NFv H. apply lex_app in H. case H; clear H; intro H.
 case H; clear H; intros t' H. exists t'; trivial.
 case H; clear H; intro H; case H; clear H; intros t' H; destruct H.
 assert (Q : ~ u -->lex t'). apply (NFu t'). contradiction.
 assert (Q : ~ v -->lex t'). apply (NFv t'). contradiction.
Qed.

Lemma NF_app_lex_eq : forall t u v, NF lex u -> NF lex v -> (pterm_app u v -->lex t) -> 
               exists t' t'' v', u = pterm_abs t' /\ t = (t''[v']).
Proof.
 intros t u v NFu NFv H. apply NF_app_lex in H; trivial.
 case H; clear H. intros t' H. destruct H.
 apply eqC_sym in H. apply eqC_abs_term in H.
 apply eqC_sym in H0. apply eqC_sub_term in H0.
 case H; clear H. intros t1 H. case H; clear H. intros L H. destruct H. 
 case H0; clear H0. intros t1' H0. case H0; clear H0. intros u' H0.
 exists t1 t1' u'. split. rewrite H. reflexivity. rewrite H0. reflexivity.
Qed.

Lemma NF_mult_app_var : forall x lt, NF lex %% lt -> NF lex ((pterm_fvar x) // lt).
Proof.
 intros x lt H. 
 induction lt; simpl in *|-*. apply NF_fvar.
 destruct H. assert (Q : NF lex (pterm_fvar x // lt)). apply IHlt; trivial.
 clear IHlt. unfold NF. intros t' H'. case eqdec_nil with (l := lt). intro H''.
 rewrite H'' in H'. simpl in H'.
 apply NF_app_lex_eq in H'; trivial. case H'; clear H'. intros t0 H'.
 case H'; clear H'. intros t0' H'. case H'; clear H'. intros v' H'.
 destruct H'. inversion H1.
 apply NF_fvar. intro H''.
 assert (Q' : exists t' u', (pterm_fvar x) // lt = pterm_app t' u').
  apply m_app_eq_app; trivial.
 case Q'; clear Q'. intros u H1. case H1; clear H1. intros v H1.
 rewrite H1 in H'. apply NF_app_lex_eq in H'; trivial.
 case H'; clear H'. intros t0 H'. case H'; clear H'. intros t0' H'.
 case H'; clear H'. intros v' H'.
 destruct H'. inversion H2; trivial. 
 rewrite <- H1; trivial. 
Qed.



Lemma lex_abs_not_NF : forall l t, l <> nil -> term (pterm_abs t // l) -> ~ NF lex (pterm_abs t // l).
Proof.
 intros. induction l. intro H'. apply H; trivial.
 simpl in *|-*. case eqdec_nil with (l := l). intro H'.
 rewrite H' in *|-*. simpl in *|-*. intro H1.
 apply (H1 (t[a])). apply ctx_to_mod_eqC. apply redex. 
 apply B_lx. apply term_distribute_over_application in H0.
 destruct H0. apply term_abs_to_body in H0. apply reg_rule_b; trivial.
 intro H'. apply term_distribute_over_application in H0. destruct H0.
 assert (Q : ~ NF lex (pterm_abs t // l)).
   apply IHl; trivial.
 clear IHl H'. intro H'. apply Q. intros t' H2.
 apply (H' (pterm_app t' a)). apply left_app_lex; trivial.
Qed. 

Lemma lex_sub_not_NF : forall x t u, body t -> term u -> x \notin (fv t) ->
      ~ NF lex (t ^ x) -> ~ NF lex (t[u]).
Proof.
 intros. intro H3. apply H2. clear H2.
 intros t0 H2. gen_eq t1 : (close t0 x). intro H4.
 replace t0 with (t1 ^ x) in H2. apply (H3 (t1 [u])).
 apply left_subst_lex with (L:= (fv t) \u (fv t1)); trivial.
 intros z Fr. apply notin_union in Fr. destruct Fr.
 apply ctx_sys_lex_red_rename with (x := x); trivial.
 rewrite H4. apply fv_close'. rewrite H4.
 rewrite open_close_var with (x := x); trivial.
 apply ctx_sys_Bex_regular in H2. apply H2.
Qed.  

Lemma lex_sub_not_NF' : forall t u, body t -> term u -> ~ NF lex (t[u]).
Proof.
  intros. apply body_size_induction with (t := t); trivial; intros; intro H'. 
  apply (H' u). apply ctx_to_mod_eqC. apply redex. apply sys_x_lx. apply reg_rule_var; trivial.
  apply (H' (pterm_fvar x)). apply ctx_to_mod_eqC. apply redex. apply sys_x_lx. apply reg_rule_gc; trivial.
  apply (H' (pterm_abs ((& t1)[u]))). apply ctx_to_mod_eqC. apply redex. apply sys_x_lx. apply reg_rule_lamb; trivial.
  rewrite body_eq_body'; unfold body'. simpl; trivial.
  apply (H' (pterm_app (t1[u]) (t2[u]))). apply ctx_to_mod_eqC. apply redex. apply sys_x_lx. apply reg_rule_app; trivial;
  rewrite body_eq_body' in *|-*; unfold body' in *|-*; simpl in *|-*; apply H2.
  case var_fresh with (L := fv t3). 
  intros x Hx. case fv_in_or_notin with (t := t3 ^ x) (x := x); intros.
  apply (H' ((& t1)[u][ t3[ u ] ])). apply ctx_to_mod_eqC. apply redex. apply sys_x_lx. apply reg_rule_comp; trivial.
  rewrite body_eq_body' in *|-*; unfold body' in *|-*; simpl in *|-*; split; trivial.
  rewrite term_eq_term'. unfold term'. apply not_body_term_fvar with (x := x); trivial.
  rewrite body_eq_body' in H2. unfold body' in H2. trivial. 
  assert (T : term t3).
    rewrite term_eq_term'; simpl. unfold term'.
    rewrite body_eq_body' in *|-; unfold body' in *|-.
    apply body_term_fvar with (x := x); trivial.
  clear x Hx H2 H5. rewrite eqC_redex in H'; trivial.
  generalize H'. case var_fresh with (L := fv ((& t1)[u])).
  intros x Fr. apply lex_sub_not_NF with (x := x); trivial.
  rewrite body_eq_body'. unfold body'. simpl.
  split. apply lc_at_bswap; try omega; trivial.
  rewrite <- body_eq_body'. apply term_is_a_body; trivial.
  unfold open. unfold bswap. simpl.  
  replace (open_rec 0 (pterm_fvar x) u) with u.
  apply H4.
  simpl in Fr. apply notin_union in Fr. apply Fr.
  rewrite size_bswap_rec; trivial. 
  rewrite body_eq_body'. unfold body'.
  rewrite <- lc_at_open with (u := pterm_fvar x); trivial.
  apply lc_at_bswap; try omega; trivial.
  rewrite open_lc_at; trivial. 
  rewrite <- term_eq_term'; trivial.
Qed.  


(** Inversion of the lex relation **)

Lemma lex_app_var : forall x t u, pterm_app (pterm_fvar x) t -->lex u -> 
                    exists t', u =e pterm_app (pterm_fvar x) t' /\ t -->lex t'.
Proof.
 intros x t u H. apply lex_app in H. 
 case H; clear H; intro H; case H; clear H.
 intros t' H. destruct H. apply eqC_fvar_term in H. apply False_ind. 
 generalize H. discriminate.
 intro H; case H; clear H. intros t' H. destruct H. apply False_ind.
 generalize H0. apply NF_fvar.
 intro H; case H; clear H. intros t' H. exists t'; trivial.
Qed.


Lemma lex_mult_app_var : forall x lt u, ((pterm_fvar x) // lt) -->lex u -> 
                        exists lt', u =e ((pterm_fvar x) // lt') /\ R_list lex lt lt'.
Proof.
 intros x lt. induction lt; simpl.
 intros u H. apply False_ind. generalize H. apply NF_fvar.
 intros u H. apply lex_app in H. case H; clear H; intro H.
 case H; clear H; intros t' H. destruct H. gen_eq t0 : (pterm_abs t').
 intro H'. case eqdec_nil with (l := lt). intro H''. rewrite H'' in H. simpl in H.
 apply eqC_fvar_term in H. rewrite H' in H. apply False_ind. generalize H. discriminate.
 intro H''. case m_app_eq_app with (t := (pterm_fvar x)) (lu := lt); trivial. intros u0 H1.
 case H1; clear H1; intros v0 H1. rewrite H1 in H. apply eqC_app_term in H.
 case H; clear H; intros u' H. case H; clear H; intros v' H. destruct H. destruct H2.
 rewrite H' in H. apply False_ind. generalize H. discriminate.
 case H; clear H; intro H; case H; clear H. intros t' H. destruct H.
 case eqdec_nil with (l := lt). intro H1. rewrite H1 in H0. simpl in H0. apply False_ind.
 generalize H0. apply NF_fvar. intro H1. case (IHlt t'); trivial. intros lt' Hlt'.
 destruct Hlt'. exists (a :: lt'). split. simpl. rewrite H. rewrite H2. reflexivity.
 unfold R_list. unfold R_list in H3. case H3; clear H3; intros t0 H3.
 case H3; clear H3; intros t1 H3. case H3; clear H3; intros l0 H3.
 case H3; clear H3; intros l1 H3. destruct H3. destruct H4.
 exists t0 t1. exists (a :: l0) l1. split. rewrite H3. simpl. reflexivity.
 split. rewrite H4. simpl. reflexivity. trivial.  
 intros a' H. destruct H. exists (a' :: lt). simpl. split; trivial.
 unfold R_list. exists a a'. exists (nil (A:=pterm)) lt. simpl. split.
 reflexivity. split; trivial.
Qed.

Lemma lex_mult_app_B : forall t t0 u lv, ((pterm_app (pterm_abs t) u) // lv) -->lex t0 -> 
                       (t0 =e ((t[u]) // lv)) \/
                       (exists L t', t0 =e ((pterm_app (pterm_abs t') u) // lv) /\
                       (forall x, x \notin L -> (t ^ x) -->lex (t' ^ x))) \/ 
                       (exists u', t0 =e ((pterm_app (pterm_abs t) u') // lv) /\
                       (u -->lex u')) \/         
                       (exists lv',  t0 =e ((pterm_app (pterm_abs t) u) // lv') /\
                       (R_list lex lv lv')).
Proof.
 intros t t0 u lv H.  generalize t t0 u H. clear t t0 u H.  induction lv.
 simpl. intros. generalize H. intro H'. apply lex_app in H.
 case H; clear H; intro H; case H; clear H.
 intros t' H. destruct H. left. 
 apply eqC_abs_term in H. 
 case H; clear H; intros t1 H; case H; clear H; intros L H.
 destruct H. assert (Q : t1 = t'). inversion H. reflexivity.
 apply ctx_sys_Bex_regular in H'. destruct H'. rewrite H0 in H3.
 rewrite <- Q in H3. apply subs_to_body in H3. destruct H3.
 rewrite H0. rewrite <- Q. apply eqC_subst_left with (L := L); trivial.
 intro H. case H; clear H; intros t1 H. destruct H. 
 right. left. apply lex_abs in H0.
 case H0; clear H0; intros L H0; case H0; clear H0; intros t2 H0.
 destruct H0. rewrite H0 in H. exists L t2. split; trivial.
 intro H. case H; clear H; intros v H. destruct H.
 right. right. left. exists v. split; trivial.
 simpl. intros. generalize H. intro H'. apply lex_app in H.
 case H; clear H; intro H; case H; clear H.
 intros t1 H1. destruct H1. case eqdec_nil with (l := lv).
 intro H1. rewrite H1 in H. simpl in H. apply eqC_app_term in H.
 case H; clear H; intros u' H. case H; clear H; intros v' H.
 destruct H. apply False_ind. generalize H. discriminate.
 intro H1. case m_app_eq_app with (t := pterm_app (pterm_abs t) u) (lu := lv); trivial.
 intros u0 H2. case H2; clear H2. intros v0 H2. rewrite H2 in H. 
 apply eqC_app_term in H.
 case H; clear H; intros u' H. case H; clear H; intros v' H.
 destruct H. apply False_ind. generalize H. discriminate.
 intro H. case H; clear H; intros u' H. destruct H.
 case (IHlv t u' u); clear IHlv; trivial. intro H1.
 left. rewrite H. rewrite H1. reflexivity. intro H1.
 case H1; clear H1; intro H1. 
 case H1; clear H1; intros L H1; case H1; clear H1; intros t' H1.
 destruct H1. right. left. exists L t'. split; trivial.
 rewrite H. rewrite H1. reflexivity. case H1; clear H1; intro H1.
 case H1; clear H1; intros u0 H1. destruct H1.
 right. right. left. exists u0. split; trivial.
 rewrite H. rewrite H1. reflexivity.
 case H1; clear H1; intros lv' H1. destruct H1.
 right. right. right. exists (a :: lv'). split. simpl.
 rewrite H. rewrite H1. reflexivity. unfold R_list in H2.
 case H2; clear H2; intros t1 H2. case H2; clear H2; intros t2 H2.
 case H2; clear H2; intros l0 H2. case H2; clear H2; intros l1 H2.
 destruct H2. destruct H3. unfold R_list. exists t1 t2. 
 rewrite H2. rewrite H3. exists (a :: l0) l1. split; trivial. split; trivial.
 intro H. case H; clear H; intros a' H. destruct H.
 right. right. right. exists (a' :: lv). simpl. split.
 rewrite H. reflexivity. unfold R_list. exists a a'. 
 exists (nil (A:=pterm)) lv; simpl. 
 split; trivial. split; trivial.
Qed.


(** SN lex Properties **)


Lemma SN_app_var : forall x t, SN lex t -> SN lex (pterm_app (pterm_fvar x) t).
Proof.
 intros x t H. case H; clear H. intros n H. exists n. generalize t H; clear t H.
 induction n. intros t H. rewrite <- NF_eq_SN0 in *|-*. 
 replace (pterm_app (pterm_fvar x) t) with ((pterm_fvar x) // (t :: nil)).
 apply NF_mult_app_var. simpl; split; trivial. simpl; trivial.
 intros t H. inversion H. apply SN_intro. intros u H'.
 apply lex_app_var in H'. case H'; clear H'; intros t' H'.
 destruct H'. case (H0 t'); clear H0; trivial. intros k H0. 
 destruct H0. exists n; split; try omega. rewrite H1. apply IHn.
 apply WSN with (k := k); try omega; trivial.
Qed.



Lemma SN_mult_app_var : forall x lt, term %% lt -> SN lex %% lt -> SN lex ((pterm_fvar x) // lt).
Proof.
 intros x lt T H. induction lt; simpl. exists 0. rewrite <- NF_eq_SN0. apply NF_fvar.
 simpl in *|-*. destruct T. destruct H. assert (H': SN lex (pterm_fvar x // lt)). apply IHlt; trivial. clear H2 IHlt.
 case H; clear H. intros n H. case H'; clear H'. intros n' H'.
 gen_eq k : (n + n'). intro Hk. exists k. generalize a lt n n'  H0 H1 H H' Hk. clear a lt n n' H0 H1 H H' Hk.
 induction k. intros. 
 assert (Qn : n = 0). symmetry in Hk. omega.
 assert (Qn': n' = 0). symmetry in Hk. omega. clear Hk.
 rewrite Qn in H. rewrite Qn' in H'. clear Qn Qn'.
 rewrite <- NF_eq_SN0 in *|-*. 
 replace (pterm_app (pterm_fvar x // lt) a) with ((pterm_fvar x) // (a :: lt)).
 apply NF_mult_app_var. simpl. split; trivial. clear a n n' H0 H.
 induction lt; simpl in *|-*; trivial. split. intros a' Ha'.
 apply (H' (pterm_app (pterm_fvar x // lt) a')).
 apply right_app_lex; trivial. rewrite term_mult_app. destruct H1. split; trivial.
 apply IHlt. apply H1. intros t' Ht'. apply (H' (pterm_app t' a)).
 apply left_app_lex; trivial. apply H1. simpl; trivial.
 intros. apply SN_intro. intros t' Ht'. inversion H. inversion H'.
 apply lex_app in Ht'. case Ht'; clear Ht'. intro Ht'. case Ht'; clear Ht'. intros u Ht'. destruct Ht'.
 case eqdec_nil with (l := lt). intro H6. rewrite H6 in H4. simpl in H4. apply eqC_fvar_term in H4. apply False_ind.
 generalize H4. discriminate. intro H6. case m_app_eq_app with (t := (pterm_fvar x)) (lu := lt); trivial.
 intros u0 H7. case H7; clear H7. intros v0 H7. rewrite H7 in H4. apply eqC_app_term in H4.
 case H4; clear H4. intros u' H4. case H4; clear H4. intros v' H4. destruct H4. apply False_ind.
 generalize H4. discriminate.
 intro H4. case H4; clear H4. intro H4. case H4; clear H4; intros u H4. destruct H4.
 case (H3 u); trivial; clear H3. intros k' H3. destruct H3. exists k. split; try omega.
 rewrite H4. apply lex_mult_app_var in H5. case H5; clear H5. intros lt' H5. destruct H5. rewrite H5.
 apply IHk with (n := n) (n' := n' - 1); trivial. apply lex_R_list_regular in H7. apply H7; trivial.
 apply WSN with (k := k'); try omega. rewrite <- H5; trivial. omega.
 intro H4. case H4; clear H4. intros a' H4. destruct H4. exists k; split; try omega.
 case (H2 a'); clear H2; trivial. intros k' H2. destruct H2. rewrite H4.
 apply IHk with (n := n - 1) (n' := n'); trivial. apply ctx_sys_Bex_regular in H5. apply H5.
 apply WSN with (k := k'); try omega; trivial. omega.
Qed.


Lemma lex_SN_abs : forall n L t, (forall x, x \notin L -> SN_ind n lex (t ^ x)) ->
                                 (SN_ind n lex (pterm_abs t)).
Proof.
 intros n L t. generalize t; clear t. induction n. 
 intros. rewrite <- NF_eq_SN0. setoid_rewrite <- NF_eq_SN0 in H.
 intros t' H'. apply lex_abs in H'. case H'; clear H'; intros L0 H'. case H'; clear H'; intros t0 H'.
 destruct H'. pick_fresh x. apply notin_union in Fr. destruct Fr. apply notin_union in H2. destruct H2.
 apply notin_union in H2. destruct H2. apply notin_union in H2. destruct H2.
 case H with (x := x) (t' := (t0 ^ x)); trivial. apply H1; trivial.
 intros t H. apply SN_intro. intros t' H'. exists n; split; try omega.
 apply lex_abs in H'. case H'; clear H'; intros L0 H'. case H'; clear H'; intros t0 H'.
 destruct H'. pick_fresh x. apply notin_union in Fr. destruct Fr. apply notin_union in H2. destruct H2.
 apply notin_union in H2. destruct H2. apply notin_union in H2. destruct H2.  apply notin_union in H2. destruct H2.
 rewrite H0. apply IHn. intros x' H8. destruct (H x'); trivial. case (H9 (t0 ^ x')).
 apply ctx_sys_lex_red_rename with (x := x); trivial. apply H1; trivial.
 intros k H10. destruct H10. apply WSN with (k := k); try omega; trivial.
Qed.


Lemma lex_SN_ind_rename : forall n x x' t, body t -> x' \notin ({{x}} \u (fv t)) -> SN_ind n lex (t ^ x) -> SN_ind n lex (t ^ x').
Proof.
 intros n x x' t B Fr H. apply notin_union in Fr; destruct Fr. apply notin_singleton in H0.
 generalize t B H0 H1 H. clear t B H0 H1 H. induction n.
 intros t B H0 H1 H. rewrite <- NF_eq_SN0 in *|-*. 
 intros t' H'. gen_eq t0 : (close t' x'). intro H2. 
 replace t' with (t0 ^ x') in H'. apply (H (t0 ^x)). apply ctx_sys_lex_red_rename with (x := x'); trivial. 
 rewrite H2. apply fv_close'. rewrite H2. rewrite open_close_var with (x := x'). reflexivity.
 apply ctx_sys_Bex_regular in H'. apply H'. intros t B H0 H1 H. destruct H.
 apply SN_intro. intros t' H'. exists n; split; try omega. gen_eq t0 : (close t' x'). intro H2.
 generalize H'. intro T. apply ctx_sys_Bex_regular in T. destruct T.
 replace t' with (t0 ^ x') in H'. case (H (t0 ^ x)); clear H. apply ctx_sys_lex_red_rename with (x := x'); trivial.
 rewrite H2. apply fv_close'. intros k H. destruct H.  replace t' with (t0 ^ x'). apply (IHn t0); trivial.
 apply ctx_sys_Bex_regular in H'. destruct H'. rewrite term_eq_term' in H7. unfold term' in H7. unfold open in H7.
 rewrite body_eq_body'. unfold body'. rewrite lc_at_open with (u := pterm_fvar x'); trivial.
 rewrite H2. apply fv_close'. apply WSN with (k := k); try omega; trivial.
 rewrite H2; rewrite open_close_var with (x := x'); try reflexivity; trivial.
 rewrite H2; rewrite open_close_var with (x := x'); try reflexivity; trivial.
Qed.

Lemma lex_SN_rename :  forall x x' t, body t -> x' \notin ({{x}} \u (fv t)) -> SN lex (t ^ x) -> SN lex (t ^ x').
Proof.
 intros. case H1; clear H1; intros n H1; exists n; apply lex_SN_ind_rename with (x := x); trivial.
Qed.

Lemma lex_SN_ind_swap : forall n x y t, SN_ind n lex t -> SN_ind n lex ([(x,y)]t).
Proof.
 intros. generalize t H. clear t H. induction n.
 intros. rewrite <- NF_eq_SN0 in *|-*. intros t' H'.
 apply (H ([(x,y)]t')). rewrite <- swap_inv with (t := t) (x := x) (y := y).
 apply ctx_sys_lex_red_swap; trivial.
 intros. inversion H. clear H. apply SN_intro. intros t' H'.
 rewrite <- swap_inv with (t := t') (x := x) (y := y).
 case (H0 ([(x, y)]t')). rewrite <- swap_inv with (t := t) (x := x) (y := y).
 apply ctx_sys_lex_red_swap; trivial.  
 intros k H. destruct H. exists n; split; try omega.  apply IHn; trivial.
 apply WSN with (k := k); try omega; trivial.
Qed.

Lemma lex_SN_swap : forall x y t, SN lex t -> SN lex ([(x,y)]t).
Proof. intros; case H; clear H; intros n H; exists n; apply lex_SN_ind_swap; trivial. Qed.

*)







