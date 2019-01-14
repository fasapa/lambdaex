(******************************************************
 * Formalization of XC function                       *
 *                                                    *
 * Fabrício S. Paranhos & Daniel L. Ventura 2017-2019 *
 ******************************************************)

Require Import Recdef.          (* Required for Function *)
Require Import Metatheory.      (* Variables metatheory *)
(* Explicit substitution definitions. *)
Require Import LambdaES_Defs LambdaES_Infra LambdaES_FV LambdaESLab Lambda_Ex.
Require Import Equation_C.
Require Import Rewriting.                    (* Rewriting theory *)
(* SN alternative definition *)
Require Import SN_Properties.
Require Import Coq.Bool.Bool.

(******************************************************************)
(** Extra usefull Chargueraud tactics *)
(******************************************************************)
(* Open existentials and conjunction from hypothesis *)
Ltac unpack_core :=
  repeat match goal with
         | H: _ /\ _ |- _ => destruct H
         | H: exists a, _ |- _ => destruct H
         end.
Ltac unpack_from H :=
  first [ progress (unpack_core)
        | destruct H; unpack_core ].
Tactic Notation "unpack" :=
  unpack_core.
Tactic Notation "unpack" constr(H) :=
  unpack_from H.

(* Instanciate with variables gathered fron context *)
Ltac exists_fresh_aux G y Fry :=
  let L := G in
  exists L; intros y Fry.

Ltac exists_fresh y Fry := exists_fresh_aux gather_vars y Fry.
Ltac exists_fresh_gen := let L := gather_vars in exists L; intros.

(******************************************************************)
(** Infraestrutura *)
(******************************************************************)
Coercion pterm_fvar : var >-> pterm.

(* ****************************************************************)
(* Basic tactic *)
(* ****************************************************************)
Ltac solve_arith_aux H := intros; simpl; H; auto with arith.
Tactic Notation "solve_arith" tactic(x) := solve_arith_aux x.
Tactic Notation "solve_arith" := solve_arith_aux idtac.

Tactic Notation "evars" ident(l1) ident(l2) constr(t) :=
  evar (l1 : t); evar (l2 : t).

Tactic Notation "notVar" constr(t) hyp(H) "as" ident(i) :=
  let x := fresh "x" in
  cuts i : (forall x : var, t <> x);
  try (unfold not; intros; subst; simpls; destruct eq_var_dec; inversion H).

Tactic Notation "notVar" constr(t) hyp(H) :=
  let G := fresh "notVar" in notVar t H as G.

(* ****************************************************************)
(* Lemas e táticas especificas *)
(* ****************************************************************)
Hint Resolve var_gen_spec has_fi_subst lab_term_var.
Hint Unfold lab_body bswap.

Lemma SNind_SNalt : forall R t, LambdaES_Defs.SN R t <-> SNalt R t. Admitted.

Lemma lab_term_abs_to_lab_body :
  forall t, lab_term (pterm_abs t) -> lab_body t.
Proof. introv H; inversion* H. Qed.

Ltac prove_lab_body :=
  match goal with
  | _ : forall x, x \notin _ -> lab_term (?t ^ x) |- lab_body ?t =>
    apply lab_term_abs_to_lab_body; eapply lab_term_abs; eauto
  | _ => idtac
  end.

Ltac prove_lab_term :=
  match goal with
  | H : term ?t |- lab_term ?t => apply term_is_lab_term in H; auto
  end.

Tactic Notation "unpack_union" "in" hyp(H) := apply notin_union in H; destruct H.
Tactic Notation "unpack_union" "in" hyp(H) "as" simple_intropattern (I) :=
  apply notin_union in H; destruct H as I.

Ltac unpack_union :=
  match goal with
  | H : _ \notin _ \u _ |- _ =>
    let U1 := fresh "U1" in
    let U2 := fresh "U2" in unpack_union in H as [U1 U2]; unpack_union
  | |- _ \notin _ \u _ => simpl; apply notin_union; split~
  | _ => idtac
  end.

Ltac solve_notin_noteq :=
  match goal with
  | H : ?x \notin {{?x}} |- _ => apply notin_same in H; contradiction
  | H : ?x \notin {{?y}} |- _ =>
    match goal with
    | |- ?x = ?y => solve [ congruence | symmetry; congruence ]
    | |- ?x <> ?y => apply notin_singleton_r in H; solve [congruence | apply not_eq_sym; congruence]
    end
  | |- _ \notin fv (_ ^ _) => apply fv_notin_open; subst~; eauto
  end.

Ltac change_bswap_fv :=
  match goal with
  | |- context[ fv(& ?t) ] => rewrite (fv_bswap_rec 0)
  | _ => idtac
  end.

Hint Extern 4 (lab_body _) => prove_lab_body.
Hint Extern 4 (lab_term _) => prove_lab_term.
Hint Extern 4 => change_bswap_fv.
Hint Extern 6 => solve_notin_noteq.

(* Induction on lab_term size *)
Theorem lab_term_size_induction : forall P : pterm -> Prop,
    (forall x, P (pterm_fvar x)) ->
    (forall t, lab_body t ->
          (forall t' x, x \notin fv t' -> pterm_size t' = pterm_size t ->
                   lab_term (t' ^ x) -> P (t' ^ x)) -> P (pterm_abs t)) ->
    (forall t1 t2,
        lab_term t1 -> P t1 -> lab_term t2 -> P t2 -> P (pterm_app t1 t2)) ->
    (forall t1 t2, lab_term t2 -> P t2 -> lab_body t1 ->
              (forall t' x, x \notin fv t' -> pterm_size t' = pterm_size t1 ->
                       lab_term (t' ^ x) -> P (t' ^ x)) -> P (t1[t2])) ->
    (forall t1 t3, term t3 -> P t3 -> lab_body t1 ->
              (forall t2 x, x \notin fv t2 -> pterm_size t2 = pterm_size t1 ->
                       lab_term (t2 ^ x) -> P (t2 ^ x)) -> P (t1 [[t3]])) ->
    (forall t, lab_term t -> P t).
Proof with simpl; abstract omega.
  introv ? Habs Happ Hsub Hsub' ?; gen_eq n: (pterm_size t); gen t;
    induction n as [? IH] using peano_induction; introv Eq ?; subst; inverts~ Eq.
  - (* app *)
    apply~ Happ; apply~ IH...
  - (* abs *)
    apply~ Habs; intros; apply~ IH; unfold open;
      rewrite <- pterm_size_open_var...
  - (* sub *)
    apply~ Hsub;
      [apply~ IH | intros; apply~ IH; unfold open; rewrite <- pterm_size_open_var]...
  - (* subs' *)
    apply~ Hsub';
      [apply~ IH | intros; apply~ IH; unfold open; rewrite <- pterm_size_open_var]...
Qed.

Lemma close_fv_notin :
  forall t x y, x <> y -> x \notin fv t -> x \notin fv (close t y).
Proof.
  unfold close; intro t; generalize dependent 0; induction t; intros; simpls~;
    destruct~ (eq_var_dec); simpls~.
Qed.

Lemma close_eq :
  forall t1 t2 x, t1 = t2 -> (close t1 x) = (close t2 x).
Proof. intros; subst~. Qed.

Hint Resolve close_fv_notin.

(* ****************************************************************)
(* Notação *)
(* ****************************************************************)
Notation "t ->_Bxc u" := (ES_contextual_closure sys_Bx t u) (at level 66).

(******************************************************************)
(** Propriedades substituição *)
(******************************************************************)
Lemma subst_preserve_body :
  forall t (x z : var), body t -> body ([z ~> x] t).
Proof.
  intros; unfold body in *; unpack; exists_fresh_gen; rewrite~ subst_open_var.
Qed.

Lemma subst_eq :
  forall t1 t2 z u, t1 = t2 -> (subst z u t1) = (subst z u t2).
Proof. intros; subst~. Qed.

Lemma subst_inverse :
  forall t (z x: var), x \notin fv t -> [x ~> z]([z ~> x] t) = t.
Proof.
  induction t; intros; simpl in *; try (rewrite IHt1,IHt2; auto); auto.
  - destruct (eq_var_dec); simpl in *; destruct~ (eq_var_dec); subst~.
  - rewrite~ IHt.
Qed.

Corollary bswap_subst_comm :
  forall t (z x : var), [z ~> x](&t) = &([z ~> x] t).
Proof. intros; apply subst_bswap_rec; simpls~. Qed.

Lemma subst_fv_notin :
  forall t (x z : var), z <> x -> z \notin fv ([z ~> x]t).
Proof. induction t; intros; simpls~; destruct~ (eq_var_dec); simpls~. Qed.

Lemma subst_eqvar : forall t x, [x ~> x]t = t.
Proof.
  induction t; simpls~; intros; try (erewrite IHt1,IHt2; auto);
    [destruct~ eq_var_dec | erewrite IHt; auto].
Qed.

Lemma subst_close_var : forall t (z x a : var),
    a <> z -> a <> x -> [z ~> x](close t a) = close ([z ~> x]t) a.
Proof.
  intros; destruct (z == x);
    [subst; do 2 rewrite~ subst_eqvar | rewrite~ subst_close; simpls~].
Qed.

Hint Resolve subst_preserve_body subst_term subst_fv_notin.

(******************************************************************)
(** Propriedades reduções *)
(******************************************************************)
(* ****************************************************************)
(* Equação_C e variáveis livres. *)
(* ****************************************************************)
Lemma eqc_fv_notin : forall t t' x, eqc t t' -> (x \notin fv t <-> x \notin fv t').
Proof.
  introv Heqc; destruct Heqc; simpl; split~.
Qed.

Lemma eqc_ctx_fv_notin : forall t t' x, t =c t' -> (x \notin fv t <-> x \notin fv t').
Proof with solve [auto | eauto].
  induction 1 as [| ? ? ? ? IH | ? ? ? ? IH | ? ? ? ? IH | ? ? ? ? ? IH | ? ? ? ? IH]; simpl.
  - eapply eqc_fv_notin in H...
  - split; intros; unpack_union; apply IH in U1...
  - split; intros; unpack_union; apply IH in U2...
  - split; intros; pick_fresh z; unpack_union; apply (@fv_notin_open _ _ z);
      try (apply~ IH; apply~ fv_notin_open)...
  - split; intros; pick_fresh z; unpack_union; apply (@fv_notin_open _ _ z);
      try (apply~ IH; apply~ fv_notin_open)...
  - split; intros; unpack_union; apply IH in U2...
Qed.

Lemma eqc_trans_fv_notin : forall t t' x, t =c+ t' -> (x \notin fv t <-> x \notin fv t').
Proof.
  induction 1 as [| ? ? ? Heqc ? IH ];
    [ apply~ eqc_ctx_fv_notin |
      split; intros; [ apply~ IH; apply~ (eqc_ctx_fv_notin _ _ x Heqc) |
                       apply~ (eqc_ctx_fv_notin _ _ x Heqc); apply~ IH ] ].
Qed.

Lemma eqC_fv_notin : forall t t' x, t =e t' -> (x \notin fv t <-> x \notin fv t').
Proof. induction 1; [split~ | apply~ eqc_trans_fv_notin]. Qed.

(* ****************************************************************)
(* Reduções e variáveis livres. *)
(* ****************************************************************)
Lemma ruleb_fv_notin :
  forall t t' x, t ->_B t' -> (x \notin fv t <-> x \notin fv t').
Proof. introv Hb; destruct Hb; simpl in *; split~. Qed.

Lemma sysx_fv_notin :
  forall t t' x, t ->_x t' -> (x \notin fv t -> x \notin fv t').
Proof. introv Hx Hfv; destruct~ Hx; simpl in *; auto. Qed.

Lemma sysBx_fv_notin : forall t t' x, t ->_Bx t' -> (x \notin fv t -> x \notin fv t').
Proof.
  introv Hb ?; destruct Hb as [a b | a b];
    [apply~ (ruleb_fv_notin a b) | apply~ (sysx_fv_notin a b) ].
Qed.

Lemma sysBx_ctx_fv_notin : forall t t' x, t ->_Bxc t' -> (x \notin fv t -> x \notin fv t').
Proof.
  induction 1 as [| | | ? ? ? ? IH | ? ? ? ? ? IH | ]; simpl; auto;
    solve [apply~ sysBx_fv_notin |
           intros; pick_fresh z; unpack_union; apply (@fv_notin_open _ _ z);
           try (apply~ IH; apply~ fv_notin_open); auto ].
Qed.

Lemma lex_fv_notin :
  forall t t' x, t -->lex t' -> (x \notin fv t -> x \notin fv t').
Proof.
  unfolds lex,red_ctx_mod_eqC; introv [? [?  [Ht [HES Ht'] ] ] ]; intros;
    eapply eqC_fv_notin in Ht; eapply eqC_fv_notin in Ht'; eapply sysBx_ctx_fv_notin in HES;
  [eapply Ht' | eapply Ht]; eauto.
Qed.

(******************************************************************)
(** Interação substituição com o cálculo. *)
(******************************************************************)
Corollary eqC_subst_var :
  forall t t' (x z : var), t =e t' -> ([z ~> x]t) =e ([z ~> x]t').
Proof. intros; lets HH: @reflexive_reduction eqc_ctx x; apply~ red_all_eqC. Qed.

Lemma ruleb_subst_var :
  forall t t' (x z : var), t ->_B t' -> ([z ~> x]t) ->_B ([z ~> x]t').
Proof. introv Hb; destruct Hb; simpls; constructor; auto. Qed.

Lemma sysx_subst_var :
  forall t t' (x z : var), t ->_x t' -> ([z ~> x]t) ->_x ([z ~> x]t').
Proof.
  introv Hx; destruct Hx; simpls~; try rewrite bswap_subst_comm; constructor~.
Qed.

Lemma Bx_subst_var :
  forall t t' (x z : var), t ->_Bx t' -> ([z ~> x]t) ->_Bx ([z ~> x]t').
Proof.
  destruct 1; [apply B_lx; apply~ ruleb_subst_var | apply sys_x_lx; apply~ sysx_subst_var].
Qed.

Lemma Bcx_subst_var :
  forall t t' (x z : var), t ->_Bxc t' -> ([z ~> x]t) ->_Bxc ([z ~> x]t').
Proof.
  induction 1;
    [apply~ ES_redex | apply~ ES_app_left | apply~ ES_app_right |
     apply ES_abs_in with (L := L \u {{z}})     |
     apply ES_subst_left with (L := L \u {{z}}) |
     apply~ ES_subst_right]; intros; do 2 (try rewrite~ subst_open_var);
      apply~ Bx_subst_var.
Qed.

Lemma lex_subst_var :
  forall t t' (x z: var), t -->lex t' -> ([z ~> x]t) -->lex ([z ~> x]t').
Proof.
  destruct 1 as [a [b [Ht [HES Ht'] ] ] ];
    apply (eqC_subst_var _ _ x z) in Ht; apply (eqC_subst_var _ _ x z) in Ht';
      exists ([z ~> x]a) ([z ~> x]b); splits~; apply~ Bcx_subst_var.
Qed.

(* ****************************************************************)
(* Lemmas de formato. *)
(* ****************************************************************)
Lemma subst_format_app :
  forall (t t1 t2 : pterm) z u,
    (forall x : var, t <> x) ->
    pterm_app t1 t2 = ([z ~> u]t) ->
    exists t' t'', t = pterm_app t' t'' /\ t1 = ([z ~> u]t') /\ t2 = ([z ~> u]t'').
Proof.
  introv Hfvar Hsub; induction t; inversion~ Hsub;
    [ specialize (Hfvar z); destruct (eq_var_dec); congruence | do 2 eexists; split~ ].
Qed.

Lemma subst_format_abs :
  forall (t t' : pterm) z u,
    (forall x : var, t <> x) ->
    pterm_abs t' = ([z ~> u]t) ->
    exists t'', t = pterm_abs t'' /\ t' = ([z ~> u]t'').
Proof.
  introv Hfvar Hsub; induction t; inversion~ Hsub;
    [ specialize (Hfvar z); destruct (eq_var_dec); congruence | eexists; split~ ].
Qed.

Lemma subst_format_sub :
  forall (t t' t'' : pterm) z u,
    (forall x : var, t <> x) ->
    pterm_sub t' t'' = ([z ~> u]t) ->
    exists t1 t2, t = pterm_sub t1 t2 /\ t' = ([z ~> u]t1) /\ t'' = ([z ~> u]t2).
Proof.
    introv Hfvar Hsub; induction t; inversion~ Hsub;
      [ specialize (Hfvar z); destruct (eq_var_dec); congruence | do 2 eexists; split~ ].
Qed.

(******************************************************************)
(** Reduções preservam a substituição. *)
(******************************************************************)
Ltac expand_format_core Hformat :=
  let F := fresh "Format" in
  let G := fresh "notVar" in
  match type of Hformat with
  | pterm_sub ?t1 ?t2 = subst ?z ?x ?t =>
    notVar t Hformat as G; lets F: subst_format_sub;
    specialize (F t t1 t2 z x G Hformat)
  | pterm_app ?t1 ?t2 = subst ?z ?x ?t =>
    notVar t Hformat as G; lets F: subst_format_app;
    specialize (F t t1 t2 z x G Hformat)
  | pterm_abs ?t1 = subst ?z ?x ?t =>
    notVar t Hformat as G; lets F: subst_format_abs;
    specialize (F t t1 z x G Hformat)
  | ?u = subst ?z ?x ?t => apply (subst_eq _ _ x (pterm_fvar z)) in Hformat
  end; clear Hformat; clear G; unpack.

Ltac expand_subst :=
  match goal with
  | H : ?t1 ^ ?x = subst ?z ?u ?t2 |- _ =>
    apply (close_eq _ _ x) in H; rewrite <- close_open_term in H; auto
  | H : ?t1 = subst ?z ?u ?t2 |- _ => expand_format_core H
  | _ => idtac
  end.

Tactic Notation "expand_format" hyp(H) := expand_format_core H.

Lemma eqc_preserve_var_subst :
  forall t t' (x z : var),
    x \notin fv t -> eqc ([z ~> x]t) t' -> exists t'', t' = ([z ~> x]t'') /\ x \notin fv t''.
Proof.
  induction t as [ | | | | ? ? T2 | ]; simpls; introv ? Heqc; try destruct (eq_var_dec);
    inversion Heqc as [? ? ? ? ? Hsub]; expand_subst; (* expand_format Hsub; *)
      exists ((& x0 [T2]) [x1]); split; subst; simpls~; rewrite~ bswap_subst_comm.
Qed.

Lemma eqc_ctx_preserve_var_subst :
  forall t t' (x z : var),
    x \notin fv t -> ([z ~> x]t) =c t' -> exists t'', t' = ([z ~> x]t'') /\ x \notin fv t''.
Proof.
  introv Hfv Heqc; lets Heqc2:Heqc; gen_eq : ([z ~> x]t); gen t;
    induction Heqc as
      [| ? ? ? HES IH | ? ? ? HES IH | ? ? ? HES IH | ? ? ? ? HES IH | ? ? ? HES IH ];
    intros ? ? Hf; subst.
  - eapply eqc_preserve_var_subst in Hfv; eauto.
  - expand_subst; subst; simpls; unpack_union in Hfv as [U1 ?];
      specialize (IH HES _ U1 eq_refl); unpack; subst; evars l1 l2 pterm.
        exists (pterm_app l1 l2); subst l1 l2; simpls~.
  - expand_subst; subst; simpls; unpack_union in Hfv as [? U2];
      specialize (IH HES _ U2 eq_refl); unpack; subst; evars l1 l2 pterm.
        exists (pterm_app l1 l2); subst l1 l2; simpls~.
  - pick_fresh a; expand_subst; subst; simpls; unpack_union; evar (w : pterm);
      cuts Hxa : (x \notin fv (w^a)); simpls;
        [ cuts Heq : (([z ~> x]w) ^ a = ([z ~> x]w ^ a));
          [ specialize (IH _ U1 (HES _ U1) _ Hxa Heq); subst w | apply~ subst_open_var] |
          apply fv_notin_open; subst w; eauto ]; clear Hxa Heq HES; unpack; expand_subst;
          subst; evar (w : pterm); exists (pterm_abs (close w a));
            split; simpls~; [rewrite subst_close_var; subst w; eauto | auto].
  - pick_fresh a; expand_subst; subst; simpls; unpack_union; subst; evar (w : pterm).
      cuts Hxa : (x \notin fv (w^a)); simpls;
        [ cuts Heq : (([z ~> x]w) ^ a = ([z ~> x]w ^ a));
          [ specialize (IH _ U2 (HES _ U2) _ Hxa Heq); subst w | apply~ subst_open_var] |
          apply fv_notin_open; subst w; eauto ]; clear Hxa Heq HES; unpack; expand_subst;
          subst; evars w1 w2 pterm; exists ((close w1 a) [w2]);
            split; simpls~; [rewrite subst_close_var; subst w1 w2; eauto | auto].
  - expand_subst; subst; simpls; unpack_union in Hfv as [? U];
      specialize (IH HES _ U eq_refl); unpack; subst; evars l1 l2 pterm;
        exists (l1 [l2]); subst l1 l2; simpls~.
Qed.

Lemma eqc_trans_preserve_var_subst :
  forall t t' (x z : var),
    x \notin fv t -> ([z ~> x]t) =c+ t' -> exists t'', t' = ([z ~> x]t'') /\ x \notin fv t''.
Proof.
  introv ? Htrans; lets _:Htrans; gen_eq : ([z ~> x]t); gen t;
    induction Htrans as [| ? ? ? Hc ? IH]; intros; subst;
      [eapply eqc_ctx_preserve_var_subst | apply eqc_ctx_preserve_var_subst in Hc; unpack];
      eauto.
Qed.

Lemma eqC_preserve_var_subst :
  forall t t' (x z : var),
    x \notin fv t -> ([z ~> x]t) =e t' -> exists t'', t' = ([z ~> x]t'') /\ x \notin fv t''.
Proof.
  introv ? HeqC; lets _:HeqC; gen_eq : ([z ~> x]t); gen t;
    induction HeqC as [| ? ? H]; intros; subst;
      [eexists | apply eqc_trans_preserve_var_subst in H]; auto.
Qed.

Lemma B_preserve_var_subst :
  forall t t' (x z : var),
    x \notin fv t -> ([z ~> x]t) ->_B t' -> exists t'', t' = ([z ~> x]t'') /\ x \notin fv t''.
Proof.
  introv ? HB; induction t; simpls; inversion HB as [? ? ? ? Heq].
  - destruct eq_var_dec; inversion Heq.
  - expand_subst; subst; simpls; evars l1 l2 pterm.
    exists (l1 [l2]); subst l1 l2; simpls; split~.
Qed.

Lemma syslx_preserve_var_subst :
  forall t t' (x z : var),
    x \notin fv t -> ([z ~> x]t) ->_x t' -> exists t'', t' = ([z ~> x]t'') /\ x \notin fv t''.
Proof.
  introv ? Hx; inversion Hx; subst; simpls.
  - expand_subst; subst; simpls; evar (w : pterm); exists w; subst w; eauto.
  - expand_subst; subst; simpls; evar (w : pterm); exists w; subst w; eauto.
  - do 2 expand_subst; subst; simpls;
      evar (w1: pterm); evar (w2 : pterm); evar (w3 : pterm); evar (w4 : pterm).
    exists (pterm_app (w1 [w2]) (w3 [w4])); simpls; subst w1 w2 w3 w4; eauto.
  - do 2 expand_subst; subst; simpls; evars w1 w2 pterm;
      exists (pterm_abs (& (w1) [w2])); simpls; rewrite bswap_subst_comm;
        subst w1 w2; eauto.
  - do 2 expand_subst; subst; simpls;
      evar (w1: pterm); evar (w2 : pterm); evar (w3 : pterm); evar (w4 : pterm).
    exists ((& w1 [w2]) [w3 [w4] ] ); simpls; subst w1 w2 w3 w4; rewrite bswap_subst_comm;
      eauto.
Qed.

Lemma Bx_preserve_var_subst :
  forall t t' (x z : var),
    x \notin fv t -> ([z ~> x]t) ->_Bx t' -> exists t'', t' = ([z ~> x]t'') /\ x \notin fv t''.
Proof.
  introv ? HBx; inversion HBx; subst; simpls;
    [eapply B_preserve_var_subst | eapply syslx_preserve_var_subst]; eauto.
Qed.

Lemma Bxc_preserve_var_subst :
  forall t t' (x z : var),
    x \notin fv t -> ([z ~> x]t) ->_Bxc t' -> exists t'', t' = ([z ~> x]t'') /\ x \notin fv t''.
Proof.
  introv Hfv HBxc; lets _:HBxc; gen_eq : ([z ~> x]t); gen t;
    induction HBxc as [| ? ? ? ? IH | ? ? ? ? IH | ? ? ? ? IH | ? ? ? ? ? IH | ? ? ? ? IH];
    intros; subst.
  - eapply Bx_preserve_var_subst; eauto.
  - expand_subst; subst; simpls; unpack_union in Hfv as [U1 ?];
      specialize (IH _ U1 eq_refl); unpack; subst; evars w1 w2 pterm;
        exists (pterm_app w1 w2); simpls; subst w1 w2; eauto.
  - expand_subst; subst; simpls; unpack_union in Hfv as [? U2];
      specialize (IH _ U2 eq_refl); unpack; subst; evars l1 l2 pterm.
    exists (pterm_app l1 l2); subst l1 l2; simpls~.
  - pick_fresh a; expand_subst; subst; simpls; unpack_union; evar (w : pterm).
    cuts Hxa : (x \notin fv (w^a)); simpls;
      [ cuts Heq : (([z ~> x]w) ^ a = ([z ~> x]w ^ a));
        [ specialize (IH _ U1 _ Hxa Heq); subst w | apply~ subst_open_var] |
        apply fv_notin_open; subst w; eauto ]; clear Hxa Heq; unpack; expand_subst;
        subst; evar (w : pterm); exists (pterm_abs (close w a));
          split; simpls~; [rewrite subst_close_var; subst w; eauto | auto].
  - pick_fresh a; expand_subst; subst; simpls; unpack_union; evar (w : pterm).
    cuts Hxa : (x \notin fv (w^a)); simpls;
      [ cuts Heq : (([z ~> x]w) ^ a = ([z ~> x]w ^ a));
        [ specialize (IH _ U2 _ Hxa Heq); subst w | apply~ subst_open_var] |
        apply fv_notin_open; subst w; eauto ];
      clear Hxa Heq; unpack; expand_subst;
        subst; evars w1 w2 pterm; exists ((close w1 a) [w2]);
          split; simpls~; [rewrite subst_close_var; subst w1 w2; eauto | auto].
  - expand_subst; subst; simpls; unpack_union in Hfv as [? U];
    specialize (IH _ U eq_refl); unpack; subst; evars l1 l2 pterm;
        exists (l1 [l2]); subst l1 l2; simpls~.
Qed.

Lemma lex_preserve_var_subst :
  forall t t' (x z : var),
    x \notin fv t -> ([z ~> x]t) -->lex t' -> exists t'', t' = ([z ~> x]t'') /\ x \notin fv t''.
Proof.
  introv Hfv Hlex; lets _:Hlex; gen_eq : ([z ~> x]t); gen t;
    destruct Hlex; unpack; intros; subst.
  apply eqC_preserve_var_subst in H; auto; unpack; subst.
  apply Bxc_preserve_var_subst in H0; auto; unpack; subst.
  apply eqC_preserve_var_subst in H1; auto.
Qed.

(******************************************************************)
(** Substituição da redução implica redução *)
(******************************************************************)

(* Encontrar local melhor *)
Lemma eqc_subst:
  forall t t' (x z : var), x \notin fv t -> eqc t t' -> eqc ([z ~> x]t) ([z ~> x]t').
Proof.
  introv _ Heqc; destruct Heqc; simpl in *;
    rewrite bswap_subst_comm; constructor;
      apply subst_term; auto.
Qed.

Lemma eqc_ctx_subst :
  forall t t' (x z : var), x \notin fv t -> t =c t' -> ([z ~> x]t) =c ([z ~> x]t').
Proof.
  introv Hfv Hec; gen x z;
    induction Hec
    as [| ? ? ? ? IH | ? ? ? ? IH | ? ? ? ? IH | ? ? ? ? ? IH | ? ? ? ? IH];
    intros; simpls.
  - apply ES_redex; apply~ eqc_subst.
  - apply ES_app_left; apply~ IH.
  - apply ES_app_right; apply~ IH.
  - evar (wL : VarSet.t); apply (ES_abs_in _ _ _ ({{x}} \u {{z}} \u wL)); intros;
      do 2 rewrite~ subst_open_var; apply IH; subst wL; unpack_union; eauto.
  - evar (wL : VarSet.t); apply (ES_subst_left _ _ _ _ ({{x}} \u {{z}} \u wL)); intros;
      do 2 rewrite~ subst_open_var; apply IH; subst wL; unpack_union; eauto.
  - apply ES_subst_right; apply~ IH.
Qed.

Lemma subst_eqc_impl_eqc :
  forall t t' (x z : var),
    x \notin (fv t \u fv t') -> eqc ([z ~> x]t) ([z ~> x]t') -> eqc t t'.
Proof.
  introv Hfv HSeqc; inversion HSeqc as [? ? ? ? ? Ha Hb];
    apply (subst_eq _ _ x z) in Ha; apply (subst_eq _ _ x z) in Hb;
  rewrite subst_inverse in Ha; rewrite subst_inverse in Hb; subst~; simpls;
    rewrite bswap_subst_comm; apply eqc_def; auto.
Qed.

Lemma subst_eqc_ctx_impl_eqc_ctx :
  forall t t' (x z : var),
    x \notin (fv t \u fv t') -> ([z ~> x]t) =c ([z ~> x]t') -> t =c t'.
Proof.
  introv ? Hec; apply (eqc_ctx_subst _ _ z x) in Hec;
    [do 2 rewrite subst_inverse in Hec |
     destruct (z == x); subst; [rewrite~ subst_fresh | apply~ subst_fv_notin] ]; auto.
Qed.

Lemma subst_eqC_impl_eqC :
  forall t t' (x z : var), x \notin (fv t \u fv t') -> ([z ~> x]t) =e ([z ~> x]t') -> t =e t'.
Proof.
  introv ? HeC.
  apply (red_all_eqC x)
    with (t := [z ~> x]t) (t' := [z ~> x]t') (u := z) (u' := z) in HeC.
  - do 2 rewrite subst_inverse in HeC; auto.
  - constructor.
Qed.

Lemma eq_subst :
  forall t1 t2 (x z : var),
    x \notin fv t1 -> x \notin fv t2 -> ([z ~> x]t1) = ([z ~> x]t2) -> t1 = t2.
Proof.
  introv ? ? Heq; apply (subst_eq _ _ x z) in Heq; do 2 rewrite subst_inverse in Heq;
    auto.
Qed.

Lemma subst_B_impl_B:
  forall t t' (x z : var),
    x \notin (fv t \u fv t') -> ([z ~> x]t) ->_B ([z ~> x]t') -> t ->_B t'.
Proof.
  introv ? HB; apply (ruleb_subst_var _ _ z x) in HB;
    do 2 rewrite subst_inverse in HB; auto.
Qed.

Lemma subst_sysx_impl_sysx :
  forall t t' (x z : var),
    x \notin (fv t \u fv t') -> ([z ~> x]t) ->_x ([z ~> x]t') -> t ->_x t'.
Proof.
  introv ? Hs; apply (sysx_subst_var _ _ z x) in Hs;
    do 2 rewrite subst_inverse in Hs; auto.
Qed.

Lemma subst_sysBx_impl_sysBx :
  forall t t' (x z : var),
    x \notin (fv t \u fv t') -> ([z ~> x]t) ->_Bx ([z ~> x]t') -> t ->_Bx t'.
Proof.
  introv ? HBx; apply (Bx_subst_var _ _ z x) in HBx;
    do 2 rewrite subst_inverse in HBx; auto.
Qed.

Lemma subst_lex_impl_lex :
  forall t t' (x z : var),
    x \notin (fv t \u fv t') -> ([z ~> x]t) -->lex ([z ~> x]t') -> t -->lex t'.
Proof.
  introv ? Hlx; apply (lex_subst_var _ _ z x) in Hlx;
    do 2 rewrite subst_inverse in Hlx; auto.
Qed.

Lemma subst_var_preserve_nf :
  forall t (x z : var), x \notin fv t -> NF lex t -> NF lex ([z ~> x]t).
Proof.
  unfold NF in *; unfold not in *; introv ? HNF Hlex; lets Hlex2:Hlex;
    apply lex_preserve_var_subst in Hlex; unpack; subst~.
  apply subst_lex_impl_lex in Hlex2; evar (w : pterm); auto;
    specialize (HNF w); eapply HNF; subst w; eauto.
  Grab Existential Variables. auto.
Qed.

Lemma subst_var_preserve_sn :
  forall t (x z : var), x \notin (fv t) -> SNalt lex t -> SNalt lex ([z ~> x]t).
Proof.
  induction 2 as [| ? IH1 IH2].
  - apply SN_nf; apply~ subst_var_preserve_nf. (* Não é necessário *)
  - apply SN_acc; introv HSN1; cuts HSN2 : (([z ~> x]t) -->lex t'); auto.
    apply lex_preserve_var_subst in HSN1; unpack; auto; subst; apply~ IH2;
      apply subst_lex_impl_lex in HSN2; auto.
Qed.

Lemma subst_var_preserve_SN :
  forall t (x z : var), x \notin (fv t) -> LambdaES_Defs.SN lex t -> LambdaES_Defs.SN lex ([z ~> x]t).
Proof.
  intros; apply SNind_SNalt. apply SNind_SNalt in H0. apply~ subst_var_preserve_sn. Qed.
  

Lemma subst_preserve_lab_term :
  forall t (x z : var), x \notin (fv t) -> lab_term t -> lab_term ([z ~> x]t).
Proof.
  induction 2 as [| | a b c IH e f | a b c d IH f| a b c d IH]; simpls*.
  - destruct eq_var_dec; subst~.
  - apply~ lab_term_app.
  - apply_fresh lab_term_abs; rewrite~ subst_open_var; apply~ IH; unpack_union;
      apply~ fv_notin_open.
  - apply_fresh lab_term_sub; auto; rewrite~ subst_open_var; apply~ IH; unpack_union;
      apply~ fv_notin_open.
  - apply_fresh lab_term_sub'; auto.
    + rewrite~ subst_open_var; apply~ IH; unpack_union; apply~ fv_notin_open.
    + apply SNind_SNalt; apply~ subst_var_preserve_sn; apply~ SNind_SNalt.
Qed.

Lemma lab_body_open_lab_term:
  forall t x, x \notin (fv t) -> lab_body t -> lab_term (t ^ x).
Proof.
  introv ? [? ?]; pick_fresh y; rewrite~ (@subst_intro y);
  apply~ subst_preserve_lab_term; unpack_union; apply~ fv_notin_open.
Qed.

(******************************************************************)
(** XC Function *)
(******************************************************************)
(* XC function: Trigger all marked explicit substitutions. *)
Function xc (t: pterm) {measure pterm_size t} : pterm :=
  match t with
  | pterm_app t1 t2  => pterm_app (xc t1) (xc t2)
  | pterm_abs t'     => let x := var_gen (fv t') in pterm_abs (close (xc (t'^x)) x)
  | pterm_sub t1 t2  => let x := var_gen (fv t1) in pterm_sub (close (xc (t1^x)) x) (xc t2)
  | pterm_sub' t1 t2 => let x := var_gen (fv t1) in (close (xc (t1^x)) x) ^^ t2
  | _                => t
  end.
Proof.
  - solve_arith.                (* pterm_size t1 < pterm_size (pterm_app t1 t2) *)
  - solve_arith.                (* pterm_size t2 < pterm_size (pterm_app t1 t2) *)
  -                             (* pterm_size t'^fv(t') < pterm_size (pterm_abs t') *)
    solve_arith (unfold open; rewrite <- pterm_size_open_var).
  - solve_arith.                (* pterm_size t2 < pterm_size (pterm_sub t1 t2) *)
  -                             (* pterm_size t1^fv(t1) < pterm_size (pterm_sub t1 t2) *)
    solve_arith (unfold open; rewrite <- pterm_size_open_var).
  -                             (* pterm_size t1^fv(t1) < pterm_size (pterm_sub' t1 t2) *)
    solve_arith (unfold open; rewrite <- pterm_size_open_var).
Defined.

Theorem xc_term_invariant : forall t : pterm , term t -> xc t = t.
Proof with auto.
  induction 1 as [|? ? IH| ? ? ? IH1 ? IH2 | ? ? ? IH1 ? IH2] using term_size_induction ;
    rewrite xc_equation ...
  -
    (* abs *)
    rewrite IH , <- close_open_term ...
  -
    (* app *)
    rewrite IH1 , IH2 ...
  -
    (* sub *)
    rewrite IH2 , IH1 , <- close_open_term ...
Qed.

Corollary xc_preserve_term : forall t : pterm, term t -> term (xc t).
Proof. intros; rewrite* xc_term_invariant. Qed.

Theorem xc_lab_term_term : forall t, lab_term t -> term (xc t).
Proof.
  introv Ht;
    induction Ht
    as [| ? ? IH | | ? ? ? ? ? IH | ? ? ? ? ? IH ] using lab_term_size_induction;
    rewrite xc_equation; try auto.
  -                    (* abs *)
    apply body_to_term_abs; apply close_var_body; apply~ IH;
      apply~ lab_body_open_lab_term.
  -                      (* sub *)
    apply~ body_to_subs; apply close_var_body; apply~ IH;
      apply~ lab_body_open_lab_term.
  -                      (* sub' *)
    apply~ body_open_term; apply~ close_var_body; apply~ IH;
      apply~ lab_body_open_lab_term.
Qed.

Ltac protect_left :=
  let x := fresh "left" in
  match goal with |- ?X = _ => sets x: X end.

Tactic Notation "name_var_gen" ident(x) :=
  match goal with
  | |- context [var_gen ?L] => sets x: (var_gen L)
  | H: context [var_gen ?L] |- _ => sets x: (var_gen L)
  end.


Lemma trm_size_rename : forall (x y : var) t,
  pterm_size ([x ~> y]t) = pterm_size t.
Proof.
  induction t; simpl; fequals. case_var~.
Qed.

Lemma close_var_rename : forall (y x : var) t,
  y \notin fv t ->
  close ([x ~> y]t) y = close t x.
Proof.
  introv Fr. unfold close. generalize 0. gen Fr.
  induction t; simpl; intros Fr i; fequals~.
  case_var; simpl; case_var~.
Qed.

Lemma notin_open (t1 t2: pterm) (x: var): x \notin fv t1 -> x \notin fv t2 -> x \notin fv (t1^^t2).
Proof.
  unfold open; generalize 0; induction t1; intros; simpls.
  - case_nat; auto.
  - auto.
  - unpack_union.
  - apply~ IHt1.
  - unpack_union.
  - unpack_union.
Qed.

Lemma xc_fv : forall t (x : var), lab_term t -> x \notin fv t -> x \notin fv (xc t).
Proof.
  introv HT; gen x; induction HT using lab_term_size_induction; intros.
  - simpl; assumption.
  - rewrite xc_equation; simpls; name_var_gen z. destruct (x == z).
    + subst. apply close_fresh.
    + apply~ close_fv_notin. apply H0.
      * apply var_gen_spec.
      * reflexivity.
      * apply~ lab_body_open_lab_term. apply var_gen_spec.
      * apply~ fv_notin_open.
  - rewrite xc_equation; simpls; unpack_union.
  - rewrite xc_equation; simpls; name_var_gen z; unpack_union; destruct (x == z).
    + subst. apply close_fresh.
    + apply~ close_fv_notin. apply H0.
      * apply var_gen_spec.
      * reflexivity.
      * apply~ lab_body_open_lab_term. apply var_gen_spec.
      * apply~ fv_notin_open.
  - rewrite xc_equation; simpls; name_var_gen z; unpack_union; destruct (x == z); apply~ notin_open.
    + subst; apply close_fresh.
    + apply~ close_fv_notin. apply H1.
      * apply var_gen_spec.
      * reflexivity.
      * apply~ lab_body_open_lab_term. apply var_gen_spec.
      * apply~ fv_notin_open.
Qed.  

Lemma subst_close :
  forall t u x y,
    x \notin fv u -> x <> y -> ([y ~> u]close t x) = close ([y ~> u]t) x.
Proof.
  introv Fr Neq. unfold close. generalize 0.
  induction t; intros i; simpl; fequal; auto.
  case_var.
  - simpl. case_var. simpl. case_var. auto.
  - case_var.
    + simpl. case_var. rewrite LambdaES_Infra.close_fresh; auto.
    + simpl. case_var. case_var. auto.
Qed.

Lemma xc_close: forall t m (x:var), lab_body t -> x \notin fv t -> (close (xc(t^x)) x)^^m = [x ~> m]xc(t^x).
Proof.
  intros; rewrite <- subst_as_close_open;
    [reflexivity | apply xc_lab_term_term; apply lab_body_open_lab_term; auto].
Qed.

Lemma xc_correct : forall m n: pterm,
    let x := var_gen (fv m) in
    lab_body m -> term n -> xc(m [[n]]) = [x ~> n]xc(m^x).
Proof.
  intros; rewrite xc_equation; name_var_gen z; rewrite xc_close; try apply notin_var_gen; auto.
Qed.
