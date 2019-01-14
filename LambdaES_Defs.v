(***************************************************************************
* Formalizing SN for lambda_ex						   *		
*									   *
* Definitions of explicit substitutions 				   *
* Brian Aydemir & Arthur Chargueraud, July 2007              	   	   *
* Fabien Renaud, 2011							   *
* Flávio L. C. de Moura, D. L. Ventura and W. Segundo, 2014                *
* Flávio L. C. de Moura, 2017                                              *
***************************************************************************)

Set Implicit Arguments.
Require Import Arith Metatheory.

(** Pre-terms are expressions arbitrarily built from the following constructors: *)
Inductive pterm : Set :=
  | pterm_bvar : nat -> pterm
  | pterm_fvar : var -> pterm
  | pterm_app  : pterm -> pterm -> pterm
  | pterm_abs  : pterm -> pterm
  | pterm_sub  : pterm -> pterm -> pterm 
  | pterm_sub' : pterm -> pterm -> pterm.

(** Bound and free variables have different constructors. In fact, [pterm_bvar] will be used to represent bound variables that are codified by deBruijn indexes. Free variables are represented with names, so the free variable x will be denoted by [pterm_fvar x]. The constructor [pterm_app] and [pterm_abs] are used respectively for representing applications and abstractions. Explicit substitutions appear in two flavors: with or without marks. Therefore, [pterm_sub t u] represents the term [t] with an explicit substitution [u], while [pterm_sub' t u] means that the explicit substitution is marked. The adopted notations for explicit substitutions are as follows: *)

Notation "t [ u ]" := (pterm_sub t u) (at level 70).
Notation "t [[ u ]]" := (pterm_sub' t u) (at level 70).

(** Opening up abstractions and substitutions *)
Fixpoint open_rec (k : nat) (u : pterm) (t : pterm) {struct t} : pterm :=
  match t with
  | pterm_bvar i    => if k === i then u else (pterm_bvar i)
  | pterm_fvar x    => pterm_fvar x
  | pterm_app t1 t2 => pterm_app (open_rec k u t1) (open_rec k u t2)
  | pterm_abs t1    => pterm_abs (open_rec (S k) u t1)
  | pterm_sub t1 t2 => pterm_sub (open_rec (S k) u t1) (open_rec k u t2)
  | pterm_sub' t1 t2 => pterm_sub' (open_rec (S k) u t1) (open_rec k u t2)
  end.

Definition open t u := open_rec 0 u t.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67). (* verificar *)
Notation "t ^ x" := (open t (pterm_fvar x)).   (* verificar *)

(** Variable closing *)
Fixpoint close_rec  (k : nat) (x : var) (t : pterm) {struct t} : pterm :=
  match t with
  | pterm_bvar i    => pterm_bvar i
  | pterm_fvar x'    => if x' == x then (pterm_bvar k) else pterm_fvar x'
  | pterm_app t1 t2 => pterm_app (close_rec k x t1) (close_rec k x t2)
  | pterm_abs t1    => pterm_abs (close_rec (S k) x t1)
  | pterm_sub t1 t2 => pterm_sub (close_rec (S k) x t1) (close_rec k x t2)
  | pterm_sub' t1 t2 => pterm_sub' (close_rec (S k) x t1) (close_rec k x t2)
  end.

Definition close t x := close_rec 0 x t.

Fixpoint fv (t : pterm) {struct t} : vars :=
  match t with
  | pterm_bvar i    => {}
  | pterm_fvar x    => {{x}}
  | pterm_app t1 t2 => (fv t1) \u (fv t2)
  | pterm_abs t1    => (fv t1)
  | pterm_sub t1 t2 => (fv t1) \u (fv t2)
  | pterm_sub' t1 t2 => (fv t1) \u (fv t2)
  end.

  
Fixpoint bswap_rec (k : nat) (t : pterm) {struct t} : pterm :=
  match t with
  | pterm_bvar i    => if k === i then (pterm_bvar (S k))
                       else (if (S k) === i then (pterm_bvar k) else (pterm_bvar i))
  | pterm_fvar x    => pterm_fvar x
  | pterm_app t1 t2 => pterm_app (bswap_rec k t1) (bswap_rec k t2)
  | pterm_abs t1    => pterm_abs (bswap_rec (S k) t1)
  | pterm_sub t1 t2 => pterm_sub (bswap_rec (S k) t1) (bswap_rec k t2)
  | pterm_sub' t1 t2 => pterm_sub' (bswap_rec (S k) t1) (bswap_rec k t2)
  end.

Definition bswap t := bswap_rec 0 t.
Notation "& t" := (bswap t) (at level 67).

(** Correctness of bswap: it replaces 0s by 1s and vice-versa. Any other index is preserved. *)
Fixpoint has_free_index (k:nat) (t:pterm) : Prop :=
  match t with
    | pterm_bvar n => if (k === n) then True else False
    | pterm_fvar x => False
    | pterm_app t1 t2 => (has_free_index k t1) \/ (has_free_index k t2)
    | pterm_abs t1 => has_free_index (S k) t1
    | pterm_sub t1 t2 => (has_free_index (S k) t1) \/ (has_free_index k t2)
    | pterm_sub' t1 t2 => (has_free_index (S k) t1) \/ (has_free_index k t2)
  end.

Lemma has_index: forall i, has_free_index i (pterm_bvar i).
Proof.
  intro i. simpl. case_nat. auto.
Qed.  
  
Lemma bswap_preserves: forall t, ~(has_free_index 0 t) -> ~(has_free_index 1 t) -> & t = t.
Proof.
  intro t. unfold bswap. generalize 0. gen t. induction t.
  - introv Hn HSn. destruct (n0 === n) as [ Heq | Hdiff ]; subst.
    + apply False_ind. apply Hn. apply has_index.
    + unfold bswap_rec. case_nat. case_nat.
      * subst. apply False_ind. apply HSn. apply has_index.        
      * reflexivity.
  - introv Hn HSn. reflexivity.
  - introv Hn HSn. simpl in *. apply Decidable.not_or in Hn.
    destruct Hn as [ Hnt1 Hnt2 ]. apply Decidable.not_or in HSn.
    destruct HSn as [ HSnt1 HSnt2 ]. rewrite IHt1. rewrite IHt2. reflexivity.
    assumption. assumption. assumption. assumption.          
  - introv Hn HSn. simpl in *. rewrite IHt. reflexivity. 
    intro HSn'. apply Hn. assumption. intro HSSn. apply HSn. assumption.
  - introv Hn HSn. simpl in *. apply Decidable.not_or in Hn.
    destruct Hn as [ Hnt1 Hnt2 ]. apply Decidable.not_or in HSn.
    destruct HSn as [ HSnt1 HSnt2 ]. rewrite IHt1. rewrite IHt2. reflexivity.
    assumption. assumption. assumption. assumption.
  - introv Hn HSn. simpl in *. apply Decidable.not_or in Hn.
    destruct Hn as [ Hnt1 Hnt2 ]. apply Decidable.not_or in HSn.
    destruct HSn as [ HSnt1 HSnt2 ]. rewrite IHt1. rewrite IHt2. reflexivity.
    assumption. assumption. assumption. assumption.
Qed.  

Fixpoint swap (x y : var) (t : pterm) {struct t} : pterm :=
  match t with
  | pterm_bvar i    => pterm_bvar i
  | pterm_fvar z    => if z == x then (pterm_fvar y) else 
                       if z == y then (pterm_fvar x) else pterm_fvar z
  | pterm_app t1 t2 => pterm_app (swap x y t1) (swap x y t2)
  | pterm_abs t1    => pterm_abs (swap x y t1)
  | pterm_sub t1 t2 => pterm_sub (swap x y t1) (swap x y t2)
  | pterm_sub' t1 t2 => pterm_sub' (swap x y t1) (swap x y t2)
  end.

Notation "[( x , y )] t" := (swap x y t) (at level 67).

(******************************************************)
(** * Definitions *)

(** ** Size of a term *)
Fixpoint pterm_size (t : pterm) {struct t} : nat :=
 match t with
 | pterm_bvar i    => 1
 | pterm_fvar x    => 1
 | pterm_abs t1    => 1 + (pterm_size t1)
 | pterm_app t1 t2 => 1 + (pterm_size t1) + (pterm_size t2)
 | pterm_sub t1 t2 => 1 + (pterm_size t1) + (pterm_size t2)
 | pterm_sub' t1 t2 => 1 + (pterm_size t1) + (pterm_size t2)
 end.

Lemma pterm_size_non_null : forall t, pterm_size t > 0.
Proof.
  induction t.
  simpl. auto.
  simpl. auto.  
  simpl. omega.
  simpl. omega.
  simpl. omega.
  simpl. omega.
Qed.

(** Implicit substitution, for free names *)
Fixpoint subst (z : var) (u : pterm) (t : pterm) : pterm :=
  match t with
  | pterm_bvar i    => pterm_bvar i
  | pterm_fvar x    => if x == z then u else (pterm_fvar x)
  | pterm_abs t1    => pterm_abs (subst z u t1)
  | pterm_app t1 t2 => pterm_app (subst z u t1) (subst z u t2)
  | pterm_sub t1 t2 => pterm_sub (subst z u t1) (subst z u t2)
  | pterm_sub' t1 t2 => pterm_sub' (subst z u t1) (subst z u t2)
  end.
Notation "[ z ~> u ] t" := (subst z u t) (at level 70).

(** ES terms are expressions without dangling deBruijn indexes. *)
Inductive term : pterm -> Prop :=
  | term_var : forall x,
      term (pterm_fvar x)
  | term_app : forall t1 t2,
      term t1 -> term t2 -> 
      term (pterm_app t1 t2)
  | term_abs : forall L t1,
      (forall x, x \notin L -> term (t1 ^ x)) ->
      term (pterm_abs t1)
  | term_sub : forall L t1 t2,
     (forall x, x \notin L -> term (t1 ^ x)) ->
      term t2 -> 
      term (pterm_sub t1 t2).

Lemma term_size_non_null : forall t, term t -> pterm_size t > 0.
Proof.
  intros t Ht. destruct t.
  simpl; auto.  
  simpl; auto.  
  simpl. omega.
  simpl. omega.
  simpl. omega.
  simpl. omega.
Qed.  

(** Body *) 
Definition body t := exists L, forall x, x \notin L -> term (t ^ x).

Hint Constructors term.

Fixpoint lc_at (k:nat) (t:pterm) {struct t} : Prop :=
  match t with 
  | pterm_bvar i    => i < k
  | pterm_fvar x    => True
  | pterm_app t1 t2 => lc_at k t1 /\ lc_at k t2
  | pterm_abs t1    => lc_at (S k) t1
  | pterm_sub t1 t2 => (lc_at (S k) t1) /\ lc_at k t2
  | pterm_sub' t1 t2 => False
  end.

Definition term' t := lc_at 0 t.

Definition body' t := lc_at 1 t.

(** Pure lambda terms. *)
Inductive Lterm : pterm -> Prop :=
  | Lterm_var : forall x,
      Lterm (pterm_fvar x)
  | Lterm_app : forall t1 t2,
      Lterm t1 -> 
      Lterm t2 -> 
      Lterm (pterm_app t1 t2)
  | Lterm_abs : forall L t1,
      (forall x, x \notin L -> Lterm (t1 ^ x)) ->
      Lterm (pterm_abs t1).

(** Body for pure lambda terms *) 
Definition Lbody t := exists L, forall x, x \notin L -> Lterm (t ^ x).

Hint Constructors Lterm.

(* (** up and down functions. *) *)
(* Fixpoint up_rec (n:nat) (t: pterm) : pterm := *)
(*   match t with *)
(*   | pterm_bvar i => if (leb n i) then pterm_bvar (S i) else pterm_bvar i *)
(*   | pterm_fvar x => pterm_fvar x *)
(*   | pterm_app t1 t2 => pterm_app (up_rec n t1) (up_rec n  t2) *)
(*   | pterm_abs t1 => pterm_abs (up_rec (S n) t1) *)
(*   | pterm_sub t1 t2 => pterm_sub (up_rec (S n) t1) (up_rec n t2) *)
(*   | pterm_sub' t1 t2 => pterm_sub' (up_rec (S n) t1) (up_rec n t2) *)
(*   end. *)

(* (** Increases by one every free index of t. *) *)
(* Definition up t := up_rec 0 t. *)

(* Lemma up_index_abs: forall n, n > 0 -> up (pterm_abs (pterm_bvar n)) = pterm_abs (pterm_bvar (S n)). *)
(* Proof. *)
(*   introv Hn. unfold up. *)
(*   destruct (n == 0). *)
(*   - subst. apply False_ind. inversion Hn. *)
(*   - change (up_rec 0 (pterm_abs (pterm_bvar n))) with (pterm_abs (up_rec 1 (pterm_bvar n))). *)
(*     f_equal. destruct n. *)
(*     + apply False_ind. apply n0; reflexivity. *)
(*     + simpl; reflexivity. *)
(* Qed. *)

(* (** refazer *) *)
(* Fixpoint down_rec (n:nat) (t: pterm) : pterm := *)
(*   match t with *)
(*   | pterm_bvar i => if (i === (S k)) /\ (leb n i) then (pterm_bvar k) else (pterm_bvar i) *)
(*   | pterm_fvar x => pterm_fvar x *)
(*   | pterm_app t1 t2 => pterm_app (down_rec n t1) (down_rec n  t2) *)
(*   | pterm_abs t1 => pterm_abs (down_rec (S n) t1) *)
(*   | pterm_sub t1 t2 => pterm_sub (down_rec (S n) t1) (down_rec n t2) *)
(*   | pterm_sub' t1 t2 => pterm_sub' (down_rec (S n) t1) (down_rec n t2) *)
(*   end. *)

(* (** Downgrades by one every non-null free index of t. *) *)
(* Definition down t := down_rec 0 t. *)

Inductive SN_ind (n : nat) (R : pterm -> pterm -> Prop) (t : pterm) : Prop :=
 | SN_intro : (forall t', R t t' -> exists k, k < n /\ SN_ind k R t') -> SN_ind n R t.

Definition SN (R : pterm -> pterm -> Prop) (t : pterm) := exists n, SN_ind n R t.
Definition NF (R : pterm -> pterm -> Prop) (t : pterm) := forall t', ~ R t t'.

Inductive SN_alt (R : pterm -> pterm -> Prop) (t : pterm) : Prop :=
| SN_nf : NF R t -> SN_alt R t
| SN_acc : forall t', R t t' -> SN_alt R t' -> SN_alt R t.
