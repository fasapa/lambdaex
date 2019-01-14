(***************************************************************************
* Formalization of SN for the lambda_ex calculus			   *
*									   *
* General rewriting definitions	for explicit substitutions		   * 
*									   *
* Fabien Renaud & Stephane Zimmerman, 2011				   *
* Flavio L. C. de Moura & Daniel L. Ventura & Washington R. Segundo, 2017  *
***************************************************************************)

Require Import Metatheory.
Require Import LambdaES_Defs LambdaESLab.
Require Import List.

Inductive ESlab_contextual_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
| ESlab_redex : forall t s, Red t s -> ESlab_contextual_closure Red t s
| ESlab_app_left : forall t t' u, ESlab_contextual_closure Red t t' -> 
	  		          ESlab_contextual_closure Red (pterm_app t u) (pterm_app t' u)
| ESlab_app_right : forall t u u', ESlab_contextual_closure Red u u' -> 
	  		           ESlab_contextual_closure Red (pterm_app t u) (pterm_app t u')
| ESlab_abs_in : forall t t' L, (forall x, x \notin L -> ESlab_contextual_closure Red (t^x) (t'^x)) ->
                                ESlab_contextual_closure Red (pterm_abs t) (pterm_abs t')
| ESlab_subst_left : forall t t' u L, (forall x, x \notin L -> ESlab_contextual_closure Red (t^x) (t'^x)) ->
                                      ESlab_contextual_closure Red  (pterm_sub t u) (pterm_sub t' u)
| ESlab_subst_right : forall t u u', ESlab_contextual_closure Red u u' -> 
	  	                     ESlab_contextual_closure Red  (pterm_sub t u) (pterm_sub t u')
| ESlab_lsubst_left : forall t t' u L, (forall x, x \notin L -> ESlab_contextual_closure Red (t^x) (t'^x)) -> ESlab_contextual_closure Red  (pterm_sub t u) (pterm_sub t' u)
| ESlab_lsubst_right : forall t u u', ESlab_contextual_closure Red u u' -> 
	  	                      ESlab_contextual_closure Red  (pterm_sub' t u) (pterm_sub' t u').

Inductive ESlab_p_contextual_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
  | ESlab_p_redex : forall t s, Red t s -> ESlab_p_contextual_closure Red t s
  | ESlab_p_app : forall t t' u u', ESlab_p_contextual_closure Red t t' -> ESlab_p_contextual_closure Red u u' ->
	  		          ESlab_p_contextual_closure Red (pterm_app t u) (pterm_app t' u')
  | ESlab_p_abs_in : forall t t' L, (forall x, x \notin L -> ESlab_p_contextual_closure Red (t^x) (t'^x)) -> 
                                  ESlab_p_contextual_closure Red (pterm_abs t) (pterm_abs t')
  | ESlab_p_subst : forall t t' u u' L, (forall x, x \notin L -> ESlab_p_contextual_closure Red (t^x) (t'^x)) -> 
                                      ESlab_p_contextual_closure Red u u' -> 
	                              ESlab_p_contextual_closure Red  (pterm_sub t u) (pterm_sub t' u')
  | ESlab_p_lsubst : forall t t' u u' L, (forall x, x \notin L -> ESlab_p_contextual_closure Red (t^x) (t'^x)) -> 
                                       ESlab_p_contextual_closure Red u u' -> 
	                               ESlab_p_contextual_closure Red (t[[u]]) (t'[[u']]).

Hint Constructors ESlab_contextual_closure ESlab_p_contextual_closure.