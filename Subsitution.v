(** * Lists: Working with Structured Data *)

From LF Require Export Induction.
From LF Require Export Tactics.
From A1 Require Export LC_term.

(*  
    Proving Subsitution lema
*)

Theorem substitution_x_x : forall (x:nat) ( e:lc_term),
  subsitute_lc x (lc_var x) e = e.
(* [x:=x]e = e*)
Proof. intros. generalize dependent x. induction e as [y'| e | e1 E1 e2 E2 ]. 
  - simpl. intros x. destruct (eqb y' x) eqn:E.
    -- apply eqb_true in E. rewrite E. reflexivity.
    -- reflexivity.
  - intros x0. induction x0.
    -- simpl. rewrite IHe. reflexivity. 
    -- simpl. rewrite IHe. reflexivity. 
  - simpl. intros x. rewrite E1. rewrite E2. reflexivity.
  Qed.   


Theorem substitution_x_e1_e1 : forall (x:nat) ( e1 e2:lc_term),
  subsitute_lc x e1 e2 = e2.
(* [x:=x]e = e*)
Proof




