(** * Lists: Working with Structured Data *)

From LF Require Export Induction.
Module NatList.

Inductive free_bound_list : Type :=
  | nil 
  | bcons (x: string) (l : free_bound_list )
  | fcons (x: nat) (l : free_bound_list ).

Compute fcons 1 (bcons "x" nil).

Inductive lc_term : Type :=
  | lc_var (x: string)
  | lc_abs (fbl : free_bound_list)
  | lc_app (e1 e2: lc_term).

Fixpoint sizefbl (p: free_bound_list): nat :=
  match p with 
  | nil =>0
  | bcons x l => 1 + (sizefbl l)
  | fcons x l => 1 + (sizefbl l) end.

Fixpoint sizelct (p : lc_term) : nat :=
  match p with
  | lc_var x => 1
  | lc_abs fbl => 1 + (sizefbl fbl)
  | lc_app e1 e2 => (sizelct e1) + (sizelct e2)
  end.

Fixpoint htlct ( e : lc_term) : nat :=
  match e with
  | lc_var x => 0
  | lc_abs e1 => 1 + (ht e1)
  | lc_app e1 e2 => 1 + ( max (ht e1) (ht e2) )
  end.

Check lc_abs 0 (lc_var 5).
Check lc_var 5.
