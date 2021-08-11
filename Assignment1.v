(** * Lists: Working with Structured Data *)

From LF Require Export Induction.
Module NatList.

Inductive lc_term : Type:=
  | lc_var ( x : nat)
  | lc_abs (n : nat)  (e : lc_term)
  | lc_app (e1 e2 : lc_term).


Fixpoint size (p : lc_term) : nat :=
  match p with
  | lc_var x => 1
  | lc_abs x e => 1 + size e
  | lc_app e1 e2 => (size e1) + (size e2)
  end.

Fixpoint ht ( e : lc_term) : nat :=
  match e with
  | lc_var x => 0
  | lc_abs x e1 => 1 + (ht e1)
  | lc_app e1 e2 => 1 + ( max (ht e1) (ht e2) )
  end.


Check lc_app (lc_abs 3 (lc_var 5)) (lc_var 2).


Notation "M --> N" := (lc_app M N)
                     (at level 61, left associativity).

Check lc_var 1 --> lc_var 2 .

Fixpoint eqlc (e1 e2 : lc_term) : nat :=
  match e1 with
    | x match e2 with 
         | y => x =? y
         | false
        end
    | lc_abs

Fixpoint check_occurs (e1 e2 : lc_term) :=
  if e1