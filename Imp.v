From Coq Require Import Strings.String.
Check string.


(** * Chapter 2: Introduction to operational semantics *)

Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)
Require Import Nat.


(* ####################################################### *)
(** §2.1 IMP syntax *)

Inductive aexp : Type :=
  | ANum   : nat          -> aexp
  | AId    : string       -> aexp
  | APlus  : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult  : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue  : bexp
  | BFalse : bexp
  | BEq    : aexp -> aexp -> bexp
  | BLe    : aexp -> aexp -> bexp
  | BNot   : bexp -> bexp
  | BAnd   : bexp -> bexp -> bexp
  | BOr    : bexp -> bexp -> bexp.

Inductive com : Type :=
  | CSkip  : com
  | CAsgn  : string -> aexp -> com
  | CSeq   : com -> com -> com
  | CIf    : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.



(* ####################################################### *)
(** §2.2 – 2.3 The evaluation of expressions *)


Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).
Notation "x || y" := (BOr x y) (in custom com at level 81, left associativity).
Open Scope com_scope.

Definition state := string -> nat.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{~ b1}> => negb (beval st b1)
  | <{b1 && b2}> => andb (beval st b1) (beval st b2)
  | <{b1 || b2}> => orb (beval st b1) (beval st b2)
  end.



(* ####################################################### *)
(** §2.4 The execution of commands *)


Notation "'skip'" :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

Definition t_update (m : string -> nat) (x : string) (v : nat) :=
  fun x' => if String.eqb x x' then v else m x'.

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Reserved Notation
         " '[' st ',' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level) .
Inductive cexec : com -> state -> state -> Prop :=
  | E_Skip : forall st,
       [ st, skip ]=> st
  | E_Asgn : forall st a n x,
      aeval st a = n ->
       [ st, x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
       [ st, c1 ]=> st' ->
       [ st', c2 ]=> st'' ->
       [ st, c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
       [ st, c1 ]=> st' ->
       [ st, if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
       [ st, c2 ]=> st' ->
       [ st, if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
       [ st, while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
       [ st, c ]=> st' ->
       [ st', while b do c end ]=> st'' ->
       [ st, while b do c end ]=> st''

  where " [ st , c ]=> st'" := (cexec c st st').


(* Exercise 2.7 (p20) *)
Lemma exo27 : forall st st', ~ ( [ st, while true do skip end ]=> st').
intros st st' h.
remember <{while true do skip end}> as pr eqn:eq_pr.
induction h; cbn in *;try discriminate.
destruct b; cbn in *; discriminate.
apply IHh2.
assumption.
Qed.


(* Definition Σ := string -> nat. *)
Definition cequiv (c0 c1 : com) : Prop :=
  forall s s', [ s, c0]=> s' <-> [ s, c1]=> s'.

