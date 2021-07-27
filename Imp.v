From Coq Require Import Strings.String.
Check string.
(** * Imp: Simple Imperative Programs *)

(** In this chapter, we begin a new direction that will continue for
    the rest of the course;  Up to now most of our attention has been
    focused on various aspects of Coq itself, while from now on we'll
    mostly be using Coq to formalize other things.  (We'll continue to
    pause from time to time to introduce a few additional aspects of
    Coq.)

    Our first case study is a _simple imperative programming language_
    called Imp, embodying a tiny core fragment of conventional
    mainstream languages such as C and Java.  Here is a familiar
    mathematical function written in Imp.
     Z ::= X;;
     Y ::= 1;;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z - 1
     END
*)

(** This chapter looks at how to define the _syntax_ and _semantics_
    of Imp; the chapters that follow develop a theory of _program
    equivalence_ and introduce _Hoare Logic_, a widely used logic for
    reasoning about imperative programs. *)

(* ####################################################### *)
(** *** Sflib *)

(** A minor technical point: Instead of asking Coq to import our
    earlier definitions from chapter [Logic], we import a small library
    called [Sflib.v], containing just a few definitions and theorems
    from earlier chapters that we'll actually use in the rest of the
    course.  This change should be nearly invisible, since most of what's
    missing from Sflib has identical definitions in the Coq standard
    library.  The main reason for doing it is to tidy the global Coq
    environment so that, for example, it is easier to search for
    relevant theorems. *)

(* Require Export SfLib. *)
Check string.
Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)
Require Import Nat.

(* ####################################################### *)
(** * Arithmetic and Boolean Expressions *)

(** We'll present Imp in three parts: first a core language of
    _arithmetic and boolean expressions_, then an extension of these
    expressions with _variables_, and finally a language of _commands_
    including assignment, conditions, sequencing, and loops. *)

(* ####################################################### *)
(** ** Syntax *)

Module AExp.

(** These two definitions specify the _abstract syntax_ of
    arithmetic and boolean expressions. *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : string -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp
  | BOr : bexp -> bexp -> bexp.
  

(** In this chapter, we'll elide the translation from the
    concrete syntax that a programmer would actually write to these
    abstract syntax trees -- the process that, for example, would
    translate the string ["1+2*3"] to the AST [APlus (ANum
    1) (AMult (ANum 2) (ANum 3))].  The optional chapter [ImpParser]
    develops a simple implementation of a lexical analyzer and parser
    that can perform this translation.  You do _not_ need to
    understand that file to understand this one, but if you haven't
    taken a course where these techniques are covered (e.g., a
    compilers course) you may want to skim it. *)

(** For comparison, here's a conventional BNF (Backus-Naur Form)
    grammar defining the same abstract syntax:
    a ::= nat
        | a + a
        | a - a
        | a * a

    b ::= true
        | false
        | a = a
        | a <= a
        | b and b
        | not b
*)

(** Compared to the Coq version above...

       - The BNF is more informal -- for example, it gives some
         suggestions about the surface syntax of expressions (like the
         fact that the addition operation is written [+] and is an
         infix symbol) while leaving other aspects of lexical analysis
         and parsing (like the relative precedence of [+], [-], and
         [*]) unspecified.  Some additional information -- and human
         intelligence -- would be required to turn this description
         into a formal definition (when implementing a compiler, for
         example).

         The Coq version consistently omits all this information and
         concentrates on the abstract syntax only.

       - On the other hand, the BNF version is lighter and
         easier to read.  Its informality makes it flexible, which is
         a huge advantage in situations like discussions at the
         blackboard, where conveying general ideas is more important
         than getting every detail nailed down precisely.

         Indeed, there are dozens of BNF-like notations and people
         switch freely among them, usually without bothering to say which
         form of BNF they're using because there is no need to: a
         rough-and-ready informal understanding is all that's
         needed. *)

(** It's good to be comfortable with both sorts of notations:
    informal ones for communicating between humans and formal ones for
    carrying out implementations and proofs. *)

(* ####################################################### *)
(** ** Evaluation *)

(** _Evaluating_ an arithmetic expression produces a number. *)

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
  | AId x => st x (* <--- NEW *)
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

(* Fixpoint beval_step (st : state) (b : bexp) : bexp := *)
(*   match b with *)
(*   | <{true}> => true *)
(*   | <{false}> => false *)
(*   | <{true = a2}> => true = (beval_step a2) *)
(*   | <{false = a2}> => false = (beval_step a2) *)
(*   | <{a1 = true}> => true = (beval_step a2) *)
(*   | <{a1 = false}> => false = (beval_step a2) *)
(*   | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2) *)
(*   | <{~ b1}> => negb (beval st b1) *)
(*   | <{b1 && b2}> => andb (beval st b1) (beval st b2) *)
(*   | <{b1 || b2}> => orb (beval st b1) (beval st b2) *)
(*   end. *)

 Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

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

Definition t_update  (m : string -> nat)
                    (x : string) (v : nat) :=
  fun x' => if String.eqb x x' then v else m x'.
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Reserved Notation
         (* "st '=[' c ']=>' st'" *)
         " '[' st ','  c ']=>' st'"
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
       [ st, if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
       [ st, c2 ]=> st' ->
       [ st, if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
       [ st, while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
       [ st, c ]=> st' ->
       [ st', while b do c end ]=> st'' ->
       [ st, while b do c end ]=> st''

  where " [ st , c ]=> st'" := (cexec c st st').

Lemma exo27 : forall st st', ~ ( [ st, while true do skip end ]=> st').
intros st st' h.
remember (CWhile BTrue CSkip) as pr eqn:eq_pr.
induction h; cbn in *;try discriminate.
destruct b; cbn in *; discriminate.
apply IHh2.
assumption.
Qed.


(* Definition Σ := string -> nat. *)
Definition cequiv (c0 c1 : com) : Prop :=
  forall s s', [ s, c0]=> s' <-> [ s, c1]=> s'.

