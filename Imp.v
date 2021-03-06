From Coq Require Import Strings.String.
Require Import Winskel.PropFixpoint.


(** * Chapter 2: Introduction to operational semantics *)

Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)
Require Import Nat.
Require Import Relations.Relation_Operators.
Require Import Coq.Program.Equality. (* dependent induction *)


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


(* TODO: Built-in map:
     Interface: https://coq.inria.fr/library/Coq.FSets.FMapInterface.html
     One implementation using lists: https://coq.inria.fr/stdlib/Coq.FSets.FMapList.html
 *)

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

Notation "x !-> v ; m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Reserved Notation
         "[ st , c ]=> st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).
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
Lemma exo27 : forall st st', ~ ([ st, while true do skip end ]=> st').
intros st st' h.
remember <{while true do skip end}> as pr eqn:eq_pr.
induction h; cbn in *; try discriminate.
destruct b; cbn in *; discriminate.
apply IHh2.
assumption.
Qed.


(* Definition Σ := string -> nat. *)
Definition cequiv (c0 c1 : com) : Prop :=
  forall s s', [s, c0]=> s' <-> [s, c1]=> s'.

Notation "c0 ~ c1" := (cequiv c0 c1)
                      (at level 90).


(* ####################################################### *)
(** §2.5 *)

Lemma prop28 : forall b c w, w = <{while b do c end}> -> w ~ <{if b then c ; w else skip end}>.
Proof.
  (* => *)
  intros.
  split.
  * intros.
    induction H0; try injection H; try discriminate; intros.
    (* 1 => as per the proof in the book *)
    + apply E_IfFalse.
      - rewrite H2 in H0. trivial.
      - apply E_Skip.
    (* 2 => *)
    + apply E_IfTrue.
      - rewrite H2 in H0; assumption.
      - apply E_Seq with (st' := st').
        ** rewrite H1 in H0_; assumption.
        ** assumption.
  (* <= *)
  * destruct (beval s b) eqn:b_eval. all:swap 1 2.
    (* 1 <= *)
    + intros.
      inversion H0.
      - rewrite H6 in b_eval; discriminate.
      - inversion H7.
        rewrite <- H10.
        rewrite H.
        apply E_WhileFalse. assumption.
    (* 2 <= *)
    + intros.
      inversion H0.
      - inversion H7.
        rewrite H.
        apply E_WhileTrue with (st := s) (st'' := s') (st' := st'0).
        ** assumption.
        ** assumption.
        ** rewrite <- H. assumption.
      - rewrite H6 in b_eval. discriminate.
Qed.


(* ####################################################### *)
(** §2.6 Small-step operational semantics *)

(* Values *)

Inductive avalue : aexp -> Prop :=
  | AV : forall n, avalue (ANum n).


(* Small-step *)

Reserved Notation
  "c0 ~>a1 c1" (at level 40).

(* NOTE: It deviates from the book in that, when an expression evaluates, we transition from
   state to state' in the inductive cases. In the book, the small-step rules are formulated as,
   e.g.
           <a0, σ> ~>a1 <a0', σ>
    ---------------------------------
     <a0 + a1, σ> ~>a1 <a0' + a1, σ>
   where the out-state is explicitly the same as the in-state.
 *)
Inductive aeval1 : (state * aexp) -> (state * aexp) -> Prop :=
  | A_Id    : forall st v, (st, AId v) ~>a1 (st, ANum (st v))
  | A_Plus   : forall st v1 v2, (st, <{ANum v1 + ANum v2}>) ~>a1 (st, ANum (v1 + v2))
  | A_PlusL  : forall st a1 a1' a2, (st, a1) ~>a1 (st, a1')
                                     -> (st, <{a1 + a2}>) ~>a1 (st, <{a1' + a2}>)
  | A_PlusR  : forall st st' v1 a2 a2', (st, a2) ~>a1 (st', a2')
                                     -> avalue v1
                                     -> (st, <{v1 + a2}>) ~>a1 (st, <{v1 + a2'}>)
  | A_Minus  : forall st v1 v2, (st, <{ANum v1 - ANum v2}>) ~>a1 (st, ANum (v1 - v2))
  | A_MinusL : forall st st' a1 a1' a2, (st, a1) ~>a1 (st', a1')
                                     -> (st, <{a1 - a2}>) ~>a1 (st', <{a1' - a2}>)
  | A_MinusR : forall st st' v1 a2 a2', (st, a2) ~>a1 (st', a2')
                                     -> avalue v1
                                     -> (st, <{v1 - a2}>) ~>a1 (st, <{v1 - a2'}>)
  | A_Mult   : forall st v1 v2, (st, <{ANum v1 * ANum v2}>) ~>a1 (st, ANum (v1 * v2))
  | A_MultL  : forall st st' a1 a1' a2, (st, a1) ~>a1 (st', a1')
                                     -> (st, <{a1 * a2}>) ~>a1 (st', <{a1' * a2}>)
  | A_NultR  : forall st st' v1 a2 a2', (st, a2) ~>a1 (st', a2')
                                     -> avalue v1
                                     -> (st, <{v1 * a2}>) ~>a1 (st, <{v1 * a2'}>)
  where "c0 ~>a1 c1" := (aeval1 c0 c1).


Reserved Notation
  "c0 ~>b1 c1" (at level 40).
Inductive beval1 : (state * bexp) -> (state * bexp) -> Prop :=
  | B_Eq    : forall st v1 v2, (st, <{ANum v1 = ANum v2}>) ~>b1 (st, if v1 =? v2 then <{true}> else <{false}>)
  | B_EqL   : forall st a1 a1' a2, (st, a1) ~>a1 (st, a1')
                                -> (st, <{a1 = a2}>) ~>b1 (st, <{a1' = a2}>)
  | B_EqR   : forall st v1 a2 a2', (st, a2) ~>a1 (st, a2')
                                -> avalue v1
                                -> (st, <{v1 = a2}>) ~>b1 (st, <{v1 = a2'}>)
  | B_Le    : forall st v1 v2, (st, <{ANum v1 <= ANum v2}>) ~>b1 (st, if v1 <=? v2 then <{true}> else <{false}>)
  | B_LeL   : forall st a1 a1' a2, (st, a1) ~>a1 (st, a1')
                                -> (st, <{a1 <= a2}>) ~>b1 (st, <{a1' <= a2}>)
  | B_LeR   : forall st v1 a2 a2', (st, a2) ~>a1 (st, a2')
                                -> avalue v1
                                -> (st, <{v1 <= a2}>) ~>b1 (st, <{v1 <= a2'}>)
  | B_NotT  : forall st, (st, <{~ true}>) ~>b1 (st, <{false}>)
  | B_NotF  : forall st, (st, <{~ false}>) ~>b1 (st, <{true}>)
  | B_Not   : forall st st' b b', (st, b) ~>b1 (st', b')
                               -> (st, <{~ b}>) ~>b1 (st', <{~ b'}>)
  | B_AndF  : forall st b2, (st, <{false && b2}>) ~>b1 (st, <{false}>)  (* a short-circuiting evaluation *)
  | B_AndT  : forall st b2, (st, <{true && b2}>) ~>b1 (st, <{b2}>)
  | B_AndL  : forall st st' b1 b1' b2, (st, b1) ~>b1 (st', b1')
                                    -> (st, <{b1 && b2}>) ~>b1 (st', <{b1' && b2}>)
  | B_OrT   : forall st b2, (st, <{true || b2}>) ~>b1 (st, <{true}>)  (* a short-circuiting evaluation *)
  | B_OrF   : forall st b2, (st, <{false || b2}>) ~>b1 (st, <{b2}>)
  | B_OrL   : forall st st' b1 b1' b2, (st, b1) ~>b1 (st', b1')
                                    -> (st, <{b1 || b2}>) ~>b1 (st', <{b1' || b2}>)
  where "c0 ~>b1 c1" := (beval1 c0 c1).


Reserved Notation
  "c0 ~>c1 c1" (at level 40).
(* NOTE: The resultant option type is hinted by the book (p25):
   "we need some way to represent the fact that the command is empty".
 *)
Inductive cexec1 : (state * com) -> (state * option com) -> Prop :=
  | C_Skip  : forall st, (st, <{skip}>) ~>c1 (st, None)
  | C_AsgnV : forall st x v, (st, <{x := ANum v}>) ~>c1 (x !-> v ; st, None)
  | C_AsgnE : forall st st' x a a', (st, a) ~>a1 (st, a')
                                 -> (st, <{x := a}>) ~>c1 (st', Some <{x := a'}>)
  | C_Seq0  : forall st st' c1 c2, (st, c1) ~>c1 (st', None)
                                -> (st, <{c1 ; c2}>) ~>c1 (st', Some c2)
  | C_Seq1  : forall st st' c1 c1' c2, (st, c1) ~>c1 (st', Some c1')
                                    -> (st, <{c1 ; c2}>) ~>c1 (st', Some <{c1' ; c2}>)
  | C_IfT   : forall st c1 c2, (st, <{if true then c1 else c2 end}>) ~>c1 (st, Some c1)
  | C_IfF   : forall st c1 c2, (st, <{if false then c1 else c2 end}>) ~>c1 (st, Some c2)
  | C_IfC   : forall st st' b b' c1 c2, (st, b) ~>b1 (st', b')
                                     -> (st, <{if b then c1 else c2 end}>) ~>c1 (st', Some <{if b' then c1 else c2 end}>)
  | CWhileT : forall st c, (st, <{while true do c end}>) ~>c1 (st, Some <{c ; while true do c end}>)
  | CWhileF : forall st c, (st, <{while false do c end}>) ~>c1 (st, None)
  | CWhileC : forall st st' b b' c, (st, b) ~>b1 (st', b')
                                 -> (st, <{while b do c end}>) ~>c1 (st', Some <{while b' do c end}>)
  where "c0 ~>c1 c1" := (cexec1 c0 c1).


(* Reflexive-transitive closure:
   https://coq.inria.fr/library/Coq.Relations.Relation_Operators.html#Reflexive_Transitive_Closure
*)

(* ####################################################### *)
(** §5.2 Denotational Semantics for Commands *)

Definition Gamma
  {A}
  (cond : A -> bool)
  (step : A -> A -> Prop)
  (R : A -> A -> Prop) : A -> A -> Prop :=
  fun a c =>
    if cond a then exists b, step a b /\ R b c else a = c.
 (* if cond a then (forall b, step a b -> R b c) /\ exists b, step a b else a = c. *)

Lemma Gamma_mon:
  forall {A} cond step (R1 R2 : A -> A -> Prop),
    (forall a b, R1 a b -> R2 a b) ->
      (forall a b, Gamma cond step R1 a b -> Gamma cond step R2 a b).
Proof.
  unfold Gamma.
  intros.
  destruct (cond a).
  * destruct H0. destruct H0.
    exists x.
    split; firstorder.
  * assumption.
Qed.

Lemma post_fixRel_Gamma:
  forall {A} cond step (a b : A),
    fixRel (Gamma cond step) a b ->
    Gamma cond step (fixRel (Gamma cond step)) a b.
Proof.
  intros A cond step.
  apply post_fixRel.
  apply Gamma_mon.
Qed.


Lemma pre_fixRel_Gamma:
  forall {A} cond step (a b : A),
  Gamma cond step (fixRel (Gamma cond step)) a b ->
  fixRel (Gamma cond step) a b.
Proof.
  intros A cond step.
  apply pre_fixRel.
  apply Gamma_mon.
Qed.

Fixpoint cexec' (prog : com) (st1 : state) (st2 : state) { struct prog }: Prop :=
  match prog with
    CWhile b c => fixRel (Gamma (fun st => beval st b) (cexec' c))
                     st1 st2
  | CSkip => st1 = st2
  | CSeq c0 c1 => exists st, cexec' c0 st1 st /\ cexec' c1 st st2
  | CIf b c0 c1 => if beval st1 b then cexec' c0 st1 st2 else cexec' c1 st1 st2
  | CAsgn x a => (x !-> aeval st1 a ; st1) = st2
  end.


Definition 𝒜 e := fun st => (aeval st e).
Definition ℬ e := fun st => (beval st e).
(* Inductive 𝒞 *)



(* Proposition 5.1, page 60. *)
Lemma prop_5_1a_unfold:
  forall b c st st',
    cexec' <{ while b do c end }> st st'
    -> cexec' <{ if b then c ; while b do c end else skip end }> st st'.
Proof.
  intros b c st st' W.
  apply post_fixRel_Gamma in W.
  fold cexec' in W.
  unfold cexec'. fold cexec'.
  unfold Gamma in W.
  destruct (beval st b).
  * destruct W.
    destruct H.
    exists x.
    split.
    all:assumption.
  * assumption.
Qed.

Lemma prop_5_1_fold:
  forall b c st st',
    cexec' <{ if b then c ; while b do c end else skip end }> st st'
    -> cexec' <{ while b do c end }> st st'.
Proof.
  intros b c st st' W.
  apply pre_fixRel_Gamma.
  fold cexec'.
  unfold cexec' in W. fold cexec' in W.
  unfold Gamma.
  destruct (beval st b).
  * destruct W.
    destruct H.
    exists x.
    split.
    all:assumption.
  * assumption.
Qed.


(* ####################################################### *)
(** §5.3 Equivalence of the semantics *)

Lemma lemma_5_6: forall st st' c, [ st , c ]=> st' -> cexec' c st st'.
Proof.
intros.
induction H.
  * unfold cexec'. trivial.
  * unfold cexec'. f_equal. assumption.
  * simpl. exists st'.
    split. apply IHcexec1. apply IHcexec2.
  * simpl. rewrite H. assumption.
  * simpl. rewrite H. assumption.
  * simpl. unfold fixRel. unfold Gamma.
    intros.
    apply H0. rewrite H. trivial.
  * apply prop_5_1_fold.
    simpl.
    rewrite H.
    exists st'.
    split.
    + assumption.
    + apply IHcexec2.
Qed.


Inductive stepRel {A} (cond : A -> bool) (R : A -> A -> Prop)
  : nat -> A -> A -> Prop :=
  | stepRel_False : forall (a : A),
      cond a = false -> stepRel cond R 0 a a
  | stepRel_True : forall n (a b c : A),
      cond a = true -> R a b -> stepRel cond R n b c -> stepRel cond R (S n) a c.

(*
Lemma forall {A} cond (step : A -> A -> Prop) n a b, 
  stepRel cond step n a a -> n=0.


Lemma Gamma_stepRel:
  forall {A} cond (step : A -> A -> Prop) n a b,
    Gamma cond step (stepRel cond step n) a b ->
    stepRel cond step (S n) a b.
Proof. 
  intros.  
  remember (stepRel cond step n) as S.
  unfold Gamma in H.
  destruct (cond a) eqn: H'.
  - destruct H. destruct H. subst.
    econstructor;
    eauto.  
  - assert (n=0).
  + 
  + subst. econstructor. assumption.
  
  apply (stepRel_True _ _ _ x).  


Lemma fixRel_to_stepRel :
  forall {A} cond (step : A -> A -> Prop) a b,
    fixRel (Gamma cond step) a b ->
    (exists n, stepRel cond step n a b).
Proof.
intros.
unfold fixRel in H.
apply H.
intros.
apply (stepRel cond step 1) in H.
eexists.
Admitted.

*)

(* As of pp. 66 of the book *)
Fixpoint theta (n : nat) b c (st st' : state) : Prop :=
  match n with
  | 0 => False
  | S n' => if beval st b
             then exists st'', cexec' c st st'' /\ theta n' b c st'' st' 
             else st = st'
end.

Lemma cexec'_theta :
forall st st' b c,
  cexec' <{ while b do c end }> st st' ->
  exists n, theta n b c st st'.
Admitted.


Lemma lemma_5_7: forall st st' c, cexec' c st st' -> [ st , c ]=> st'.
Proof.
intros.
dependent induction c generalizing st st'.
* unfold cexec' in H. rewrite <- H. apply E_Skip.
* unfold cexec' in H. rewrite <- H. apply E_Asgn. trivial.
* simpl in H.
  destruct H as [st''].
  destruct H as [H1 H2].
  apply E_Seq with (st' := st'').
  + apply IHc1. apply H1.
  + apply IHc2. apply H2.
* simpl in H.
  destruct (beval st b) eqn:b_eq.
  + apply E_IfTrue. 
    - assumption.
    - apply IHc1. trivial.
  + apply E_IfFalse.
    - trivial.
    - apply IHc2. trivial.
* assert (forall n st st', theta n b c st st' -> [ st , <{while b do c end}> ]=> st').
  + induction n.
    - intros st0 st0' H_theta.
      unfold theta in H_theta. destruct H_theta.
    - intros st0 st0' H_theta.
      simpl in H_theta.
      destruct (beval st0 b) eqn:b_eq.
      ** destruct H_theta as [st'' H_theta].
          destruct H_theta as [H0 Hs].
          apply IHc in H0.
          apply E_WhileTrue with (st' := st'').
          ++ trivial.
          ++ trivial.
          ++ apply IHn. trivial. 
      ** rewrite <- H_theta.
          apply E_WhileFalse. trivial.
  + apply cexec'_theta in H.
    destruct H as [n].
    apply H0 with (n := n).
    apply H.
Qed.


(* ####################################################### *)
(** §6.2 The Assertion Language Assn *)

Definition avar := string.


(* Extending aexp to include integer variables (c.f. the beginning of p.81) *)
Inductive aexpv : Type :=
  | AvNum   : nat            -> aexpv
  | AvId    : string         -> aexpv
  | AvVar   : avar           -> aexpv
  | AvPlus  : aexpv -> aexpv -> aexpv
  | AvMinus : aexpv -> aexpv -> aexpv
  | AvMult  : aexpv -> aexpv -> aexpv.


Inductive assn : Type :=
  | AsTrue  : assn
  | AsFalse : assn
  | AsEq    : aexpv -> aexpv -> assn
  | AsLe    : aexpv -> aexpv -> assn
  | AsNot   : assn  -> assn
  | AsAnd   : assn  -> assn  -> assn
  | AsOr    : assn  -> assn  -> assn
  | AsImp   : assn  -> assn  -> assn
  | AsAll   : avar  -> assn  -> assn
  | AsEx    : avar  -> assn  -> assn.



Fixpoint fv_av (a : aexpv) : (avar -> Prop) :=
  match a with
  | AvNum n => fun _ => False
  | AvId  x => fun _ => False
  | AvVar i => fun j => if (j =? i)%string then True else False
  | AvPlus  a1 a2 => fun j => fv_av a1 j \/ fv_av a2 j
  | AvMinus a1 a2 => fun j => fv_av a1 j \/ fv_av a2 j
  | AvMult  a1 a2 => fun j => fv_av a1 j \/ fv_av a2 j
  end.

Fixpoint fv_as (A : assn) : avar -> Prop :=
  match A with
  | AsTrue  => fun _ => False
  | AsFalse => fun _ => False
  | AsEq  a1 a2 => fun j => fv_av a1 j \/ fv_av a2 j
  | AsLe  a1 a2 => fun j => fv_av a1 j \/ fv_av a2 j
  | AsNot A1    => fv_as A1
  | AsAnd A1 A2 => fun j => fv_as A1 j \/ fv_as A2 j
  | AsOr  A1 A2 => fun j => fv_as A1 j \/ fv_as A2 j
  | AsImp A1 A2 => fun j => fv_as A1 j \/ fv_as A2 j
  | AsAll i A1  => fun j => if (i =? j)%string then False else fv_as A1 j
  | AsEx  i A1  => fun j => if (i =? j)%string then False else fv_as A1 j
  end.

(** Define Sematics of assertions**)

Fixpoint av (a : aexpv) (I : avar -> nat) (st : state) : nat :=
  match a with
  | AvNum n => n
  | AvId  x => st x
  | AvVar i => I i
  | AvPlus  a1 a2 => (av a1 I st) + (av a2 I st)
  | AvMinus a1 a2 => (av a1 I st) - (av a2 I st)
  | AvMult  a1 a2 => (av a1 I st) * (av a2 I st)
  end.


Fixpoint subst_av (a : aexpv) (i : avar) (a' : aexpv) : aexpv :=
  match a with
    | AvNum n => AvNum n
    | AvId  x => AvId x
    | AvVar j => if (j =? i)%string then a' else AvVar j 
    | AvPlus  a1 a2 => AvPlus  (subst_av a1 i a') (subst_av a2 i a')
    | AvMinus a1 a2 => AvMinus (subst_av a1 i a') (subst_av a2 i a')
    | AvMult  a1 a2 => AvMult  (subst_av a1 i a') (subst_av a2 i a')
  end.

(* Substitution for assertions, pg 83*)

Fixpoint subst_as (ass : assn) (i : avar) (a : aexpv) : assn :=
  match ass with 
  | AsTrue  => AsTrue
  | AsFalse => AsFalse
  | AsEq  a1 a2 => AsEq  (subst_av a1 i a) (subst_av a2 i a)
  | AsLe  a1 a2 => AsLe  (subst_av a1 i a) (subst_av a2 i a)
  | AsNot a1    => AsNot (subst_as a1 i a)
  | AsAnd a1 a2 => AsAnd (subst_as a1 i a) (subst_as a2 i a)
  | AsOr  a1 a2 => AsOr  (subst_as a1 i a) (subst_as a2 i a)  
  | AsImp a1 a2 => AsImp (subst_as a1 i a) (subst_as a2 i a)
  | AsAll j  a1 => AsAll j (if (j =? i)%string then a1 else subst_as a1 i a)
  | AsEx  j  a1 => AsEx  j (if (j =? i)%string then a1 else subst_as a1 i a)
  end.

Notation "a [ x / i ]av" := (subst_av a i x) (at level 40).
Notation "a [ x / i ]as" := (subst_as a i x) (at level 40).


(** §6.3 The semantics of Assn *)


