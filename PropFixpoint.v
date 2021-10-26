
(*

The goal of this file is to construct the smallest fixpoint of a monotone
function F : Prop -> Prop.
Then we extend straightforwardly the construction to relations on some type A

 *)

(*

Definition of the infimum of a subset Q of Prop, modelled as Q : Prop -> prop.
The infimum inf Q satisfies (by definition) the following (universal) property:
  ∀ (P : Prop),
                      "P is smaller than anything in Q"
     P -> inf Q   ≃    ∀ (R : Prop), Q R -> P -> R

The right handside can be reorganised as 
     P -> ∀ (R : Prop), Q R -> R

which has exactly the shape of the left handside. Thus it induces
the following (impredicative) definition of inf Q
 *)
Definition inf (Q : Prop -> Prop) : Prop :=  forall (R : Prop), Q R -> R.

(* As expected, the inf is smaller than all the elements in Q *)
Lemma inf_smaller (Q : Prop -> Prop) : forall (R : Prop), Q R -> inf Q -> R.
unfold inf.
firstorder.
Qed.

(* Given a function F : Prop -> Prop, we define the subset of Prop consisting
 of prefixpoint *)
Definition is_pre (F : Prop -> Prop) : Prop -> Prop :=
  fun P => F P -> P.

(* We can also define the postfixpoint *)
Definition is_post (F : Prop -> Prop) : Prop -> Prop :=
  fun P => P -> F P.

(*
If Q = is_pre F is the set of pre-fixpoints of a monotone F : Prop -> Prop, then 
inf Q is in Q.

This follows from the standard categorical result that the category of algebras of an endofunctor
(here F) is stable under limits (here, inf Q)
*)

Lemma inf_is_pre (F : Prop -> Prop)(Fmon : forall (P P' : Prop), (P -> P') -> (F P -> F P')) : is_pre F (inf (is_pre F)).
  unfold is_pre,inf.
  firstorder.
Qed.

(*
Moreover, the infimum, in this case, is also a postfixpoint.

This follows from the standard categorical result that the initial algebra X of
any endofunctor F is isomorphic to F X (Lambek's theorem).
 *)
Lemma inf_is_post (F : Prop -> Prop)(Fmon : forall (P P' : Prop), (P -> P') -> (F P -> F P')) : is_post F (inf (is_pre F)).
  unfold is_post.
  intro H.
  apply H.
  unfold is_pre, inf, is_post.
  firstorder.
Qed.


(* The same, but for relations, and faster *)
Section Relation.
  Context {A : Type}.

  Notation Rel := (A -> A -> Prop).

  Notation "P ~> Q" := (forall a a', P a a' -> Q a a') (at level 40).

  Context (F : Rel -> Rel)
          (Fmon : forall (P Q : Rel), P ~> Q -> F P ~> F Q).
  Definition fixRel : Rel :=
    fun a a' => forall (R : Rel), (F R ~> R) -> R a a'.

  Lemma pre_fixRel : F fixRel ~> fixRel.
  Proof.
    intros a a'.
    unfold fixRel.
    intros H R H'.
    apply H'.
    revert H.
    apply Fmon.
    firstorder.
  Qed.

  Lemma post_fixRel : fixRel ~> F fixRel.
  Proof.
    unfold fixRel.
    intros a a' H.
    apply H.
    apply Fmon.
    apply pre_fixRel.
  Qed.

End Relation.
