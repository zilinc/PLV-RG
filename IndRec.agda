module IndRec where

-- open import Agda.Builtin.Nat using (_-_)
open import Agda.Builtin.Unit using (⊤; tt)
-- open import Agda.Primitive
open import Data.Bool hiding (T)
-- open import Data.Empty
-- open import Data.List
-- open import Data.Nat
open import Data.Nat.Base
-- open import Data.Nat.Properties
open import Data.Product using (Σ; proj₁; proj₂; _,_; <_,_>; uncurry; curry; _×_; ∃; ∃-syntax)
-- open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
-- open import Function using (_∘_; _$_; case_of_; id; flip)
-- open import Function.Bundles
-- open Inverse
open import Relation.Binary.PropositionalEquality hiding ([_]; Extensionality; ∀-extensionality; cong₂)
-- open import Relation.Nullary
open ≡-Reasoning


-- --------------------------------------------------------------------------
-- DList: it does not have to use induction-recursion.

module _ where

  open Data.Bool using (T)

  data DList : Set
  Fresh : (a : ℕ) → (l : DList) → Set

  data DList where
    dnil  : DList
    dcons : (a : ℕ) → (l : DList) → Fresh a l → DList

  Fresh a dnil = ⊤
  Fresh a (dcons b l _) = a ≢ b × Fresh a l


  data List′ : Set where
    nil′  : List′
    cons′ : ℕ → List′ → List′

  all : (ℕ → Bool) → List′ → Bool
  all p nil′ = true
  all p (cons′ a as) = p a ∧ all p as

  Fresh′ : ℕ → List′ → Set
  Fresh′ a nil′ = ⊤
  Fresh′ a (cons′ b l) = a ≢ b × Fresh′ a l

  data DList′ : List′ → Set → Set₁ where
    dnil′  : DList′ nil′ ⊤
    dcons′ : ∀{l}{prf} → (a : ℕ) → DList′ l prf → DList′ (cons′ a l) ((Fresh′ a l) × prf)

  3≢5 : 3 ≢ 5
  3≢5 = λ ()

  ex₁ : DList
  ex₁ = dcons 3 (dcons 5 dnil tt) (3≢5 , tt)

  ex₁′ : DList′ (cons′ 3 (cons′ 5 nil′)) (Fresh′ 3 (cons′ 5 nil′) × Fresh′ 5 nil′ × ⊤)
  ex₁′ = dcons′ 3 (dcons′ 5 dnil′)


-- --------------------------------------------------------------------------
-- An exampe where induction-recursion is necessary.

module _ where

  data U : Set₁
  T : U → Set₁

  data U where
    ★ : U
    π : (u : U) → (T u → U) → U

  T ★ = Set
  T (π u u′) = (a : T u) → T (u′ a)





-- --------------------------------------------------------------------------
-- An example where induction-induction will lead to different results than
-- using induction-recursion.

