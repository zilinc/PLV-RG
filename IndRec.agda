module IndRec where

open import Agda.Builtin.Nat using (_-_)
open import Agda.Builtin.Unit using (⊤; tt)
-- open import Agda.Primitive
open import Data.Bool hiding (T)
-- open import Data.Empty
-- open import Data.List
open import Data.Nat
open import Data.Nat.Base
-- open import Data.Nat.Properties
open import Data.Product using (Σ; proj₁; proj₂; _,_; <_,_>; uncurry; curry; _×_; ∃; ∃-syntax)
-- open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (_∘_; _$_; case_of_; id; flip)
open import Function.Bundles
open Inverse
open import Relation.Binary.PropositionalEquality renaming (cong₂ to cong₂≡) hiding ([_]; Extensionality; ∀-extensionality)
-- open import Relation.Nullary
open ≡-Reasoning


data List′ : Set where
  nil′  : List′
  cons′ : ℕ → List′ → List′

all : (ℕ → Bool) → List′ → Bool
all p nil′ = true
all p (cons′ a as) = p a ∧ all p as

Len′ : List′ → Set
Len′ nil′ = ℕ
Len′ (cons′ _ l) = ℕ × Len′ l

-- --------------------------------------------------------------------------
-- DList: it does not have to use induction-recursion.

module DList where

  open Data.Bool using (T)

  data DList : Set
  Fresh : (a : ℕ) → (l : DList) → Set

  data DList where
    dnil  : DList
    dcons : (a : ℕ) → (l : DList) → Fresh a l → DList

  Fresh a dnil = ⊤
  Fresh a (dcons b l _) = a ≢ b × Fresh a l

  Fresh′ : ℕ → List′ → Set
  Fresh′ a nil′ = ⊤
  Fresh′ a (cons′ b l) = a ≢ b × Fresh′ a l
  
  AllFresh : List′ → Set
  AllFresh nil′ = ⊤
  AllFresh (cons′ a l) = Fresh′ a l × AllFresh l

  AllFresh-tail : ∀{x}{xs} → AllFresh (cons′ x xs) → AllFresh xs
  AllFresh-tail {xs = nil′} p = tt
  AllFresh-tail {xs = cons′ a as} (_ , p) = p

  data DList′ : List′ → Set → Set₁ where
    dnil′  : DList′ nil′ ⊤
    dcons′ : ∀{l}{prf} → (a : ℕ) → DList′ l prf → DList′ (cons′ a l) ((Fresh′ a l) × prf)


  data DList″ : Set where
    dl″ : (l : List′) → AllFresh l → DList″

  undl″-l : DList″ → List′
  undl″-l (dl″ l _) = l

  undl″-p : DList″ → ∃[ l ] AllFresh l
  undl″-p (dl″ l p) = l , p

  3≢5 : 3 ≢ 5
  3≢5 = λ ()

  ex₁ : DList
  ex₁ = dcons 3 (dcons 5 dnil tt) (3≢5 , tt)

  ex₁′ : DList′ (cons′ 3 (cons′ 5 nil′)) (Fresh′ 3 (cons′ 5 nil′) × Fresh′ 5 nil′ × ⊤)
  ex₁′ = dcons′ 3 (dcons′ 5 dnil′)

  ex₁″ : DList″
  ex₁″ = dl″ (cons′ 3 (cons′ 5 nil′)) ((3≢5 , tt) , (tt , tt))

  DList→List′ : DList → List′
  DList→List′ dnil = nil′
  DList→List′ (dcons a l x) = cons′ a (DList→List′ l)


  dl-iso : DList ↔ DList″

  Fresh→Fresh′ : ∀{a}{l}{l″}
               → (f dl-iso l ≡ l″)
               → Fresh a l
               → Fresh′ a (undl″-l l″)

  Fresh→AllFresh : ∀{a}{l}{l″}
                 → (f dl-iso l ≡ l″)
                 → Fresh a l
                 → AllFresh (undl″-l l″)

  All/Fresh′→Fresh : ∀{a}{l}{l″}
         → (l ≡ f⁻¹ dl-iso l″)
         → Fresh′ a (undl″-l l″) × AllFresh (undl″-l l″)
         → Fresh a l

  f dl-iso dnil = dl″ nil′ tt
  f dl-iso (dcons a l p)
    = dl″ (cons′ a (undl″-l (f dl-iso l)))
          ((Fresh→Fresh′ {l = l}{l″ = f dl-iso l} refl p) ,
           (Fresh→AllFresh {a = a}{l = l}{l″ = f dl-iso l} refl p))

  f⁻¹ dl-iso (dl″ nil′ p) = dnil
  f⁻¹ dl-iso (dl″ (cons′ a l′) p)
    = dcons a (f⁻¹ dl-iso (dl″ l′ (proj₂ p)))
              (All/Fresh′→Fresh {l″ = dl″ l′ (proj₂ p)} refl p)

  cong₁ dl-iso refl = refl

  cong₂ dl-iso refl = refl

  inverse dl-iso = (λ x → invˡ) , (λ x → invʳ)
    where invˡ : ∀{x} → f dl-iso (f⁻¹ dl-iso x) ≡ x
          invˡ {dl″ nil′ _} = refl
          invˡ {dl″ (cons′ a l) p} = {!!}

          invʳ : ∀{x} → f⁻¹ dl-iso (f dl-iso x) ≡ x
          invʳ {dnil} = refl
          invʳ {dcons a l p} = {!!}

  Fresh→Fresh′ {a} {dnil} eq p rewrite sym eq = tt
  Fresh→Fresh′ {a} {dcons a₁ l x} eq p rewrite sym eq
    = proj₁ p ,  Fresh→Fresh′ {l″ = f dl-iso l} refl (proj₂ p)

  Fresh→AllFresh {l = dnil} eq p rewrite sym eq = tt
  Fresh→AllFresh {l = dcons a l x} eq p rewrite sym eq
    = (Fresh→Fresh′ {l″ = f dl-iso l} refl x) , Fresh→AllFresh {a = a}{l = l}{l″ = f dl-iso l} refl x

  {-# TERMINATING #-}
  All/Fresh′→Fresh {a} {l″ = dl″ nil′ x} eq p rewrite eq = tt
  All/Fresh′→Fresh {a} {l″ = dl″ (cons′ b l) x} eq p rewrite eq
    = (proj₁ ∘ proj₁ $ p) , All/Fresh′→Fresh {a = a}{l″ = dl″ l (proj₂ x)} refl ((proj₂ ∘ proj₁ $ p) , (proj₂ x))


-- --------------------------------------------------------------------------
-- An exampe where induction-recursion is necessary.

module Universe where

  data U : Set₁
  T : U → Set₁

  data U where
    ★ : U
    π : (u : U) → (T u → U) → U

  T ★ = Set
  T (π u u′) = (a : T u) → T (u′ a)



module XList1 where

  -- XList is a list, which, at every xcons node, it keeps a function
  -- whose type is (ℕ, ℕ, ..., ℕ) → ℕ, where the domain is a k-tuple
  -- of ℕs, where k is the length of the tail of the xlist.

  data XList : Set
  Len : XList → Set

  data XList where
    xnil  : XList
    xcons : (a : ℕ) → (l : XList) → (Len l → ℕ) → XList

  Len xnil = ℕ
  Len (xcons a l _) = ℕ × Len l

  ex₁ : XList
  ex₁ = xcons 3 (xcons 5 xnil (λ x → x)) (λ (x , y) → x + y)

  ex₂ : XList
  ex₂ = xcons 3 (xcons 5 xnil λ x → x + 1) λ (x , y) → x * y

module XList2 where

  data XList : Set
  Len : XList → Set

  data XList where
    xnil  : XList
    xcons : (a : ℕ) → (l : XList) → (Len l) → XList

  Len xnil = ℕ
  Len (xcons a l _) = ℕ × Len l

  ex : XList
  ex = xcons 3 (xcons 5 xnil 0) (0 , 0) 


module XList2≡ where
  -- It should be equivalent to XList2

  data XList′ : List′ → Set₁ where
    xnil′  : XList′ nil′
    xcons′ : ∀{l} → (a : ℕ) → XList′ l → Len′ l → XList′ (cons′ a l)

  ex : ∃[ l ] XList′ l
  ex = _ , (xcons′ 3 (xcons′ 5 xnil′ 0) (0 , 0))


module XList1≡ where
  -- It should be equivalent to XList1

  data XList′ : List′ → Set₁ where
    xnil′  : XList′ nil′
    xcons′ : ∀{l} → (a : ℕ) → XList′ l → (Len′ l → ℕ) → XList′ (cons′ a l)

  ex : ∃[ l ] XList′ l
  ex = _ , xcons′ 3 (xcons′ 5 xnil′ λ x → x) λ (x , y) → x + y


-- --------------------------------------------------------------------------
-- An example where induction-induction will lead to different results than
-- using induction-recursion.



-- --------------------------------------------------------------------------
-- Experiments on "boxing up" a family of indexed types

module SNats where

  data SNat : ℕ → Set where
    sze : SNat 0
    ssu : ∀{n} → SNat n → SNat (n + 1)

  -- Now, we want to have a type of all SNats

  SNats : Set
  SNats = Σ ℕ λ n → SNat n

  -- s1 ∈ SNats
  s1∈SNats : SNats
  s1∈SNats = (_ , ssu sze)

