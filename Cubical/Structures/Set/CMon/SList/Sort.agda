{-# OPTIONS --cubical --safe --exact-split #-}

module Cubical.Structures.Set.CMon.SList.Sort where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Empty as ⊥
open import Cubical.Induction.WellFounded
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order 
open import Cubical.Relation.Nullary
open import Cubical.Data.List
open import Cubical.HITs.PropositionalTruncation as P
import Cubical.Data.List as L

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity
open import Cubical.Structures.Set.Mon.List
open import Cubical.Structures.Set.CMon.SList.Base renaming (_∷_ to _∷*_; [] to []*)
import Cubical.Structures.Set.CMon.SList.Base as S

open Iso

module Toset→Sort {ℓ : Level} {A : Type ℓ}
                  (_≤_ : A -> A -> Type ℓ) (≤-isTo : IsToset _≤_) 
                  (_≤?_ : (m n : A) -> (m ≤ n) ⊎ (¬(m ≤ n))) where

  open IsToset ≤-isTo

  unneg : {m n : A} -> ¬(m ≤ n) -> n ≤ m
  unneg {m} {n} p with n ≤? m
  ... | inl q = q
  ... | inr q = P.rec (is-prop-valued n m) (⊎.rec (⊥.rec ∘ p) (⊥.rec ∘ q)) (is-strongly-connected m n)

  ≤?-beta : {m n : A} -> (p : m ≤ n) -> m ≤? n ≡ inl p
  ≤?-beta {m} {n} p with m ≤? n
  ... | inl q = congS inl (is-prop-valued _ _ q p)
  ... | inr q = ⊥.rec (q p)

  ≤?-beta' : {m n : A} -> (p : ¬(m ≤ n)) -> m ≤? n ≡ inr p
  ≤?-beta' {m} {n} p with m ≤? n
  ... | inl q = ⊥.rec (p q)
  ... | inr q = congS inr (isProp¬ _ q p)

  data AscList : Type ℓ

  headOr : A -> AscList -> A

  data AscList where
    []* : AscList
    cons* : (x : A) -> (xs : AscList) -> x ≤ (headOr x xs) -> AscList

  headOr x []* = x
  headOr _ (cons* x xs p) = x

  AscList→List : AscList -> List A
  AscList→List []* = []
  AscList→List (cons* x xs p) = x ∷ AscList→List xs

  insert : A -> AscList -> AscList
  insertAux : (x y : A) -> (ys : AscList) -> y ≤ headOr y ys -> (x ≤ y) ⊎ (¬(x ≤ y)) -> AscList
  insert≤ : (x y : A) (ys : AscList) -> y ≤ x -> y ≤ headOr y ys -> y ≤ headOr y (insert x ys)
  insert x []* = cons* x []* (is-refl x)
  insert x (cons* y ys p) = insertAux x y ys p (x ≤? y)
  insertAux x y ys p = ⊎.rec (cons* x (cons* y ys p)) (λ q -> cons* y (insert x ys) (insert≤ x y ys (unneg q) p))
  insert≤ x y []* p q = p
  insert≤ x y (cons* z ys r) p q with x ≤? z
  ... | inl s = p
  ... | inr s = q

  insert-insert : (x y : A) (xs : AscList) -> insert x (insert y xs) ≡ insert y (insert x xs)
  insert-insert x y []* with x ≤? y | y ≤? x
  ... | inl p | inl q = let r = is-antisym x y p q in
      cons* x (cons* y []* (is-refl y)) p
    ≡⟨ cong₂ (λ w z -> cons* x (cons* w []* (is-refl w)) z) (sym r) (subst-filler (x ≤_) (sym r) p) ⟩
      cons* x (cons* x []* (is-refl x)) (subst (x ≤_) (sym r) p)
    ≡⟨ cong₂ (λ w z → cons* w (cons* x []* (is-refl x)) z) r (subst-filler (_≤ x) r _) ⟩
      cons* y (cons* x []* (is-refl x)) (subst (_≤ x) r ((subst (x ≤_) (sym r) p)))
    ≡⟨ congS (cons* y (cons* x []* (is-refl x))) (is-prop-valued _ _ _ q) ⟩
      cons* y (cons* x []* (is-refl x)) q ∎
  ... | inl p | inr q = refl
  ... | inr p | inl q = refl
  ... | inr p | inr q = let r = is-antisym y x (unneg p) (unneg q) in
      cons* y (cons* x []* (is-refl x)) _
    ≡⟨ cong₂ (λ w z -> cons* w (cons* x []* (is-refl x)) z) r (subst-filler (_≤ x) r _) ⟩
      cons* x (cons* x []* (is-refl x)) _
    ≡⟨ cong₂ (λ w z -> cons* x (cons* w []* (is-refl w)) z) (sym r) (subst-filler (x ≤_) (sym r) _) ⟩
      cons* x (cons* y []* (is-refl y)) _
    ≡⟨ congS (cons* x (cons* y []* (is-refl y))) (is-prop-valued _ _ _ _) ⟩
      cons* x (cons* y []* (is-refl y)) _ ∎
  insert-insert x y (cons* z zs p) with y ≤? z | x ≤? z
  insert-insert x y (cons* z zs p) | inl q | inl r with x ≤? y | y ≤? x
  insert-insert x y (cons* z zs p) | inl q | inl r | inl s | inl t = {!   !}
  insert-insert x y (cons* z zs p) | inl q | inl r | inl s | inr t = sym $
    {!   !}
    --   cons* x (⊎.rec (cons* y (cons* z zs p)) _ (y ≤? z)) _
    -- ≡⟨ congS (λ u -> cons* x (⊎.rec (cons* y (cons* z zs p)) _ u) _) (≤?-beta q) ⟩
    --   cons* x (cons* y (cons* z zs p) q) s ∎
  insert-insert x y (cons* z zs p) | inl q | inl r | inr s | what2 = {!   !}
  insert-insert x y (cons* z zs p) | inl q | inr r = {!   !}
  insert-insert x y (cons* z zs p) | inr q | what2 = {!   !}

  list→slist-Hom : structHom < List A , list-α > < SList A , slist-α >
  list→slist-Hom = ListDef.Free.ext listDef trunc (M.cmonSatMon slist-sat) S.[_]

  list→slist : List A -> SList A
  list→slist = list→slist-Hom .fst

  SList→AscList : SList A -> AscList
  SList→AscList = Elim.f []* (λ x xs -> insert x xs)
    {!   !}
    {!   !}

  sort : Σ[ s ∈ (SList A -> List A) ] (∀ x -> list→slist (s x) ≡ x)
  sort = {!   !} , {!   !}