{-# OPTIONS --cubical #-}

module Cubical.Structures.Gpd.SMon.Free where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
import Cubical.Data.Empty as ⊥

import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity

data FreeSMon {ℓ : Level} (A : Type ℓ) : Type ℓ where
  η : (a : A) -> FreeSMon A
  e : FreeSMon A
  _⊕_ : FreeSMon A -> FreeSMon A -> FreeSMon A
  unitl : ∀ m -> e ⊕ m ≡ m
  unitr : ∀ m -> m ⊕ e ≡ m
  assocr : ∀ m n o -> (m ⊕ n) ⊕ o ≡ m ⊕ (n ⊕ o)
  symm : ∀ m n -> m ⊕ n ≡ n ⊕ m
  triangle : ∀ m n ->
    assocr m e n ∙ cong (m ⊕_) (unitl n)
    ≡ cong (_⊕ n) (unitr m)
  pentagon : ∀ l m n o ->
    assocr (l ⊕ m) n o ∙ assocr l m (n ⊕ o)
    ≡ cong (_⊕ o) (assocr l m n) ∙ assocr l (m ⊕ n) o ∙ cong (l ⊕_) (assocr m n o)
  hexagon : ∀ m n o ->
    assocr m n o ∙ symm m (n ⊕ o) ∙ assocr n o m
    ≡ cong (_⊕ o) (symm m n) ∙ assocr n m o ∙ cong (n ⊕_) (symm m o)
  symm² : ∀ m n -> (symm n m) ∙ (symm m n) ≡ refl
  trunc : isGroupoid (FreeSMon A)

