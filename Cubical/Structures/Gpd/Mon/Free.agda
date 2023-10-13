{-# OPTIONS --cubical #-}

module Cubical.Structures.Gpd.Mon.Free where

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

data FreeMon {ℓ : Level} (A : Type ℓ) : Type ℓ where
  η : (a : A) -> FreeMon A
  e : FreeMon A
  _⊕_ : FreeMon A -> FreeMon A -> FreeMon A
  unitl : ∀ m -> e ⊕ m ≡ m
  unitr : ∀ m -> m ⊕ e ≡ m
  assocr : ∀ m n o -> (m ⊕ n) ⊕ o ≡ m ⊕ (n ⊕ o)
  triangle : ∀ m n ->
    assocr m e n ∙ cong (m ⊕_) (unitl n)
    ≡ cong (_⊕ n) (unitr m)
  pentagon : ∀ l m n o ->
    assocr (l ⊕ m) n o ∙ assocr l m (n ⊕ o)
    ≡ cong (_⊕ o) (assocr l m n) ∙ assocr l (m ⊕ n) o ∙ cong (l ⊕_) (assocr m n o)
  trunc : isGroupoid (FreeMon A)

