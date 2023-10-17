{-# OPTIONS --cubical #-}

module Experiments.Mon where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Functions.FunExtEquiv 
open import Agda.Primitive

record MonStruct (A : Type) : Type where
  field
    e : A
    _⊕_ : A -> A -> A
    unitl : ∀ m -> e ⊕ m ≡ m
    unitr : ∀ m -> m ⊕ e ≡ m
    assocr : ∀ m n o -> (m ⊕ n) ⊕ o ≡ m ⊕ (n ⊕ o)
    trunc : isSet A

record isMonHom {A B : Type} (M : MonStruct A) (N : MonStruct B) (f : A -> B) : Type where
  pattern
  inductive
  constructor monHom

  module M = MonStruct M
  module N = MonStruct N

  field
    f-e : f (M.`e) ≡ N.e
    f-⊕ : ∀ a b -> f (a M.`⊕ b) ≡ f a N.⊕ f b

  f-unitl : ∀ a -> cong f (M.unitl a) ≡ f-⊕ M.`e a ∙ cong (N._⊕ f a) f-e ∙ N.unitl (f a)
  f-unitl a = N.trunc _ _ _ _

module _ {A B : Type} {M : MonStruct A} {N : MonStruct B} (f : A -> B) where
  module M = MonStruct M
  module N = MonStruct N

  isMonHom-isProp : isProp (isMonHom M N f)
  isMonHom-isProp (monHom x-e x-⊕) (monHom y-e y-⊕) =
    cong₂ monHom (N.trunc _ _ x-e y-e) ((isPropΠ λ _ → isPropΠ (λ _ → N.trunc _ _)) x-⊕ y-⊕)

MonHom : {A B : Type} (M : MonStruct A) (N : MonStruct B) -> Type
MonHom {A} {B} M N = Σ[ f ∈ (A -> B) ] isMonHom M N f
  