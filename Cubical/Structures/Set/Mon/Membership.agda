{-# OPTIONS --cubical --safe --exact-split #-}

module Cubical.Structures.Set.Mon.Membership where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
import Cubical.Data.Empty as ⊥
open import Cubical.Functions.Logic as L

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Data.Sum as ⊎

module FMonDef = F.Definition M.MonSig M.MonEqSig M.MonSEq

module Membership {ℓ} (𝔉 : FMonDef.Free ℓ (ℓ-suc ℓ) 2) {A : Type ℓ} (isSetA : isSet A) where
  open FMonDef.Free
  open M.MonStruct < 𝔉 .F A , 𝔉 .α >

  yoneda : A -> A -> hProp ℓ
  yoneda x y = (x ≡ y) , (isSetA x y)

  ∈PropHom : A -> structHom < 𝔉 .F A , 𝔉 .α > (M.⊔-MonStr ℓ)
  ∈PropHom x = ext 𝔉 isSetHProp (M.⊔-MonStr-MonSEq ℓ) (yoneda x)

  ∈Prop : A -> 𝔉 .F A -> hProp ℓ
  ∈Prop x = ∈PropHom x .fst

  _∈_ : A -> 𝔉 .F A -> Type ℓ
  x ∈ xs = ∈Prop x xs .fst

  isProp-∈ : (x : A) -> (xs : 𝔉 .F A) -> isProp (x ∈ xs)
  isProp-∈ x xs = (∈Prop x xs) .snd

  private
    singleton-lemma : ∀ x -> (∈PropHom x) .fst ∘ 𝔉 .η ≡ yoneda x
    singleton-lemma = ext-η 𝔉 isSetHProp (M.⊔-MonStr-MonSEq ℓ) ∘ yoneda
 
  x∈ηx : ∀ x -> x ∈ 𝔉 .η x
  x∈ηx x = transport (λ i -> singleton-lemma x (~ i) x .fst) refl

  x∈xs→x∈xs+ys : ∀ x xs ys -> x ∈ xs -> x ∈ (xs ⊕ ys)
  x∈xs→x∈xs+ys x xs ys x∈xs = transport
    (λ i -> ∈PropHom x .snd M.`⊕ ⟪ xs ⨾ ys ⟫ i .fst) (L.inl x∈xs)

  x∈ys→x∈xs+ys : ∀ x xs ys -> x ∈ ys -> x ∈ (xs ⊕ ys)
  x∈ys→x∈xs+ys x xs ys x∈ys = transport
    (λ i -> ∈PropHom x .snd M.`⊕ ⟪ xs ⨾ ys ⟫ i .fst) (L.inr x∈ys)

  x∈xs : ∀ x xs -> x ∈ (𝔉 .η x ⊕ xs)
  x∈xs x xs = x∈xs→x∈xs+ys x (𝔉 .η x) xs (x∈ηx x)

  x∈y∷xs : ∀ x y xs -> x ∈ xs -> x ∈ (𝔉 .η y ⊕ xs)
  x∈y∷xs x y xs x∈xs = x∈ys→x∈xs+ys x (𝔉 .η y) xs x∈xs

  ¬∈e : ∀ x -> (x ∈ e) -> ⊥.⊥
  ¬∈e x = ⊥.rec* ∘ transport (λ i -> ∈PropHom x .snd M.`e ⟪⟫ (~ i) .fst)

  x∈[y]→x≡y : ∀ x y -> x ∈ (𝔉 .η y) -> x ≡ y
  x∈[y]→x≡y x y = transport λ i -> singleton-lemma x i y .fst
