{-# OPTIONS --cubical --exact-split #-}
module Cubical.Structures.Gpd.Mon.List where

open import Cubical.Foundations.Everything hiding (str)
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
import Cubical.Data.Empty as ⊥
open import Cubical.Functions.Logic as L

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public hiding (struct ; car)
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity
open import Cubical.HITs.PropositionalTruncation as P

open import Cubical.Structures.Prelude
import Cubical.Structures.Set.Mon.List as L
open import Cubical.Structures.Gpd.Mon.Desc as L

private
  variable
    ℓ : Level
    A : Type ℓ

list-α : sig M.MonSig (List A) -> List A
list-α = L.list-α

private
  list-▿ : (xs ys : List A)
         → ++-assoc xs [] ys ∙ ap (xs ++_) (idp ys)
          ≡ ap (_++ ys) (++-unit-r xs)
  list-▿ [] ys =
      ++-assoc [] [] ys ∙ ap ([] ++_) (idp ys)
    ≡⟨⟩
      refl ∙ refl
    ≡⟨ sym (lUnit refl) ⟩
      refl
    ≡⟨⟩
      ap (_++ ys) (++-unit-r [])
    ∎
  list-▿ (x ∷ xs) ys =
      ++-assoc (x ∷ xs) [] ys ∙ ap ((x ∷ xs) ++_) (idp ys)
    ≡⟨⟩
      ap (x ∷_) (++-assoc xs [] ys) ∙ idp (x ∷ xs ++ ys)
    ≡⟨ sym (rUnit (ap (x ∷_) (++-assoc xs [] ys))) ⟩
      ap (x ∷_) (++-assoc xs [] ys)
    ≡⟨ ap (ap (x ∷_)) (rUnit (++-assoc xs [] ys)) ⟩
      ap (x ∷_) (++-assoc xs [] ys ∙ ap (xs ++_) (idp ys))
    ≡⟨ ap (ap (x ∷_)) (list-▿ xs ys) ⟩
      ap (x ∷_) (ap (_++ ys) (++-unit-r xs))
    ≡⟨⟩
      ap (_++ ys) (ap (x ∷_) (++-unit-r xs))
    ≡⟨⟩
      ap (_++ ys) (++-unit-r (x ∷ xs))
    ∎

private
  list-⬠ : (xs ys zs ws : List A)
         → ++-assoc (ws ++ xs) ys zs ∙ ++-assoc ws xs (ys ++ zs)
         ≡ ap (_++ zs) (++-assoc ws xs ys) ∙ ++-assoc ws (xs ++ ys) zs ∙ ap (_++_ ws) (++-assoc xs ys zs)
  list-⬠ xs ys zs [] = 
      ((++-assoc) ((_++_) ([]) (xs)) (ys) (zs)) ∙ ((++-assoc) ([]) (xs) ((_++_) (ys) (zs)))
    ≡⟨⟩
      ((++-assoc) (xs) (ys) (zs)) ∙ ((++-assoc) ([]) (xs) ((_++_) (ys) (zs)))
    ≡⟨⟩
      ((++-assoc) (xs) (ys) (zs)) ∙ (idp _)
    ≡⟨ sym (rUnit _) ⟩
      (++-assoc) (xs) (ys) (zs)
    ≡⟨⟩
      ap (idfun _) ((++-assoc) (xs) (ys) (zs))
    ≡⟨⟩
      ap (λ p → (p)) ((++-assoc) (xs) (ys) (zs))
    ≡⟨⟩
      ap (λ p → ((_++_) ([]) (p))) ((++-assoc) (xs) (ys) (zs))
    ≡⟨ sym (sym (lUnit _)) ⟩
      (idp _) ∙ (ap (λ p → ((_++_) ([]) (p))) ((++-assoc) (xs) (ys) (zs)))
    ≡⟨⟩
      ((++-assoc) ([]) ((_++_) (xs) (ys)) (zs)) ∙ (ap (λ p → ((_++_) ([]) (p))) ((++-assoc) (xs) (ys) (zs)))
    ≡⟨ sym (sym (lUnit _)) ⟩
      (idp _) ∙ (((++-assoc) ([]) ((_++_) (xs) (ys)) (zs)) ∙ (ap (λ p → ((_++_) ([]) (p))) ((++-assoc) (xs) (ys) (zs))))
    ≡⟨⟩
      (ap (λ p → ((_++_) (p) (zs))) (idp _)) ∙ (((++-assoc) ([]) ((_++_) (xs) (ys)) (zs)) ∙ (ap (λ p → ((_++_) ([]) (p))) ((++-assoc) (xs) (ys) (zs))))
    ≡⟨⟩
      (ap (λ p → ((_++_) (p) (zs))) ((++-assoc) ([]) (xs) (ys))) ∙ (((++-assoc) ([]) ((_++_) (xs) (ys)) (zs)) ∙ (ap (λ p → ((_++_) ([]) (p))) ((++-assoc) (xs) (ys) (zs)))) 
    ∎
 
  list-⬠ xs ys zs (w ∷ ws) =
      ((++-assoc) ((_++_) ((w) ∷ (ws)) (xs)) (ys) (zs)) ∙ ((++-assoc) ((w) ∷ (ws)) (xs) ((_++_) (ys) (zs)))
    ≡⟨⟩
      ((++-assoc) ((w) ∷ ((_++_) (ws) (xs))) (ys) (zs)) ∙ ((++-assoc) ((w) ∷ (ws)) (xs) ((_++_) (ys) (zs)))
    ≡⟨⟩
      (ap (λ a0 → ((_∷_) (w) (a0))) ((++-assoc) ((_++_) (ws) (xs)) (ys) (zs))) ∙ ((++-assoc) ((w) ∷ (ws)) (xs) ((_++_) (ys) (zs)))
    ≡⟨⟩
      (ap (λ a0 → ((_∷_) (w) (a0))) ((++-assoc) ((_++_) (ws) (xs)) (ys) (zs))) ∙ (ap (λ a0 → ((_∷_) (w) (a0))) ((++-assoc) (ws) (xs) ((_++_) (ys) (zs))))
    ≡⟨ sym (ap-compPath (λ a0 → ((_∷_) (w) (a0))) ((++-assoc) ((_++_) (ws) (xs)) (ys) (zs)) ((++-assoc) (ws) (xs) ((_++_) (ys) (zs))) ) ⟩
      ap (λ a0 → ((_∷_) (w) (a0))) (((++-assoc) ((_++_) (ws) (xs)) (ys) (zs)) ∙ ((++-assoc) (ws) (xs) ((_++_) (ys) (zs))))
    ≡⟨ ap  (λ p → (ap (λ a0 → ((_∷_) (w) (a0)))) p) (list-⬠ xs ys zs ws) ⟩
      ap (λ a0 → ((_∷_) (w) (a0))) (ap (_++ zs) (++-assoc ws xs ys) ∙ ++-assoc ws (xs ++ ys) zs ∙ ap (_++_ ws) (++-assoc xs ys zs))
    ≡⟨⟩
      ap (λ a0 → ((_∷_) (w) (a0))) (ap (_++ zs) (++-assoc ws xs ys) ∙ (++-assoc ws (xs ++ ys) zs ∙ ap (_++_ ws) (++-assoc xs ys zs)))
    ≡⟨ ap-compPath ((λ a0 → ((_∷_) (w) (a0)))) ((ap (_++ zs) (++-assoc ws xs ys))) ((++-assoc ws (xs ++ ys) zs ∙ ap (_++_ ws) (++-assoc xs ys zs))) ⟩ -- ap (x . y) ~> ap x . ap y
      ap (λ a0 → ((_∷_) (w) (a0))) (ap (_++ zs) (++-assoc ws xs ys)) ∙ ap (λ a0 → ((_∷_) (w) (a0))) (++-assoc ws (xs ++ ys) zs ∙ ap (_++_ ws) (++-assoc xs ys zs))
    ≡⟨⟩
      ap (λ a0 → ((_∷_) (w) (a0))) (ap (λ p → ((_++_) (p) (zs))) (++-assoc ws xs ys)) ∙ ap (λ a0 → ((_∷_) (w) (a0))) (++-assoc ws (xs ++ ys) zs ∙ ap (_++_ ws) (++-assoc xs ys zs))
    ≡⟨⟩
      ap (λ a0 → (w ∷ a0) ++ zs) (++-assoc ws xs ys) ∙ ap (λ a0 → ((_∷_) (w) (a0))) (++-assoc ws (xs ++ ys) zs ∙ ap (_++_ ws) (++-assoc xs ys zs))
    ≡⟨⟩
      ap (λ a0 → (w ∷ a0) ++ zs) (++-assoc ws xs ys) ∙ ap (λ a0 → w ∷ a0) (++-assoc ws (xs ++ ys) zs ∙ ap (_++_ ws) (++-assoc xs ys zs))
    ≡⟨⟩
      ap (λ a0 → (w ∷ a0) ++ zs) (++-assoc ws xs ys) ∙ ap (λ a0 → w ∷ a0) (++-assoc ws (xs ++ ys) zs ∙ ap (_++_ ws) (++-assoc xs ys zs))
    ≡⟨⟩ 
      ap (λ a0 → (w ∷ a0) ++ zs) (++-assoc ws xs ys) ∙ ap (λ a0 → w ∷ a0) (++-assoc ws (xs ++ ys) zs ∙ ap (λ p → ws ++ p) (++-assoc xs ys zs)) 
    ≡⟨ ap (λ p → ap (λ a0 → (w ∷ a0) ++ zs) (++-assoc ws xs ys) ∙ p) (ap-compPath ((λ a0 → w ∷ a0)) ((++-assoc ws (xs ++ ys) zs)) ((ap (λ p → ws ++ p) (++-assoc xs ys zs)))) ⟩ 
      ap (λ a0 → (w ∷ a0) ++ zs) (++-assoc ws xs ys) ∙ ap (λ a0 → w ∷ a0) (++-assoc ws (xs ++ ys) zs) ∙ ap (λ a0 → w ∷ a0) (ap (λ p → ws ++ p) (++-assoc xs ys zs))
    ≡⟨⟩ 
      ap (λ a0 → (w ∷ a0) ++ zs) (++-assoc ws xs ys) ∙ ap (λ a0 → w ∷ a0) (++-assoc ws (xs ++ ys) zs) ∙ (ap (λ p → w  ∷ (ws ++ p) ) (++-assoc xs ys zs))
    ≡⟨⟩ 
      ap (λ a0 → (w ∷ a0) ++ zs) (++-assoc ws xs ys) ∙ ap (λ a0 → w ∷ a0) (++-assoc ws (xs ++ ys) zs) ∙ (ap (λ p → ((w) ∷ ((_++_) (ws) (p)))) (++-assoc xs ys zs))
    ≡⟨⟩ 
      ap (λ a0 → (w ∷ a0) ++ zs) (++-assoc ws xs ys) ∙ (ap (λ a0 → w ∷ a0) (++-assoc ws (xs ++ ys) zs) ∙ (ap (λ p → ((w) ∷ ((_++_) (ws) (p)))) ((++-assoc) (xs) (ys) (zs))))
    ≡⟨⟩
      ap (λ a0 → (w ∷ a0) ++ zs) (++-assoc ws xs ys) ∙ ((ap (λ a0 → ((_∷_) (w) (a0))) ((++-assoc) (ws) ((_++_) (xs) (ys)) (zs))) ∙ (ap (λ p → ((w) ∷ ((_++_) (ws) (p)))) ((++-assoc) (xs) (ys) (zs))))
    ≡⟨⟩ 
      ap (λ p → p ++ zs) (ap (λ a0 → w ∷ a0) (++-assoc ws xs ys)) ∙ ((ap (λ a0 → ((_∷_) (w) (a0))) ((++-assoc) (ws) ((_++_) (xs) (ys)) (zs))) ∙ (ap (λ p → ((w) ∷ ((_++_) (ws) (p)))) ((++-assoc) (xs) (ys) (zs))))
    ≡⟨⟩
      (ap (λ p → p ++ zs) (ap (λ a0 → w ∷ a0) (++-assoc ws xs ys))) ∙ ((ap (λ a0 → ((_∷_) (w) (a0))) ((++-assoc) (ws) ((_++_) (xs) (ys)) (zs))) ∙ (ap (λ p → ((w) ∷ ((_++_) (ws) (p)))) ((++-assoc) (xs) (ys) (zs))))
    ≡⟨⟩
      (ap (λ p → ((_++_) (p) (zs))) (ap (λ a0 → ((_∷_) (w) (a0))) ((++-assoc) (ws) (xs) (ys)))) ∙ ((ap (λ a0 → ((_∷_) (w) (a0))) ((++-assoc) (ws) ((_++_) (xs) (ys)) (zs))) ∙ (ap (λ p → ((_++_) ((w) ∷ (ws)) (p))) ((++-assoc) (xs) (ys) (zs))))
    ≡⟨⟩
      (ap (λ p → ((_++_) (p) (zs))) (ap (λ a0 → ((_∷_) (w) (a0))) ((++-assoc) (ws) (xs) (ys)))) ∙ (((++-assoc) ((w) ∷ (ws)) ((_++_) (xs) (ys)) (zs)) ∙ (ap (λ p → ((_++_) ((w) ∷ (ws)) (p))) ((++-assoc) (xs) (ys) (zs))))
    ≡⟨⟩
      (ap (λ p → ((_++_) (p) (zs))) ((++-assoc) ((w) ∷ (ws)) (xs) (ys))) ∙ (((++-assoc) ((w) ∷ (ws)) ((_++_) (xs) (ys)) (zs)) ∙ (ap (λ p → ((_++_) ((w) ∷ (ws)) (p))) ((++-assoc) (xs) (ys) (zs))))
    ∎


list-str : MonStr (List A)
𝟙 list-str = []
_⊗_ list-str = _++_
Λ list-str = idp
ρ list-str = ++-unit-r
α list-str = ++-assoc
▿ list-str = list-▿
⬠ list-str = list-⬠

module Free {x y : Level} {A : Type x} (𝔜 : MonGpd y) where

  module _ (f : A -> 𝔜 .car) where
    _♯ : List A -> 𝔜 .car
    [] ♯ = 𝔜 .str .𝟙
    (x ∷ xs) ♯ = 𝔜 .str ._⊗_ (f x) (xs ♯)
