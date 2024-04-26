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
    ≡⟨ sym (rUnit _) ⟩
      (++-assoc) (xs) (ys) (zs)
    ≡⟨ sym (sym (lUnit _)) ⟩
      (idp _) ∙ (ap (λ p → ((_++_) ([]) (p))) ((++-assoc) (xs) (ys) (zs)))
    ≡⟨ sym (sym (lUnit _)) ⟩
      (idp _) ∙ (((++-assoc) ([]) ((_++_) (xs) (ys)) (zs)) ∙ (ap (λ p → ((_++_) ([]) (p))) ((++-assoc) (xs) (ys) (zs))))
    ∎
 
  list-⬠ xs ys zs (w ∷ ws) =
      ((++-assoc) ((_++_) ((w) ∷ (ws)) (xs)) (ys) (zs)) ∙ ((++-assoc) ((w) ∷ (ws)) (xs) ((_++_) (ys) (zs)))
    ≡⟨⟩
      ((++-assoc) ((w) ∷ ((_++_) (ws) (xs))) (ys) (zs)) ∙ ((++-assoc) ((w) ∷ (ws)) (xs) ((_++_) (ys) (zs)))
    ≡⟨ sym (ap-compPath (λ a0 → ((_∷_) (w) (a0))) ((++-assoc) ((_++_) (ws) (xs)) (ys) (zs)) ((++-assoc) (ws) (xs) ((_++_) (ys) (zs))) ) ⟩
      ap (λ a0 → ((_∷_) (w) (a0))) (((++-assoc) ((_++_) (ws) (xs)) (ys) (zs)) ∙ ((++-assoc) (ws) (xs) ((_++_) (ys) (zs))))
    ≡⟨ ap  (λ p → (ap (λ a0 → ((_∷_) (w) (a0)))) p) (list-⬠ xs ys zs ws) ⟩
      ap (λ a0 → ((_∷_) (w) (a0))) (ap (_++ zs) (++-assoc ws xs ys) ∙ ++-assoc ws (xs ++ ys) zs ∙ ap (_++_ ws) (++-assoc xs ys zs))
    ≡⟨ ap-compPath ((λ a0 → ((_∷_) (w) (a0)))) ((ap (_++ zs) (++-assoc ws xs ys))) ((++-assoc ws (xs ++ ys) zs ∙ ap (_++_ ws) (++-assoc xs ys zs))) ⟩
      ap (λ a0 → ((_∷_) (w) (a0))) (ap (_++ zs) (++-assoc ws xs ys)) ∙ ap (λ a0 → ((_∷_) (w) (a0))) (++-assoc ws (xs ++ ys) zs ∙ ap (_++_ ws) (++-assoc xs ys zs))
    ≡⟨ ap (λ p → ap (λ a0 → (w ∷ a0) ++ zs) (++-assoc ws xs ys) ∙ p) (ap-compPath ((λ a0 → w ∷ a0)) ((++-assoc ws (xs ++ ys) zs)) ((ap (λ p → ws ++ p) (++-assoc xs ys zs)))) ⟩ 
      ap (λ a0 → (w ∷ a0) ++ zs) (++-assoc ws xs ys) ∙ ap (λ a0 → w ∷ a0) (++-assoc ws (xs ++ ys) zs) ∙ ap (λ a0 → w ∷ a0) (ap (λ p → ws ++ p) (++-assoc xs ys zs))
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

    private
      ♯-𝟙 : [] ♯ ≡ 𝔜 .str .𝟙
      ♯-𝟙 = refl

      ♯-++ : ∀ xs ys -> (xs ++ ys) ♯ ≡ 𝔜 .str ._⊗_ (xs ♯) (ys ♯)
      ♯-++ [] ys = sym (𝔜 .str .Λ (ys ♯))
      ♯-++ (x ∷ xs) ys = cong (𝔜 .str ._⊗_ (f x)) (♯-++ xs ys) ∙ sym (𝔜 .str .α (f x) (xs ♯) (ys ♯))

      -- Coherence
      ρ𝟙-Λ𝟙 : 𝔜 .str .ρ (𝔜 .str .𝟙) ≡ 𝔜 .str .Λ (𝔜 .str .𝟙)
      ρ𝟙-Λ𝟙 = TODO

      α𝟙ρ : ∀ x y -> (𝔜 .str .α x y (𝔜 .str .𝟙)) ∙ ap (𝔜 .str ._⊗_ x) (𝔜 .str .ρ y) ≡ 𝔜 .str .ρ (𝔜 .str ._⊗_ x y)
      α𝟙ρ = TODO

      sym-α𝟙ρ : ∀ x y → sym (𝔜 .str .α x y (𝔜 .str .𝟙)) ∙ (𝔜 .str .ρ  (𝔜 .str ._⊗_ x y)) ≡ ap (𝔜 .str ._⊗_ x) (𝔜 .str .ρ y)
      sym-α𝟙ρ = TODO

      ♯-ρ : ∀ xs -> ap _♯ (++-unit-r xs) ≡ ♯-++ xs [] ∙ ap (𝔜 .str ._⊗_ (xs ♯)) ♯-𝟙 ∙ 𝔜 .str .ρ (xs ♯)
      ♯-ρ [] =
          ap _♯ (++-unit-r [])
        ≡⟨⟩
          refl
        ≡⟨ sym (lCancel _) ⟩
          sym ((𝔜 .str .ρ (𝔜 .str .𝟙))) ∙ (𝔜 .str .ρ (𝔜 .str .𝟙))
        ≡⟨ ap (λ p → sym p ∙ (𝔜 .str .ρ (𝔜 .str .𝟙))) ρ𝟙-Λ𝟙 ⟩
          sym (𝔜 .str .Λ (𝔜 .str .𝟙)) ∙ (𝔜 .str .ρ (𝔜 .str .𝟙))
        ≡⟨ sym (ap (λ p → sym (𝔜 .str .Λ (𝔜 .str .𝟙)) ∙ p)  (sym (lUnit _))) ⟩ 
          sym (𝔜 .str .Λ (𝔜 .str .𝟙)) ∙ (refl ∙ 𝔜 .str .ρ (𝔜 .str .𝟙))
        ≡⟨⟩
          ♯-++ [] [] ∙ ap (𝔜 .str ._⊗_ ([] ♯)) ♯-𝟙 ∙ 𝔜 .str .ρ ([] ♯)
        ∎

      ♯-ρ (x ∷ xs) =
          ap _♯ (++-unit-r (x ∷ xs))
        ≡⟨⟩
          ap _♯ (cong (_∷_ x) (++-unit-r xs))
        ≡⟨⟩
          ap _♯ (ap (_∷_ x) (++-unit-r xs))
        ≡⟨⟩
          ap (_♯  ∘ (_∷_ x)) (++-unit-r xs)
        ≡⟨ {!   !} ⟩ -- ???
          ap (𝔜 .str ._⊗_ (f x)) ((♯-++ xs []) ∙ (𝔜 .str .ρ (xs ♯)))
        ≡⟨ {!   !} ⟩ -- ap fusion
          ap (𝔜 .str ._⊗_ (f x)) (♯-++ xs []) ∙ ap (𝔜 .str ._⊗_ (f x)) (𝔜 .str .ρ (xs ♯))
        ≡⟨ ap (λ p → cong (𝔜 .str ._⊗_ (f x)) (♯-++ xs []) ∙ p) (sym (sym-α𝟙ρ _ _)) ⟩
          ap (𝔜 .str ._⊗_ (f x)) (♯-++ xs []) ∙ (sym (𝔜 .str .α (f x) (xs ♯) (𝔜 .str .𝟙)) ∙ 𝔜 .str .ρ (𝔜 .str ._⊗_ (f x) (xs ♯)))
        ≡⟨ {!   !} ⟩ -- sym reassoc
          (cong (𝔜 .str ._⊗_ (f x)) (♯-++ xs []) ∙ sym (𝔜 .str .α (f x) (xs ♯) (𝔜 .str .𝟙))) ∙ 𝔜 .str .ρ (𝔜 .str ._⊗_ (f x) (xs ♯))
        ≡⟨⟩
          (cong (𝔜 .str ._⊗_ (f x)) (♯-++ xs []) ∙ sym (𝔜 .str .α (f x) (xs ♯) ([] ♯))) ∙ 𝔜 .str .ρ (𝔜 .str ._⊗_ (f x) (xs ♯))
        ≡⟨⟩
          ♯-++ (x ∷ xs) [] ∙ 𝔜 .str .ρ (𝔜 .str ._⊗_ (f x) (xs ♯))
        ≡⟨ ap (λ p →  (♯-++ (x ∷ xs) []) ∙ p) (lUnit _) ⟩
          ♯-++ (x ∷ xs) [] ∙ refl ∙ 𝔜 .str .ρ (𝔜 .str ._⊗_ (f x) (xs ♯))
        ≡⟨⟩
          ♯-++ (x ∷ xs) [] ∙ ap (𝔜 .str ._⊗_ (𝔜 .str ._⊗_ (f x) (xs ♯))) refl ∙ 𝔜 .str .ρ (𝔜 .str ._⊗_ (f x) (xs ♯))
        ≡⟨⟩
          ♯-++ (x ∷ xs) [] ∙ ap (𝔜 .str ._⊗_ (𝔜 .str ._⊗_ (f x) (xs ♯))) ♯-𝟙 ∙ 𝔜 .str .ρ (𝔜 .str ._⊗_ (f x) (xs ♯))
        ≡⟨⟩
          ♯-++ (x ∷ xs) [] ∙ ap (𝔜 .str ._⊗_ ((x ∷ xs) ♯)) ♯-𝟙 ∙ 𝔜 .str .ρ ((x ∷ xs) ♯)
        ∎


      ♯-Λ : ∀ xs -> ap _♯ (idp xs) ≡ ♯-++ [] xs ∙ ap (λ r → 𝔜 .str ._⊗_ r (xs ♯)) ♯-𝟙 ∙ 𝔜 .str .Λ (xs ♯)
      ♯-Λ [] =
          ap _♯ (idp [])
        ≡⟨⟩
          refl
        ≡⟨ sym (lCancel _) ⟩
          sym (𝔜 .str .Λ (𝔜 .str .𝟙)) ∙ 𝔜 .str .Λ (𝔜 .str .𝟙)
        ≡⟨ ap (λ p →  sym (𝔜 .str .Λ (𝔜 .str .𝟙)) ∙ p) (lUnit (𝔜 .str .Λ (𝔜 .str .𝟙))) ⟩
          sym (𝔜 .str .Λ (𝔜 .str .𝟙)) ∙ refl ∙ 𝔜 .str .Λ (𝔜 .str .𝟙)
        ≡⟨ ap (λ p → sym (𝔜 .str .Λ (𝔜 .str .𝟙)) ∙ p ∙ 𝔜 .str .Λ (𝔜 .str .𝟙)) refl  ⟩
          sym (𝔜 .str .Λ (𝔜 .str .𝟙)) ∙ ap (λ r → 𝔜 .str ._⊗_ r (𝔜 .str .𝟙)) refl ∙ 𝔜 .str .Λ (𝔜 .str .𝟙)
        ≡⟨⟩
          sym (𝔜 .str .Λ (𝔜 .str .𝟙)) ∙ ap (λ r → 𝔜 .str ._⊗_ r (𝔜 .str .𝟙)) ♯-𝟙 ∙ 𝔜 .str .Λ (𝔜 .str .𝟙)
        ≡⟨⟩
          sym (𝔜 .str .Λ (𝔜 .str .𝟙)) ∙ ap (λ r → 𝔜 .str ._⊗_ r ([] ♯)) ♯-𝟙 ∙ 𝔜 .str .Λ (𝔜 .str .𝟙)
        ≡⟨⟩
          sym (𝔜 .str .Λ ([] ♯)) ∙ ap (λ r → 𝔜 .str ._⊗_ r ([] ♯)) ♯-𝟙 ∙ 𝔜 .str .Λ ([] ♯)
        ≡⟨⟩
          ♯-++ [] [] ∙ ap (λ r → 𝔜 .str ._⊗_ r ([] ♯)) ♯-𝟙 ∙ 𝔜 .str .Λ ([] ♯)
        ∎

      ♯-Λ (x ∷ xs) = TODO

      -- TODO: ♯-α