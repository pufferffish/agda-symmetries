{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.Mon.List where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
import Cubical.Data.Empty as ⊥

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity

private
  variable
    ℓ : Level
    A : Type ℓ

list-α : sig M.MonSig (List A) -> List A
list-α (M.`e , i) = []
list-α (M.`⊕ , i) = i fzero ++ i fone

module Free {x y : Level} {A : Type x} {𝔜 : struct y M.MonSig} (isSet𝔜 : isSet (𝔜 .car)) (𝔜-monoid : 𝔜 ⊨ M.MonSEq) where  
  module 𝔜 = M.MonSEq 𝔜 𝔜-monoid

  𝔏 : M.MonStruct
  𝔏 = < List A , list-α >

  module _ (f : A -> 𝔜 .car) where
    _♯ : List A -> 𝔜 .car
    [] ♯ = 𝔜.e
    (x ∷ xs) ♯ = f x 𝔜.⊕ (xs ♯)

    private
      ♯-++ : ∀ xs ys -> (xs ++ ys) ♯ ≡ (xs ♯) 𝔜.⊕ (ys ♯)
      ♯-++ [] ys = sym (𝔜.unitl (ys ♯))
      ♯-++ (x ∷ xs) ys = cong (f x 𝔜.⊕_) (♯-++ xs ys) ∙ sym (𝔜.assocr (f x) (xs ♯) (ys ♯)) 

    ♯-isMonHom : structHom 𝔏 𝔜
    fst ♯-isMonHom = _♯
    snd ♯-isMonHom M.`e i = 𝔜.e-eta
    snd ♯-isMonHom M.`⊕ i = 𝔜.⊕-eta i _♯ ∙ sym (♯-++ (i fzero) (i fone))

  private
    listEquivLemma : (g : structHom 𝔏 𝔜) -> (x : List A) -> g .fst x ≡ ((g .fst ∘ [_]) ♯) x
    listEquivLemma (g , homMonWit) [] = sym (homMonWit M.`e (lookup [])) ∙ 𝔜.e-eta
    listEquivLemma (g , homMonWit) (x ∷ xs) =
      g (x ∷ xs) ≡⟨ sym (homMonWit M.`⊕ (lookup ([ x ] ∷ xs ∷ []))) ⟩
      𝔜 .alg (M.`⊕ , (λ w -> g (lookup ((x ∷ []) ∷ xs ∷ []) w))) ≡⟨ 𝔜.⊕-eta (lookup ([ x ] ∷ xs ∷ [])) g ⟩
      g [ x ] 𝔜.⊕ g xs ≡⟨ cong (g [ x ] 𝔜.⊕_) (listEquivLemma (g , homMonWit) xs) ⟩ 
      _ ∎

    listEquivLemma-β : (g : structHom 𝔏 𝔜) -> g ≡ ♯-isMonHom (g .fst ∘ [_])
    listEquivLemma-β g = structHom≡ 𝔏 𝔜 g (♯-isMonHom (g .fst ∘ [_])) isSet𝔜 (funExt (listEquivLemma g))

  listEquiv : structHom 𝔏 𝔜 ≃ (A -> 𝔜 .car)
  listEquiv =
    isoToEquiv (iso (λ g -> g .fst ∘ [_]) ♯-isMonHom (λ g -> funExt (𝔜.unitr ∘ g)) (sym ∘ listEquivLemma-β))

module ListDef = F.Definition M.MonSig M.MonEqSig M.MonSEq

list-sat : ∀ {n} {X : Type n} -> < List X , list-α > ⊨ M.MonSEq
list-sat M.`unitl ρ = refl
list-sat M.`unitr ρ = ++-unit-r (ρ fzero)
list-sat M.`assocr ρ = ++-assoc (ρ fzero) (ρ fone) (ρ ftwo)

listDef : ∀ {ℓ ℓ'} -> ListDef.Free ℓ ℓ' 2
F.Definition.Free.F listDef = List
F.Definition.Free.η listDef = [_]
F.Definition.Free.α listDef = list-α
F.Definition.Free.sat listDef = list-sat
F.Definition.Free.isFree listDef isSet𝔜 satMon = (Free.listEquiv isSet𝔜 satMon) .snd
