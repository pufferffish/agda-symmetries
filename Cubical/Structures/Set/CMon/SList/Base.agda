{-# OPTIONS --cubical --safe --exact-split #-}

module Cubical.Structures.Set.CMon.SList.Base where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
open import Cubical.Induction.WellFounded
import Cubical.Data.List as L

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity
open import Cubical.HITs.FiniteMultiset public renaming (FMSet to SList; comm to swap)

pattern [_] a = a ∷ []

private
  variable
    ℓ : Level
    A : Type ℓ

slist-α : ∀ {n : Level} {X : Type n} -> sig M.MonSig (SList X) -> SList X
slist-α (M.`e , i) = []
slist-α (M.`⊕ , i) = i fzero ++ i fone

module Free {x y : Level} {A : Type x} {𝔜 : struct y M.MonSig} (isSet𝔜 : isSet (𝔜 .car)) (𝔜-cmon : 𝔜 ⊨ M.CMonSEq) where
  module 𝔜 = M.CMonSEq 𝔜 𝔜-cmon

  𝔛 : M.CMonStruct
  𝔛 = < SList A , slist-α >

  module _ (f : A -> 𝔜 .car) where
    _♯ : SList A -> 𝔜 .car    
    _♯ = Elim.f 𝔜.e
      (λ x xs -> (f x) 𝔜.⊕ xs)
      (λ a b xs i ->
        ( sym (𝔜.assocr (f a) (f b) xs)
        ∙ cong (𝔜._⊕ xs) (𝔜.comm (f a) (f b))
        ∙ 𝔜.assocr (f b) (f a) xs
        ) i
      )
      (λ _ -> isSet𝔜)

    -- export these for computation
    ♯-++ : ∀ xs ys -> (xs ++ ys) ♯ ≡ (xs ♯) 𝔜.⊕ (ys ♯)
    ♯-++ = ElimProp.f (isPropΠ λ _ -> isSet𝔜 _ _)
      (λ ys -> sym (𝔜.unitl (ys ♯)))
      (λ a {xs} p ys ->
        f a 𝔜.⊕ ((xs ++ ys) ♯) ≡⟨ cong (f a 𝔜.⊕_) (p ys) ⟩
        f a 𝔜.⊕ ((xs ♯) 𝔜.⊕ (ys ♯)) ≡⟨ sym (𝔜.assocr (f a) (xs ♯) (ys ♯)) ⟩
        _
      ∎)

    ♯-∷ : ∀ x xs -> (x ∷ xs) ♯ ≡ (f x) 𝔜.⊕ (xs ♯)
    ♯-∷ x xs = ♯-++ [ x ] xs ∙ congS (𝔜._⊕ (xs ♯)) (𝔜.unitr (f x))

    ♯-isMonHom : structHom 𝔛 𝔜
    fst ♯-isMonHom = _♯
    snd ♯-isMonHom M.`e i = 𝔜.e-eta
    snd ♯-isMonHom M.`⊕ i = 𝔜.⊕-eta i _♯ ∙ sym (♯-++ (i fzero) (i fone))

  private
    slistEquivLemma : (g : structHom 𝔛 𝔜) -> (x : SList A) -> g .fst x ≡ ((g .fst ∘ [_]) ♯) x
    slistEquivLemma (g , homMonWit) = ElimProp.f (isSet𝔜 _ _)
      (sym (homMonWit M.`e (lookup L.[])) ∙ 𝔜.e-eta)
      (λ x {xs} p ->
        g (x ∷ xs) ≡⟨ sym (homMonWit M.`⊕ (lookup ([ x ] L.∷ xs L.∷ L.[]))) ⟩
        _ ≡⟨ 𝔜.⊕-eta (lookup ([ x ] L.∷ xs L.∷ L.[])) g ⟩
        _ ≡⟨ cong (g [ x ] 𝔜.⊕_) p ⟩
        _ ∎
      )
  
    slistEquivLemma-β : (g : structHom 𝔛 𝔜) -> g ≡ ♯-isMonHom (g .fst ∘ [_])
    slistEquivLemma-β g = structHom≡ 𝔛 𝔜 g (♯-isMonHom (g .fst ∘ [_])) isSet𝔜 (funExt (slistEquivLemma g))

  slistMonEquiv : structHom 𝔛 𝔜 ≃ (A -> 𝔜 .car)
  slistMonEquiv =
    isoToEquiv (iso (λ g -> g .fst ∘ [_]) ♯-isMonHom (λ g -> funExt (𝔜.unitr ∘ g)) (sym ∘ slistEquivLemma-β))

module SListDef = F.Definition M.MonSig M.CMonEqSig M.CMonSEq

slist-sat : ∀ {n} {X : Type n} -> < SList X , slist-α > ⊨ M.CMonSEq
slist-sat (M.`mon M.`unitl) ρ = unitl-++ (ρ fzero)
slist-sat (M.`mon M.`unitr) ρ = unitr-++ (ρ fzero)
slist-sat (M.`mon M.`assocr) ρ = sym (assoc-++ (ρ fzero) (ρ fone) (ρ ftwo))
slist-sat M.`comm ρ = comm-++ (ρ fzero) (ρ fone)

slistDef : ∀ {ℓ ℓ'} -> SListDef.Free ℓ ℓ' 2
F.Definition.Free.F slistDef = SList
F.Definition.Free.η slistDef = [_]
F.Definition.Free.α slistDef = slist-α
F.Definition.Free.sat slistDef = slist-sat
F.Definition.Free.isFree slistDef isSet𝔜 satMon = (Free.slistMonEquiv isSet𝔜 satMon) .snd
