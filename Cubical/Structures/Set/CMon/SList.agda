{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.CMon.SList where

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

infixr 20 _∷_

data SList {a} (A : Type a) : Type a where
  [] : SList A
  _∷_ : (a : A) -> (as : SList A) -> SList A
  swap : (a b : A) (cs : SList A)
      -> a ∷ b ∷ cs ≡ b ∷ a ∷ cs
  isSetSList : isSet (SList A)

pattern [_] a = a ∷ []

module elimSListSet {ℓ p : Level} {A : Type ℓ} (P : SList A -> Type p)
                   ([]* : P [])
                   (_∷*_ : (x : A) {xs : SList A} -> P xs -> P (x ∷ xs))
                   (swap* : (a b : A) -> {cs : SList A}
                            -> (cs* : P cs)
                            -> PathP (λ i -> P (swap a b cs i)) (a ∷* (b ∷* cs*)) (b ∷* (a ∷* cs*))
                   )
                   (isSetSList* : {xs : SList A} -> isSet (P xs))
                   where
  f : (xs : SList A) -> P xs
  f [] = []*
  f (a ∷ xs) = a ∷* f xs
  f (swap a b xs i) = swap* a b (f xs) i
  f (isSetSList xs ys p q i j) =
    isOfHLevel→isOfHLevelDep 2 (\xs -> isSetSList* {xs = xs}) (f xs) (f ys) (cong f p) (cong f q) (isSetSList xs ys p q) i j

module elimSListProp {ℓ p : Level} {A : Type ℓ} (P : SList A -> Type p)
                   ([]* : P [])
                   (_∷*_ : (x : A) {xs : SList A} -> P xs -> P (x ∷ xs))
                   (isSetSList* : {xs : SList A} -> isProp (P xs))
                   where
  f : (xs : SList A) -> P xs
  f = elimSListSet.f P []* _∷*_ comm* (isProp→isSet isSetSList*)
    where
      abstract
        comm* : (a b : A) {cs : SList A} (cs* : P cs) ->
                PathP (λ i -> P (swap a b cs i)) (a ∷* (b ∷* cs*)) (b ∷* (a ∷* cs*))
        comm* a b {cs} cs* = toPathP (isSetSList* _ (b ∷* (a ∷* cs*)))

private
  variable
    ℓ : Level
    A : Type ℓ

length : SList A -> ℕ
length [] = 0
length (a ∷ as) = suc (length as)
length (swap a b as i) =
  (idfun (suc (suc (length as)) ≡ suc (suc (length as)))) refl i
length (isSetSList as bs p q i j) =
  isSetℕ (length as) (length bs) (cong length p) (cong length q) i j

_++_ : SList A -> SList A -> SList A
[] ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)
swap a b as i ++ bs = swap a b (as ++ bs) i
isSetSList a b p q i j ++ bs = isSetSList (a ++ bs) (b ++ bs) (cong (_++ bs) p) (cong (_++ bs) q) i j

++-unitl : (as : SList A) -> [] ++ as ≡ as
++-unitl as = refl

++-unitr : (as : SList A) -> as ++ [] ≡ as
++-unitr = elimSListProp.f _ refl (λ x p -> cong (x ∷_) p) (isSetSList _ _)

++-assocr : (as bs cs : SList A) -> (as ++ bs) ++ cs ≡ as ++ (bs ++ cs)
++-assocr = elimSListProp.f _
  (λ _ _ -> refl)
  (λ x p bs cs -> cong (x ∷_) (p bs cs))
  (isPropΠ λ _ -> isPropΠ λ _ -> isSetSList _ _)

++-∷ : (a : A) (as : SList A) -> a ∷ as ≡ as ++ [ a ]
++-∷ a = elimSListProp.f (λ as -> a ∷ as ≡ as ++ [ a ])
  refl
  (λ b {as} p -> swap a b as ∙ cong (b ∷_) p)
  (isSetSList _ _) 

++-comm : (as bs : SList A) -> as ++ bs ≡ bs ++ as
++-comm = elimSListProp.f _
  (sym ∘ ++-unitr)
  (λ a {as} p bs -> cong (a ∷_) (p bs) ∙ cong (_++ as) (++-∷ a bs) ∙ ++-assocr bs [ a ] as)
  (isPropΠ λ _ -> isSetSList _ _)

slist-α : ∀ {n : Level} {X : Type n} -> sig M.MonSig (SList X) -> SList X
slist-α (M.`e , i) = []
slist-α (M.`⊕ , i) = i fzero ++ i fone

module Free {x y : Level} {A : Type x} {𝔜 : struct y M.MonSig} (isSet𝔜 : isSet (𝔜 .car)) (𝔜-cmon : 𝔜 ⊨ M.CMonSEq) where
  module 𝔜 = M.CMonSEq 𝔜 𝔜-cmon

  𝔛 : M.CMonStruct
  𝔛 = < SList A , slist-α >

  module _ (f : A -> 𝔜 .car) where
    _♯ : SList A -> 𝔜 .car    
    [] ♯ = 𝔜.e
    (a ∷ as) ♯ = (f a) 𝔜.⊕ (as ♯)
    swap a b xs i ♯ =
      ( sym (𝔜.assocr (f a) (f b) (xs ♯))
      ∙ cong (𝔜._⊕ (xs ♯)) (𝔜.comm (f a) (f b))
      ∙ 𝔜.assocr (f b) (f a) (xs ♯)
      ) i
    isSetSList xs ys p q i j ♯ = isSet𝔜 (xs ♯) (ys ♯) (cong _♯ p) (cong _♯ q) i j

    private
      ♯-++ : ∀ xs ys -> (xs ++ ys) ♯ ≡ (xs ♯) 𝔜.⊕ (ys ♯)
      ♯-++ = elimSListProp.f _
        (λ ys -> sym (𝔜.unitl (ys ♯)))
        (λ a {xs} p ys ->
          f a 𝔜.⊕ ((xs ++ ys) ♯) ≡⟨ cong (f a 𝔜.⊕_) (p ys) ⟩
          f a 𝔜.⊕ ((xs ♯) 𝔜.⊕ (ys ♯)) ≡⟨ sym (𝔜.assocr (f a) (xs ♯) (ys ♯)) ⟩
          _ ∎
        )
        (isPropΠ λ _ -> isSet𝔜 _ _)

    ♯-isMonHom : structHom 𝔛 𝔜
    fst ♯-isMonHom = _♯
    snd ♯-isMonHom M.`e i = 𝔜.e-eta
    snd ♯-isMonHom M.`⊕ i = 𝔜.⊕-eta i _♯ ∙ sym (♯-++ (i fzero) (i fone))

  private
    slistEquivLemma : (g : structHom 𝔛 𝔜) -> (x : SList A) -> g .fst x ≡ ((g .fst ∘ [_]) ♯) x
    slistEquivLemma (g , homMonWit) = elimSListProp.f _
      (sym (homMonWit M.`e (lookup L.[])) ∙ 𝔜.e-eta)
      (λ x {xs} p ->
        g (x ∷ xs) ≡⟨ sym (homMonWit M.`⊕ (lookup ([ x ] L.∷ xs L.∷ L.[]))) ⟩
        _ ≡⟨ 𝔜.⊕-eta (lookup ([ x ] L.∷ xs L.∷ L.[])) g ⟩
        _ ≡⟨ cong (g [ x ] 𝔜.⊕_) p ⟩
        _ ∎
      )
      (isSet𝔜 _ _)

    slistEquivLemma-β : (g : structHom 𝔛 𝔜) -> g ≡ ♯-isMonHom (g .fst ∘ [_])
    slistEquivLemma-β g = structHom≡ 𝔛 𝔜 g (♯-isMonHom (g .fst ∘ [_])) isSet𝔜 (funExt (slistEquivLemma g))

  slistMonEquiv : structHom 𝔛 𝔜 ≃ (A -> 𝔜 .car)
  slistMonEquiv =
    isoToEquiv (iso (λ g -> g .fst ∘ [_]) ♯-isMonHom (λ g -> funExt (𝔜.unitr ∘ g)) (sym ∘ slistEquivLemma-β))

module SListDef = F.Definition M.MonSig M.CMonEqSig M.CMonSEq

slist-sat : ∀ {n} {X : Type n} -> < SList X , slist-α > ⊨ M.CMonSEq
slist-sat (M.`mon M.`unitl) ρ = ++-unitl (ρ fzero)
slist-sat (M.`mon M.`unitr) ρ = ++-unitr (ρ fzero)
slist-sat (M.`mon M.`assocr) ρ = ++-assocr (ρ fzero) (ρ fone) (ρ ftwo)
slist-sat M.`comm ρ = ++-comm (ρ fzero) (ρ fone)

slistDef : ∀ {ℓ ℓ'} -> SListDef.Free ℓ ℓ' 2
F.Definition.Free.F slistDef = SList
F.Definition.Free.η slistDef = [_]
F.Definition.Free.α slistDef = slist-α
F.Definition.Free.sat slistDef = slist-sat
F.Definition.Free.isFree slistDef isSet𝔜 satMon = (Free.slistMonEquiv isSet𝔜 satMon) .snd
 