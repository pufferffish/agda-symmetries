{-# OPTIONS --cubical --safe --exact-split #-}

module Cubical.Structures.Set.CMon.CList where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
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

data CList {a} (A : Type a) : Type a where
  [] : CList A
  _∷_ : (a : A) -> (as : CList A) -> CList A
  comm : (a b : A)
      -> {as bs : CList A} (cs : CList A)
      -> (p : as ≡ b ∷ cs) (q : bs ≡ a ∷ cs)
      -> a ∷ as ≡ b ∷ bs
  isSetCList : isSet (CList A)

pattern [_] a = a ∷ []

module elimCListSet {ℓ p : Level} {A : Type ℓ} (P : CList A -> Type p)
                   ([]* : P [])
                   (_∷*_ : (x : A) {xs : CList A} -> P xs -> P (x ∷ xs))
                   (comm* : (a b : A)
                            -> {as bs : CList A} {cs : CList A}
                            -> {as* : P as}
                            -> {bs* : P bs}
                            -> (cs* : P cs)
                            -> {p : as ≡ b ∷ cs} {q : bs ≡ a ∷ cs}
                            -> (bp : PathP (λ i -> P (p i)) as* (b ∷* cs*))
                            -> (bq : PathP (λ i -> P (q i)) bs* (a ∷* cs*))
                            -> PathP (λ i -> P (comm a b cs p q i)) (a ∷* as*) (b ∷* bs*)
                   )
                   (isSetCList* : {xs : CList A} -> isSet (P xs))
                   where
  f : (xs : CList A) -> P xs
  f [] = []*
  f (a ∷ as) = a ∷* f as
  f (comm a b {as} {bs} cs p q i) =
    comm* a b (f cs) (cong f p) (cong f q) i
  f (isSetCList xs ys p q i j) =
    isOfHLevel→isOfHLevelDep 2 (λ xs -> isSetCList* {xs = xs}) (f xs) (f ys) (cong f p) (cong f q) (isSetCList xs ys p q) i j

module elimCListProp {ℓ p : Level} {A : Type ℓ} (P : CList A -> Type p)
                   ([]* : P [])
                   (_∷*_ : (x : A) {xs : CList A} -> P xs -> P (x ∷ xs))
                   (isSetCList* : {xs : CList A} -> isProp (P xs))
                   where
  f : (xs : CList A) -> P xs
  f = elimCListSet.f P []* _∷*_
    (λ a b {as} {bs} {cs} {as*} {bs*} cs* bp bq -> toPathP (isSetCList* _ (b ∷* bs*)))
    (isProp→isSet isSetCList*)

private
  variable
    ℓ : Level
    A : Type ℓ

_++_ : CList A -> CList A -> CList A
[] ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)
comm a b cs p q i ++ bs = comm a b (cs ++ bs) (cong (_++ bs) p) (cong (_++ bs) q) i
isSetCList a b p q i j ++ bs = isSetCList (a ++ bs) (b ++ bs) (cong (_++ bs) p) (cong (_++ bs) q) i j

++-unitl : (as : CList A) -> [] ++ as ≡ as
++-unitl as = refl

++-unitr : (as : CList A) -> as ++ [] ≡ as
++-unitr = elimCListProp.f _ refl (λ a p -> cong (a ∷_) p) (isSetCList _ _)

++-assocr : (as bs cs : CList A) -> (as ++ bs) ++ cs ≡ as ++ (bs ++ cs)
++-assocr = elimCListProp.f _
  (λ _ _ -> refl)
  (λ x p bs cs -> cong (x ∷_) (p bs cs))
  (isPropΠ λ _ -> isPropΠ λ _ -> isSetCList _ _)

swap : (a b : A) (cs : CList A) -> a ∷ b ∷ cs ≡ b ∷ a ∷ cs
swap a b cs = comm a b cs refl refl

++-∷ : (a : A) (as : CList A) -> a ∷ as ≡ as ++ [ a ]
++-∷ a = elimCListProp.f (λ as -> a ∷ as ≡ as ++ [ a ])
  refl
  (λ b {as} p -> swap a b as ∙ cong (b ∷_) p)
  (isSetCList _ _) 

++-comm : (as bs : CList A) -> as ++ bs ≡ bs ++ as
++-comm = elimCListProp.f _
  (sym ∘ ++-unitr)
  (λ a {as} p bs -> cong (a ∷_) (p bs) ∙ cong (_++ as) (++-∷ a bs) ∙ ++-assocr bs [ a ] as)
  (isPropΠ λ _ -> isSetCList _ _)

clist-α : ∀ {n : Level} {X : Type n} -> sig M.MonSig (CList X) -> CList X
clist-α (M.`e , i) = []
clist-α (M.`⊕ , i) = i fzero ++ i fone

module Free {x y : Level} {A : Type x} {𝔜 : struct y M.MonSig} (isSet𝔜 : isSet (𝔜 .car)) (𝔜-cmon : 𝔜 ⊨ M.CMonSEq) where
  module 𝔜 = M.CMonSEq 𝔜 𝔜-cmon

  𝔛 : M.CMonStruct
  𝔛 = < CList A , clist-α >

  module _ (f : A -> 𝔜 .car) where
    _♯ : CList A -> 𝔜 .car
    _♯ = elimCListSet.f _
      𝔜.e
      (λ a p -> f a 𝔜.⊕ p)
      (λ a b {ab} {bs} {cs} {as*} {bs*} cs* bp bq ->
        f a 𝔜.⊕ as* ≡⟨ cong (f a 𝔜.⊕_) bp ⟩
        f a 𝔜.⊕ f b 𝔜.⊕ cs* ≡⟨ sym (𝔜.assocr _ _ _) ⟩
        (f a 𝔜.⊕ f b) 𝔜.⊕ cs* ≡⟨ cong (𝔜._⊕ cs*) (𝔜.comm _ _) ⟩
        (f b 𝔜.⊕ f a) 𝔜.⊕ cs* ≡⟨ 𝔜.assocr _ _ _ ⟩
        f b 𝔜.⊕ (f a 𝔜.⊕ cs*) ≡⟨ cong (f b 𝔜.⊕_) (sym bq) ⟩
        f b 𝔜.⊕ bs* ∎
      )
      isSet𝔜

    private
      ♯-++ : ∀ xs ys -> (xs ++ ys) ♯ ≡ (xs ♯) 𝔜.⊕ (ys ♯)
      ♯-++ = elimCListProp.f _
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
    clistEquivLemma : (g : structHom 𝔛 𝔜) -> (x : CList A) -> g .fst x ≡ ((g .fst ∘ [_]) ♯) x
    clistEquivLemma (g , homMonWit) = elimCListProp.f _
      (sym (homMonWit M.`e (lookup L.[])) ∙ 𝔜.e-eta)
      (λ x {xs} p ->
        g (x ∷ xs) ≡⟨ sym (homMonWit M.`⊕ (lookup ([ x ] L.∷ xs L.∷ L.[]))) ⟩
        _ ≡⟨ 𝔜.⊕-eta (lookup ([ x ] L.∷ xs L.∷ L.[])) g ⟩
        _ ≡⟨ cong (g [ x ] 𝔜.⊕_) p ⟩
        _ ∎
      )
      (isSet𝔜 _ _)

    clistEquivLemma-β : (g : structHom 𝔛 𝔜) -> g ≡ ♯-isMonHom (g .fst ∘ [_])
    clistEquivLemma-β g = structHom≡ 𝔛 𝔜 g (♯-isMonHom (g .fst ∘ [_])) isSet𝔜 (funExt (clistEquivLemma g))

  clistMonEquiv : structHom 𝔛 𝔜 ≃ (A -> 𝔜 .car)
  clistMonEquiv =
    isoToEquiv (iso (λ g -> g .fst ∘ [_]) ♯-isMonHom (λ g -> funExt (𝔜.unitr ∘ g)) (sym ∘ clistEquivLemma-β))

module CListDef = F.Definition M.MonSig M.CMonEqSig M.CMonSEq

clist-sat : ∀ {n} {X : Type n} -> < CList X , clist-α > ⊨ M.CMonSEq
clist-sat (M.`mon M.`unitl) ρ = ++-unitl (ρ fzero)
clist-sat (M.`mon M.`unitr) ρ = ++-unitr (ρ fzero)
clist-sat (M.`mon M.`assocr) ρ = ++-assocr (ρ fzero) (ρ fone) (ρ ftwo)
clist-sat M.`comm ρ = ++-comm (ρ fzero) (ρ fone)

clistDef : ∀ {ℓ ℓ'} -> CListDef.Free ℓ ℓ' 2
F.Definition.Free.F clistDef = CList
F.Definition.Free.η clistDef = [_]
F.Definition.Free.α clistDef = clist-α
F.Definition.Free.sat clistDef = clist-sat
F.Definition.Free.isFree clistDef isSet𝔜 satMon = (Free.clistMonEquiv isSet𝔜 satMon) .snd
