{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.CMon.CList where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
import Cubical.Data.List as L

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.Mon.Free as FM
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
                            -> {as bs : CList A} (cs : CList A)
                            -> (as* : P as)
                            -> (bs* : P bs)
                            -> (p : as ≡ b ∷ cs) (q : bs ≡ a ∷ cs)
                            -> PathP (λ i -> P (comm a b cs p q i)) (a ∷* as*) (b ∷* bs*)
                   )
                   (isSetCList* : {xs : CList A} -> isSet (P xs))
                   where
  f : (xs : CList A) -> P xs
  f [] = []*
  f (x ∷ xs) = x ∷* f xs
  f (comm a b {xs} {ys} cs p q i) = comm* a b cs (f xs) (f ys) p q i
  f (isSetCList xs ys p q i j) =
    isOfHLevel→isOfHLevelDep 2 (\xs -> isSetCList* {xs = xs}) (f xs) (f ys) (cong f p) (cong f q) (isSetCList xs ys p q) i j

module elimCListProp {ℓ p : Level} {A : Type ℓ} (P : CList A -> Type p)
                   ([]* : P [])
                   (_∷*_ : (x : A) {xs : CList A} -> P xs -> P (x ∷ xs))
                   (isSetCList* : {xs : CList A} -> isProp (P xs))
                   where
  f : (xs : CList A) -> P xs
  f = elimCListSet.f P []* _∷*_ comm* (isProp→isSet isSetCList*)
    where
      abstract
        comm* : (a b : A) {as bs : CList A} (cs : CList A) (as* : P as)
                (bs* : P bs) (p : as ≡ (b ∷ cs)) (q : bs ≡ (a ∷ cs)) ->
                PathP (λ i -> P (comm a b cs p q i)) (a ∷* as*) (b ∷* bs*)
        comm* a b cs as* bs* p q =
          toPathP (isSetCList* (subst P (comm a b cs p q) (a ∷* as*)) (b ∷* bs*))

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
swap a b = elimCListProp.f _
  (comm a b [] refl refl)
  (λ x {xs} p -> comm a b (x ∷ xs) refl refl)
  (isSetCList _ _)

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
clist-α (M.e , i) = []
clist-α (M.⊕ , i) = i fzero ++ i fone

module Free {x y : Level} {A : Type x} {𝔜 : struct y M.MonSig} (isSet𝔜 : isSet (𝔜 .carrier)) (𝔜-cmon : 𝔜 ⊨ M.CMonSEq) where
  𝔉 : struct x M.MonSig
  𝔉 = < CList A , clist-α >

  module _ (f : A -> 𝔜 .carrier) where
    _♯ : CList A -> 𝔜 .carrier
    ♯-α :
      ∀ a b as bs cs p q ->
      𝔜 .algebra (M.⊕ , lookup (f a L.∷ (as ♯) L.∷ L.[]))
      ≡
      𝔜 .algebra (M.⊕ , lookup (f b L.∷ (bs ♯) L.∷ L.[]))
    [] ♯ = 𝔜 .algebra (M.e , lookup L.[])
    (a ∷ as) ♯ = 𝔜 .algebra (M.⊕ , lookup (f a L.∷ (as ♯) L.∷ L.[]))
    comm a b {as} {bs} cs p q i ♯ = {!   !} -- ♯-α a b as bs cs p q i
    (isSetCList m n p q i j) ♯ = isSet𝔜 (_♯ m) (_♯ n) (cong _♯ p) (cong _♯ q) i j
    
    ♯-α a b as bs cs p q =
      𝔜 .algebra (M.⊕ , lookup (f a L.∷ (as ♯) L.∷ L.[])) ≡⟨ lemma-α ⟩
      -- _ ≡⟨ 𝔜-cmon M.comm (lookup (f a L.∷ (as ♯) L.∷ L.[])) ⟩
      {!    !}
      where
      lemma-α : -- needs to be a lemma to pass termination check??
        𝔜 .algebra (M.⊕ , lookup (f a L.∷ (as ♯) L.∷ L.[]))
        ≡
        𝔜 .algebra (M.⊕ , lookup (f a L.∷ ((b ∷ cs) ♯) L.∷ L.[]))
      lemma-α = cong (λ z -> 𝔜 .algebra (M.⊕ , lookup (f a L.∷ (z ♯) L.∷ L.[]))) p
      lemma-β : -- needs to be a lemma to pass termination check??
        𝔜 .algebra (M.⊕ , lookup (f b L.∷ (bs ♯) L.∷ L.[]))
        ≡
        𝔜 .algebra (M.⊕ , lookup (f b L.∷ ((a ∷ cs) ♯) L.∷ L.[]))
      lemma-β = cong (λ z -> 𝔜 .algebra (M.⊕ , lookup (f b L.∷ (z ♯) L.∷ L.[]))) q


      -- lemma-α : (z : Arity 2) ->
      --   lookup (f a L.∷ (as ♯) L.∷ L.[]) z
      --   ≡
      --   sharp M.MonSig 𝔜 (lookup (f a L.∷ ((b ∷ cs) ♯) L.∷ L.[])) (lookup (leaf fzero L.∷ leaf fone L.∷ L.[]) z)
      -- lemma-α (zero , p) = ?
      -- lemma-α (suc zero , p) = ?
      -- lemma-α (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)


module CListDef = F.Definition M.MonSig M.CMonEqSig M.CMonSEq

freeCMon-sat : ∀ {n} {X : Type n} -> < CList X , clist-α > ⊨ M.CMonSEq
freeCMon-sat M.unitl ρ = ++-unitl (ρ fzero)
freeCMon-sat M.unitr ρ = ++-unitr (ρ fzero)
freeCMon-sat M.assocr ρ = ++-assocr (ρ fzero) (ρ fone) (ρ ftwo)
freeCMon-sat M.comm ρ = ++-comm (ρ fzero) (ρ fone)

clistDef : CListDef.Free 2
F.Definition.Free.F clistDef = CList
F.Definition.Free.η clistDef = [_]
F.Definition.Free.α clistDef = clist-α
F.Definition.Free.sat clistDef = freeCMon-sat
F.Definition.Free.isFree clistDef isSet𝔜 satMon = {!   !}
 