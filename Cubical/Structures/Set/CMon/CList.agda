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
import Cubical.Structures.Set.CMon.Free as FCM
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
                   (isSetCList* : (xs : CList A) -> isSet (P xs))
                   where
  f : (xs : CList A) -> P xs
  f [] = []*
  f (a ∷ as) = a ∷* f as
  f (comm a b {as} {bs} cs p q i) =
    comm* a b (f cs) (cong f p) (cong f q) i
  f (isSetCList xs ys p q i j) =
    isOfHLevel→isOfHLevelDep 2 isSetCList* (f xs) (f ys) (cong f p) (cong f q) (isSetCList xs ys p q) i j

module elimCListProp {ℓ p : Level} {A : Type ℓ} (P : CList A -> Type p)
                   ([]* : P [])
                   (_∷*_ : (x : A) {xs : CList A} -> P xs -> P (x ∷ xs))
                   (isSetCList* : (xs : CList A) -> isProp (P xs))
                   where
  f : (xs : CList A) -> P xs
  f = elimCListSet.f P []* _∷*_
    (λ a b {as} {bs} {cs} {as*} {bs*} cs* bp bq ->
      toPathP (isSetCList* _ _ (b ∷* bs*))
    )
    (isProp→isSet ∘ isSetCList*)

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
++-unitr = elimCListProp.f _ refl (λ a p -> cong (a ∷_) p) (λ _ -> isSetCList _ _)

++-assocr : (as bs cs : CList A) -> (as ++ bs) ++ cs ≡ as ++ (bs ++ cs)
++-assocr = elimCListProp.f _
  (λ _ _ -> refl)
  (λ x p bs cs -> cong (x ∷_) (p bs cs))
  (λ _ -> isPropΠ λ _ -> isPropΠ λ _ -> isSetCList _ _)

swap : (a b : A) (cs : CList A) -> a ∷ b ∷ cs ≡ b ∷ a ∷ cs
swap a b cs = comm a b cs refl refl

++-∷ : (a : A) (as : CList A) -> a ∷ as ≡ as ++ [ a ]
++-∷ a = elimCListProp.f (λ as -> a ∷ as ≡ as ++ [ a ])
  refl
  (λ b {as} p -> swap a b as ∙ cong (b ∷_) p)
  (λ _ -> isSetCList _ _) 

++-comm : (as bs : CList A) -> as ++ bs ≡ bs ++ as
++-comm = elimCListProp.f _
  (sym ∘ ++-unitr)
  (λ a {as} p bs -> cong (a ∷_) (p bs) ∙ cong (_++ as) (++-∷ a bs) ∙ ++-assocr bs [ a ] as)
  (λ _ -> isPropΠ λ _ -> isSetCList _ _)

clist-α : ∀ {n : Level} {X : Type n} -> sig M.MonSig (CList X) -> CList X
clist-α (M.e , i) = []
clist-α (M.⊕ , i) = i fzero ++ i fone

module Free {x y : Level} {A : Type x} {𝔜 : struct y M.MonSig} (isSet𝔜 : isSet (𝔜 .carrier)) (𝔜-cmon : 𝔜 ⊨ M.CMonSEq) where
  module Free = FCM.Free {A = A} isSet𝔜 𝔜-cmon

  𝔛 : struct x M.MonSig
  𝔛 = < CList A , clist-α >

  𝔉 : struct x M.MonSig
  𝔉 = Free.𝔉

  module _ (f : A -> 𝔜 .carrier) where
    toFree : CList A -> 𝔉 .carrier
    toFree = elimCListSet.f _
      FCM.e
      (λ x {xs} p -> FCM.η x FCM.⊕ p)
      (λ a b {as} {bs} {cs} {as*} {bs*} cs* bp bq ->
        FCM.η a FCM.⊕ as* ≡⟨ cong (FCM.η a FCM.⊕_) bp ⟩
        FCM.η a FCM.⊕ (FCM.η b FCM.⊕ cs*) ≡⟨ sym (FCM.assocr _ _ _) ⟩
        (FCM.η a FCM.⊕ FCM.η b) FCM.⊕ cs* ≡⟨ cong (FCM._⊕ cs*) (FCM.comm _ _) ⟩
        (FCM.η b FCM.⊕ FCM.η a) FCM.⊕ cs* ≡⟨ FCM.assocr _ _ _ ⟩
        FCM.η b FCM.⊕ (FCM.η a FCM.⊕ cs*) ≡⟨ cong (FCM.η b FCM.⊕_) (sym bq) ⟩
        FCM.η b FCM.⊕ bs* ∎
      )
      (λ _ -> FCM.trunc)

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
