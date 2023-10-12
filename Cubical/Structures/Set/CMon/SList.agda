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
import Cubical.Structures.Set.Mon.Free as FM
import Cubical.Structures.Set.CMon.Free as FCM
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
        comm* a b {cs} cs* =
          toPathP (isSetSList* (subst P (swap a b cs) (a ∷* (b ∷* cs*))) (b ∷* (a ∷* cs*)))

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
slist-α (M.e , i) = []
slist-α (M.⊕ , i) = i fzero ++ i fone

module Free {x y : Level} {A : Type x} {𝔜 : struct y M.MonSig} (isSet𝔜 : isSet (𝔜 .carrier)) (𝔜-cmon : 𝔜 ⊨ M.CMonSEq) where
  module Free = FCM.Free {A = A} isSet𝔜 𝔜-cmon

  𝔛 : struct x M.MonSig
  𝔛 = < SList A , slist-α >

  𝔉 : struct x M.MonSig
  𝔉 = Free.𝔉

  module _ (f : A -> 𝔜 .carrier) where
    toFree : SList A -> 𝔉 .carrier
    toFree [] = FCM.e
    toFree (a ∷ as) = FCM.η a FCM.⊕ toFree as
    toFree (swap a b cs i) =
      ( sym (FCM.assocr (FCM.η a) (FCM.η b) (toFree cs))
      ∙ cong (FCM._⊕ toFree cs) (FCM.comm (FCM.η a) (FCM.η b))
      ∙ FCM.assocr (FCM.η b) (FCM.η a) (toFree cs)
      ) i
    toFree (isSetSList x y p q i j) =
      FCM.trunc (toFree x) (toFree y) (cong toFree p) (cong toFree q) i j

    toFree-++ : ∀ xs ys -> toFree (xs ++ ys) ≡ toFree xs FCM.⊕ toFree ys
    toFree-++ = elimSListProp.f _
      (λ ys -> sym (FCM.unitl (toFree ys)))
      (λ x {xs} p ys ->
        FCM.η x FCM.⊕ toFree (xs ++ ys) ≡⟨ cong (FCM.η x FCM.⊕_) (p ys) ⟩
        FCM.η x FCM.⊕ (toFree xs FCM.⊕ toFree ys) ≡⟨ sym (FCM.assocr _ _ _) ⟩
        _ ∎)
      (isPropΠ λ _ -> FCM.trunc _ _)

    toFree-isMonHom : structHom 𝔛 𝔉
    toFree-isMonHom = toFree , lemma-α
      where
      lemma-α : structIsHom 𝔛 𝔉 toFree
      lemma-α M.e i = refl
      lemma-α M.⊕ i = sym (toFree-++ (i fzero) (i fone))

    _♯ : SList A -> 𝔜 .carrier    
    _♯ = Free._♯ f ∘ toFree

    ♯-isMonHom : structHom 𝔛 𝔜
    ♯-isMonHom = structHom∘ 𝔛 𝔉 𝔜 (Free.♯-isMonHom f) toFree-isMonHom

  private
    slistEquivLemma : (g : structHom 𝔛 𝔜) -> (x : SList A) -> g .fst x ≡ ((g .fst ∘ [_]) ♯) x
    slistEquivLemma (g , homMonWit) = elimSListProp.f _
      ( sym (homMonWit M.e (lookup L.[]))
      ∙ cong (λ p -> 𝔜 .algebra (M.e , p)) (funExt λ p -> lookup L.[] p)
      )
      (λ x {xs} p ->
        g (x ∷ xs) ≡⟨ sym (homMonWit M.⊕ (lookup ([ x ] L.∷ xs L.∷ L.[]))) ⟩
        _ ≡⟨ cong (λ p -> 𝔜 .algebra (M.⊕ , p)) (funExt (lemma-α x xs p)) ⟩
        _ ∎
      )
      (isSet𝔜 _ _)
      where
      lemma-α : (x : A) (xs : SList A)
        -> (g xs ≡ ((g ∘ [_]) ♯) xs)
        -> (z : Arity 2)
        -> g (lookup ([ x ] L.∷ xs L.∷ L.[]) z)
           ≡
           lookup ((g ∘ [_]) x L.∷ (Free._♯ (g ∘ [_])) (toFree (g ∘ [_]) xs) L.∷ L.[]) z
      lemma-α x xs p (zero , q) = refl
      lemma-α x xs p (suc zero , q) = p
      lemma-α x xs p (suc (suc n) , q) = ⊥.rec (¬m+n<m {m = 2} q)

    slistEquivLemma-β : (g : structHom 𝔛 𝔜) -> g ≡ ♯-isMonHom (g .fst ∘ [_])
    slistEquivLemma-β g = structHom≡ 𝔛 𝔜 g (♯-isMonHom (g .fst ∘ [_])) isSet𝔜 (funExt (slistEquivLemma g))
  
  slistMonEquiv : structHom 𝔛 𝔜 ≃ (A -> 𝔜 .carrier)
  slistMonEquiv =
    isoToEquiv
      ( iso
        (λ g -> g .fst ∘ [_])
        ♯-isMonHom
        (λ g -> funExt (λ x ->
          _ ≡⟨ cong (λ z -> 𝔜 .algebra (M.⊕ , lookup (g x L.∷ 𝔜 .algebra (M.e , z) L.∷ L.[]))) (funExt λ z -> lookup L.[] z) ⟩
          _ ≡⟨ cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt (lemma-β g x)) ⟩
          _ ≡⟨ 𝔜-cmon M.unitr (λ _ -> g x)  ⟩
          _ ∎
        ))
        (sym ∘ slistEquivLemma-β)
      )
    where
    lemma-β : (g : (a : A) -> 𝔜 .carrier) (x : A) (z : Arity 2) ->
      lookup (g x L.∷ 𝔜 .algebra (M.e , (λ num → ⊥.rec (¬Fin0 num))) L.∷ L.[]) z
      ≡
      sharp M.MonSig 𝔜 (λ _ → g x) (lookup (leaf fzero L.∷ node (M.e , (λ num → ⊥.rec (¬Fin0 num))) L.∷ L.[]) z)
    lemma-β g x (zero , p) = refl
    lemma-β g x (suc zero , p) = cong (λ z → 𝔜 .algebra (M.e , z)) (funExt λ z -> lookup L.[] z)
    lemma-β g x (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)  

module SListDef = F.Definition M.MonSig M.CMonEqSig M.CMonSEq

freeCMon-sat : ∀ {n} {X : Type n} -> < SList X , slist-α > ⊨ M.CMonSEq
freeCMon-sat M.unitl ρ = ++-unitl (ρ fzero)
freeCMon-sat M.unitr ρ = ++-unitr (ρ fzero)
freeCMon-sat M.assocr ρ = ++-assocr (ρ fzero) (ρ fone) (ρ ftwo)
freeCMon-sat M.comm ρ = ++-comm (ρ fzero) (ρ fone)

slistDef : SListDef.Free 2
F.Definition.Free.F slistDef = SList
F.Definition.Free.η slistDef = [_]
F.Definition.Free.α slistDef = slist-α
F.Definition.Free.sat slistDef = freeCMon-sat
F.Definition.Free.isFree slistDef isSet𝔜 satMon = (Free.slistMonEquiv isSet𝔜 satMon) .snd
 