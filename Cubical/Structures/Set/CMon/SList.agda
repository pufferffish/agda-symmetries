{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.CMon.SList where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
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
  𝔛 : struct x M.MonSig
  𝔛 = < SList A , slist-α >

  𝔉 : struct x M.MonSig
  𝔉 = FCM.Free.𝔉 {A = A} isSet𝔜 𝔜-cmon

  module _ (f : A -> 𝔜 .carrier) where
    toFree : SList A -> 𝔉 .carrier
    toFree [] = FCM.e
    toFree (a ∷ as) = FCM.η a FCM.⊕ toFree as
    toFree (swap a b cs i) =
      let
        p =
          FCM.η a FCM.⊕ (FCM.η b FCM.⊕ toFree cs) ≡⟨ sym (FCM.assocr (FCM.η a) (FCM.η b) (toFree cs))  ⟩
          (FCM.η a FCM.⊕ FCM.η b) FCM.⊕ toFree cs ≡⟨ cong (FCM._⊕ toFree cs) (FCM.comm (FCM.η a) (FCM.η b)) ⟩
          (FCM.η b FCM.⊕ FCM.η a) FCM.⊕ toFree cs ≡⟨ FCM.assocr (FCM.η b) (FCM.η a) (toFree cs) ⟩
          FCM.η b FCM.⊕ (FCM.η a FCM.⊕ toFree cs) ∎
      in
        p i
    toFree (isSetSList x y p q i j) =
      FCM.trunc (toFree x) (toFree y) (cong toFree p) (cong toFree q) i j

    toFree-isMonHom : structHom 𝔛 𝔉
    toFree-isMonHom = toFree , lemma-α
      where
      lemma-α : structIsHom 𝔛 𝔉 toFree
      lemma-α M.e i = refl
      lemma-α M.⊕ i with i fzero | i fone
      ... | []     | []     = FCM.unitl _
      ... | []     | a ∷ as = FCM.unitl _
      ... | a ∷ as | []     =
        (FCM.η a FCM.⊕ toFree as) FCM.⊕ FCM.e ≡⟨ FCM.unitr _ ⟩
        FCM.η a FCM.⊕ toFree as ≡⟨ cong (λ z -> FCM.η a FCM.⊕ toFree z) (sym (++-unitr as)) ⟩
        FCM.η a FCM.⊕ toFree (as ++ []) ∎
      ... | a ∷ as | b ∷ bs = {!   !}
      ... | [] | swap a b ys i₁ = {!   !}
      ... | [] | isSetSList ys ys₁ x y i₁ i₂ = {!   !}
      ... | swap a b xs i₁ | ys = {!   !}
      ... | isSetSList xs xs₁ x y i₁ i₂ | ys = {!   !}
      ... | a ∷ xs | swap a₁ b ys i₁ = {!   !}
      ... | a ∷ xs | isSetSList ys ys₁ x y i₁ i₂ = {!   !}




    _♯ : SList A -> 𝔜 .carrier    
    xs ♯ = FCM.Free._♯ isSet𝔜 𝔜-cmon f (toFree xs)

    -- ♯-isMonHom = _♯ , lemma-α
    --   where
    --   lemma-α : structIsHom 𝔉 𝔜 _♯
    --   lemma-β : (i : Arity 2 -> SList A)
    --     -> (z : Arity 2)
    --     -> (i z ♯) ≡ lookup ((i fzero ♯) L.∷ (i fone ♯) L.∷ L.[]) z

    --   lemma-α M.e i = cong (λ z -> 𝔜 .algebra (M.e , z)) (funExt λ p -> lookup L.[] p)
    --   lemma-α M.⊕ i with 𝔉 .algebra (M.⊕ , i)
    --   ... | [] =
    --     𝔜 .algebra (M.⊕ , (λ z -> (i z) ♯)) ≡⟨ cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt (lemma-β i)) ⟩
    --     𝔜 .algebra (M.⊕ , lookup ((i fzero) ♯ L.∷ (i fone) ♯ L.∷ L.[])) ≡⟨⟩
    --     {!   !}
    --   ... | a ∷ as =
    --     cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt {!   !})
    --   ... | swap a b lol i₁ = {!  !}
    --   ... | isSetSList lol lol₁ x y i₁ i₂ = {!   !}

    --   lemma-β i (zero , p) = cong (λ z -> i z ♯) (Σ≡Prop (λ _ -> isProp≤) refl)
    --   lemma-β i (suc zero , p) = cong (λ z -> i z ♯) (Σ≡Prop (λ _ -> isProp≤) refl)
    --   lemma-β i (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

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
F.Definition.Free.isFree slistDef isSet𝔜 satMon = {!   !}
 
    