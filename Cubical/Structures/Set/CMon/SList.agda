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
  𝔉 : struct x M.MonSig
  𝔉 = < SList A , slist-α >

  module _ (f : A -> 𝔜 .carrier) where
    _♯ : SList A -> 𝔜 .carrier
    ♯-α :
      ∀ a b cs ->
      𝔜 .algebra (M.⊕ , lookup (f a L.∷ 𝔜 .algebra (M.⊕ , lookup (f b L.∷ (cs ♯) L.∷ L.[])) L.∷ L.[]))
      ≡
      𝔜 .algebra (M.⊕ , lookup (f b L.∷ 𝔜 .algebra (M.⊕ , lookup (f a L.∷ (cs ♯) L.∷ L.[])) L.∷ L.[]))
    ♯-asscor :
      ∀ a b cs z ->
        lookup (a L.∷ 𝔜 .algebra (M.⊕ , lookup (b L.∷ cs L.∷ L.[])) L.∷ L.[]) z
        ≡
        sharp M.MonSig 𝔜 (lookup (a L.∷ b L.∷ cs L.∷ L.[])) (lookup (leaf fzero L.∷ node (M.⊕ , lookup (leaf fone L.∷ leaf ftwo L.∷ L.[])) L.∷ L.[]) z)
    ♯-comm :
      ∀ a b cs z ->
        lookup (𝔜 .algebra (M.⊕ , lookup (a L.∷ b L.∷ L.[])) L.∷ cs L.∷ L.[]) z
        ≡
        sharp M.MonSig 𝔜 (lookup (a L.∷ b L.∷ cs L.∷ L.[])) (lookup (node (M.⊕ , lookup (leaf fzero L.∷ leaf fone L.∷ L.[])) L.∷ leaf ftwo L.∷ L.[]) z)

    [] ♯ = 𝔜 .algebra (M.e , lookup L.[])
    (a ∷ as) ♯ = 𝔜 .algebra (M.⊕ , lookup (f a L.∷ (as ♯) L.∷ L.[]))
    swap a b cs i ♯ = ♯-α a b cs i
    (isSetSList m n p q i j) ♯ = isSet𝔜 (_♯ m) (_♯ n) (cong _♯ p) (cong _♯ q) i j

    ♯-asscor a b cs = lemma-α
      where
      lemma-α : (z : Arity 2) ->
        lookup (a L.∷ 𝔜 .algebra (M.⊕ , lookup (b L.∷ cs L.∷ L.[])) L.∷ L.[]) z
        ≡
        sharp M.MonSig 𝔜 (lookup (a L.∷ b L.∷ cs L.∷ L.[])) (lookup (leaf fzero L.∷ node (M.⊕ , lookup (leaf fone L.∷ leaf ftwo L.∷ L.[])) L.∷ L.[]) z)
      lemma-β : (z : Arity 2) ->
        lookup (b L.∷ cs L.∷ L.[]) z
        ≡
        sharp M.MonSig 𝔜 (lookup (a L.∷ b L.∷ cs L.∷ L.[])) (lookup (leaf fone L.∷ leaf ftwo L.∷ L.[]) z)
      lemma-α (zero , p) = refl
      lemma-α (suc zero , p) = cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt lemma-β)
      lemma-α (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)
      lemma-β (zero , p) = refl
      lemma-β (suc zero , p) = refl
      lemma-β (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

    ♯-comm a b cs = lemma-γ
      where
      lemma-γ : (z : Arity 2) ->
        lookup (𝔜 .algebra (M.⊕ , lookup (a L.∷ b L.∷ L.[])) L.∷ cs L.∷ L.[]) z
        ≡
        sharp M.MonSig 𝔜 (lookup (a L.∷ b L.∷ cs L.∷ L.[])) (lookup (node (M.⊕ , lookup (leaf fzero L.∷ leaf fone L.∷ L.[])) L.∷ leaf ftwo L.∷ L.[]) z)
      lemma-δ : (z : Arity 2) ->
        lookup (a L.∷ b L.∷ L.[]) z
        ≡
        sharp M.MonSig 𝔜 (lookup (a L.∷ b L.∷ cs L.∷ L.[])) (lookup (leaf fzero L.∷ leaf fone L.∷ L.[]) z)
      lemma-γ (zero , p) = cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt lemma-δ)
      lemma-γ (suc zero , p) = refl
      lemma-γ (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)
      lemma-δ (zero , p) = refl
      lemma-δ (suc zero , p) = refl
      lemma-δ (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

    ♯-α a b cs =
      _ ≡⟨ cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt (♯-asscor (f a) (f b) (cs ♯))) ⟩
      _ ≡⟨ sym (𝔜-cmon M.assocr (lookup (f a L.∷ f b L.∷ (cs ♯) L.∷ L.[]))) ⟩ -- sym assocr, a + (b + c) = (a + b) + c
      _ ≡⟨ cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (sym (funExt (♯-comm (f a) (f b) (cs ♯)))) ⟩
      _ ≡⟨ cong (λ z -> 𝔜 .algebra (M.⊕ , lookup (z L.∷ (cs ♯) L.∷ L.[]) )) lemma-comm ⟩ -- comm (a + b) + c = (b + a) + c
      _ ≡⟨ cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt (♯-comm (f b) (f a) (cs ♯))) ⟩
      _ ≡⟨ 𝔜-cmon M.assocr (lookup (f b L.∷ f a L.∷ (cs ♯) L.∷ L.[])) ⟩ -- assocr, (b + a) + c = b + (a + c)
      _ ≡⟨ cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (sym (funExt (♯-asscor (f b) (f a) (cs ♯)))) ⟩
      _ ∎
      where
      lemma-comm :
        𝔜 .algebra (M.⊕ , lookup (f a L.∷ f b L.∷ L.[]))
        ≡
        𝔜 .algebra (M.⊕ , lookup (f b L.∷ f a L.∷ L.[]))
      lemma-comm-α : (z : Arity 2) ->
        lookup (f a L.∷ f b L.∷ L.[]) z
        ≡
        sharp M.MonSig 𝔜 (lookup (f a L.∷ f b L.∷ L.[])) (lookup (leaf fzero L.∷ leaf fone L.∷ L.[]) z)
      lemma-comm-β : (z : Arity 2) ->
        sharp M.MonSig 𝔜 (lookup (f a L.∷ f b L.∷ L.[])) (lookup (leaf fone L.∷ leaf fzero L.∷ L.[]) z)
        ≡
        lookup (f b L.∷ f a L.∷ L.[]) z
      lemma-comm-α (zero , p) = refl
      lemma-comm-α (suc zero , p) = refl
      lemma-comm-α (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)
      lemma-comm-β (zero , p) = refl
      lemma-comm-β (suc zero , p) = refl
      lemma-comm-β (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

      lemma-comm =
        _ ≡⟨ cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt lemma-comm-α) ⟩
        _ ≡⟨ 𝔜-cmon M.comm (lookup (f a L.∷ f b L.∷ L.[])) ⟩
        _ ≡⟨ cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt lemma-comm-β) ⟩
        _ ∎


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
 
 