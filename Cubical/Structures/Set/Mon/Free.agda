{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.Mon.Free where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
import Cubical.Data.Empty as ⊥

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.Free as F
open import Cubical.Structures.Set.Sig
open import Cubical.Structures.Set.Str public
open import Cubical.Structures.Set.Tree
open import Cubical.Structures.Set.Eq
open import Cubical.Structures.Arity

data FreeMon {ℓ : Level} (A : Type ℓ) : Type ℓ where
  η : (a : A) -> FreeMon A
  e : FreeMon A
  _⊕_ : FreeMon A -> FreeMon A -> FreeMon A
  unitl : ∀ m -> e ⊕ m ≡ m
  unitr : ∀ m -> m ⊕ e ≡ m
  assocr : ∀ m n o -> (m ⊕ n) ⊕ o ≡ m ⊕ (n ⊕ o)
  trunc : isSet (FreeMon A)

module elimFreeMonSet {p n : Level} {A : Type n} (P : FreeMon A -> Type p)
                    (η* : (a : A) -> P (η a))
                    (e* : P e)
                    (_⊕*_ : {m n : FreeMon A} -> P m -> P n -> P (m ⊕ n))
                    (unitl* : {m : FreeMon A} (m* : P m) -> PathP (λ i → P (unitl m i)) (e* ⊕* m*) m*)
                    (unitr* : {m : FreeMon A} (m* : P m) -> PathP (λ i → P (unitr m i)) (m* ⊕* e*) m*)
                    (assocr* : {m n o : FreeMon A}
                               (m* : P m) ->
                               (n* : P n) ->
                               (o* : P o) -> PathP (λ i → P (assocr m n o i)) ((m* ⊕* n*) ⊕* o*) (m* ⊕* (n* ⊕* o*)))
                    (trunc* : {xs : FreeMon A} -> isSet (P xs))
                    where
  f : (x : FreeMon A) -> P x
  f (η a) = η* a
  f e = e*
  f (x ⊕ y) = f x ⊕* f y
  f (unitl x i) = unitl* (f x) i
  f (unitr x i) = unitr* (f x) i
  f (assocr x y z i) = assocr* (f x) (f y) (f z) i
  f (trunc xs ys p q i j) =
     isOfHLevel→isOfHLevelDep 2 (\xs -> trunc* {xs = xs}) (f xs) (f ys) (cong f p) (cong f q) (trunc xs ys p q) i j

module recFreeMonSet {p n : Level} {A : Type n} (P : Type p)
                    (η* : (a : A) -> P)
                    (e* : P)
                    (_⊕*_ : P -> P -> P)
                    (unitl* : (m* : P) -> PathP (λ i → P) (e* ⊕* m*) m*)
                    (unitr* : (m* : P) -> PathP (λ i → P) (m* ⊕* e*) m*)
                    (assocr* : (m* : P) ->
                               (n* : P) ->
                               (o* : P) -> PathP (λ i → P) ((m* ⊕* n*) ⊕* o*) (m* ⊕* (n* ⊕* o*)))
                    (trunc* : isSet P)
                    where
  f : (x : FreeMon A) -> P
  f = elimFreeMonSet.f (\_ -> P) η* e* _⊕*_ unitl* unitr* assocr* trunc*

module elimFreeMonProp {p n : Level} {A : Type n} (P : FreeMon A -> Type p)
                    (η* : (a : A) -> P (η a))
                    (e* : P e)
                    (_⊕*_ : {m n : FreeMon A} -> P m -> P n -> P (m ⊕ n))
                    (trunc* : {xs : FreeMon A} -> isProp (P xs))
                    where
  f : (x : FreeMon A) -> P x
  f = elimFreeMonSet.f P η* e* _⊕*_ unitl* unitr* assocr* (isProp→isSet trunc*)
    where
      abstract
        unitl* : {m : FreeMon A} (m* : P m) -> PathP (λ i → P (unitl m i)) (e* ⊕* m*) m*
        unitl* {m} m* = toPathP (trunc* (transp (λ i -> P (unitl m i)) i0 (e* ⊕* m*)) m*)
        unitr* : {m : FreeMon A} (m* : P m) -> PathP (λ i → P (unitr m i)) (m* ⊕* e*) m*
        unitr* {m} m* = toPathP (trunc* (transp (λ i -> P (unitr m i)) i0 (m* ⊕* e*)) m*)
        assocr* : {m n o : FreeMon A}
                  (m* : P m) ->
                  (n* : P n) ->
                  (o* : P o) -> PathP (λ i → P (assocr m n o i)) ((m* ⊕* n*) ⊕* o*) (m* ⊕* (n* ⊕* o*))
        assocr* {m} {n} {o} m* n* o* =
          toPathP (trunc* (transp (λ i -> P (assocr m n o i)) i0 ((m* ⊕* n*) ⊕* o*)) (m* ⊕* (n* ⊕* o*)))

freeMon-α : ∀ {n : Level} {X : Type n} -> sig M.MonSig (FreeMon X) -> FreeMon X
freeMon-α (M.e , i) = e
freeMon-α (M.⊕ , i) = i fzero ⊕ i fone

module _ {x y : Level} {A : Type x} {𝔜 : struct y M.MonSig} (isSet𝔜 : isSet (𝔜 .carrier)) (𝔜-monoid : 𝔜 ⊨ M.MonSEq) where
  𝔉 : struct x M.MonSig
  𝔉 = < FreeMon A , freeMon-α >

  module _ (f : A -> 𝔜 .carrier) where
    freeMon-sharp : FreeMon A -> 𝔜 .carrier
    freeMon-sharp-α :
      ∀ m ->
      𝔜 .algebra (M.⊕ , lookup (𝔜 .algebra (M.e , fabsurd) ∷ freeMon-sharp m ∷ []))
      ≡
      freeMon-sharp m
    freeMon-sharp-β :
      ∀ m ->
      𝔜 .algebra (M.⊕ , lookup (freeMon-sharp m ∷ 𝔜 .algebra (M.e , fabsurd) ∷ []))
      ≡
      freeMon-sharp m

    freeMon-sharp (η a) = f a
    freeMon-sharp e = 𝔜 .algebra (M.e , fabsurd)
    freeMon-sharp (m ⊕ n) = 𝔜 .algebra (M.⊕ , lookup (freeMon-sharp m ∷ freeMon-sharp n ∷ []))
    freeMon-sharp (unitl m i) = freeMon-sharp-α m i
    freeMon-sharp (unitr m i) = freeMon-sharp-β m i
    freeMon-sharp (assocr m n o i) = {!   !}
    freeMon-sharp (trunc m n p q i j) =
      isSet𝔜 (freeMon-sharp m) (freeMon-sharp n) (cong freeMon-sharp p) (cong freeMon-sharp q) i j

    freeMon-sharp-α m =
      𝔜 .algebra (M.⊕ , lookup (𝔜 .algebra (M.e , fabsurd) ∷ freeMon-sharp m ∷ [])) ≡⟨ cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt lemma) ⟩
      𝔜 .algebra (M.⊕ , λ z -> sharp M.MonSig 𝔜 (λ _ → freeMon-sharp m) (lookup (node (M.e , fabsurd) ∷ leaf fzero ∷ []) z)) ≡⟨ 𝔜-monoid M.unitl (λ _ -> freeMon-sharp m) ⟩
      freeMon-sharp m ∎
      where
      lemma : (z : Arity 2) ->
        lookup (𝔜 .algebra (M.e , fabsurd) ∷ freeMon-sharp m ∷ []) z
        ≡
        sharp M.MonSig 𝔜 (λ _ → freeMon-sharp m) (lookup (node (M.e , fabsurd) ∷ leaf fzero ∷ []) z)
      lemma (zero , p) = cong (λ q → 𝔜 .algebra (M.e , q)) (funExt λ z -> fabsurd z)
      lemma (suc zero , p) = refl
      lemma (suc (suc _), p) = ⊥.rec (¬m+n<m {m = 2} p)
    freeMon-sharp-β m =
      𝔜 .algebra (M.⊕ , lookup (freeMon-sharp m ∷ 𝔜 .algebra (M.e , fabsurd) ∷ [])) ≡⟨ cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt lemma) ⟩
      𝔜 .algebra (M.⊕ , λ z -> sharp M.MonSig 𝔜 (λ _ → freeMon-sharp m) (lookup (leaf fzero ∷ node (M.e , fabsurd) ∷ []) z)) ≡⟨ 𝔜-monoid M.unitr (λ _ -> freeMon-sharp m) ⟩
      freeMon-sharp m ∎
      where
      lemma : (z : Arity 2) ->
        lookup (freeMon-sharp m ∷ 𝔜 .algebra (M.e , fabsurd) ∷ []) z
        ≡
        sharp M.MonSig 𝔜 (λ _ → freeMon-sharp m) (lookup (leaf fzero ∷ node (M.e , fabsurd) ∷ []) z)
      lemma (zero , p) = refl
      lemma (suc zero , p) = cong (λ q → 𝔜 .algebra (M.e , q)) (funExt λ z -> fabsurd z)
      lemma (suc (suc _), p) = ⊥.rec (¬m+n<m {m = 2} p)

    freeMon-sharp-isMonHom : structHom 𝔉 𝔜
    freeMon-sharp-isMonHom = freeMon-sharp , {!   !}

  private
    freeMonEquivLemma : (g : structHom 𝔉 𝔜) -> (x : FreeMon A) -> g .fst x ≡ freeMon-sharp (g .fst ∘ η) x
    freeMonEquivLemma (g , homMonWit) = elimFreeMonProp.f (λ x -> g x ≡ freeMon-sharp (g ∘ η) x)
      (λ _ -> refl)
      {!   !}
      {!   !}
      (isSet𝔜 _ _)

    freeMonEquivLemma-β : (g : structHom 𝔉 𝔜) -> g ≡ freeMon-sharp-isMonHom (g .fst ∘ η)
    freeMonEquivLemma-β g = structHom≡ 𝔉 𝔜 g (freeMon-sharp-isMonHom (g .fst ∘ η)) isSet𝔜 (funExt (freeMonEquivLemma g))

  freeMonEquiv : structHom 𝔉 𝔜 ≃ (A -> 𝔜 .carrier)
  freeMonEquiv =
    isoToEquiv (iso (λ g -> g .fst ∘ η) freeMon-sharp-isMonHom (λ _ -> refl) (sym ∘ freeMonEquivLemma-β))
      
module FreeMonDef = F.Definition M.MonSig M.MonEqSig M.MonSEq

freeMon-sat : ∀ {n} {X : Type n} -> < FreeMon X , freeMon-α > ⊨ M.MonSEq
freeMon-sat M.unitl ρ = unitl (ρ fzero)
freeMon-sat M.unitr ρ = unitr (ρ fzero)
freeMon-sat M.assocr ρ = assocr (ρ fzero) (ρ fone) (ρ ftwo)

freeMonDef : FreeMonDef.Free 2
F.Definition.Free.F freeMonDef = FreeMon
F.Definition.Free.η freeMonDef = η
F.Definition.Free.α freeMonDef = freeMon-α
F.Definition.Free.sat freeMonDef = freeMon-sat
F.Definition.Free.isFree freeMonDef isSet𝔜 satMon = (freeMonEquiv isSet𝔜 satMon) .snd
