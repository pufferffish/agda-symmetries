{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.Mon.Free where

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
freeMon-α (M.`e , i) = e
freeMon-α (M.`⊕ , i) = i fzero ⊕ i fone

module Free {x y : Level} {A : Type x} {𝔜 : struct y M.MonSig} (isSet𝔜 : isSet (𝔜 .carrier)) (𝔜-monoid : 𝔜 ⊨ M.MonSEq) where
  module M' = M.MonSEq 𝔜 𝔜-monoid

  𝔉 : struct x M.MonSig
  𝔉 = < FreeMon A , freeMon-α >

  module _ (f : A -> 𝔜 .carrier) where
    _♯ : FreeMon A -> 𝔜 .carrier
    _♯ (η a) = f a
    _♯ e = M'.e
    _♯ (m ⊕ n) = (m ♯) M'.⊕ (n ♯)
    _♯ (unitl m i) = M'.unitl (m ♯) i
    _♯ (unitr m i) = M'.unitr (m ♯) i
    _♯ (assocr m n o i) = M'.assocr (m ♯) (n ♯) (o ♯) i
    _♯ (trunc m n p q i j) = isSet𝔜 (_♯ m) (_♯ n) (cong _♯ p) (cong _♯ q) i j

    ♯-isMonHom : structHom 𝔉 𝔜
    fst ♯-isMonHom = _♯
    snd ♯-isMonHom M.`e i = M'.e-eta
    snd ♯-isMonHom M.`⊕ i = M'.⊕-eta i _♯

  private
    freeMonEquivLemma : (g : structHom 𝔉 𝔜) -> (x : FreeMon A) -> g .fst x ≡ ((g .fst ∘ η) ♯) x
    freeMonEquivLemma (g , homMonWit) = elimFreeMonProp.f (λ x -> g x ≡ ((g ∘ η) ♯) x)
      (λ _ -> refl)
      (sym (homMonWit M.`e (lookup [])) ∙ M'.e-eta)
      (λ {m} {n} p q ->
        g (m ⊕ n) ≡⟨ sym (homMonWit M.`⊕ (lookup (m ∷ n ∷ []))) ⟩
        𝔜 .algebra (M.`⊕ , (λ w -> g (lookup (m ∷ n ∷ []) w))) ≡⟨ M'.⊕-eta (lookup (m ∷ n ∷ [])) g ⟩
        g m M'.⊕ g n ≡⟨ cong₂ M'._⊕_ p q ⟩
        _ ∎
      )
      (isSet𝔜 _ _)

    freeMonEquivLemma-β : (g : structHom 𝔉 𝔜) -> g ≡ ♯-isMonHom (g .fst ∘ η)
    freeMonEquivLemma-β g = structHom≡ 𝔉 𝔜 g (♯-isMonHom (g .fst ∘ η)) isSet𝔜 (funExt (freeMonEquivLemma g))

  freeMonEquiv : structHom 𝔉 𝔜 ≃ (A -> 𝔜 .carrier)
  freeMonEquiv =
    isoToEquiv (iso (λ g -> g .fst ∘ η) ♯-isMonHom (λ _ -> refl) (sym ∘ freeMonEquivLemma-β))
      
module FreeMonDef = F.Definition M.MonSig M.MonEqSig M.MonSEq

freeMon-sat : ∀ {n} {X : Type n} -> < FreeMon X , freeMon-α > ⊨ M.MonSEq
freeMon-sat M.`unitl ρ = unitl (ρ fzero)
freeMon-sat M.`unitr ρ = unitr (ρ fzero)
freeMon-sat M.`assocr ρ = assocr (ρ fzero) (ρ fone) (ρ ftwo)

freeMonDef : FreeMonDef.Free 2
F.Definition.Free.F freeMonDef = FreeMon
F.Definition.Free.η freeMonDef = η
F.Definition.Free.α freeMonDef = freeMon-α
F.Definition.Free.sat freeMonDef = freeMon-sat
F.Definition.Free.isFree freeMonDef isSet𝔜 satMon = (Free.freeMonEquiv isSet𝔜 satMon) .snd
 