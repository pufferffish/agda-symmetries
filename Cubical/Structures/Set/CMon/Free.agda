{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.CMon.Free where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
import Cubical.Data.Empty as ⊥

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.Mon.Free as FM
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity

data FreeCMon {ℓ : Level} (A : Type ℓ) : Type ℓ where
  η : (a : A) -> FreeCMon A
  e : FreeCMon A
  _⊕_ : FreeCMon A -> FreeCMon A -> FreeCMon A
  unitl : ∀ m -> e ⊕ m ≡ m
  unitr : ∀ m -> m ⊕ e ≡ m
  assocr : ∀ m n o -> (m ⊕ n) ⊕ o ≡ m ⊕ (n ⊕ o)
  comm : ∀ m n -> m ⊕ n ≡ n ⊕ m
  trunc : isSet (FreeCMon A)

module elimFreeCMonSet {p n : Level} {A : Type n} (P : FreeCMon A -> Type p)
                    (η* : (a : A) -> P (η a))
                    (e* : P e)
                    (_⊕*_ : {m n : FreeCMon A} -> P m -> P n -> P (m ⊕ n))
                    (unitl* : {m : FreeCMon A} (m* : P m) -> PathP (λ i → P (unitl m i)) (e* ⊕* m*) m*)
                    (unitr* : {m : FreeCMon A} (m* : P m) -> PathP (λ i → P (unitr m i)) (m* ⊕* e*) m*)
                    (assocr* : {m n o : FreeCMon A}
                               (m* : P m) ->
                               (n* : P n) ->
                               (o* : P o) ->
                               PathP (λ i → P (assocr m n o i)) ((m* ⊕* n*) ⊕* o*) (m* ⊕* (n* ⊕* o*)))
                    (comm* : {m n : FreeCMon A}
                               (m* : P m) ->
                               (n* : P n) ->  
                               PathP (λ i → P (comm m n i)) (m* ⊕* n*) (n* ⊕* m*))
                    (trunc* : {xs : FreeCMon A} -> isSet (P xs))
                    where
  f : (x : FreeCMon A) -> P x
  f (η a) = η* a
  f e = e*
  f (x ⊕ y) = f x ⊕* f y
  f (unitl x i) = unitl* (f x) i
  f (unitr x i) = unitr* (f x) i
  f (assocr x y z i) = assocr* (f x) (f y) (f z) i
  f (comm x y i) = comm* (f x) (f y) i
  f (trunc xs ys p q i j) =
     isOfHLevel→isOfHLevelDep 2 (\xs -> trunc* {xs = xs}) (f xs) (f ys) (cong f p) (cong f q) (trunc xs ys p q) i j

module elimFreeCMonProp {p n : Level} {A : Type n} (P : FreeCMon A -> Type p)
                    (η* : (a : A) -> P (η a))
                    (e* : P e)
                    (_⊕*_ : {m n : FreeCMon A} -> P m -> P n -> P (m ⊕ n))
                    (trunc* : {xs : FreeCMon A} -> isProp (P xs))
                    where
  f : (x : FreeCMon A) -> P x
  f = elimFreeCMonSet.f P η* e* _⊕*_ unitl* unitr* assocr* comm* (isProp→isSet trunc*)
    where
      abstract
        unitl* : {m : FreeCMon A} (m* : P m) -> PathP (λ i → P (unitl m i)) (e* ⊕* m*) m*
        unitl* {m} m* = toPathP (trunc* (transp (λ i -> P (unitl m i)) i0 (e* ⊕* m*)) m*)
        unitr* : {m : FreeCMon A} (m* : P m) -> PathP (λ i → P (unitr m i)) (m* ⊕* e*) m*
        unitr* {m} m* = toPathP (trunc* (transp (λ i -> P (unitr m i)) i0 (m* ⊕* e*)) m*)
        assocr* : {m n o : FreeCMon A}
                  (m* : P m) ->
                  (n* : P n) ->
                  (o* : P o) -> PathP (λ i → P (assocr m n o i)) ((m* ⊕* n*) ⊕* o*) (m* ⊕* (n* ⊕* o*))
        assocr* {m} {n} {o} m* n* o* =
          toPathP (trunc* (transp (λ i -> P (assocr m n o i)) i0 ((m* ⊕* n*) ⊕* o*)) (m* ⊕* (n* ⊕* o*)))
        comm* : {m n : FreeCMon A} (m* : P m) (n* : P n) -> PathP (λ i → P (comm m n i)) (m* ⊕* n*) (n* ⊕* m*)
        comm* {m} {n} m* n* = toPathP (trunc* (transp (λ i -> P (comm m n i)) i0 (m* ⊕* n*)) (n* ⊕* m*))

freeCMon-α : ∀ {ℓ} {X : Type ℓ} -> sig M.MonSig (FreeCMon X) -> FreeCMon X
freeCMon-α (M.`e , _) = e
freeCMon-α (M.`⊕ , i) = i fzero ⊕ i fone

module Free {x y : Level} {A : Type x} {𝔜 : struct y M.MonSig} (isSet𝔜 : isSet (𝔜 .car)) (𝔜-cmon : 𝔜 ⊨ M.CMonSEq) where
  module 𝔜 = M.CMonSEq 𝔜 𝔜-cmon

  𝔉 : struct x M.MonSig
  𝔉 = < FreeCMon A , freeCMon-α >

  module _ (f : A -> 𝔜 .car) where
    _♯ : FreeCMon A -> 𝔜 .car
    _♯ (η a) = f a
    _♯ e = 𝔜.e
    _♯ (m ⊕ n) = (m ♯) 𝔜.⊕ (n ♯)
    _♯ (unitl m i) = 𝔜.unitl (m ♯) i
    _♯ (unitr m i) = 𝔜.unitr (m ♯) i
    _♯ (assocr m n o i) = 𝔜.assocr (m ♯) (n ♯) (o ♯) i
    comm m n i ♯ = 𝔜.comm (m ♯) (n ♯) i
    (trunc m n p q i j) ♯ = isSet𝔜 (m ♯) (n ♯) (cong _♯ p) (cong _♯ q) i j

    ♯-isMonHom : structHom 𝔉 𝔜
    fst ♯-isMonHom = _♯
    snd ♯-isMonHom M.`e i = 𝔜.e-eta
    snd ♯-isMonHom M.`⊕ i = 𝔜.⊕-eta i _♯

  private
    freeCMonEquivLemma : (g : structHom 𝔉 𝔜) -> (x : FreeCMon A) -> g .fst x ≡ ((g .fst ∘ η) ♯) x
    freeCMonEquivLemma (g , homMonWit) = elimFreeCMonProp.f (λ x -> g x ≡ ((g ∘ η) ♯) x)
      (λ _ -> refl)
      (sym (homMonWit M.`e (lookup [])) ∙ 𝔜.e-eta)
      (λ {m} {n} p q ->
        g (m ⊕ n) ≡⟨ sym (homMonWit M.`⊕ (lookup (m ∷ n ∷ []))) ⟩
        𝔜 .alg (M.`⊕ , (λ w -> g (lookup (m ∷ n ∷ []) w))) ≡⟨ 𝔜.⊕-eta (lookup (m ∷ n ∷ [])) g ⟩
        g m 𝔜.⊕ g n ≡⟨ cong₂ 𝔜._⊕_ p q ⟩
        _ ∎
      )
      (isSet𝔜 _ _)

    freeCMonEquivLemma-β : (g : structHom 𝔉 𝔜) -> g ≡ ♯-isMonHom (g .fst ∘ η)
    freeCMonEquivLemma-β g = structHom≡ 𝔉 𝔜 g (♯-isMonHom (g .fst ∘ η)) isSet𝔜 (funExt (freeCMonEquivLemma g))

  freeCMonEquiv : structHom 𝔉 𝔜 ≃ (A -> 𝔜 .car)
  freeCMonEquiv =
    isoToEquiv (iso (λ g -> g .fst ∘ η) ♯-isMonHom (λ _ -> refl) (sym ∘ freeCMonEquivLemma-β))

module FreeCMonDef = F.Definition M.MonSig M.CMonEqSig M.CMonSEq

freeCMon-sat : ∀ {n} {X : Type n} -> < FreeCMon X , freeCMon-α > ⊨ M.CMonSEq
freeCMon-sat (M.`mon M.`unitl) ρ = unitl (ρ fzero)
freeCMon-sat (M.`mon M.`unitr) ρ = unitr (ρ fzero)
freeCMon-sat (M.`mon M.`assocr) ρ = assocr (ρ fzero) (ρ fone) (ρ ftwo)
freeCMon-sat M.`comm ρ = comm (ρ fzero) (ρ fone)

freeMonDef : ∀ {ℓ ℓ'} -> FreeCMonDef.Free ℓ ℓ' 2
F.Definition.Free.F freeMonDef = FreeCMon
F.Definition.Free.η freeMonDef = η
F.Definition.Free.α freeMonDef = freeCMon-α
F.Definition.Free.sat freeMonDef = freeCMon-sat
F.Definition.Free.isFree freeMonDef isSet𝔜 satMon = (Free.freeCMonEquiv isSet𝔜 satMon) .snd
