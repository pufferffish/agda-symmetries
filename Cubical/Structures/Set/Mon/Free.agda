{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.Mon.Free where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.FinData as Fin using (rec; zero; one; two; ¬Fin0; Fin; suc)
open import Cubical.Data.List
open import Cubical.Data.List.FinData using (lookup)

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.Free as F
open import Cubical.Structures.Set.Sig
open import Cubical.Structures.Set.Str public
open import Cubical.Structures.Set.Tree
open import Cubical.Structures.Set.Eq

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
freeMon-α (M.⊕ , i) = i zero ⊕ i one

freeMon-sat : ∀ {n} {X : Type n} -> < FreeMon X , freeMon-α > ⊨ M.MonSEq
freeMon-sat M.unitl ρ = unitl (ρ zero)
freeMon-sat M.unitr ρ = unitr (ρ zero)
freeMon-sat M.assocr ρ = assocr (ρ zero) (ρ one) (ρ two)

module _ {x y : Level} {A : Type x} (𝔜 : struct y M.MonSig) (isSet𝔜 : isSet (𝔜 .carrier)) (𝔜-monoid : 𝔜 ⊨ M.MonSEq) where
  𝔉 : struct x M.MonSig
  𝔉 = < FreeMon A , freeMon-α >

  module _ (f : A -> 𝔜 .carrier) where
    freeMon-sharp : FreeMon A -> 𝔜 .carrier
    freeMon-sharp-α :
      ∀ m ->
      𝔜 .algebra (M.⊕ , rec (𝔜 .algebra (M.e , (λ ()))) (freeMon-sharp m)) ≡ freeMon-sharp m
    freeMon-sharp-β :
      ∀ m ->
      𝔜 .algebra (M.⊕ , rec (freeMon-sharp m) (𝔜 .algebra (M.e , (λ ())))) ≡ freeMon-sharp m
    freeMon-sharp-γ :
      ∀ m n o ->
      𝔜 .algebra
       (M.⊕ ,
        rec (𝔜 .algebra (M.⊕ , rec (freeMon-sharp m) (freeMon-sharp n)))
        (freeMon-sharp o))
      ≡
      𝔜 .algebra
       (M.⊕ ,
        rec (freeMon-sharp m)
        (𝔜 .algebra (M.⊕ , rec (freeMon-sharp n) (freeMon-sharp o))))

    freeMon-sharp (η a) = f a
    freeMon-sharp e = 𝔜 .algebra (M.e , λ ())
    freeMon-sharp (m ⊕ n) = 𝔜 .algebra (M.⊕ , rec (freeMon-sharp m) (freeMon-sharp n))
    freeMon-sharp (unitl m i) = freeMon-sharp-α m i
    freeMon-sharp (unitr m i) = freeMon-sharp-β m i
    freeMon-sharp (assocr m n o i) = freeMon-sharp-γ m n o i
    freeMon-sharp (trunc m n p q i j) =
      isSet𝔜 (freeMon-sharp m) (freeMon-sharp n) (cong freeMon-sharp p) (cong freeMon-sharp q) i j

    freeMon-sharp-α m =
      let
        lemma =
          Fin.elim (λ z -> rec (𝔜 .algebra (M.e , (λ ()))) (freeMon-sharp m) z ≡ sharp M.MonSig 𝔜 (λ _ → freeMon-sharp m) (rec (node (M.e , (λ ()))) (leaf (zero {0})) z))
            (cong (λ p -> 𝔜 .algebra (M.e , p)) (funExt λ ()))
            λ _  -> refl
      in
        𝔜 .algebra (M.⊕ , rec (𝔜 .algebra (M.e , (λ ()))) (freeMon-sharp m)) ≡⟨ cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt lemma) ⟩
        𝔜 .algebra (M.⊕ , (λ x₁ -> sharp M.MonSig 𝔜 (λ _ → freeMon-sharp m) (rec (node (M.e , (λ ()))) (leaf zero) x₁))) ≡⟨ 𝔜-monoid M.unitl (λ _ -> freeMon-sharp m) ⟩
        freeMon-sharp m
        ∎
    freeMon-sharp-β m =
      let
        lemma =
          Fin.elim (λ z -> rec (freeMon-sharp m) (𝔜 .algebra (M.e , (λ ()))) z ≡ sharp M.MonSig 𝔜 (λ _ → freeMon-sharp m) (rec (leaf (zero {0})) (node (M.e , (λ ()))) z))
            refl
            λ _ -> (cong (λ p -> 𝔜 .algebra (M.e , p)) (funExt λ ()))
      in
        𝔜 .algebra (M.⊕ , rec (freeMon-sharp m) (𝔜 .algebra (M.e , (λ ())))) ≡⟨ cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt lemma) ⟩
        𝔜 .algebra (M.⊕ , (λ x₁ → sharp M.MonSig 𝔜 (λ _ → freeMon-sharp m) (rec (leaf zero) (node (M.e , (λ ()))) x₁))) ≡⟨ 𝔜-monoid M.unitr (λ _ -> freeMon-sharp m) ⟩
        freeMon-sharp m
        ∎
    freeMon-sharp-γ m n o =
      let
        p =
          Fin.elim (λ z -> rec (freeMon-sharp m) (freeMon-sharp n) z ≡ sharp M.MonSig 𝔜 (lookup (freeMon-sharp m ∷ freeMon-sharp n ∷ [ freeMon-sharp o ])) (rec (leaf zero) (leaf one) z))
            refl
            λ _ -> refl
        q =
          Fin.elim (λ z -> rec (𝔜 .algebra (M.⊕ , rec (freeMon-sharp m) (freeMon-sharp n))) (freeMon-sharp o) z ≡ sharp M.MonSig 𝔜 (lookup (freeMon-sharp m ∷ freeMon-sharp n ∷ [ freeMon-sharp o ])) (rec (node (M.⊕ , rec (leaf zero) (leaf one))) (leaf two) z))
            (cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt p))
            λ _ -> refl
        r =
          Fin.elim (λ z -> sharp M.MonSig 𝔜 (lookup (freeMon-sharp m ∷ freeMon-sharp n ∷ [ freeMon-sharp o ])) (rec (leaf one) (leaf two) z) ≡ rec (freeMon-sharp n) (freeMon-sharp o) z)
            refl
            λ _ -> refl 
        s =
          Fin.elim (λ z -> sharp M.MonSig 𝔜 (lookup (freeMon-sharp m ∷ freeMon-sharp n ∷ [ freeMon-sharp o ])) (rec (leaf zero) (node (M.⊕ , rec (leaf one) (leaf two))) z) ≡ rec (freeMon-sharp m) (𝔜 .algebra (M.⊕ , rec (freeMon-sharp n) (freeMon-sharp o))) z)
            refl
            λ _ -> cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt r)
      in
        𝔜 .algebra (M.⊕ , rec (𝔜 .algebra (M.⊕ , rec (freeMon-sharp m) (freeMon-sharp n))) (freeMon-sharp o)) ≡⟨ cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt q) ⟩
        _ ≡⟨ 𝔜-monoid M.assocr (lookup (freeMon-sharp m ∷ freeMon-sharp n ∷ [ freeMon-sharp o ])) ⟩
        _ ≡⟨ cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt s) ⟩
        _ 
        ∎

    freeMon-sharp-isMonHom : structHom 𝔉 𝔜
    freeMon-sharp-isMonHom = freeMon-sharp , lemma-β
      where
      lemma-β : structIsHom 𝔉 𝔜 freeMon-sharp
      lemma-β M.e i = cong (λ z -> 𝔜 .algebra (M.e , z)) (funExt λ ())
      lemma-β M.⊕ i =
        cong (λ z -> 𝔜 .algebra (M.⊕ , z)) (funExt {!   !})

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

freeMonDef : FreeMonDef.Free 2
F.Definition.Free.F freeMonDef = FreeMon
F.Definition.Free.η freeMonDef = η
F.Definition.Free.α freeMonDef = freeMon-α
F.Definition.Free.sat freeMonDef = freeMon-sat
F.Definition.Free.isFree freeMonDef {𝔜 = 𝔜} isSet𝔜 satMon = (freeMonEquiv 𝔜 isSet𝔜 satMon) .snd
