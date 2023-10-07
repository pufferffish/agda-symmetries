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

module elimFreeMonSet {p : Level} {A : Type} (P : FreeMon A -> Type p)
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

module elimFreeMonProp {p : Level} {A : Type} (P : FreeMon A -> Type p)
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

module FreeMonDef = F.Definition M.MonSig M.MonEqSig M.MonSEq

freeMonDef : FreeMonDef.Free 2
F.Definition.Free.F freeMonDef = FreeMon
F.Definition.Free.η freeMonDef = η
F.Definition.Free.α freeMonDef = freeMon-α
F.Definition.Free.sat freeMonDef = freeMon-sat
F.Definition.Free.isFree freeMonDef isSet𝔜 satMon = {!   !}

module _ {ns x y : Level} {A : Type x} (𝔜 : struct y M.MonSig) (isSet𝔜 : isSet (𝔜 .carrier)) (𝔜-monoid : 𝔜 ⊨ M.MonSEq) where
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
        lol = 𝔜-monoid M.assocr (lookup (freeMon-sharp m ∷ freeMon-sharp n ∷ [ freeMon-sharp o ])) 
      in
        𝔜 .algebra (M.⊕ , rec (𝔜 .algebra (M.⊕ , rec (freeMon-sharp m) (freeMon-sharp n))) (freeMon-sharp o)) ≡⟨⟩
        {!   !}


-- TODO: the same for list

-- module _ {A B : Type} (M : M.MonStruct B) where
--   module B = M.MonStruct M
--   module _ (f : A -> B) where

--     _♯ : FreeMon A -> B
--     (_♯) (η a) = f a
--     (_♯) e = B.e
--     (_♯) (m ⊕ n) = (_♯) m B.⊕ (_♯) n
--     (_♯) (unitl m i) = B.unitl ((_♯) m) i
--     (_♯) (unitr m i) = B.unitr ((_♯) m) i
--     (_♯) (assocr m n o i) = B.assocr ((_♯) m) ((_♯) n) ((_♯) o) i
--     (_♯) (trunc m n p q i j) = B.trunc ((_♯) m) ((_♯) n) (cong (_♯) p) (cong (_♯) q) i j

--     _♯-isMonHom : M.isMonHom (freeMon A) M _♯
--     M.isMonHom.f-e _♯-isMonHom = refl
--     M.isMonHom.f-⊕ _♯-isMonHom m n = refl

--   private
--     freeMonEquivLemma : (f : FreeMon A -> B) -> M.isMonHom (freeMon A) M f -> (x : FreeMon A) -> f x ≡ ((f ∘ η) ♯) x
--     freeMonEquivLemma f homMonWit = elimFreeMonProp.f _
--       (λ _ -> refl)
--       (M.isMonHom.f-e homMonWit)
--       (λ {m} {n} p q ->
--         f (m ⊕ n) ≡⟨ M.isMonHom.f-⊕ homMonWit m n ⟩
--         f m B.⊕ f n ≡⟨ cong (B._⊕ f n) p ⟩
--         ((f ∘ η) ♯) m B.⊕ f n ≡⟨ cong (((f ∘ η) ♯) m B.⊕_) q ⟩
--         ((f ∘ η) ♯) m B.⊕ ((f ∘ η) ♯) n
--         ∎
--       )
--       (B.trunc _ _)

--     freeMonEquivLemma-β : (f : FreeMon A -> B) -> M.isMonHom (freeMon A) M f -> ((f ∘ η) ♯) ≡ f
--     freeMonEquivLemma-β f homMonWit i x = freeMonEquivLemma f homMonWit x (~ i)

--   freeMonEquiv : M.MonHom (freeMon A) M ≃ (A -> B)
--   freeMonEquiv = isoToEquiv
--     ( iso
--       (λ (f , ϕ) -> f ∘ η)
--       (λ f -> (f ♯) , (f ♯-isMonHom))
--       (λ _ -> refl)
--       (λ (f , homMonWit) -> Σ≡Prop M.isMonHom-isProp (freeMonEquivLemma-β f homMonWit))
--     )

--   freeMonIsEquiv : isEquiv {A = M.MonHom (freeMon A) M} (\(f , ϕ) -> f ∘ η)
--   freeMonIsEquiv = freeMonEquiv .snd
       