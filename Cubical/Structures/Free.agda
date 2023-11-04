{-# OPTIONS --cubical #-}

module Cubical.Structures.Free where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Image
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Data.Nat
open import Cubical.Data.List as L
open import Cubical.Data.Sigma
open import Cubical.Reflection.RecordEquiv
open import Cubical.HITs.SetQuotients as Q
open import Agda.Primitive

open import Cubical.Structures.Sig
open import Cubical.Structures.Str
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq

-- defines a free structure on a signature and equations
module Definition {f a e n s : Level} (σ : Sig f a) (τ : EqSig e (ℓ-max n s)) (ε : seq {n = ℓ-max n s} σ τ) where
  ns : Level
  ns = ℓ-max n s

  record Free (ℓ ℓ' : Level) (h : HLevel) : Type (ℓ-suc (ℓ-max ℓ' (ℓ-max ℓ (ℓ-max f (ℓ-max a (ℓ-max e ns)))))) where
    field
      F : (X : Type ℓ) -> Type (ℓ-max ℓ ns)
      η : {X : Type ℓ} -> X -> F X
      α : {X : Type ℓ} -> sig σ (F X) -> F X
      sat : {X : Type ℓ} -> < F X , α > ⊨ ε
      isFree : {X : Type ℓ}
        {𝔜 : struct (ℓ-max ℓ' ns) σ}
        (H : isOfHLevel h (𝔜 .car)) (ϕ : 𝔜 ⊨ ε)
        -> isEquiv (\(f : structHom {x = ℓ-max ℓ ns} < F X , α > 𝔜) -> f .fst ∘ η)

    ext : {X : Type ℓ} {𝔜 : struct (ℓ-max ℓ' ns) σ}
          (H : isOfHLevel h (𝔜 .car)) (ϕ : 𝔜 ⊨ ε)
       -> (hom : X -> 𝔜 .car) -> structHom < F X , α > 𝔜
    ext h ϕ = invIsEq (isFree h ϕ)

    ext-β : {X : Type ℓ} {𝔜 : struct (ℓ-max ℓ' ns) σ}
            (H : isOfHLevel h (𝔜 .car)) (ϕ : 𝔜 ⊨ ε) (Hom : structHom < F X , α > 𝔜)
         -> ext H ϕ (Hom .fst ∘ η) ≡ Hom
    ext-β h ϕ Hom = retIsEq (isFree h ϕ) Hom

    ext-η : {X : Type ℓ} {𝔜 : struct (ℓ-max ℓ' ns) σ}
            (H : isOfHLevel h (𝔜 .car)) (ϕ : 𝔜 ⊨ ε) (h : X -> 𝔜 .car)
         -> (ext H ϕ h .fst) ∘ η ≡ h
    ext-η H ϕ h = secIsEq (isFree H ϕ) h

    hom≡ : {X : Type ℓ} {𝔜 : struct (ℓ-max ℓ' ns) σ}
        -> (H : isOfHLevel h (𝔜 .car)) (ϕ : 𝔜 ⊨ ε)
        -> (H1 H2 : structHom < F X , α > 𝔜)
        -> H1 .fst ∘ η ≡ H2 .fst ∘ η
        -> H1 ≡ H2
    hom≡ H ϕ H1 H2 α = sym (ext-β H ϕ H1) ∙ cong (ext H ϕ) α ∙ ext-β H ϕ H2

  -- Alternative definition where F is paramterized, used for transporting Free proofs
  record FreeAux (ℓ ℓ' : Level) (h : HLevel) (F : (X : Type ℓ) -> Type (ℓ-max ℓ ns)) : Type (ℓ-suc (ℓ-max ℓ' (ℓ-max ℓ (ℓ-max f (ℓ-max a (ℓ-max e ns)))))) where
    field
      η : {X : Type ℓ} -> X -> F X
      α : {X : Type ℓ} -> sig σ (F X) -> F X
      sat : {X : Type ℓ} -> < F X , α > ⊨ ε
      isFree : {X : Type ℓ}
        {𝔜 : struct (ℓ-max ℓ' ns) σ}
        (H : isOfHLevel h (𝔜 .car)) (ϕ : 𝔜 ⊨ ε)
        -> isEquiv (\(f : structHom {x = ℓ-max ℓ ns} < F X , α > 𝔜) -> f .fst ∘ η)

  isoAux : {ℓ ℓ' : Level} {h : HLevel} ->
           Iso (Σ[ F ∈ ((X : Type ℓ) -> Type (ℓ-max ℓ ns)) ] FreeAux ℓ ℓ' h F) (Free ℓ ℓ' h)
  isoAux {ℓ = ℓ} {ℓ' = ℓ'} {h = h} = iso to from (λ _ -> refl) (λ _ -> refl)
    where
    to : Σ[ F ∈ ((X : Type ℓ) -> Type (ℓ-max ℓ ns)) ] FreeAux ℓ ℓ' h F -> Free ℓ ℓ' h
    Free.F (to (F , aux)) = F
    Free.η (to (F , aux)) = FreeAux.η aux
    Free.α (to (F , aux)) = FreeAux.α aux
    Free.sat (to (F , aux)) = FreeAux.sat aux
    Free.isFree (to (F , aux)) = FreeAux.isFree aux

    from : Free ℓ ℓ' h -> Σ[ F ∈ ((X : Type ℓ) -> Type (ℓ-max ℓ ns)) ] FreeAux ℓ ℓ' h F
    fst (from free) = Free.F free
    FreeAux.η (snd (from free)) = Free.η free
    FreeAux.α (snd (from free)) = Free.α free
    FreeAux.sat (snd (from free)) = Free.sat free
    FreeAux.isFree (snd (from free)) = Free.isFree free


-- -- constructions of a free structure on a signature and equations
-- -- TODO: generalise the universe levels!!
-- -- using a HIT
-- module Construction {f a e n : Level} (σ : Sig f a) (τ : EqSig e n) (ε : seq σ τ) where
-- 
--   data Free (X : Type n) : Type (ℓ-suc (ℓ-max f (ℓ-max a (ℓ-max e n)))) where
--       η : X -> Free X
--       α : sig σ (Free X) -> Free X
--       sat : mkStruct (Free X) α ⊨ ε

--  freeStruct : (X : Type) -> struct σ
--  car (freeStruct X) = Free X
--  alg (freeStruct _) = α
--
--  module _ (X : Type) (𝔜 : struct σ) (ϕ : 𝔜 ⊨ ε) where

    -- private
    --   Y = 𝔜 .fst
    --   β = 𝔜 .snd

    -- ext : (h : X -> Y) -> Free X -> Y
    -- ext h (η x) = h x
    -- ext h (α (f , o)) = β (f , (ext h ∘ o))
    -- ext h (sat e ρ i) = ϕ e (ext h ∘ ρ) {!i!}

    -- module _  where
    --   postulate
    --     Fr : Type (ℓ-max (ℓ-max f a) n)
    --     Fα : sig σ Fr -> Fr
    --     Fs : sat σ τ ε (Fr , Fα)

    --   module _ (Y : Type (ℓ-max (ℓ-max f a) n)) (α : sig σ Y -> Y) where
    --     postulate
    --       Frec : sat σ τ ε (Y , α) -> Fr -> Y
    --       Fhom : (p : sat σ τ ε (Y , α)) -> walgIsH σ (Fr , Fα) (Y , α) (Frec p)
    --       Feta : (p : sat σ τ ε (Y , α)) (h : Fr -> Y) -> walgIsH σ (Fr , Fα) (Y , α) h -> Frec p ≡ h
    
-- -- using a quotient
-- module Construction2 (σ : Sig ℓ-zero ℓ-zero) (τ : EqSig ℓ-zero ℓ-zero) (ε : seq σ τ) where
-- 
--   -- congruence relation generated by equations
--   data _≈_ {X : Type} : Tree σ X -> Tree σ X -> Type (ℓ-suc ℓ-zero) where
--     ≈-refl : ∀ t -> t ≈ t
--     ≈-sym : ∀ t s -> t ≈ s -> s ≈ t
--     ≈-trans : ∀ t s r -> t ≈ s -> s ≈ r -> t ≈ r
--     ≈-cong : (f : σ .symbol) -> {t s : σ .arity f -> Tree σ X}
--           -> ((a : σ .arity f) -> t a ≈ s a)
--           -> node (f , t) ≈ node (f , s)
--     ≈-eqs : (𝔜 : struct {ℓ-zero} {ℓ-zero} {ℓ-zero} σ) (ϕ : 𝔜 ⊨ ε)
--          -> (e : τ .name) (ρ : X -> 𝔜 .car)
--          -> ∀ t s -> sharp σ {𝔜 = 𝔜} ρ t ≡ sharp σ {𝔜 = 𝔜} ρ s
--          -> t ≈ s
-- 
--   Free : Type -> Type₁
--   Free X = Tree σ X / _≈_
-- 
--   -- freeAlg : (X : Type) -> sig σ (Free X) -> Free X
--   -- freeAlg X (f , i) = Q.[ node (f , {!!}) ] -- needs choice?
-- 
--   -- freeStruct : (X : Type) -> struct σ
--   -- freeStruct X = Free X , freeAlg X
-- 
--   -- module _ (X : Type) (𝔜 : struct σ) (ϕ : 𝔜 ⊨ ε) where
-- 
--   --   private
--   --     Y = 𝔜 .fst
--   --     β = 𝔜 .snd
