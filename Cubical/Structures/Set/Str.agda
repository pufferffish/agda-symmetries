{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.Str where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Image
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Data.Nat
open import Cubical.Data.FinData as F
open import Cubical.Data.List as L
open import Cubical.Data.List.FinData as F
open import Cubical.Data.Sigma
open import Cubical.Reflection.RecordEquiv
open import Cubical.HITs.SetQuotients as Q
open import Agda.Primitive

open import Cubical.Structures.Set.Sig

-- record Str {f a : Level} (x : Level) (σ : Sig f a) : Type (ℓ-max (ℓ-max f a) (ℓ-suc x)) where
--   field
--     carrier : Type x
--     ops : (f : σ .symbol) -> (o : σ .arity f -> carrier) -> carrier
--     -- TODO: drop this and prove lemmas about homotopy type of Tree
--     isSetStr : isSet carrier
-- open Str public
-- 
-- record StrHom {f a : Level} {x y : Level} (σ : Sig f a) (X : Str x σ) (Y : Str y σ) : Type (ℓ-max (ℓ-max f a) (ℓ-max (ℓ-suc x) (ℓ-suc y))) where
--   field
--     fun : X .carrier -> Y .carrier
--     fun-prsrv-ops : (f : σ .symbol) -> (op : σ .arity f -> X .carrier) -> fun (X .ops f op) ≡ Y .ops f (fun ∘ op)
-- 
-- unquoteDecl StrHomIsoΣ = declareRecordIsoΣ StrHomIsoΣ (quote StrHom)
-- 
-- StrHom≡ : {f a : Level} {x y : Level} {σ : Sig f a} {X : Str x σ} {Y : Str y σ} (g h : StrHom σ X Y) -> StrHom.fun g ≡ StrHom.fun h -> g ≡ h
-- StrHom≡ {X = X} {Y = Y} g h p =
--   let g' = Iso.fun StrHomIsoΣ g ; h' = Iso.fun StrHomIsoΣ h
--       q : g' ≡ h'
--       q = Σ≡Prop (\fun -> isPropΠ \f -> isPropΠ (\o -> Y .isSetStr (fun (X .ops f o)) (Y .ops f (fun ∘ o)))) p
--   in cong (Iso.inv StrHomIsoΣ) q

-- alternative definition as algebras of signature functor
-- TODO: prove lemmas about its homotopy type
record struct {f a n : Level} (σ : Sig f a) : Type (ℓ-max f (ℓ-max a (ℓ-suc n))) where
  constructor mkStruct
  field
    carrier : Type n
    algebra : sig σ carrier -> carrier
open struct public

module _  {f a x y : Level} {σ : Sig f a} (𝔛 : struct {f} {a} {x} σ) (𝔜 : struct {f} {a} {y} σ)  where
  structIsHom : (h : 𝔛 .carrier -> 𝔜 .carrier) -> Type (ℓ-max f (ℓ-max a (ℓ-max x y)))
  structIsHom h =
    ((f : σ .symbol) -> (i : σ .arity f -> 𝔛 .carrier) -> 𝔜 .algebra (f , h ∘ i) ≡ h (𝔛 .algebra (f , i)))

  structHom : Type (ℓ-max f (ℓ-max a (ℓ-max x y)))
  structHom = Σ[ h ∈ (𝔛 .carrier -> 𝔜 .carrier) ] structIsHom h

  structHom≡ : (g h : structHom) -> isSet (𝔜 .carrier) -> g .fst ≡ h .fst -> g ≡ h
  structHom≡ (g-f , g-hom) (h-f , h-hom) isSetY p =
    Σ≡Prop (\fun -> isPropΠ \f -> isPropΠ \o -> isSetY (𝔜 .algebra (f , (λ x → fun (o x)))) (fun (𝔛 .algebra (f , o)))) p
