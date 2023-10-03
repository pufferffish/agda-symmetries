{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.Tree where

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
open import Cubical.Structures.Set.Str

-- term algebras

-- module _ {f a n : Level} (σ : Sig f a) where
--   data Tree (X : Type n) : Type (ℓ-max f (ℓ-max a n)) where
--     leaf : X -> Tree X
--     node : (f : σ .symbol) -> (o : σ .arity f -> Tree X) -> Tree X
--     isSetTree : isSet (Tree X)
-- open Tree
-- 
-- module _ {f a : Level} (σ : Sig f a) where
-- 
--    TreeStr : ∀ {x} (X : Type x) -> Str (ℓ-max (ℓ-max f a) x) σ
--    Str.carrier (TreeStr X) = Tree σ X
--    Str.ops (TreeStr X) = node
--    Str.isSetStr (TreeStr X) = isSetTree
-- 
--    module elimTreeSet {x p} {X : Type x} (P : Tree σ X -> Type p)
--                (leaf* : (x : X) -> P (leaf x))
--                (node* : (f : σ .symbol) -> {o : σ .arity f -> Tree σ X} -> ((a : σ .arity f) -> P (o a)) -> P (node f o))
--                (isSetTree* : (x : Tree σ X) -> isSet (P x)) where
--      F : (x : Tree σ X) -> P x
--      F (leaf x) = leaf* x
--      F (node f o) = node* f (λ a -> F (o a))
--      F (isSetTree x y p q i j) = isOfHLevel→isOfHLevelDep 2 isSetTree* (F x) (F y) (cong F p) (cong F q) (isSetTree x y p q) i j
-- 
--    module recTreeSet {x p} {X : Type x} (P : Type p)
--                (leaf* : X -> P)
--                (node* : (f : σ .symbol) -> (σ .arity f -> P) -> P)
--                (isSetTree* : isSet P) where
--      F : (x : Tree σ X) -> P
--      F = elimTreeSet.F (\_ -> P) leaf* (\f o -> node* f o) \_ -> isSetTree*
-- 
--    module elimTreeProp {x p} {X : Type x} (P : Tree σ X -> Type p)
--                (leaf* : (x : X) -> P (leaf x))
--                (node* : (f : σ .symbol) -> {o : σ .arity f -> Tree σ X} -> ((a : σ .arity f) -> P (o a)) -> P (node f o))
--                (isPropTree* : (x : Tree σ X) -> isProp (P x)) where
--      F : (x : Tree σ X) -> P x
--      F = elimTreeSet.F P leaf* node* (isProp→isSet ∘ isPropTree*)
-- 
--    module _ {x y} {X : Type x} {Y : Str y σ} where
--      open Str
--      open StrHom
-- 
--      _♯ : (X -> Y .carrier) -> Tree σ X -> Y .carrier
--      (h ♯) (leaf x) = h x
--      (h ♯) (node f o) = Y .ops f (h ♯ ∘ o)
--      (h ♯) (isSetTree a b p q i j) =
--        Str.isSetStr Y ((h ♯) a) ((h ♯) b) (cong (h ♯) p) (cong (h ♯) q) i j
-- 
--      _♯-hom : (X -> Y .carrier) -> StrHom σ (TreeStr X) Y
--      fun (h ♯-hom) = h ♯
--      fun-prsrv-ops (h ♯-hom) f o = refl
-- 
--      _♯-eta : (g : StrHom σ (TreeStr X) Y) -> (f : Tree σ X) -> g .fun f ≡ ((g .fun ∘ leaf) ♯) f
--      (g ♯-eta) =
--        elimTreeProp.F (\f -> g .fun f ≡ ((g .fun ∘ leaf) ♯) f)
--          (\_ -> refl)
--          (\f {o} p -> g .fun-prsrv-ops f o ∙ cong (Y .ops f) (funExt p))
--          (\f -> Str.isSetStr Y (g .fun f) (((g .fun ∘ leaf) ♯) f))
-- 
--      _♯-hom-eta : (g : StrHom σ (TreeStr X) Y) -> g ≡ (g .fun ∘ leaf) ♯-hom
--      (g ♯-hom-eta) = StrHom≡ g ((g .fun ∘ leaf) ♯-hom) (funExt (g ♯-eta))
-- 
--      treeEquiv : StrHom σ (TreeStr X) Y ≃ (X -> Y .carrier)
--      treeEquiv = isoToEquiv (iso (\g -> g .fun ∘ leaf) _♯-hom (\h -> refl) (\g -> sym (g ♯-hom-eta)))
-- 
--      treeIsEquiv : isEquiv (\g -> g .fun ∘ leaf)
--      treeIsEquiv = treeEquiv .snd

-- alternative but equivalent definition
-- no truncation
module _ {f a n : Level} (σ : Sig f a) where
  data Tr (V : Type n) : Type (ℓ-max (ℓ-max f a) n) where
    leaf : V -> Tr V
    node : sig σ (Tr V) -> Tr V
  open Tr

module _ {f a : Level} (σ : Sig f a) where
  algTr : ∀ {x} (X : Type x) -> struct σ
  carrier (algTr X) = Tr σ X
  algebra (algTr X) = node

module _ {f a n : Level} (σ : Sig f a) where

  module _ {x y} {X : Type x} {𝔜 : struct {f} {a} {y} σ} where
    sharp : (X -> 𝔜 .carrier) -> Tr σ X -> 𝔜 .carrier
    sharp ρ (leaf v) = ρ v
    sharp ρ (node (f , o)) = 𝔜 .algebra (f , sharp ρ ∘ o)

    eval : (X -> 𝔜 .carrier) -> structHom (algTr σ X) 𝔜
    eval h = sharp h , λ _ _ -> refl

    sharp-eta : (g : structHom (algTr σ X) 𝔜) -> (tr : Tr σ X) -> g .fst tr ≡ sharp (g .fst ∘ leaf) tr
    sharp-eta g (leaf x) = refl
    sharp-eta (g-f , g-hom) (node x) =
      g-f (node x) ≡⟨ sym (g-hom (x .fst) (x .snd)) ⟩
      𝔜 .algebra (x .fst , (λ y → g-f (x .snd y))) ≡⟨ cong (λ z → 𝔜 .algebra (x .fst , z)) (funExt λ y -> sharp-eta ((g-f , g-hom)) (x .snd y)) ⟩
      𝔜 .algebra (x .fst , (λ y → sharp (g-f ∘ leaf) (x .snd y)))
      ∎

    -- sharp-hom-eta : isSet (𝔜 .carrier) -> (g : structHom (algTr σ X) 𝔜) -> g ≡ eval (g .fst ∘ leaf)
    -- sharp-hom-eta p g = structHom≡ g (eval (g .fst ∘ leaf)) p (funExt (sharp-eta g))


-- module _ {f a x y : Level} (σ : Sig f a) {X : Type x} {Y : struct {f} {a} {ℓ-max (ℓ-max f a) y} σ}  where
--   sharp-hom : (X -> Y .carrier) ->
--               structHom {f} {a} {ℓ-max (ℓ-max f a) x} {ℓ-max (ℓ-max f a) y} (algTr σ X) Y
--   sharp-hom h = sharp {f} {a} {y} σ Y h , {!   !}

-- module _ {f a n : Level} (σ : Sig f a) {V : Type n} where
--   mu : Tr σ (Tr σ V) -> Tr σ V
--   mu = sharp σ (algTr σ V) (idfun (Tr σ V))
 