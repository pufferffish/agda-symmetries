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

module _ {f a n : Level} (σ : Sig f a) where
  data Tree (X : Type n) : Type (ℓ-max f (ℓ-max a n)) where
    leaf : X -> Tree X
    node : (f : σ .symbol) -> (o : σ .arity f -> Tree X) -> Tree X
    isSetTree : isSet (Tree X)
open Tree

module _ {f a : Level} (σ : Sig f a) where

   TreeStr : ∀ {x} (X : Type x) -> Str (ℓ-max (ℓ-max f a) x) σ
   Str.carrier (TreeStr X) = Tree σ X
   Str.ops (TreeStr X) = node
   Str.isSetStr (TreeStr X) = isSetTree

   module elimTreeSet {x p} {X : Type x} (P : Tree σ X -> Type p)
               (leaf* : (x : X) -> P (leaf x))
               (node* : (f : σ .symbol) -> {o : σ .arity f -> Tree σ X} -> ((a : σ .arity f) -> P (o a)) -> P (node f o))
               (isSetTree* : (x : Tree σ X) -> isSet (P x)) where
     F : (x : Tree σ X) -> P x
     F (leaf x) = leaf* x
     F (node f o) = node* f (λ a -> F (o a))
     F (isSetTree x y p q i j) = isOfHLevel→isOfHLevelDep 2 isSetTree* (F x) (F y) (cong F p) (cong F q) (isSetTree x y p q) i j

   module recTreeSet {x p} {X : Type x} (P : Type p)
               (leaf* : X -> P)
               (node* : (f : σ .symbol) -> (σ .arity f -> P) -> P)
               (isSetTree* : isSet P) where
     F : (x : Tree σ X) -> P
     F = elimTreeSet.F (\_ -> P) leaf* (\f o -> node* f o) \_ -> isSetTree*

   module elimTreeProp {x p} {X : Type x} (P : Tree σ X -> Type p)
               (leaf* : (x : X) -> P (leaf x))
               (node* : (f : σ .symbol) -> {o : σ .arity f -> Tree σ X} -> ((a : σ .arity f) -> P (o a)) -> P (node f o))
               (isPropTree* : (x : Tree σ X) -> isProp (P x)) where
     F : (x : Tree σ X) -> P x
     F = elimTreeSet.F P leaf* node* (isProp→isSet ∘ isPropTree*)

   module _ {x y} {X : Type x} {Y : Str y σ} where
     open Str
     open StrHom

     _♯ : (X -> Y .carrier) -> Tree σ X -> Y .carrier
     (h ♯) (leaf x) = h x
     (h ♯) (node f o) = Y .ops f (h ♯ ∘ o)
     (h ♯) (isSetTree a b p q i j) =
       Str.isSetStr Y ((h ♯) a) ((h ♯) b) (cong (h ♯) p) (cong (h ♯) q) i j

     _♯-hom : (X -> Y .carrier) -> StrHom σ (TreeStr X) Y
     fun (h ♯-hom) = h ♯
     fun-prsrv-ops (h ♯-hom) f o = refl

     _♯-eta : (g : StrHom σ (TreeStr X) Y) -> (f : Tree σ X) -> g .fun f ≡ ((g .fun ∘ leaf) ♯) f
     (g ♯-eta) =
       elimTreeProp.F (\f -> g .fun f ≡ ((g .fun ∘ leaf) ♯) f)
         (\_ -> refl)
         (\f {o} p -> g .fun-prsrv-ops f o ∙ cong (Y .ops f) (funExt p))
         (\f -> Str.isSetStr Y (g .fun f) (((g .fun ∘ leaf) ♯) f))

     _♯-hom-eta : (g : StrHom σ (TreeStr X) Y) -> g ≡ (g .fun ∘ leaf) ♯-hom
     (g ♯-hom-eta) = StrHom≡ g ((g .fun ∘ leaf) ♯-hom) (funExt (g ♯-eta))

     treeEquiv : StrHom σ (TreeStr X) Y ≃ (X -> Y .carrier)
     treeEquiv = isoToEquiv (iso (\g -> g .fun ∘ leaf) _♯-hom (\h -> refl) (\g -> sym (g ♯-hom-eta)))

     treeIsEquiv : isEquiv (\g -> g .fun ∘ leaf)
     treeIsEquiv = treeEquiv .snd

-- alternative but equivalent definition
-- no truncation
module _ {f a n : Level} (σ : Sig f a) where
  data Tr (V : Type n) : Type (ℓ-max (ℓ-max f a) n) where
    leaf : V -> Tr V
    node : sig σ (Tr V) -> Tr V

  algTr : (V : Type n) -> struct σ
  algTr V = Tr V , node

module _ {f a n : Level} (σ : Sig f a) {V : Type n} where
  open Tr {f} {a} {n} σ

  module _ ((X , α) : struct {f} {a} {ℓ-max (ℓ-max f a) n} σ) (ρ : V -> X) where
    sharp : Tr σ V -> X
    sharp (leaf v) = ρ v
    sharp (node (f , o)) = α (f , (sharp ∘ o))

  module _ ((X , α) : struct σ) (ρ : V -> X) where
    eval : structHom σ (Tr σ V , Tr.node) (X , α)
    eval = sharp (X , α) ρ , \f i -> refl

module _ {f a n : Level} (σ : Sig f a) {V : Type n} where
  mu : Tr σ (Tr σ V) -> Tr σ V
  mu = sharp σ (algTr σ V) (idfun (Tr σ V))
  -- mu (leaf t) = t
  -- mu (node (f , i)) = node (f , (\a -> mu (i a)))
