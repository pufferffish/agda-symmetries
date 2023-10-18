{-# OPTIONS --cubical #-}

module Cubical.Structures.Tree where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Image
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Structures.Sig
open import Cubical.Structures.Str
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as S
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)

module _ {f a n : Level} (σ : Sig f a) where
  data Tree (V : Type n) : Type (ℓ-max (ℓ-max f a) n) where
    leaf : V -> Tree V
    node : sig σ (Tree V) -> Tree V
  open Tree


module _  {f a n y : Level} (σ : Sig f a) {V : Type n} where
  open import Cubical.Data.W.Indexed

  -- shapes
  S : Type n -> Type (ℓ-max f n)
  S _ = V ⊎ (σ .symbol)

  -- positions
  P : (V : Type n) -> S V -> Type a
  P V (inl v) = ⊥*
  P V (inr f) = σ .arity f

  inX : ∀ V (s : S V) -> P V s -> Type n
  inX V s p = V

  RepTree : Type (ℓ-max f (ℓ-max a (ℓ-suc n)))
  RepTree = IW S P inX V

  Tree→RepTree : Tree σ V -> RepTree
  Tree→RepTree (leaf v) = node (inl v) ⊥.rec*
  Tree→RepTree (node (f , i)) = node (inr f) (Tree→RepTree ∘ i)

  RepTree→Tree : RepTree -> Tree σ V
  RepTree→Tree (node (inl v) subtree) = leaf v
  RepTree→Tree (node (inr f) subtree) = node (f , RepTree→Tree ∘ subtree)

  Tree→RepTree→Tree : ∀ t -> RepTree→Tree (Tree→RepTree t) ≡ t
  Tree→RepTree→Tree (leaf v) = refl
  Tree→RepTree→Tree (node (f , i)) j = node (f , \a -> Tree→RepTree→Tree (i a) j)

  RepTree→Tree→RepTree : ∀ r -> Tree→RepTree (RepTree→Tree r) ≡ r
  RepTree→Tree→RepTree (node (inl v) subtree) = congS (node (inl v)) (funExt (⊥.rec ∘ lower))
  RepTree→Tree→RepTree (node (inr f) subtree) = congS (node (inr f)) (funExt (RepTree→Tree→RepTree ∘ subtree))

  isoRepTree : Tree σ V ≅ RepTree
  Iso.fun isoRepTree = Tree→RepTree
  Iso.inv isoRepTree = RepTree→Tree
  Iso.rightInv isoRepTree = RepTree→Tree→RepTree
  Iso.leftInv isoRepTree = Tree→RepTree→Tree

  isOfHLevelMax : ∀ {ℓ} {n m : HLevel} {A : Type ℓ}
    -> isOfHLevel n A
    -> isOfHLevel (max n m) A
  isOfHLevelMax {n = n} {m = m} {A = A} p =
    let
      (k , o) = left-≤-max {m = n} {n = m}
    in
      subst (λ l -> isOfHLevel l A) o (isOfHLevelPlus k p)

  isOfHLevelS : (h h' : HLevel)
    (p : isOfHLevel (2 + h) V) (q : isOfHLevel (2 + h') (σ .symbol))
    -> isOfHLevel (max (2 + h) (2 + h')) (S V)
  isOfHLevelS h h' p q =
    isOfHLevel⊎ _
      (isOfHLevelMax {n = 2 + h} {m = 2 + h'} p)
      (subst (λ h'' -> isOfHLevel h'' (σ .symbol)) (maxComm (2 + h') (2 + h)) (isOfHLevelMax {n = 2 + h'} {m = 2 + h} q))

  isOfHLevelRepTree : ∀ {h h' : HLevel}
    -> isOfHLevel (2 + h) V
    -> isOfHLevel (2 + h') (σ .symbol)
    -> isOfHLevel (max (2 + h) (2 + h')) RepTree
  isOfHLevelRepTree {h} {h'} p q =
    isOfHLevelSuc-IW (max (suc h) (suc h')) (λ _ -> isOfHLevelPath' _ (isOfHLevelS _ _ p q)) V

  isOfHLevelTree : ∀ {h h' : HLevel}
    -> isOfHLevel (2 + h) V
    -> isOfHLevel (2 + h') (σ .symbol)
    -> isOfHLevel (max (2 + h) (2 + h')) (Tree σ V)
  isOfHLevelTree {h} {h'} p q =
    isOfHLevelRetract (max (2 + h) (2 + h'))
      Tree→RepTree
      RepTree→Tree
      Tree→RepTree→Tree
      (isOfHLevelRepTree p q)

module _ {f : Level} (σ : FinSig f) where
  FinTree : (k : ℕ) -> Type f
  FinTree k = Tree (finSig σ) (Fin k)

module _ {f a : Level} (σ : Sig f a) where
  algTr : ∀ {x} (X : Type x) -> struct (ℓ-max f (ℓ-max a x)) σ
  car (algTr X) = Tree σ X
  alg (algTr X) = node

module _  {f a : Level} (σ : Sig f a) {x y} {X : Type x} (𝔜 : struct y σ) where
  private
    𝔛 : struct (ℓ-max f (ℓ-max a x)) σ
    𝔛 = algTr σ X

  sharp : (X -> 𝔜 .car) -> Tree σ X -> 𝔜 .car
  sharp ρ (leaf v) = ρ v
  sharp ρ (node (f , o)) = 𝔜 .alg (f , sharp ρ ∘ o)

  eval : (X -> 𝔜 .car) -> structHom 𝔛 𝔜
  eval h = sharp h , λ _ _ -> refl

  sharp-eta : (g : structHom 𝔛 𝔜) -> (tr : Tree σ X) -> g .fst tr ≡ sharp (g .fst ∘ leaf) tr
  sharp-eta g (leaf x) = refl
  sharp-eta (g-f , g-hom) (node x) =
    g-f (node x) ≡⟨ sym (g-hom (x .fst) (x .snd)) ⟩
    𝔜 .alg (x .fst , (λ y → g-f (x .snd y))) ≡⟨ cong (λ z → 𝔜 .alg (x .fst , z)) (funExt λ y -> sharp-eta ((g-f , g-hom)) (x .snd y)) ⟩
    𝔜 .alg (x .fst , (λ y → sharp (g-f ∘ leaf) (x .snd y)))
    ∎

  sharp-hom-eta : isSet (𝔜 .car) -> (g : structHom 𝔛 𝔜) -> g ≡ eval (g .fst ∘ leaf)
  sharp-hom-eta p g = structHom≡ 𝔛 𝔜 g (eval (g .fst ∘ leaf)) p (funExt (sharp-eta g))

  trEquiv : isSet (𝔜 .car) -> structHom 𝔛 𝔜 ≃ (X -> 𝔜 .car)
  trEquiv isSetY = isoToEquiv (iso (\g -> g .fst ∘ leaf) eval (\_ -> refl) (sym ∘ sharp-hom-eta isSetY))

  trIsEquiv : isSet (𝔜 .car) -> isEquiv (\g -> g .fst ∘ leaf)
  trIsEquiv = snd ∘ trEquiv
