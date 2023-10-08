{-# OPTIONS --cubical #-}

module Cubical.Structures.Tree where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Image
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Data.Nat
open import Cubical.Structures.Sig
open import Cubical.Structures.Str
open import Cubical.Structures.Arity
open import Cubical.Data.Empty as ⊥

data Tree {f a n : Level} (σ : Sig f a) (V : Type n) : Type (ℓ-max (ℓ-max f a) n) where
  leaf : V -> Tree σ V
  node : sig σ (Tree σ V) -> Tree σ V

module _ {f : Level} (σ : FinSig f) where
  FinTree : (k : ℕ) -> Type f
  FinTree k = Tree (finSig σ) (Arity k)

module TreePath {f a n} {σ : Sig f a} {V : Type n} where
  Cover : Tree σ V -> Tree σ V -> Type (ℓ-max (ℓ-max f a) n)
  Cover (leaf x) (leaf y) = Lift {j = ℓ-max f a} (x ≡ y)
  Cover (leaf x) (node y) = Lift ⊥
  Cover (node x) (leaf y) = Lift ⊥
  Cover (node x) (node y) = x ≡ y

  reflCode : ∀ tr -> Cover tr tr
  reflCode (leaf x) = lift refl
  reflCode (node x) = refl

  encode : ∀ trx try -> (p : trx ≡ try) -> Cover trx try
  encode trx _ = J (λ try _ -> Cover trx try) (reflCode trx)
  
  encodeRefl : ∀ xs -> encode xs xs refl ≡ reflCode xs
  encodeRefl trx = JRefl (λ try _ -> Cover trx try) (reflCode trx)

  decode : ∀ trx try -> Cover trx try -> trx ≡ try
  decode (leaf x) (leaf y) (lift p) = cong leaf p
  decode (leaf x) (node y) (lift p) = ⊥.rec p
  decode (node x) (leaf y) (lift p) = ⊥.rec p
  decode (node x) (node y) p = cong node p

  decodeRefl : ∀ trx -> decode trx trx (reflCode trx) ≡ refl
  decodeRefl (leaf x) i = refl
  decodeRefl (node x) i = refl

  decodeEncode : ∀ trx try -> (p : trx ≡ try) → decode trx try (encode trx try p) ≡ p
  decodeEncode trx _ =
    J (λ try p -> decode trx try (encode trx try p) ≡ p)
      ((cong (decode trx trx) (encodeRefl trx) ∙ decodeRefl trx))

  

algTr : ∀ {f a x} {h : HLevel} {X : Type x} (σ : Sig f a) ->
        isOfHLevel (suc (suc h)) X -> struct h (ℓ-max f (ℓ-max a x)) σ
carrier (algTr {X = X} σ _) = Tree σ X
algebra (algTr _ _) = node
trunc (algTr {h = h} {X = X} σ trunc) x y = {!   !}

module _  {f a : Level} (σ : Sig f a) {x y} {X : Type x} {h : HLevel} (trunc : isOfHLevel (suc (suc h)) X) (𝔜 : struct h y σ) where
  private
    𝔛 : struct h (ℓ-max f (ℓ-max a x)) σ
    𝔛 = algTr σ trunc

  sharp : (X -> 𝔜 .carrier) -> Tree σ X -> 𝔜 .carrier
  sharp ρ (leaf v) = ρ v
  sharp ρ (node (f , o)) = 𝔜 .algebra (f , sharp ρ ∘ o)

  eval : (X -> 𝔜 .carrier) -> structHom h 𝔛 𝔜
  eval h = sharp h , λ _ _ -> refl

  sharp-eta : (g : structHom h 𝔛 𝔜) -> (tr : Tree σ X) -> g .fst tr ≡ sharp (g .fst ∘ leaf) tr
  sharp-eta g (leaf x) = refl
  sharp-eta (g-f , g-hom) (node x) =
    g-f (node x) ≡⟨ sym (g-hom (x .fst) (x .snd)) ⟩
    𝔜 .algebra (x .fst , (λ y → g-f (x .snd y))) ≡⟨ cong (λ z → 𝔜 .algebra (x .fst , z)) (funExt λ y -> sharp-eta ((g-f , g-hom)) (x .snd y)) ⟩
    𝔜 .algebra (x .fst , (λ y → sharp (g-f ∘ leaf) (x .snd y)))
    ∎

  sharp-hom-eta : isSet (𝔜 .carrier) -> (g : structHom h 𝔛 𝔜) -> g ≡ eval (g .fst ∘ leaf)
  sharp-hom-eta p g = structHom≡ h 𝔛 𝔜 g (eval (g .fst ∘ leaf)) p (funExt (sharp-eta g))

  trEquiv : isSet (𝔜 .carrier) -> structHom h 𝔛 𝔜 ≃ (X -> 𝔜 .carrier)
  trEquiv isSetY = isoToEquiv (iso (\g -> g .fst ∘ leaf) eval (\_ -> refl) (sym ∘ sharp-hom-eta isSetY))

  trIsEquiv : isSet (𝔜 .carrier) -> isEquiv (\g -> g .fst ∘ leaf)
  trIsEquiv = snd ∘ trEquiv
