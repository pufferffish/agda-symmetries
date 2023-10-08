{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Cubical.Structures.Tree where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Image
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
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
  Cover (node (sym-α , ari-α)) (node (sym-β , ari-β)) =
    Σ[ p ∈ sym-α ≡ sym-β ] ((α : σ .arity sym-α) -> Cover (ari-α α) (ari-β (subst (σ .arity) p α)))

  reflCode : ∀ tr -> Cover tr tr
  reflCode (leaf x) = lift refl
  reflCode (node (sym-α , ari-α)) =
    refl , λ α -> subst (Cover (ari-α α)) (cong ari-α (sym (substRefl {B = σ .arity} α))) (reflCode (ari-α α))

  encode : ∀ trx try -> (p : trx ≡ try) -> Cover trx try
  encode trx _ = J (λ try _ -> Cover trx try) (reflCode trx)
  
  encodeRefl : ∀ xs -> encode xs xs refl ≡ reflCode xs
  encodeRefl trx = JRefl (λ try _ -> Cover trx try) (reflCode trx)

  decode : ∀ trx try -> Cover trx try -> trx ≡ try
  decode (leaf x) (leaf y) (lift p) = cong leaf p
  decode (leaf x) (node y) (lift p) = ⊥.rec p
  decode (node x) (leaf y) (lift p) = ⊥.rec p
  decode (node (sym-α , ari-α)) (node (sym-β , ari-β)) (p , f) =
    cong node (cong₂ _,_ p {!   !})

  decodeRefl : ∀ trx -> decode trx trx (reflCode trx) ≡ refl
  decodeRefl (leaf x) i = refl
  decodeRefl (node x) i = refl

  decodeEncode : ∀ trx try -> (p : trx ≡ try) -> decode trx try (encode trx try p) ≡ p
  decodeEncode trx _ =
    J (λ try p -> decode trx try (encode trx try p) ≡ p)
      (cong (decode trx trx) (encodeRefl trx) ∙ decodeRefl trx)

  isOfHLevelMax : ∀ {ℓ} {n m : HLevel} {A : Type ℓ}
    -> isOfHLevel n A
    -> isOfHLevel (max n m) A
  isOfHLevelMax {n = n} {m = m} {A = A} p =
    let
      (k , o) = left-≤-max {m = n} {n = m}
    in
      subst (λ l -> isOfHLevel l A) o (isOfHLevelPlus k p)

  isOfHLevelSym :
    (n : HLevel) (sym : σ .symbol)
    -> isOfHLevel n V
    -> isOfHLevel n (σ .arity sym -> V)
  isOfHLevelSym n sym p = isOfHLevelΠ n λ _ -> p

  isOfHLevelSig :
    (n : HLevel) (sym : σ .symbol)
    -> isOfHLevel n V
    -> isOfHLevel n (σ .symbol)
    -> isOfHLevel n (sig σ (Tree σ V))
  isOfHLevelSig n sym p q = isOfHLevelΣ n q {!   !}

  isOfHLevelCover : (n m : HLevel)
    (p : isOfHLevel (2 + n) V) (q : isOfHLevel (2 + m) (σ .symbol))
    (trx try : Tree σ V) -> isOfHLevel (max (suc n) (suc m)) (Cover trx try)
  isOfHLevelCover n m p q (leaf x) (leaf y) =
    isOfHLevelMax {m = suc m} (isOfHLevelLift (suc n) (p x y))
  isOfHLevelCover n m p q (leaf x) (node y) =
    isOfHLevelMax {m = suc m} (isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥))
  isOfHLevelCover n m p q (node x) (leaf y) =
    isOfHLevelMax {m = suc m} (isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥))
  isOfHLevelCover n m p q (node x) (node y) =
    {!   !}

algTr : ∀ {f a x} {h : HLevel} {X : Type x} (σ : Sig f a) ->
        isOfHLevel (suc (suc h)) X -> struct h (ℓ-max f (ℓ-max a x)) σ
carrier (algTr {X = X} σ _) = Tree σ X
algebra (algTr _ _) = node
trunc (algTr {h = h} {X = X} σ trunc) x y = {!   !}

module _  {f a : Level} (σ : Sig f a) {x y} {X : Type x} {h : HLevel} (trunc : isOfHLevel (2 + h) X) (𝔜 : struct h y σ) where
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
 