{-# OPTIONS --cubical --safe --exact-split #-}

module Cubical.Structures.Eq where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Image
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.List as L
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Reflection.RecordEquiv
open import Cubical.HITs.SetQuotients as Q
open import Agda.Primitive

open import Cubical.Structures.Sig
open import Cubical.Structures.Str
open import Cubical.Structures.Tree

record EqSig (e n : Level) : Type (ℓ-max (ℓ-suc e) (ℓ-suc n)) where
  field
    name : Type e
    free : name -> Type n
open EqSig public

FinEqSig : (e : Level) -> Type (ℓ-max (ℓ-suc e) (ℓ-suc ℓ-zero))
FinEqSig = FinSig

finEqSig : {e : Level} -> FinEqSig e -> EqSig e ℓ-zero
name (finEqSig σ) = σ .fst
free (finEqSig σ) = Fin ∘ σ .snd

emptyEqSig : EqSig ℓ-zero ℓ-zero
name emptyEqSig = ⊥.⊥
free emptyEqSig = ⊥.rec

sumEqSig : {e n e' n' : Level} -> EqSig e n -> EqSig e' n' -> EqSig (ℓ-max e e') (ℓ-max n n')
name (sumEqSig σ τ) = (name σ) ⊎ (name τ)
free (sumEqSig {n' = n} σ τ) (inl x) = Lift {j = n} ((free σ) x)
free (sumEqSig {n = n} σ τ) (inr x) = Lift {j = n} ((free τ) x)

-- equational signature functor
module _ {e n : Level} (ε : EqSig e n) where
  eqsig : Type e -> Type (ℓ-max e n)
  eqsig X = Σ (ε .name) \f -> ε .free f -> X

  eqsig≡ : {X : Type e} (f : ε .name) {i j : ε .free f -> X}
         -> ((a : ε .free f) -> i a ≡ j a)
         -> Path (eqsig X) (f , i) (f , j)
  eqsig≡ f H = ΣPathP (refl , funExt H)

  eqsigF : {X Y : Type e} -> (X -> Y) -> eqsig X -> eqsig Y
  eqsigF h (f , i) = f , h ∘ i

_⇒_ : {a b c : Level} -> (F : Type a -> Type b) (G : Type a -> Type c) -> Type (ℓ-max (ℓ-max (ℓ-suc a) b) c)
_⇒_ {a = a} F G = (X : Type a) -> F X -> G X

module _ {f a e n : Level} (σ : Sig f a) (ε : EqSig e n) where
  nsysEq : Type (ℓ-max (ℓ-max (ℓ-max f a) (ℓ-suc e)) n)
  nsysEq = (eqsig ε ⇒ Tree σ) × (eqsig ε ⇒ Tree σ)

module _ {f a e n : Level} (σ : Sig f a) (ε : EqSig e n) where
  -- simplified
  sysEq : Type (ℓ-max (ℓ-max (ℓ-max f a) e) n)
  sysEq = (e : ε .name) -> Tree σ (ε .free e) × Tree σ (ε .free e)

module _ {f a e n : Level} (σ : Sig f a) (ε : EqSig e n) where
  nseq : sysEq σ ε -> nsysEq σ ε
  nseq f = (\V (eqn , v) -> trMap σ v (f eqn .fst)) , (\V (eqn , v) -> trMap σ v (f eqn .snd))

emptySEq : sysEq emptySig emptyEqSig
emptySEq = ⊥.elim

nemptySEq : nsysEq emptySig emptyEqSig
nemptySEq = (\_ -> ⊥.rec ∘ fst) , (\_ -> ⊥.rec ∘ fst)

module _ {f a e n s : Level} {σ : Sig f a} {ε : EqSig e n} where
  -- type of structure satisfying equations
  infix 30 _⊨n_ _⊨_
  _⊨n_ : struct s σ -> nsysEq σ ε -> Type (ℓ-max (ℓ-max (ℓ-suc e) n) s)
  𝔛 ⊨n ℯ = (V : Type e) (𝓋 : V -> 𝔛 .car)
         -> sharp σ 𝔛 𝓋 ∘ ℯ .fst V ≡ sharp σ 𝔛 𝓋 ∘ ℯ .snd V

  -- simplified
  _⊨_ : struct s σ -> sysEq σ ε -> Type (ℓ-max (ℓ-max e n) s)
  𝔛 ⊨ ℯ = (eqn : ε .name) (ρ : ε .free eqn -> 𝔛 .car)
        -> sharp σ 𝔛 ρ (ℯ eqn .fst) ≡ sharp σ 𝔛 ρ (ℯ eqn .snd)

  nsat : {𝔛 : struct s σ} {ℯ : sysEq σ ε} -> 𝔛 ⊨ ℯ -> 𝔛 ⊨n nseq σ ε ℯ
  nsat {𝔛 = 𝔛} {ℯ = ℯ} H V 𝓋 =
    funExt \{ (eqn , v) ->
      sharp σ 𝔛 𝓋 (sharp σ (algTr σ V) (leaf ∘ v) (ℯ eqn .fst))
    ≡⟨ sym (sharp-∘ σ 𝔛 (leaf ∘ v) 𝓋 (ℯ eqn .fst)) ⟩
      sharp σ 𝔛 (𝓋 ∘ v) (ℯ eqn .fst)
    ≡⟨ H eqn (𝓋 ∘ v) ⟩
      sharp σ 𝔛 (𝓋 ∘ v) (ℯ eqn .snd)
    ≡⟨ sharp-∘ σ 𝔛 (leaf ∘ v) 𝓋 (ℯ eqn .snd) ⟩
      sharp σ 𝔛 𝓋 (sharp σ (algTr σ V) (leaf ∘ v) (ℯ eqn .snd))
    ∎ }
