{-# OPTIONS --cubical #-}

module Experiments.FreeStr where

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

-- module _ {f a e n : Level} (σ : Sig f a) (τ : EqSig e n) (ε : seq σ τ) where
--   srel : (X : Type n) -> Tree σ X -> Tree σ X -> Type {!!}
--   srel X l r = sat σ τ ε {!!}

--   Fr : (X : Type n) -> walg σ
--   Fr X = (Tree σ X / {!!}) , {!!}

module _ {f a e n : Level} (σ : Sig f a) (τ : EqSig e n) where

  evalEq : {X : Type n} -> (n : τ .name) -> (ρ : X -> τ .free n) -> Tree σ X -> Tree σ (τ .free n)
  evalEq {X = X} n ρ = _♯ σ {X = X} {Y = TreeStr σ (τ .free n)} (leaf ∘ ρ)

  eqs : {X : Type n} -> Tree σ X -> Tree σ X -> Type (ℓ-max (ℓ-max f a) (ℓ-max e n))
  eqs {X = X} lhs rhs = (n : τ .name) (ρ : X -> τ .free n) -> evalEq n ρ lhs ≡ evalEq n ρ rhs

  Free : Type n -> Type (ℓ-max (ℓ-max f a) (ℓ-max e n))
  Free X = Tree σ X / eqs

module _ {f a e n : Level} (σ : Sig f a) (τ : EqSig e n) where

  t2f : {X : Type n} -> Tree σ X -> Free σ τ X
  t2f = Q.[_]

  f2t : {X : Type n} -> Free σ τ X -> ∥ Tree σ X ∥₁
  f2t F = let p = ([]surjective F) in P.map fst p

  FreeStr : (X : Type n) -> Str (ℓ-max (ℓ-max (ℓ-max f a) e) n) σ
  carrier (FreeStr X) = Free σ τ X
  ops (FreeStr X) f o = {!!}
  isSetStr (FreeStr X) = {!!}

-- ℕ-MonStrEq : Eqs ℓ-zero MonSig ℕ-MonStr
-- Eqs.name ℕ-MonStrEq = MonEq
-- Eqs.free ℕ-MonStrEq = MonEqFree
-- Eqs.lhs ℕ-MonStrEq = MonEqLhs
-- Eqs.rhs ℕ-MonStrEq = MonEqRhs
-- Eqs.equ ℕ-MonStrEq unitl = refl
-- Eqs.equ ℕ-MonStrEq unitr = funExt \v -> +-zero (v zero)
-- Eqs.equ ℕ-MonStrEq assocr = funExt \v -> sym (+-assoc (v zero) (v one) (v two))

-- Free-MonStr : (X : Type) -> Str ℓ-zero MonSig
-- Str.carrier (Free-MonStr X) = Free MonSig X
-- Str.ops (Free-MonStr X) e f = op e f
-- Str.ops (Free-MonStr X) ⊕ f = op ⊕ f
-- Str.isSetStr (Free-MonStr X) = isSetStr


-- Sig : (f a : Level) -> Type (ℓ-max (ℓ-suc f) (ℓ-suc a))
-- Sig f a = Σ[ F ∈ Type f ] (F -> Type a)

-- Op : {a x : Level} -> Type a -> Type x -> Type (ℓ-max a x)
-- Op A X = (A -> X) -> X

-- Str : {f a : Level} (x : Level) -> Sig f a -> Type (ℓ-max (ℓ-max f a) (ℓ-suc x))
-- Str {f} {a} x (F , ar) = Σ[ X ∈ Type x ] ((f : F) -> Op (ar f) X)

-- MonSig : Sig ℓ-zero ℓ-zero
-- MonSig = MonDesc , MonAr

-- MonStr = Str ℓ-zero MonSig

-- ℕ-MonStr : MonStr
-- ℕ-MonStr = ℕ , \{ e f -> 0
--                 ; ⊕ f -> f zero + f (suc zero) }
-- --

-- module FreeStr {f a : Level} (σ @ (F , ar) : Sig f a) where

  -- data Free {x} (X : Type x) : Type {!!} where
  --   η : X -> Free X
  --   op : (f : F) -> Op (ar f) (Free X) -> Free X
  --   isSetStr : isSet (Free X)

-- Op : (a : Level) -> ℕ -> Type a -> Type a
-- Op a n A = (Fin n -> A) -> A

-- Str : {f : Level} (a : Level) -> Sig f -> Type {!!}
-- Str {f} a (F , ar) = Σ[ A ∈ Type a ] ((f : F) -> Op a (ar f) A)

-- MonSig : Sig ℓ-zero
-- MonSig = Fin 2 , lookup (0 ∷ 2 ∷ [])

-- ℕ-MonStr : Str ℓ-zero MonSig
-- ℕ-MonStr = ℕ , F.elim {!!} (\_ -> 0) {!!}

-- F.elim (\{k} f -> Op ℓ-zero {!!} ℕ) {!!} {!!}
-- (f : Fin 2) → (Fin (lookup (0 ∷ 2 ∷ []) f) → ℕ) → ℕ
-- (f : fst MonSig) → Op ℓ-zero (snd MonSig f) ℕ

-- F.elim (\f -> Op ℓ-zero (rec 0 2 f) ℕ) (\_ -> 0) (\_ -> {!!})

-- record FreeS (ℓ : Level) (S : Type ℓ → Type ℓ') : Type (ℓ-max (ℓ-suc ℓ) ℓ') where
--   field
--     F : Type ℓ -> Type ℓ
--     F-S : (A : Type ℓ) -> S (F A)
--     η : (A : Type ℓ) -> A -> F A

-- freeS : (S : Type ℓ -> Type ℓ') -> FreeS ℓ S
-- monad T, T-algebra

-- monads on hSet

-- record Monad {ℓ : Level} : Type (ℓ-suc ℓ) where
--   field
--     T : Type ℓ -> Type ℓ
--     map : ∀ {A B} -> (A -> B) -> T A -> T B
--     η : ∀ {A} -> A -> T A
--     μ : ∀ {A} -> T (T A) -> T A

-- record T-Alg {ℓ} (T : Monad {ℓ}) : Type (ℓ-suc ℓ) where
--   module T = Monad T
--   field
--     el : Type ℓ
--     alg : T.T el -> el
--     unit : alg ∘ T.η ≡ idfun _
--     action : alg ∘ T.map alg ≡ alg ∘ T.μ

-- record T-AlgHom {ℓ} {T : Monad {ℓ}} (α β : T-Alg T) : Type (ℓ-suc ℓ) where
--   module T = Monad T
--   module α = T-Alg α
--   module β = T-Alg β
--   field
--     f : α.el -> β.el
--     f-coh : β.alg ∘ T.map f ≡ f ∘ α.alg
