{-# OPTIONS --cubical #-}

module FreeStr where

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

record Sig (f a : Level) : Type (ℓ-max (ℓ-suc f) (ℓ-suc a)) where
  field
    symbol : Type f
    arity : symbol -> Type a
open Sig

record Str {f a : Level} (x : Level) (σ : Sig f a) : Type (ℓ-max (ℓ-max f a) (ℓ-suc x)) where
  field
    carrier : Type x
    ops : (f : σ .symbol) -> (o : σ .arity f -> carrier) -> carrier
    isSetStr : isSet carrier
open Str

record StrHom {f a : Level} {x y : Level} (σ : Sig f a) (X : Str x σ) (Y : Str y σ) : Type (ℓ-max (ℓ-max f a) (ℓ-max (ℓ-suc x) (ℓ-suc y))) where
  field
    fun : X .carrier -> Y .carrier
    fun-prsrv-ops : (f : σ .symbol) -> (op : σ .arity f -> X .carrier) -> fun (X .ops f op) ≡ Y .ops f (fun ∘ op)

unquoteDecl StrHomIsoΣ = declareRecordIsoΣ StrHomIsoΣ (quote StrHom)

StrHom≡ : {f a : Level} {x y : Level} {σ : Sig f a} {X : Str x σ} {Y : Str y σ} (g h : StrHom σ X Y) -> StrHom.fun g ≡ StrHom.fun h -> g ≡ h
StrHom≡ {X = X} {Y = Y} g h p =
  let g' = Iso.fun StrHomIsoΣ g ; h' = Iso.fun StrHomIsoΣ h
      q : g' ≡ h'
      q = Σ≡Prop (\fun -> isPropΠ \f -> isPropΠ (\o -> Str.isSetStr Y (fun (Str.ops X f o)) (Str.ops Y f (fun ∘ o)))) p
  in cong (Iso.inv StrHomIsoΣ) q

module _ {f a n : Level} (σ : Sig f a) where
  data Tree (X : Type n) : Type (ℓ-max f (ℓ-max a n)) where
    leaf : X -> Tree X
    node : (f : σ .symbol) -> (o : σ .arity f -> Tree X) -> Tree X
open Tree

record EqSig (e n : Level) : Type (ℓ-max (ℓ-suc e) (ℓ-suc n)) where
  field
    name : Type e
    free : name -> Type n
open EqSig

record EqThy {f a e n x : Level} (σ : Sig f a) (τ : EqSig e n) : Type (ℓ-max (ℓ-max f a) (ℓ-max (ℓ-suc e) (ℓ-suc (ℓ-max x n)))) where
  field
    lhs : (n : τ .name) -> Tree σ (τ .free n)
    rhs : (n : τ .name) -> Tree σ (τ .free n)
open EqThy

-- record Thy {f a : Level} (e n : Level) (σ : Sig f a) : Type (ℓ-max (ℓ-max f a) (ℓ-max (ℓ-suc e) (ℓ-suc n))) where
--   field
--     name : Type e
--     free : name -> Type n

-- open Thy

module _ {f a x n : Level} (σ : Sig f a) (X : Type n) (Y : Str x σ) where
  eval : Tree σ X -> (X -> Y .carrier) -> Y .carrier
  eval (leaf i) var = var i
  eval (node f o) var = Y .ops f \x -> eval (o x) var
open Tree

-- record Eqs {f a x n : Level} (e : Level) (σ : Sig f a) (T : Thy e n σ) (Y : Str x σ) : Type (ℓ-max (ℓ-max f a) (ℓ-max (ℓ-suc x) (ℓ-max e n))) where
--   field
--     equ : (n : T .name) -> eval σ (T .free n) Y (T .lhs n) ≡ eval σ (T .free n) Y (T .rhs n)

-- TODO: Tree is the same as Free without equations, defined later
-- just prove the freeness of Tree without equations

-- TODO: Free as a quotient of Tree / Eqs?
-- this should be easy to do
-- then reproduce the proof of freeness
-- but with equations

-- TODO: Free as a recursive HIT??
-- might need some mutual recursion or other trick
-- Some ideas:
-- - define Free with an mutually recursive eval function
-- - define two types: Free without equations, Free with equations, mutually recursively
-- - define Tree and Free mutually recursively

module _ {f a e n : Level} (σ : Sig f a) (τ : EqSig e n) (T : EqThy σ τ) where

  -- need a way to use lhs/rhs in T but with Free instead of Tree
  -- maybe mutual recursion could work

  -- maybe another way if you add an assumption that τ .free n ≃ X ?
  -- have a function: τ .free N -> X ? check
  mutual
    data Free {x} (X : Type x) : Type (ℓ-max x (ℓ-max f (ℓ-max a (ℓ-max e n)))) where
      η : X -> Free X
      op : (f : σ .symbol) -> (σ .arity f -> Free X) -> Free X
      eqs : (n : τ .name) -> (let l = T .lhs n in freeN {!!} l) ≡ (let r = T .rhs n in freeN {!!} r)
      isSetFree : isSet (Free X)

    freeT : ∀ {x} {X : Type x} -> Tree σ X -> Free X
    freeT (leaf i) = η i
    freeT (node f o) = op f \a -> freeT (o a)

    -- maybe another way?
    freeN : ∀ {x} {X : Type x} {n : τ .name} -> (τ .free n -> X) -> Tree σ (τ .free n) -> Free X
    freeN ren (leaf i) = η (ren i)
    freeN ren (node f o) = op f (\a -> freeN ren (o a))

    -- like ♯
    evalF : ∀ {x} {X : Type x} (Y : Str x σ) -> Free X -> (X -> Y .carrier) -> Y .carrier
    evalF Y (η x) h = h x
    evalF Y (op f o) h = Y .ops f \a -> evalF Y (o a) h
    evalF Y (eqs n i) h = {!!}
    evalF Y (isSetFree x y p q i j) = {!!}

--   FreeStr : ∀ {x} (X : Type x) -> Str (ℓ-max (ℓ-max f a) x) σ
--   Str.carrier (FreeStr X) = Free X
--   Str.ops (FreeStr X) = op
--   Str.isSetStr (FreeStr X) = isSetStr

--   module elimFreeSet {x p} {X : Type x} (P : Free X -> Type p)
--               (η* : (x : X) -> P (η x))
--               (op* : (f : σ .symbol) -> {o : σ .arity f -> Free X} -> ((a : σ .arity f) -> P (o a)) -> P (op f o))
--               (isSetStr* : (x : Free X) -> isSet (P x)) where
--     F : (x : Free X) -> P x
--     F (η x) = η* x
--     F (op f o) = op* f (F ∘ o)
--     F (isSetStr x y p q i j) = isOfHLevel→isOfHLevelDep 2 isSetStr* (F x) (F y) (cong F p) (cong F q) (isSetStr x y p q) i j

--   module recFreeSet {x p} {X : Type x} (P : Type p)
--               (η* : X -> P)
--               (op* : (f : σ .symbol) -> (σ .arity f -> P) -> P)
--               (isSetStr* : isSet P) where
--     F : (x : Free X) -> P
--     F = elimFreeSet.F (\_ -> P) η* (\f o -> op* f o) \_ -> isSetStr*

--   module elimFreeProp {x p} {X : Type x} (P : Free X -> Type p)
--               (η* : (x : X) -> P (η x))
--               (op* : (f : σ .symbol) -> {o : σ .arity f -> Free X} -> ((a : σ .arity f) -> P (o a)) -> P (op f o))
--               (isSetStr* : (x : Free X) -> isProp (P x)) where
--     F : (x : Free X) -> P x
--     F = elimFreeSet.F P η* op* (isProp→isSet ∘ isSetStr*)

--   module _ {x y} {X : Type x} {Y : Str y σ} where
--     open Str
--     open StrHom

--     _♯ : (X -> Y .carrier) -> Free X -> Y .carrier
--     (h ♯) (η x) = h x
--     (h ♯) (op f o) = Y .ops f (h ♯ ∘ o)
--     (h ♯) (isSetStr a b p q i j) =
--       Str.isSetStr Y ((h ♯) a) ((h ♯) b) (cong (h ♯) p) (cong (h ♯) q) i j

--     _♯-hom : (X -> Y .carrier) -> StrHom σ (FreeStr X) Y
--     fun (h ♯-hom) = h ♯
--     fun-prsrv-ops (h ♯-hom) f o = refl

--     _♯-eta : (g : StrHom σ (FreeStr X) Y) -> (f : Free X) -> g .fun f ≡ ((g .fun ∘ η) ♯) f
--     (g ♯-eta) =
--       elimFreeProp.F (\f -> g .fun f ≡ ((g .fun ∘ η) ♯) f)
--         (\_ -> refl)
--         (\f {o} p -> g .fun-prsrv-ops f o ∙ cong (Y .ops f) (funExt p))
--         (\f -> Str.isSetStr Y (g .fun f) (((g .fun ∘ η) ♯) f))

--     _♯-hom-eta : (g : StrHom σ (FreeStr X) Y) -> g ≡ (g .fun ∘ η) ♯-hom
--     (g ♯-hom-eta) = StrHom≡ g ((g .fun ∘ η) ♯-hom) (funExt (g ♯-eta))

--     freeEquiv : StrHom σ (FreeStr X) Y ≃ (X -> Y .carrier)
--     freeEquiv = isoToEquiv (iso (\g -> g .fun ∘ η) _♯-hom (\h -> refl) (\g -> sym (g ♯-hom-eta)))

--     freeIsEquiv : isEquiv (\g -> g .fun ∘ η)
--     freeIsEquiv = freeEquiv .snd

--
data MonSym : Type where
  e : MonSym
  ⊕ : MonSym

MonAr : MonSym -> Type
MonAr e = Fin 0
MonAr ⊕ = Fin 2

MonSig : Sig ℓ-zero ℓ-zero
Sig.symbol MonSig = MonSym
Sig.arity MonSig = MonAr

ℕ-MonStr : Str ℓ-zero MonSig
Str.carrier ℕ-MonStr = ℕ
Str.ops ℕ-MonStr e f = 0
Str.ops ℕ-MonStr ⊕ f = f zero + f (suc zero)
Str.isSetStr ℕ-MonStr = isSetℕ

data MonEq : Type where
  unitl unitr assocr : MonEq

-- Vec n A ≃ Fin n -> A

-- MonEqFree : MonEq -> ℕ
-- MonEqFree unitl = 1
-- MonEqFree unitr = 1
-- MonEqFree assocr = 3

-- MonEqLhs : (eq : MonEq) -> Tree MonSig (MonEqFree eq)
-- MonEqLhs unitl = node ⊕ (F.rec (node e \()) (leaf zero))
-- MonEqLhs unitr = node ⊕ (F.rec (leaf zero) (node e \()))
-- MonEqLhs assocr = node ⊕ (F.rec (node ⊕ (F.rec (leaf zero) (leaf (suc zero))))
--                                 (leaf (suc (suc zero))))

-- MonEqRhs : (eq : MonEq) -> Tree MonSig (MonEqFree eq)
-- MonEqRhs unitl = leaf zero
-- MonEqRhs unitr = leaf zero
-- MonEqRhs assocr = node ⊕ (F.rec (leaf zero)
--                          (node ⊕ (F.rec (leaf (suc zero)) (leaf two))))

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
