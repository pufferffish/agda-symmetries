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
open import Cubical.HITs.SetQuotients renaming ([_] to liftToQuo)
open import Agda.Primitive

record Sig (f a : Level) : Type ((ℓ-suc f) ⊔ (ℓ-suc a)) where
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
    isSetTree : isSet (Tree X)
open Tree

record EqSig (e n : Level) : Type (ℓ-max (ℓ-suc e) (ℓ-suc n)) where
  field
    name : Type e
    free : name -> Type n
open EqSig

record EqThy {f a e n : Level} (σ : Sig f a) (τ : EqSig e n) : Type (ℓ-max (ℓ-max f a) (ℓ-max (ℓ-suc e) (ℓ-suc n))) where
  field
    lhs : (n : τ .name) -> Tree σ (τ .free n)
    rhs : (n : τ .name) -> Tree σ (τ .free n)
open EqThy

module _ {f a e n : Level} {τ : EqSig e n} {σ : Sig f a} (eqs : EqThy σ τ) where
 data Free : Type (ℓ-max (ℓ-max f a) (ℓ-max (ℓ-suc e) (ℓ-suc n))) where
    tree : {X : Type n} -> Tree σ X -> Free
    eq/ : (n : τ .name) -> tree (eqs .lhs n) ≡ tree (eqs .rhs n)
    isSetFree : isSet Free

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

-- module _ {f a e : Level} (σ : Sig f a) where
-- 
--   -- freeToTree : ∀ {x} (X : Type x) -> {eqs : Tree σ X -> Tree σ X -> Type e} -> Free σ X eqs -> Tree σ X
--   -- freeToTree X (liftToQuo a) = a
--   -- freeToTree X (eq/ a b r i) = {! a !}
--   -- freeToTree X (squash/ free₁ free₂ p q i i₁) = {!   !}
-- 
--   freeOps : ∀ {g} {x} {X : Type x} (eqs : EqThy {f} {a} {e} {x} σ X) -> (σ .arity g -> Free eqs) -> (σ .arity g -> Tree σ X)
--   freeOps eqs vars op with vars op
--   freeOps eqs vars op | tree t = t
--   freeOps eqs vars op | eq/ n i = {! (eq/ n) i!}
--   freeOps eqs vars op | isSetFree x y p q i j = {!  !}
-- 
-- 
--   FreeStr : ∀ {x} (X : Type x) -> (eqs : EqThy {f} {a} {e} {x} σ X) -> Str (ℓ-max (ℓ-max (ℓ-max f a) (ℓ-suc x)) (ℓ-suc e)) σ
--   Str.carrier (FreeStr X eqs) = Free eqs
--   Str.ops (FreeStr X eqs) g o = tree {!   !}
--   Str.isSetStr (FreeStr X eqs) = isSetFree


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
 