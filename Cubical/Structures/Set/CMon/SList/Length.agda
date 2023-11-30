{-# OPTIONS --cubical --exact-split --safe #-}

-- Taken from https://github.com/vikraman/generalised-species/
module Cubical.Structures.Set.CMon.SList.Length where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Empty as E
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding

open import Cubical.Structures.Set.CMon.SList.Base as SList

private
  variable
    ℓ : Level
    A B : Type ℓ
    ϕ : isSet A
    a x : A
    xs ys : SList A

disj-nil-cons : x ∷ xs ≡ [] -> ⊥
disj-nil-cons p = transport (λ i → fst (code (p i))) tt
  where code : SList A -> hProp ℓ-zero
        code = Elim.f (⊥ , isProp⊥)
          (λ _ _ -> Unit , isPropUnit)
          (λ _ _ _ _ -> Unit , isPropUnit)
          (λ _ -> isSetHProp)

disj-cons-nil : [] ≡ x ∷ xs -> ⊥
disj-cons-nil p = disj-nil-cons (sym p)

length : SList A → ℕ
length = Elim.f 0 (λ _ n -> suc n) (λ _ _ _ -> refl) (λ _ -> isSetℕ)

length-++ : (x y : SList A) → length (x ++ y) ≡ length x + length y
length-++ x y = ElimProp.f {B = λ xs → length (xs ++ y) ≡ length xs + length y}
  (isSetℕ _ _) refl (λ a p -> cong suc p) x
  
lenZero-out : (xs : SList A) → length xs ≡ 0 → [] ≡ xs
lenZero-out = ElimProp.f (isPropΠ λ _ → trunc _ _)
  (λ _ -> refl)
  (λ x p q -> E.rec (snotz q))

lenZero-eqv : (xs : SList A) → (length xs ≡ 0) ≃ ([] ≡ xs)
lenZero-eqv xs = propBiimpl→Equiv (isSetℕ _ _) (trunc _ _) (lenZero-out xs) (λ p i → length (p (~ i)))

is-sing-pred : SList A → A → Type _
is-sing-pred xs a = [ a ] ≡ xs

is-sing-pred-prop : (xs : SList A) (z : A) → isProp (is-sing-pred xs z)
is-sing-pred-prop xs a = trunc [ a ] xs

is-sing : SList A → Type _
is-sing xs = Σ _ (is-sing-pred xs)

Sing : Type ℓ → Type ℓ
Sing A = Σ (SList A) is-sing

[_]-is-sing : (a : A) → is-sing [ a ]
[ a ]-is-sing = a , refl

sing=isProp : ∀ {x y : A} → isProp ([ x ] ≡ [ y ])
sing=isProp {x = x} {y = y} = trunc [ x ] [ y ]

sing=-in : ∀ {x y : A} → x ≡ y → [ x ] ≡ [ y ]
sing=-in p i = [ p i ]

sing=isContr : ∀ {x y : A} → x ≡ y → isContr ([ x ] ≡ [ y ])
sing=isContr p = sing=-in p , sing=isProp (sing=-in p)

lenOne-down : (x : A) (xs : SList A) → length (x ∷ xs) ≡ 1 → [] ≡ xs
lenOne-down x xs p = lenZero-out xs (injSuc p)

lenOne-cons : (x : A) (xs : SList A) → length (x ∷ xs) ≡ 1 → is-sing (x ∷ xs)
lenOne-cons x xs p =
  let q = lenOne-down x xs p
  in transport (λ i → is-sing (x ∷ q i)) [ x ]-is-sing

lenTwo-⊥ : (x y : A) (xs : SList A) → (length (y ∷ x ∷ xs) ≡ 1) ≃ ⊥
lenTwo-⊥ x y xs = (λ p → E.rec (snotz (injSuc p))) , record { equiv-proof = E.elim }

isContrlenTwo-⊥→X : (X : Type ℓ) (x y : A) (xs : SList A) → isContr (length (y ∷ x ∷ xs) ≡ 1 → X)
isContrlenTwo-⊥→X X x y xs = subst (λ Z → isContr (Z → X)) (sym (ua (lenTwo-⊥ x y xs))) (isContr⊥→A {A = X})

lenOne-swap : {A : Type ℓ} (x y : A) (xs : SList A)
            → PathP (λ i → length (SList.swap x y xs i) ≡ 1 → is-sing (SList.swap x y xs i))
                    (λ p → lenOne-cons x (y ∷ xs) p)
                    (λ p → lenOne-cons y (x ∷ xs) p)
lenOne-swap {A = A} x y xs =
  transport (sym (PathP≡Path (λ i → length (SList.swap x y xs i) ≡ 1 → is-sing (SList.swap x y xs i)) _ _))
            (isContr→isProp (isContrlenTwo-⊥→X _ x y xs) _ _)

lenOne : Type ℓ → Type _
lenOne A = Σ (SList A) (λ xs → length xs ≡ 1)

module _ {ϕ : isSet A} where

  is-sing-set : (xs : SList A) → isSet (is-sing xs)
  is-sing-set xs = isSetΣ ϕ λ x → isProp→isSet (is-sing-pred-prop xs x)

  lenOne-out : (xs : SList A) → length xs ≡ 1 → is-sing xs
  lenOne-out = Elim.f (λ p → E.rec (znots p))
    (λ x {xs} f p → lenOne-cons x xs p)
    (λ x y {xs} f → lenOne-swap x y xs)
    λ xs → isSetΠ (λ p → is-sing-set xs)
 
  head : lenOne A → A
  head (xs , p) = lenOne-out xs p .fst

  -- not definitional due to lack of regularity
  head-β : (a : A) → head ([ a ] , refl) ≡ a
  head-β a i = transp (λ _ → A) i a

  lenOnePath : (a b : A) → Type _
  lenOnePath a b = Path (lenOne A) ([ a ] , refl) ([ b ] , refl)

  lenOnePath-in : {a b : A} → [ a ] ≡ [ b ] → lenOnePath a b
  lenOnePath-in = Σ≡Prop (λ xs → isSetℕ _ _)

  [-]-inj : {a b : A} → [ a ] ≡ [ b ] → a ≡ b
  [-]-inj {a = a} {b = b} p = aux (lenOnePath-in p)
    where aux : lenOnePath a b → a ≡ b
          aux p = sym (head-β a) ∙ cong head p ∙ head-β b

  is-sing-prop : (xs : SList A) → isProp (is-sing xs)
  is-sing-prop xs (a , ψ) (b , ξ) = Σ≡Prop (is-sing-pred-prop xs) ([-]-inj (ψ ∙ sym ξ))

  lenOne-eqv : (xs : SList A) → (length xs ≡ 1) ≃ (is-sing xs)
  lenOne-eqv xs = propBiimpl→Equiv (isSetℕ _ _) (is-sing-prop xs) (lenOne-out xs) (λ χ → cong length (sym (χ .snd)))

  lenOne-set-eqv : lenOne A ≃ A
  lenOne-set-eqv = isoToEquiv (iso head g head-β g-f)
    where g : A → lenOne A
          g a = [ a ] , refl
          g-f : (as : lenOne A) → g (head as) ≡ as
          g-f (as , ϕ) =
            let (a , ψ) = lenOne-out as ϕ
            in Σ≡Prop (λ xs → isSetℕ _ _) {u = ([ a ] , refl)} {v = (as , ϕ)} ψ

  sing-set-eqv : Sing A ≃ A
  sing-set-eqv = isoToEquiv (iso f (λ a → [ a ] , [ a ]-is-sing) (λ _ → refl) ret)
    where f : Sing A → A
          f s = s .snd .fst
          ret : (s : Sing A) → ([ f s ] , f s , refl) ≡ s
          ret (s , ψ) = Σ≡Prop is-sing-prop (ψ .snd)
