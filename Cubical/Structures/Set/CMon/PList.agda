{-# OPTIONS --cubical #-}

-- Taken from https://drops.dagstuhl.de/opus/volltexte/2023/18395/pdf/LIPIcs-ITP-2023-20.pdf
module Cubical.Structures.Set.CMon.PList where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.List as L
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.HITs.SetQuotients as Q

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.Mon.List as LM
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity hiding (_/_)

data Perm {ℓ : Level} {A : Type ℓ} : List A -> List A -> Type ℓ where
  perm-refl : ∀ {xs} -> Perm xs xs
  perm-swap : ∀ {x y xs ys zs} -> Perm (xs ++ x ∷ y ∷ ys) zs -> Perm (xs ++ y ∷ x ∷ ys) zs 

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B : Type ℓ

map++ : {f : A -> B} (xs : List A) {ys : List A} -> L.map f (xs ++ ys) ≡ L.map f xs ++ L.map f ys
map++ [] = refl
map++ (x ∷ xs) = cong (_ ∷_) (map++ xs)

infixr 30 _∙ₚ_
_∙ₚ_ : ∀ {xs ys zs} -> Perm xs ys -> Perm ys zs -> Perm {A = A} xs zs
perm-refl ∙ₚ q = q
(perm-swap p) ∙ₚ q = perm-swap (p ∙ₚ q)

perm-sym : ∀ {xs ys} -> Perm xs ys -> Perm {A = A} ys xs
perm-sym perm-refl = perm-refl
perm-sym (perm-swap p) = perm-sym p ∙ₚ perm-swap perm-refl

perm-subst : ∀ {xs ys} -> xs ≡ ys -> Perm {A = A} xs ys
perm-subst {xs = xs} p = subst (Perm xs) p perm-refl

perm-∷ : ∀ {x xs ys} -> Perm xs ys -> Perm {A = A} (x ∷ xs) (x ∷ ys)
perm-∷ perm-refl = perm-refl
perm-∷ {x = x} (perm-swap {xs = xs} p) = perm-swap {xs = x ∷ xs} (perm-∷ p)

perm-prepend : (xs : List A) {ys zs : List A} -> Perm ys zs -> Perm (xs ++ ys) (xs ++ zs)
perm-prepend [] p = p
perm-prepend (x ∷ xs) p = perm-∷ (perm-prepend xs p)

perm-append : ∀ {xs ys} -> Perm xs ys -> (zs : List A) -> Perm (xs ++ zs) (ys ++ zs)
perm-append perm-refl _ = perm-refl
perm-append (perm-swap {xs = xs} p) _ =
  perm-subst (++-assoc xs _ _) ∙ₚ perm-swap (perm-subst (sym (++-assoc xs _ _)) ∙ₚ perm-append p _)

perm-movehead : (x : A) (xs : List A) {ys : List A} -> Perm (x ∷ xs ++ ys) (xs ++ x ∷ ys)
perm-movehead x [] = perm-refl
perm-movehead x (y ∷ xs) = perm-swap {xs = []} (perm-∷ (perm-movehead x xs))

perm-map : (f : A -> B) {xs ys : List A} -> Perm xs ys -> Perm (L.map f xs) (L.map f ys)
perm-map f perm-refl = perm-refl
perm-map f (perm-swap {xs = xs} p) = perm-subst (map++ xs) ∙ₚ perm-swap (perm-subst (sym (map++ xs)) ∙ₚ perm-map f p)

_≈ₚ_ : ∀ {ℓ} {A : Type ℓ} -> List A -> List A -> Type ℓ
xs ≈ₚ ys = ∥ Perm xs ys ∥₁

PList : Type ℓ -> Type ℓ
PList A = List A / _≈ₚ_

e : PList A
e = Q.[ [] ]

_⊕_ : PList A -> PList A -> PList A
_⊕_ = Q.rec2 squash/
  (λ xs ys -> Q.[ xs ++ ys ])
  (λ as bs cs p -> eq/ (as ++ cs) (bs ++ cs) (P.map (λ p -> perm-append p cs) p))
  (λ as bs cs p -> eq/ (as ++ bs) (as ++ cs) (P.map (λ p -> perm-prepend as p) p))

⊕-unitlₚ : (as : List A) -> Perm ([] ++ as) as
⊕-unitlₚ _ = perm-refl

⊕-unitl : (as : PList A) -> e ⊕ as ≡ as
⊕-unitl = elimProp (λ _ -> squash/ _ _) (λ as -> eq/ _ _ ∣ ⊕-unitlₚ as ∣₁)

⊕-unitrₚ : (as : List A) -> Perm (as ++ []) as
⊕-unitrₚ [] = perm-refl
⊕-unitrₚ (a ∷ as) = perm-∷ (⊕-unitrₚ as)

⊕-unitr : (as : PList A) -> as ⊕ e ≡ as
⊕-unitr = elimProp (λ _ -> squash/ _ _) (λ as -> eq/ _ _ ∣ ⊕-unitrₚ as ∣₁)

⊕-assocrₚ : (as bs cs : List A) -> Perm ((as ++ bs) ++ cs) (as ++ (bs ++ cs))
⊕-assocrₚ [] bs cs = perm-refl
⊕-assocrₚ (a ∷ as) bs cs = perm-∷ (⊕-assocrₚ as bs cs)

⊕-assocr : (as bs cs : PList A) -> (as ⊕ bs) ⊕ cs ≡ as ⊕ (bs ⊕ cs)
⊕-assocr =
  elimProp (λ _ -> isPropΠ (λ _ -> isPropΠ (λ _ -> squash/ _ _))) λ xs ->
    elimProp (λ _ -> isPropΠ λ _ -> squash/ _ _) λ ys ->
      elimProp (λ _ -> squash/ _ _) λ zs ->
        eq/ _ _ ∣ ⊕-assocrₚ xs ys zs ∣₁

⊕-commₚ : (xs ys : List A) -> Perm (xs ++ ys) (ys ++ xs)
⊕-commₚ xs [] = perm-subst (++-unit-r xs)
⊕-commₚ xs (y ∷ ys) = perm-sym (perm-movehead y xs {ys = ys}) ∙ₚ perm-∷ (⊕-commₚ xs ys)

⊕-comm : (xs ys : PList A) -> xs ⊕ ys ≡ ys ⊕ xs
⊕-comm =
  elimProp (λ _ -> isPropΠ (λ _ -> squash/ _ _)) λ xs ->
    elimProp (λ _ -> squash/ _ _) λ ys ->
      eq/ _ _ ∣ ⊕-commₚ xs ys ∣₁

plist-α : ∀ {n : Level} {X : Type n} -> sig M.MonSig (PList X) -> PList X
plist-α (M.`e , i) = Q.[ [] ]
plist-α (M.`⊕ , i) = i fzero ⊕ i fone

module Free {x y : Level} {A : Type x} {𝔜 : struct y M.MonSig} (isSet𝔜 : isSet (𝔜 .car)) (𝔜-cmon : 𝔜 ⊨ M.CMonSEq) where
  module 𝔜' = M.CMonSEq 𝔜 𝔜-cmon

  𝔛 : M.CMonStruct
  𝔛 = < PList A , plist-α >

  module _ (f : A -> 𝔜 .car) where
    open LM.Free {A = A} isSet𝔜 (M.cmonSatMon 𝔜-cmon)

    ♯-≅ₚ-α : ∀ {x y : A} (xs ys : List A) -> (f ♯) (xs ++ x ∷ y ∷ ys) ≡ (f ♯) (xs ++ y ∷ x ∷ ys)
    ♯-≅ₚ-α {x} {y} [] ys =
      (f ♯) ((L.[ x ] ++ L.[ y ]) ++ ys) ≡⟨ ♯-++ f (L.[ x ] ++ L.[ y ]) ys  ⟩
      (f ♯) (L.[ x ] ++ L.[ y ]) 𝔜.⊕ (f ♯) ys ≡⟨ cong (𝔜._⊕ (f ♯) ys) (♯-++ f L.[ x ] L.[ y ]) ⟩
      ((f ♯) L.[ x ] 𝔜.⊕ (f ♯) L.[ y ]) 𝔜.⊕ (f ♯) ys ≡⟨ cong (𝔜._⊕ (f ♯) ys) (𝔜'.comm _ _) ⟩
      ((f ♯) L.[ y ] 𝔜.⊕ (f ♯) L.[ x ]) 𝔜.⊕ (f ♯) ys ≡⟨ cong (𝔜._⊕ (f ♯) ys) (sym (♯-++ f L.[ y ] L.[ x ])) ⟩
      (f ♯) (L.[ y ] ++ L.[ x ]) 𝔜.⊕ (f ♯) ys ≡⟨ sym (♯-++ f (L.[ y ] ++ L.[ x ]) ys) ⟩
      (f ♯) ((L.[ y ] ++ L.[ x ]) ++ ys) ∎
    ♯-≅ₚ-α {x} {y} (a ∷ as) ys =
      (f ♯) (L.[ a ] ++ (as ++ x ∷ y ∷ ys)) ≡⟨ ♯-++ f L.[ a ] (as ++ x ∷ y ∷ ys) ⟩
      (f ♯) L.[ a ] 𝔜.⊕ (f ♯) (as ++ x ∷ y ∷ ys) ≡⟨ cong ((f ♯) L.[ a ] 𝔜.⊕_) (♯-≅ₚ-α as ys) ⟩
      (f ♯) L.[ a ] 𝔜.⊕ (f ♯) (as ++ y ∷ x ∷ ys) ≡⟨ sym (♯-++ f L.[ a ] (as ++ y ∷ x ∷ ys)) ⟩
      (f ♯) (L.[ a ] ++ (as ++ y ∷ x ∷ ys)) ≡⟨⟩
      (f ♯) ((a ∷ as) ++ y ∷ x ∷ ys) ∎

    ♯-≅ₚ : ∀ {xs zs} -> Perm xs zs -> (f ♯) xs ≡ (f ♯) zs
    ♯-≅ₚ perm-refl = refl
    ♯-≅ₚ (perm-swap {xs = xs} p) = ♯-≅ₚ-α xs _ ∙ ♯-≅ₚ p

    _♯ₚ : PList A -> 𝔜 .car    
    Q.[ as ] ♯ₚ = (f ♯) as
    eq/ as bs r i ♯ₚ = P.rec (isSet𝔜 _ _) (♯-≅ₚ {as} {bs}) r i
    squash/ xs ys p q i j ♯ₚ = isSet𝔜 (xs ♯ₚ) (ys ♯ₚ) (cong _♯ₚ p) (cong _♯ₚ q) i j

plist-sat : ∀ {n} {X : Type n} -> < PList X , plist-α > ⊨ M.CMonSEq
plist-sat (M.`mon M.`unitl) ρ = ⊕-unitl (ρ fzero)
plist-sat (M.`mon M.`unitr) ρ = ⊕-unitr (ρ fzero)
plist-sat (M.`mon M.`assocr) ρ = ⊕-assocr (ρ fzero) (ρ fone) (ρ ftwo)
plist-sat M.`comm ρ = ⊕-comm (ρ fzero) (ρ fone)
 