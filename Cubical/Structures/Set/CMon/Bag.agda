{-# OPTIONS --cubical #-}

-- Definition taken from https://drops.dagstuhl.de/opus/volltexte/2023/18395/pdf/LIPIcs-ITP-2023-20.pdf
module Cubical.Structures.Set.CMon.Bag where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List renaming (_∷_ to _∷ₗ_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
import Cubical.Data.Empty as ⊥

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Set.Mon.Array as A
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity hiding (_/_)
open import Cubical.Structures.Set.CMon.QFreeMon
open import Cubical.Relation.Nullary

open Iso

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ

_≈_ : ∀ {A : Type ℓ} -> Array A -> Array A -> Type ℓ
_≈_ (n , v) (m , w) = Σ[ σ ∈ Iso (Fin n) (Fin m) ] v ≡ w ∘ σ .fun

Bag≈ = _≈_

refl≈ : {as : Array A} -> as ≈ as
refl≈ {as = as} = idIso , refl

sym≈ : {as bs : Array A} -> as ≈ bs -> bs ≈ as
sym≈ {as = (n , f)} {bs = (m , g)} (σ , p) =
  invIso σ , congS (g ∘_) (sym (funExt (σ .rightInv)))
           ∙ congS (_∘ σ .inv) (sym p)

trans≈ : {as bs cs : Array A} -> as ≈ bs -> bs ≈ cs -> as ≈ cs
trans≈ {as = (n , f)} {bs = (m , g)} {cs = (o , h)} (σ , p) (τ , q) =
  compIso σ τ , sym
    ((h ∘ τ .fun) ∘ σ .fun ≡⟨ congS (_∘ σ .fun) (sym q) ⟩
    g ∘ σ .fun ≡⟨ sym p ⟩
    f ∎)

Fin+-cong : {n m n' m' : ℕ} -> Iso (Fin n) (Fin n') -> Iso (Fin m) (Fin m') -> Iso (Fin (n + m)) (Fin (n' + m'))
Fin+-cong {n} {m} {n'} {m'} σ τ =
  compIso (Fin≅Fin+Fin n m) (compIso (⊎Iso σ τ) (invIso (Fin≅Fin+Fin n' m')))

⊎Iso-eta : {A B A' B' : Type ℓ} {C : Type ℓ'} (f : A' -> C) (g : B' -> C)
        -> (σ : Iso A A') (τ : Iso B B')
        -> ⊎.rec (f ∘ σ .fun) (g ∘ τ .fun) ≡ ⊎.rec f g ∘ ⊎Iso σ τ .fun
⊎Iso-eta f g σ τ = ⊎-eta (⊎.rec f g ∘ ⊎Iso σ τ .fun) refl refl

⊎Swap-eta : {A B : Type ℓ} {C : Type ℓ'} (f : A -> C) (g : B -> C)
        -> ⊎.rec f g ≡ ⊎.rec g f ∘ ⊎-swap-Iso .fun
⊎Swap-eta f g = ⊎-eta (⊎.rec g f ∘ ⊎-swap-Iso .fun) refl refl

cong≈ : {as bs cs ds : Array A} -> as ≈ bs -> cs ≈ ds -> (as ⊕ cs) ≈ (bs ⊕ ds)
cong≈ {as = n , f} {bs = n' , f'} {m , g} {m' , g'} (σ , p) (τ , q) =
  Fin+-cong σ τ ,
  (
    combine n m f g
  ≡⟨ cong₂ (combine n m) p q ⟩
    combine n m (f' ∘ σ .fun) (g' ∘ τ .fun)
  ≡⟨⟩
    ⊎.rec (f' ∘ σ .fun) (g' ∘ τ .fun) ∘ finSplit n m
  ≡⟨ congS (_∘ finSplit n m) (⊎Iso-eta f' g' σ τ) ⟩
    ⊎.rec f' g' ∘ ⊎Iso σ τ .fun ∘ finSplit n m
  ≡⟨⟩
    ⊎.rec f' g' ∘ idfun _ ∘ ⊎Iso σ τ .fun ∘ finSplit n m
  ≡⟨ congS (\h -> ⊎.rec f' g' ∘ h ∘ ⊎Iso σ τ .fun ∘ finSplit n m) (sym (funExt (Fin≅Fin+Fin n' m' .rightInv))) ⟩
    ⊎.rec f' g' ∘ (Fin≅Fin+Fin n' m' .fun ∘ Fin≅Fin+Fin n' m' .inv) ∘ ⊎Iso σ τ .fun ∘ finSplit n m
  ≡⟨⟩
    (⊎.rec f' g' ∘ Fin≅Fin+Fin n' m' .fun) ∘ (Fin≅Fin+Fin n' m' .inv ∘ ⊎Iso σ τ .fun ∘ finSplit n m)
  ≡⟨⟩
    combine n' m' f' g' ∘ Fin+-cong σ τ .fun
  ∎)

Fin+-comm : (n m : ℕ) -> Iso (Fin (n + m)) (Fin (m + n))
Fin+-comm n m = compIso (Fin≅Fin+Fin n m) (compIso ⊎-swap-Iso (invIso (Fin≅Fin+Fin m n)))

comm≈ : {as bs : Array A} -> (as ⊕ bs) ≈ (bs ⊕ as)
comm≈ {as = n , f} {bs = m , g} =
  Fin+-comm n m , sym
    (
      ⊎.rec g f ∘ finSplit m n ∘ Fin≅Fin+Fin m n .inv ∘ ⊎-swap-Iso .fun ∘ Fin≅Fin+Fin n m .fun
    ≡⟨⟩
      ⊎.rec g f ∘ (Fin≅Fin+Fin m n .fun ∘ Fin≅Fin+Fin m n .inv) ∘ ⊎-swap-Iso .fun ∘ Fin≅Fin+Fin n m .fun
    ≡⟨ congS (λ h -> ⊎.rec g f ∘ h ∘ ⊎-swap-Iso .fun ∘ Fin≅Fin+Fin n m .fun) (funExt (Fin≅Fin+Fin m n .rightInv)) ⟩
      ⊎.rec g f ∘ ⊎-swap-Iso .fun ∘ Fin≅Fin+Fin n m .fun
    ≡⟨ congS (_∘ Fin≅Fin+Fin n m .fun) (sym (⊎Swap-eta f g)) ⟩
      ⊎.rec f g ∘ Fin≅Fin+Fin n m .fun
    ∎)

fpred : ∀ {n} -> Fin (suc (suc n)) -> Fin (suc n)
fpred (zero , p) = fzero
fpred (suc w , p) = w , pred-≤-pred p

fsuc∘fpred : ∀ {n} -> (x : Fin (suc (suc n))) -> ¬ x ≡ fzero -> fsuc (fpred x) ≡ x
fsuc∘fpred (zero , p) q = ⊥.rec (q (Fin-fst-≡ refl))
fsuc∘fpred (suc k , p) q = Fin-fst-≡ refl

fpred∘fsuc : ∀ {n} -> (x : Fin (suc n)) -> fpred (fsuc x) ≡ x
fpred∘fsuc (k , p) = Fin-fst-≡ refl

isoFunInv : ∀ {A B : Type ℓ} {x y} -> (σ : Iso A B) -> σ .fun x ≡ y -> σ .inv y ≡ x
isoFunInv σ p = congS (σ .inv) (sym p) ∙ σ .leftInv _

isoFunInvContra : ∀ {A B : Type ℓ} {x y z} -> (σ : Iso A B) -> σ .fun x ≡ y -> ¬ (z ≡ y) -> ¬ (σ .inv z ≡ x)
isoFunInvContra σ p z≠y q = z≠y (sym (σ .rightInv _) ∙ congS (σ .fun) q ∙ p)

autInvIs0 : ∀ {n} -> (σ : Iso (Fin (suc (suc n))) (Fin (suc (suc n))))
          -> σ .fun fzero ≡ fzero -> σ .inv fzero ≡ fzero
autInvIs0 = isoFunInv

autSucNot0 : ∀ {n} -> (σ : Iso (Fin (suc (suc n))) (Fin (suc (suc n))))
          -> (x : Fin (suc n)) -> σ .fun fzero ≡ fzero -> ¬ σ .fun (fsuc x) ≡ fzero
autSucNot0 σ x p = isoFunInvContra (invIso σ) (isoFunInv σ p) (snotz ∘ congS fst)

punchOutZero : ∀ {n} (σ : Iso (Fin (suc (suc n))) (Fin (suc (suc n)))) -> σ .fun fzero ≡ fzero
              -> Iso (Fin (suc n)) (Fin (suc n))
punchOutZero {n = n} σ p =
  iso (punch σ) (punch (invIso σ)) (punch∘punch σ p) (punch∘punch (invIso σ) (autInvIs0 σ p))
  where
  punch : Iso (Fin (suc (suc n))) (Fin (suc (suc n))) -> Fin (suc n) -> Fin (suc n)
  punch σ = fpred ∘ σ .fun ∘ fsuc
  punch∘punch : (σ : Iso (Fin (suc (suc n))) (Fin (suc (suc n))))
              -> σ .fun fzero ≡ fzero
              -> (x : Fin (suc n))
              -> punch σ (punch (invIso σ) x) ≡ x
  punch∘punch σ p x =
      punch σ (punch (invIso σ) x)
    ≡⟨⟩
      fpred (σ .fun ((fsuc ∘ fpred) (σ .inv (fsuc x))))
    ≡⟨ congS (fpred ∘ σ .fun) (fsuc∘fpred (σ .inv (fsuc x)) (autSucNot0 (invIso σ) x (autInvIs0 σ p))) ⟩
      fpred (σ .fun (σ .inv (fsuc x)))
    ≡⟨ congS fpred (σ .rightInv (fsuc x)) ⟩
      fpred (fsuc x)
    ≡⟨ fpred∘fsuc x ⟩
      x ∎

punchOutZero≡fsuc : ∀ {n} (σ : Iso (Fin (suc (suc n))) (Fin (suc (suc n)))) -> (σ-0≡0 : σ .fun fzero ≡ fzero)
                  -> (w : Fin (suc n)) -> σ .fun (fsuc w) ≡ fsuc (punchOutZero σ σ-0≡0 .fun w)
punchOutZero≡fsuc σ σ-0≡0 w = sym (fsuc∘fpred _ (autSucNot0 σ w σ-0≡0))

finSubst : ∀ {n m} -> n ≡ m -> Fin n -> Fin m
finSubst {n = n} {m = m} p (k , q) = k , (subst (k <_) p q)

Fin≅ : ∀ {n m} -> n ≡ m -> Iso (Fin n) (Fin m)
Fin≅ {n = n} {m = m} p = iso
  (finSubst p)
  (finSubst (sym p))
  (λ (k , q) -> Fin-fst-≡ refl)
  (λ (k , q) -> Fin-fst-≡ refl)

Fin≅-inj : {n m : ℕ} -> Iso (Fin n) (Fin m) -> n ≡ m
Fin≅-inj {n = n} {m = m} σ = Fin-inj n m (isoToPath σ)

≈-fsuc-on-0 : ∀ n m
          -> (f : Fin (suc (suc n)) -> A) (g : Fin (suc (suc m)) -> A)
          -> (r : (suc (suc n) , f) ≈ (suc (suc m) , g))
          -> (r .fst) .fun fzero ≡ fzero
          -> (suc n , f ∘ fsuc) ≈ (suc m , g ∘ fsuc)
≈-fsuc-on-0 n m f g (σ , p) q =
  compIso (Fin≅ (injSuc (Fin≅-inj σ))) (punchOutZero τ lemma-α) , sym (funExt lemma-β)
  where
  τ : _
  τ = compIso (Fin≅ (sym (Fin≅-inj σ))) σ
  lemma-α : _
  lemma-α =
    σ .fun (finSubst (sym (Fin≅-inj σ)) fzero) ≡⟨⟩
    σ .fun (0 , _) ≡⟨ congS (σ .fun) (Fin-fst-≡ refl) ⟩
    σ .fun fzero ≡⟨ q ⟩
    fzero ∎
  lemma-β : _
  lemma-β (k , r) =
      g (fsuc ((punchOutZero τ lemma-α) .fun ((Fin≅ (injSuc (Fin≅-inj σ))) .fun (k , r))))
    ≡⟨⟩
      g (fsuc ((punchOutZero τ lemma-α) .fun (k , _)))
    ≡⟨ congS g (sym (punchOutZero≡fsuc τ lemma-α (k , _))) ⟩
      g (τ .fun (fsuc (k , _)))
    ≡⟨ congS (g ∘ σ .fun) (Fin-fst-≡ refl) ⟩
      g (σ .fun (fsuc (k , r)))
    ≡⟨ congS (λ h -> h (fsuc (k , r))) (sym p) ⟩
      f (fsuc (k , r)) ∎

≈-length : {n m : ℕ} -> Iso (Fin n) (Fin m) -> n ≡ m 
≈-length {n = n} {m = m} σ = Fin-inj n m (isoToPath σ)

module _ {n} (σ : Iso (Fin (suc n)) (Fin (suc n))) where
  private
    m : ℕ
    m = suc n

    cutoff : ℕ
    cutoff = (σ .inv fzero) .fst

    cutoff< : cutoff < m
    cutoff< = (σ .inv fzero) .snd

    cutoff+- : cutoff + (m ∸ cutoff) ≡ m
    cutoff+- = ∸-lemma (<-weaken cutoff<)

    0<m-cutoff : 0 < m ∸ cutoff
    0<m-cutoff = n∸l>0 m cutoff cutoff<

  swapAut : Iso (Fin (suc n)) (Fin (suc n))
  swapAut = compIso (Fin≅ (sym cutoff+- ∙ +-comm cutoff _)) (compIso (Fin+-comm (m ∸ cutoff) cutoff) (compIso (Fin≅ cutoff+-) σ))

  swapAut0≡0 : swapAut .fun fzero ≡ fzero
  swapAut0≡0 =
      σ .fun (finSubst cutoff+- (⊎.rec finCombine-inl finCombine-inr (fun ⊎-swap-Iso (finSplit (m ∸ cutoff) cutoff (0 , _)))))
    ≡⟨ congS (λ z -> σ .fun (finSubst cutoff+- (⊎.rec (finCombine-inl {m = cutoff}) (finCombine-inr {m = cutoff}) (fun ⊎-swap-Iso z)))) (finSplit-beta-inl 0 0<m-cutoff _) ⟩
      σ .fun (σ .inv fzero .fst + 0 , _)
    ≡⟨ congS (σ .fun) (Fin-fst-≡ (+-zero (σ .inv (0 , suc-≤-suc zero-≤) .fst) ∙ congS (fst ∘ σ .inv) (Fin-fst-≡ refl))) ⟩
      σ .fun (σ .inv fzero)
    ≡⟨ σ .rightInv fzero ⟩
      fzero ∎

module _ {ℓA ℓB} {A : Type ℓA} {𝔜 : struct ℓB M.MonSig} (isSet𝔜 : isSet (𝔜 .car)) (𝔜-cmon : 𝔜 ⊨ M.CMonSEq) (f : A -> 𝔜 .car) where
  module 𝔜 = M.CMonSEq 𝔜 𝔜-cmon

  f♯-hom = ArrayDef.Free.ext arrayDef isSet𝔜 (M.cmonSatMon 𝔜-cmon) f

  f♯ : Array A -> 𝔜 .car
  f♯ = f♯-hom .fst

  f♯-η : (a : A) -> f♯ (η a) ≡ f a
  f♯-η a i = ArrayDef.Free.ext-η arrayDef isSet𝔜 (M.cmonSatMon 𝔜-cmon) f i a

  f♯-hom-⊕ : (as bs : Array A) -> f♯ (as ⊕ bs) ≡ f♯ as 𝔜.⊕ f♯ bs
  f♯-hom-⊕ as bs =
    f♯ (as ⊕ bs) ≡⟨ sym ((f♯-hom .snd) M.`⊕ ⟪ as ⨾ bs ⟫) ⟩
    𝔜 .alg (M.`⊕ , (λ w -> f♯ (⟪ as ⨾ bs ⟫ w))) ≡⟨ 𝔜.⊕-eta ⟪ as ⨾ bs ⟫ f♯ ⟩
    f♯ as 𝔜.⊕ f♯ bs ∎

  f♯-comm : (as bs : Array A) -> f♯ (as ⊕ bs) ≡ f♯ (bs ⊕ as)
  f♯-comm as bs =
    f♯ (as ⊕ bs) ≡⟨ f♯-hom-⊕ as bs ⟩
    f♯ as 𝔜.⊕ f♯ bs ≡⟨ 𝔜.comm (f♯ as) (f♯ bs) ⟩
    f♯ bs 𝔜.⊕ f♯ as ≡⟨ sym (f♯-hom-⊕ bs as) ⟩
    f♯ (bs ⊕ as) ∎

  swapAutToAut : ∀ {n} (zs : Fin (suc (suc n)) -> A) (σ : Iso (Fin (suc (suc n))) (Fin (suc (suc n))))
               -> f♯ (suc (suc n) , zs ∘ swapAut σ .fun) ≡ f♯ (suc (suc n) , zs ∘ σ .fun)
  swapAutToAut {n = n} zs σ =
      f♯ (m , zs ∘ swapAut σ .fun)
    ≡⟨ congS f♯ lemma-α ⟩
      f♯ (((m ∸ cutoff) , (zs ∘ σ .fun ∘ finSubst cutoff+- ∘ finCombine cutoff _ ∘ inr))
        ⊕ (cutoff , (zs ∘ σ .fun ∘ finSubst cutoff+- ∘ finCombine cutoff _ ∘ inl)))
    ≡⟨ f♯-comm ((m ∸ cutoff) , (zs ∘ σ .fun ∘ finSubst cutoff+- ∘ finCombine cutoff _ ∘ inr)) _ ⟩
      f♯ ((cutoff , (zs ∘ σ .fun ∘ finSubst cutoff+- ∘ finCombine cutoff _ ∘ inl))
        ⊕ ((m ∸ cutoff) , (zs ∘ σ .fun ∘ finSubst cutoff+- ∘ finCombine cutoff _ ∘ inr)))
    ≡⟨ congS f♯ lemma-β ⟩
      f♯ (m , zs ∘ σ .fun) ∎
    where
    m : ℕ
    m = suc (suc n)

    cutoff : ℕ
    cutoff = (σ .inv fzero) .fst

    cutoff< : cutoff < m
    cutoff< = (σ .inv fzero) .snd

    cutoff+- : cutoff + (m ∸ cutoff) ≡ m
    cutoff+- = ∸-lemma (<-weaken cutoff<)

    lemma-α : Path (Array A) (m , zs ∘ swapAut σ .fun) ((m ∸ cutoff) + cutoff , _)
    lemma-α = Array≡ (sym cutoff+- ∙ +-comm cutoff _) λ k k<m∸cutoff+cutoff -> ⊎.rec
      (λ k<m∸cutoff ->
          zs (σ .fun (finSubst cutoff+- (⊎.rec finCombine-inl finCombine-inr (fun ⊎-swap-Iso (finSplit (m ∸ cutoff) cutoff (k , _))))))
        ≡⟨ congS (λ z -> zs (σ .fun (finSubst cutoff+- (⊎.rec (finCombine-inl {m = cutoff}) finCombine-inr (fun ⊎-swap-Iso z))))) (finSplit-beta-inl k k<m∸cutoff _) ⟩
          zs (σ .fun (cutoff + k , _))
        ≡⟨ congS (zs ∘ σ .fun) (Fin-fst-≡ refl) ⟩
          zs (σ .fun (finSubst cutoff+- (finCombine cutoff (m ∸ cutoff) (inr (k , k<m∸cutoff)))))
        ≡⟨⟩
          ⊎.rec
            (zs ∘ σ .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inr)
            (zs ∘ σ .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inl)
            (inl (k , k<m∸cutoff))
        ≡⟨ congS (⊎.rec _ _) (sym (finSplit-beta-inl k k<m∸cutoff k<m∸cutoff+cutoff)) ⟩
          ⊎.rec
            (zs ∘ σ .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inr)
            (zs ∘ σ .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inl)
            (finSplit (m ∸ cutoff) cutoff (k , k<m∸cutoff+cutoff))
      ∎)
      (λ m∸cutoff≤k ->
          zs (σ .fun (finSubst cutoff+- (⊎.rec finCombine-inl finCombine-inr (fun ⊎-swap-Iso (finSplit (m ∸ cutoff) cutoff (k , _))))))
        ≡⟨ congS (λ z -> zs (σ .fun (finSubst cutoff+- (⊎.rec (finCombine-inl {m = cutoff}) finCombine-inr (fun ⊎-swap-Iso z))))) (finSplit-beta-inr k _ m∸cutoff≤k (∸-<-lemma (m ∸ cutoff) cutoff k k<m∸cutoff+cutoff m∸cutoff≤k)) ⟩
          zs (σ .fun (finSubst cutoff+- (finCombine-inl (k ∸ (m ∸ cutoff) , ∸-<-lemma (m ∸ cutoff) cutoff k k<m∸cutoff+cutoff m∸cutoff≤k))))
        ≡⟨ congS (zs ∘ σ .fun ∘ finSubst cutoff+-) (Fin-fst-≡ refl) ⟩
          zs (σ .fun (finSubst cutoff+- (finCombine cutoff (m ∸ cutoff) (inl (k ∸ (m ∸ cutoff) , ∸-<-lemma (m ∸ cutoff) cutoff k k<m∸cutoff+cutoff m∸cutoff≤k)))))
        ≡⟨ congS (⊎.rec _ _) (sym (finSplit-beta-inr k k<m∸cutoff+cutoff m∸cutoff≤k (∸-<-lemma (m ∸ cutoff) cutoff k k<m∸cutoff+cutoff m∸cutoff≤k))) ⟩
          ⊎.rec
            (zs ∘ σ .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inr)
            (zs ∘ σ .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inl)
            (finSplit (m ∸ cutoff) cutoff (k , k<m∸cutoff+cutoff))
      ∎)
      (k ≤? (m ∸ cutoff))
    
    lemma-β : Path (Array A) (cutoff + (m ∸ cutoff) , _) (m , zs ∘ σ .fun)
    lemma-β = Array≡ cutoff+- λ k k<m -> ⊎.rec
      (λ k<cutoff ->
          ⊎.rec
            (zs ∘ σ .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inl)
            (zs ∘ σ .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inr)
            (finSplit cutoff (m ∸ cutoff) (k , _))
        ≡⟨ congS (⊎.rec _ _) (finSplit-beta-inl k k<cutoff _) ⟩
          ⊎.rec  
            (zs ∘ σ .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inl)
            (zs ∘ σ .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inr)
            (inl (k , _))
        ≡⟨⟩
          zs (σ .fun (finSubst cutoff+- (finCombine cutoff (m ∸ cutoff) (inl (k , _)))))
        ≡⟨ congS (zs ∘ σ .fun) (Fin-fst-≡ refl) ⟩
          zs (σ .fun (k , k<m))
      ∎)
      (λ cutoff≤k ->
          ⊎.rec
            (zs ∘ σ .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inl)
            (zs ∘ σ .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inr)
            (finSplit cutoff (m ∸ cutoff) (k , _))
        ≡⟨ congS (⊎.rec _ _) (finSplit-beta-inr k _ cutoff≤k (<-∸-< k m cutoff k<m cutoff<)) ⟩
          ⊎.rec
            (zs ∘ σ .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inl)
            (zs ∘ σ .fun ∘ finSubst cutoff+- ∘ finCombine cutoff (m ∸ cutoff) ∘ inr)
            (inr (k ∸ cutoff , _))
        ≡⟨⟩
          zs (σ .fun (finSubst cutoff+- (finCombine cutoff (m ∸ cutoff) (inr (k ∸ cutoff , _)))))
        ≡⟨ congS (zs ∘ σ .fun) (Fin-fst-≡ (+-comm cutoff (k ∸ cutoff) ∙ ≤-∸-+-cancel cutoff≤k)) ⟩
          zs (σ .fun (k , k<m))
      ∎)
      (k ≤? cutoff)

  permuteInvariant : ∀ n (zs : Fin n -> A) (σ : Iso (Fin n) (Fin n)) -> f♯ (n , zs ∘ σ .fun) ≡ f♯ (n , zs)
  permuteInvariant zero zs σ =
    congS f♯ (Array≡ {f = zs ∘ σ .fun} {g = zs} refl \k k<0 -> ⊥.rec (¬-<-zero k<0))
  permuteInvariant (suc zero) zs σ =
    congS f♯ (Array≡ {f = zs ∘ σ .fun} {g = zs} refl \k k<1 -> congS zs (isContr→isProp isContrFin1 _ _))
  permuteInvariant (suc (suc n)) zs σ =
    let τ = swapAut σ ; τ-0≡0 = swapAut0≡0 σ
        IH = permuteInvariant (suc n) (zs ∘ fsuc) (punchOutZero τ τ-0≡0)
    in
      f♯ (suc (suc n) , zs ∘ σ .fun)
    ≡⟨ sym (swapAutToAut zs σ) ⟩
      f♯ (suc (suc n) , zs ∘ τ .fun)
    ≡⟨ permuteInvariantOnZero τ τ-0≡0 IH ⟩
      f♯ (suc (suc n) , zs) ∎
      where
        permuteInvariantOnZero : (τ : Iso (Fin (suc (suc n))) (Fin (suc (suc n)))) (τ-0≡0 : τ .fun fzero ≡ fzero) -> (IH : _)
                              -> f♯ (suc (suc n) , zs ∘ τ .fun) ≡ f♯ (suc (suc n) , zs)
        permuteInvariantOnZero τ τ-0≡0 IH =
            f♯ (suc (suc n) , zs ∘ τ .fun)
          ≡⟨⟩
            f (zs (τ .fun fzero)) 𝔜.⊕ f♯ (suc n , zs ∘ τ .fun ∘ fsuc)
          ≡⟨ congS (\z -> f (zs z) 𝔜.⊕ f♯ (suc n , zs ∘ τ .fun ∘ fsuc)) (Fin-fst-≡ (congS fst τ-0≡0)) ⟩
            f (zs fzero) 𝔜.⊕ f♯ (suc n , zs ∘ τ .fun ∘ fsuc)
          ≡⟨ congS (\z -> f (zs fzero) 𝔜.⊕ f♯ z)
                   (Array≡ {f = zs ∘ τ .fun ∘ fsuc} refl \k k≤n ->
                           congS (zs ∘ τ .fun ∘ fsuc) (Fin-fst-≡ refl) ∙ congS zs (punchOutZero≡fsuc τ τ-0≡0 (k , k≤n))) ⟩
            f (zs fzero) 𝔜.⊕ f♯ (suc n , zs ∘ fsuc ∘ punchOutZero τ τ-0≡0 .fun)
          ≡⟨ cong₂ 𝔜._⊕_ (sym (f♯-η (zs fzero))) IH ⟩
            f♯ (η (zs fzero)) 𝔜.⊕ f♯ (suc n , zs ∘ fsuc)
          ≡⟨ sym (f♯-hom-⊕ (η (zs fzero)) (suc n , zs ∘ fsuc)) ⟩
            f♯ (η (zs fzero) ⊕ (suc n , zs ∘ fsuc))
          ≡⟨ congS f♯ (η+fsuc zs) ⟩
            f♯ (suc (suc n) , zs)
          ∎

  ≈-resp-♯ : {as bs : Array A} -> as ≈ bs -> f♯ as ≡ f♯ bs
  ≈-resp-♯ {as = n , g} {bs = m , h} (σ , p) =
      f♯ (n , g)
    ≡⟨ congS (λ z -> f♯ (n , z)) p ⟩
      f♯ (n , h ∘ σ .fun)
    ≡⟨ congS f♯ (Array≡ n≡m λ _ _ -> refl) ⟩
      f♯ (m , h ∘ σ .fun ∘ (Fin≅ (sym n≡m)) .fun)
    ≡⟨⟩
      f♯ (m , h ∘ (compIso (Fin≅ (sym n≡m)) σ) .fun)
    ≡⟨ permuteInvariant m h (compIso (Fin≅ (sym n≡m)) σ) ⟩
      f♯ (m , h) ∎
    where
    n≡m : n ≡ m
    n≡m = Fin≅-inj σ

module _ {ℓ} (A : Type ℓ) where
  open import Cubical.Relation.Binary
  module P = BinaryRelation {A = Array A} _≈_
  module R = isPermRel

  isPermRelPerm : isPermRel arrayDef (_≈_ {A = A})
  P.isEquivRel.reflexive (R.isEquivRel isPermRelPerm) _ = refl≈
  P.isEquivRel.symmetric (R.isEquivRel isPermRelPerm) _ _ = sym≈
  P.isEquivRel.transitive (R.isEquivRel isPermRelPerm) _ _ cs = trans≈ {cs = cs}
  R.isCongruence isPermRelPerm {as} {bs} {cs} {ds} p q = cong≈ p q
  R.isCommutative isPermRelPerm = comm≈
  R.resp-♯ isPermRelPerm {isSet𝔜 = isSet𝔜} 𝔜-cmon f p = ≈-resp-♯ isSet𝔜 𝔜-cmon f p

  PermRel : PermRelation arrayDef A
  PermRel = _≈_ , isPermRelPerm

module BagDef = F.Definition M.MonSig M.CMonEqSig M.CMonSEq

bagFreeDef : ∀ {ℓ} -> BagDef.Free ℓ ℓ 2
bagFreeDef = qFreeMonDef (PermRel _)

Bag : Type ℓ -> Type ℓ
Bag A = BagDef.Free.F bagFreeDef A

-- Proof taken from https://arxiv.org/pdf/2110.05412.pdf
module IsoToCList {ℓ} (A : Type ℓ) where
  open import Cubical.Structures.Set.CMon.CList as CL
  open import Cubical.HITs.SetQuotients as Q

  module 𝔅 = M.CMonSEq < Bag A , BagDef.Free.α bagFreeDef > (BagDef.Free.sat bagFreeDef)
  module ℭ = M.CMonSEq < CList A , clist-α > clist-sat

  fromCList : CList A -> Bag A
  fromCList = CL.Free._♯ squash/ (BagDef.Free.sat bagFreeDef) (BagDef.Free.η bagFreeDef)

  tabulate' : ∀ n -> (Fin n -> A) -> CList A
  tabulate' zero ^a = []
  tabulate' (suc n) ^a = ^a fzero ∷ tabulate' n (^a ∘ fsuc)

  except : ∀ {o} -> Fin (suc o) -> (Fin o -> Fin (suc o))
  except (t , r) (j , s) with j ≤? t
  ... | inl _ = j , <-trans s (0 , refl)
  ... | inr _ = fsuc (j , s)

  except-suc≡ : ∀ {t o : ℕ} (p : suc t < suc (suc o))
              -> (x : Fin o)
              -> except ((suc t , p)) (fsuc x) ≡ fsuc (except (t , pred-≤-pred p) x)
  except-suc≡ {t = t} _ (k , p) with suc k ≤? suc t | k ≤? t
  ... | inl q | inl r = Σ≡Prop (λ _ -> isProp≤) refl
  ... | inr q | inr r = Σ≡Prop (λ _ -> isProp≤) refl
  ... | inr q | inl r = ⊥.rec (<-asym q r)
  ... | inl q | inr r = ⊥.rec (<-asym q (suc-≤-suc r))

  {-# TERMINATING #-}
  toCList-eq : ∀ n m
             -> (f : Fin n -> A) (g : Fin m -> A) (r : (n , f) ≈ (m , g))
             -> tabulate' n f ≡ tabulate' m g
  toCList-eq (suc n) zero f g (σ , p) = ⊥.rec (snotz (≈-length σ))
  toCList-eq zero (suc zero) f g (σ , p) = ⊥.rec (znots (≈-length σ))
  toCList-eq (suc (suc n)) (suc zero) f g (σ , p) = ⊥.rec (snotz (injSuc (≈-length σ)))
  toCList-eq zero (suc (suc m)) f g (σ , p) = ⊥.rec (znots (≈-length σ))
  toCList-eq (suc zero) (suc (suc m)) f g (σ , p) = ⊥.rec (znots (injSuc (≈-length σ))) 
  toCList-eq zero zero f g (σ , p) = refl
  toCList-eq (suc zero) (suc zero) f g (σ , p) =
    f fzero ∷ [] ≡⟨ congS (λ h -> h fzero ∷ []) p ⟩
    g (σ .fun fzero) ∷ [] ≡⟨ congS (λ z -> g z ∷ []) (isContr→isProp isContrFin1 _ _) ⟩
    g fzero ∷ [] ∎
  toCList-eq (suc (suc n)) (suc (suc m)) f g (σ , p) with σ .fun fzero | inspect (σ .fun) fzero
  ... | zero , q | [ σ-path ]ᵢ =
      f fzero ∷ tabulate' (suc n) (f ∘ fsuc)
    ≡⟨ congS (λ h -> h fzero ∷ tabulate' (suc n) (f ∘ fsuc)) p ⟩
      g (σ .fun fzero) ∷ tabulate' (suc n) (f ∘ fsuc)
    ≡⟨ congS (λ z -> g z ∷ tabulate' (suc n) (f ∘ fsuc)) σ-path ⟩
      g (zero , q) ∷ tabulate' (suc n) (f ∘ fsuc)
    ≡⟨ cong₂ _∷_ (congS g (Σ≡Prop (λ _ -> isProp≤) refl)) (toCList-eq (suc n) (suc m) (f ∘ fsuc) (g ∘ fsuc) (≈-fsuc-on-0 n m f g (σ , p) σ-zero)) ⟩
      g fzero ∷ tabulate' (suc m) (g ∘ fsuc)
    ≡⟨⟩
      tabulate' (suc (suc m)) g ∎
    where
    σ-zero : σ .fun fzero ≡ fzero
    σ-zero = σ-path ∙ Σ≡Prop (λ _ -> isProp≤) refl
  ... | suc k , q | [ σ-path ]ᵢ =
    comm (f fzero) (g fzero) tail lemma-α lemma-β
    where
    n≡m : n ≡ m
    n≡m = injSuc (injSuc (≈-length σ))

    k<sucn : k < suc n
    k<sucn = subst (k <_) (congS suc (sym n≡m)) (pred-≤-pred q)

    tail : CList A
    tail = tabulate' n (g ∘ fsuc ∘ finSubst (congS suc n≡m) ∘ except (k , k<sucn))

    aut-α : (suc n , f ∘ fsuc) ≈ (suc m , g ∘ except (σ .fun fzero))
    aut-α = {!   !}

    lemma-α-γ : ∀ x (r : x < n)
              -> fst (except (k , pred-≤-pred q) (x , subst (_<_ x) n≡m r))
               ≡ fst (except (k , k<sucn) (x , r))
    lemma-α-γ x r with x ≤? k
    ... | inl s = refl
    ... | inr s = refl

    lemma-γ : _
    lemma-γ (x , r) =
        _
      ≡⟨ sym (transport-filler _ _) ⟩
        g (fsuc (except (k , pred-≤-pred q) (finSubst n≡m (x , r))))
      ≡⟨ congS (g ∘ fsuc) (Σ≡Prop (λ _ -> isProp≤) (lemma-α-γ x r)) ⟩
        g (fsuc (finSubst (λ i → suc (n≡m i)) (except (k , k<sucn) (x , r)))) ∎

    lemma-α : tabulate' (suc n) (f ∘ fsuc) ≡ g fzero ∷ tail
    lemma-α =
        tabulate' (suc n) (f ∘ fsuc)
      ≡⟨ toCList-eq (suc n) (suc m) (f ∘ fsuc) (g ∘ except (σ .fun fzero)) aut-α ⟩
        g (except (σ .fun fzero) fzero) ∷ tabulate' m (g ∘ except (σ .fun fzero) ∘ fsuc)
      ≡⟨ congS (λ z -> g (except z fzero) ∷ tabulate' m (g ∘ except z ∘ fsuc)) σ-path ⟩
        g (zero , _) ∷ tabulate' m (g ∘ except (suc k , q) ∘ fsuc)
      ≡⟨ cong₂ (λ y z -> g y ∷ tabulate' m (g ∘ z)) (Σ≡Prop (λ _ -> isProp≤) refl) (funExt (except-suc≡ q)) ⟩
        g fzero ∷ tabulate' m (g ∘ fsuc ∘ except (k , pred-≤-pred q))
      ≡⟨ cong₂ (λ y z -> g fzero ∷ tabulate' y z) (sym n≡m) (toPathP (funExt lemma-γ)) ⟩
        g fzero ∷ tail ∎    

    apply-β-α : Fin (suc m) -> A
    apply-β-α (zero , r) = g (σ .fun fzero)
    apply-β-α (suc x , r) = g (fsuc (except (k , pred-≤-pred q) (x , pred-≤-pred r)))

    transform-β-α : Fin m -> Fin m
    transform-β-α (x , r) = x , pred-≤-pred (snd (fsuc (x , r)))

    transform-β-α≡id : transform-β-α ≡ idfun _
    transform-β-α≡id = funExt (λ _ -> Σ≡Prop (λ _ -> isProp≤) refl)

    aut-β : (suc m , g ∘ fsuc) ≈ (suc m , apply-β-α)
    aut-β = {!   !}

    lemma-β : tabulate' (suc m) (g ∘ fsuc) ≡ f fzero ∷ tail
    lemma-β =
        tabulate' (suc m) (g ∘ fsuc)
      ≡⟨ toCList-eq (suc m) (suc m) (g ∘ fsuc) apply-β-α aut-β ⟩
        tabulate' (suc m) apply-β-α
      ≡⟨⟩
        g (σ .fun fzero) ∷ tabulate' m (λ x → g (fsuc (except (k , pred-≤-pred q) (fst x , pred-≤-pred (snd (fsuc x))))))
      ≡⟨⟩
        g (σ .fun fzero) ∷ tabulate' m (g ∘ fsuc ∘ except (k , pred-≤-pred q) ∘ transform-β-α)
      ≡⟨ congS (λ z -> g (σ .fun fzero) ∷ tabulate' m (g ∘ fsuc ∘ except (k , pred-≤-pred q) ∘ z)) transform-β-α≡id ⟩
        g (σ .fun fzero) ∷ tabulate' m (g ∘ fsuc ∘ except (k , pred-≤-pred q))
      ≡⟨ congS (λ h -> h fzero ∷ tabulate' m (g ∘ fsuc ∘ except (k , pred-≤-pred q))) (sym p) ⟩
        f fzero ∷ tabulate' m (g ∘ fsuc ∘ except (k , pred-≤-pred q))
      ≡⟨ cong₂ (λ y z -> f fzero ∷ tabulate' y z) (sym n≡m) (toPathP (funExt lemma-γ)) ⟩
        f fzero ∷ tail ∎    

  toCList : Bag A -> CList A
  toCList Q.[ (n , f) ] = tabulate' n f
  toCList (eq/ (n , f) (m , g) r i) = toCList-eq n m f g r i
  toCList (squash/ xs ys p q i j) =
    isSetCList (toCList xs) (toCList ys) (congS toCList p) (congS toCList q) i j  
