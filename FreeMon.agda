{-# OPTIONS --cubical #-}

module FreeMon where

open import Cubical.Foundations.Everything
import Mon as M

data FreeMon (A : Type) : Type where
  η : (a : A) -> FreeMon A
  e : FreeMon A
  _⊕_ : FreeMon A -> FreeMon A -> FreeMon A
  unitl : ∀ m -> e ⊕ m ≡ m
  unitr : ∀ m -> m ⊕ e ≡ m
  assocr : ∀ m n o -> (m ⊕ n) ⊕ o ≡ m ⊕ (n ⊕ o)
  trunc : isSet (FreeMon A)

freeMon : (A : Type) -> M.MonStruct (FreeMon A)
M.MonStruct.e (freeMon A) = e
M.MonStruct._⊕_ (freeMon A) = _⊕_
M.MonStruct.unitl (freeMon A) = unitl
M.MonStruct.unitr (freeMon A) = unitr
M.MonStruct.assocr (freeMon A) = assocr
M.MonStruct.trunc (freeMon A) = trunc

module elimFreeMonSet {p : Level} {A : Type} (P : FreeMon A -> Type p)
                    (η* : (a : A) -> P (η a))
                    (e* : P e)
                    (_⊕*_ : {m n : FreeMon A} -> P m -> P n -> P (m ⊕ n))
                    (unitl* : {m : FreeMon A} (m* : P m) -> PathP (λ i → P (unitl m i)) (e* ⊕* m*) m*)
                    (unitr* : {m : FreeMon A} (m* : P m) -> PathP (λ i → P (unitr m i)) (m* ⊕* e*) m*)
                    (assocr* : {m n o : FreeMon A}
                               (m* : P m) ->
                               (n* : P n) ->
                               (o* : P o) -> PathP (λ i → P (assocr m n o i)) ((m* ⊕* n*) ⊕* o*) (m* ⊕* (n* ⊕* o*)))
                    (trunc* : {xs : FreeMon A} -> isSet (P xs))
                    where
  f : (x : FreeMon A) -> P x
  f (η a) = η* a
  f e = e*
  f (x ⊕ y) = f x ⊕* f y
  f (unitl x i) = unitl* (f x) i
  f (unitr x i) = unitr* (f x) i
  f (assocr x y z i) = assocr* (f x) (f y) (f z) i
  f (trunc xs ys p q i j) =
     isOfHLevel→isOfHLevelDep 2 (\xs -> trunc* {xs = xs}) (f xs) (f ys) (cong f p) (cong f q) (trunc xs ys p q) i j

module elimFreeMonProp {p : Level} {A : Type} (P : FreeMon A -> Type p)
                    (η* : (a : A) -> P (η a))
                    (e* : P e)
                    (_⊕*_ : {m n : FreeMon A} -> P m -> P n -> P (m ⊕ n))
                    (trunc* : {xs : FreeMon A} -> isProp (P xs))
                    where 
  f : (x : FreeMon A) -> P x
  f = elimFreeMonSet.f P η* e* _⊕*_ unitl* unitr* assocr* (isProp→isSet trunc*)
    where
      abstract
        unitl* : {m : FreeMon A} (m* : P m) -> PathP (λ i → P (unitl m i)) (e* ⊕* m*) m*
        unitl* {m} m* = toPathP (trunc* (transp (λ i -> P (unitl m i)) i0 (e* ⊕* m*)) m*)
        unitr* : {m : FreeMon A} (m* : P m) -> PathP (λ i → P (unitr m i)) (m* ⊕* e*) m*
        unitr* {m} m* = toPathP (trunc* (transp (λ i -> P (unitr m i)) i0 (m* ⊕* e*)) m*)
        assocr* : {m n o : FreeMon A}
                  (m* : P m) ->
                  (n* : P n) ->
                  (o* : P o) -> PathP (λ i → P (assocr m n o i)) ((m* ⊕* n*) ⊕* o*) (m* ⊕* (n* ⊕* o*))
        assocr* {m} {n} {o} m* n* o* =
          toPathP (trunc* (transp (λ i -> P (assocr m n o i)) i0 ((m* ⊕* n*) ⊕* o*)) (m* ⊕* (n* ⊕* o*)))


module _ {A B : Type} (M : M.MonStruct B) where
  module B = M.MonStruct M
  module _ (f : A -> B) where

    _♯ : FreeMon A -> B
    (_♯) (η a) = f a
    (_♯) e = B.e
    (_♯) (m ⊕ n) = (_♯) m B.⊕ (_♯) n
    (_♯) (unitl m i) = B.unitl ((_♯) m) i
    (_♯) (unitr m i) = B.unitr ((_♯) m) i
    (_♯) (assocr m n o i) = B.assocr ((_♯) m) ((_♯) n) ((_♯) o) i
    (_♯) (trunc m n p q i j) = B.trunc ((_♯) m) ((_♯) n) (cong (_♯) p) (cong (_♯) q) i j

    _♯-isMonHom : M.isMonHom (freeMon A) M _♯
    M.isMonHom.f-e _♯-isMonHom = refl
    M.isMonHom.f-⊕ _♯-isMonHom m n = refl

  private
    freeMonEquivLemma : (f : FreeMon A -> B) -> M.isMonHom (freeMon A) M f -> (x : FreeMon A) -> f x ≡ ((f ∘ η) ♯) x
    freeMonEquivLemma f homMonWit = elimFreeMonProp.f (λ x -> f x ≡ ((f ∘ η) ♯) x)
      (λ _ -> refl)
      (M.isMonHom.f-e homMonWit)
      (λ {m} {n} x y ->
        f (m ⊕ n) ≡⟨ M.isMonHom.f-⊕ homMonWit m n ⟩
        f m B.⊕ f n ≡⟨ cong (B._⊕ f n) x ⟩
        ((f ∘ η) ♯) m B.⊕ f n ≡⟨ cong (((f ∘ η) ♯) m B.⊕_) y ⟩
        ((f ∘ η) ♯) m B.⊕ ((f ∘ η) ♯) n
        ∎
      )
      (B.trunc _ _)
    
    freeMonEquivLemma-β : (f : FreeMon A -> B) -> M.isMonHom (freeMon A) M f -> ((f ∘ η) ♯) ≡ f
    freeMonEquivLemma-β f homMonWit i x = freeMonEquivLemma f homMonWit x (~ i)

  freeMonEquiv : M.MonHom (freeMon A) M ≃ (A -> B)
  freeMonEquiv = isoToEquiv (iso (\(f , ϕ) -> f ∘ η) (\f -> (f ♯) , (f ♯-isMonHom)) (\f -> refl) lemma)
    where
    lemma : (homMon : Σ (FreeMon A -> B) (M.isMonHom (freeMon A) M))
            -> ((fst homMon ∘ η) ♯ , (fst homMon ∘ η) ♯-isMonHom) ≡ homMon
    lemma (f , homMonWit) i =
      let p = freeMonEquivLemma-β f homMonWit 
      in p i , {!   !}


  freeMonIsEquiv : isEquiv {A = M.MonHom (freeMon A) M} (\(f , ϕ) -> f ∘ η)
  freeMonIsEquiv = freeMonEquiv .snd
  