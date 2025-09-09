{-# OPTIONS --safe --without-K #-}
open import Frame.IFrame

module Frame.CFrame {W : Set} {_⊆_ : W → W → Set} (IF : IFrame W _⊆_) where

open IFrame IF

open import Data.Unit using (⊤)
open import Function using (const)

open import Relation.Binary using (IsEquivalence)

open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; cong to ≡-cong
           ; subst to ≡-subst ; subst₂ to ≡-subst₂)
open import Data.Product using (Σ ; ∃; ∃₂; _×_; _,_; -,_)
  renaming (proj₁ to fst; proj₂ to snd)

open import Function using (id ; _∘_)

open import PUtil using (Σ×-≡,≡,≡→≡)

private
  variable
    w w' w'' u u' v v' : W

module Core
  (K   : W → Set)
  -- `v ∈ (k : K w)` means v is in the cover k
  (_∈_ : (v : W) {w : W} → K w → Set)
  -- wkK is functorial
  --(wkK : {w w' : W} → w ⊆ w' → K w → K w')
  --(wkK-pres-refl  : {w : W} (k : K w) → wkK ⊆-refl[ w ] k ≡ k)
  --(wkK-pres-trans : {w w' w'' : W} (i : w ⊆ w') (i' : w' ⊆ w'') (k : K w) → wkK (⊆-trans i i') k ≡ wkK i' (wkK i k))
  where

  -- a predicate is satisfied by all elements of a cover
  ForAllW : (k : K w) (P : W → Set) → Set
  ForAllW k P = ∀ {v} → v ∈ k → P v

  AllForW : (P : W → Set) (k : K w) → Set
  AllForW P k = ForAllW k P

  -- a predicate is satisfied by all proofs witnessing membership of a cover
  ForAll∈ : (k : K w) (P : ∀ {v} → v ∈ k → Set) → Set
  ForAll∈ k P = ∀ {v} → (p : v ∈ k) → P p

  -- inclusion of covers
  _⊆k_ : K w → K w' → Set
  k ⊆k k' = ForAllW k' (λ v' → ∃ λ v → v ∈ k × (v ⊆ v'))

  ⊆k-refl[_] : (k : K w) → k ⊆k k
  ⊆k-refl[ k ] {v} p = v , p , ⊆-refl[ v ]

  ⊆k-trans : {k : K w} {k' : K w'} {k'' : K w''}
    → k ⊆k k' → k' ⊆k k'' → k ⊆k k''
  ⊆k-trans is is' {v''} p'' = let
    (v' , p' , i') = is' p''
    (v , p , i)    = is p'
    in (v , p , ⊆-trans i i')

  --
  ForAllW≋ : (k : K w) {P : W → Set} → (f : ForAllW k P) (g : ForAllW k P) →  Set
  ForAllW≋  {w} k f g = ForAll∈ k λ p → f p ≡ g p

  module _ {k : K w} {P : W → Set}  where

    ForAllW≋-refl : (f : ForAllW k P) → ForAllW≋ k f f
    ForAllW≋-refl f = λ _p → ≡-refl

    ForAllW≋-sym : {f f' : ForAllW k P} → ForAllW≋ k f f' → ForAllW≋ k f' f
    ForAllW≋-sym f≡f' = λ p → ≡-sym (f≡f' p)

    ForAllW≋-trans : {f f' f'' : ForAllW k P} → ForAllW≋ k f f' → ForAllW≋ k f' f'' → ForAllW≋ k f f''
    ForAllW≋-trans f≡f' f'≡f'' = λ p → ≡-trans (f≡f' p) (f'≡f'' p)

  module _ {k : K w} {k' : K w'} where

    -- equality on cover inclusion proofs
    _≋[⊆k]_ : k ⊆k k' → k ⊆k k' → Set
    _≋[⊆k]_ = ForAllW≋ k'

    ≋[⊆k]-refl : (is : k ⊆k k') → is ≋[⊆k] is
    ≋[⊆k]-refl = ForAllW≋-refl

    ≋[⊆k]-sym : {is is' : k ⊆k k'} → is ≋[⊆k] is' → is' ≋[⊆k] is
    ≋[⊆k]-sym = ForAllW≋-sym

    ≋[⊆k]-trans : {is is' is'' : k ⊆k k'} → is ≋[⊆k] is' → is' ≋[⊆k] is'' → is ≋[⊆k] is''
    ≋[⊆k]-trans = ForAllW≋-trans

  ⊆k-trans-unit-left : {k : K w} {k' : K w'} (is : k ⊆k k')
    → ⊆k-trans ⊆k-refl[ k ] is ≋[⊆k] is
  ⊆k-trans-unit-left is p = let (_ , _ , i) = is p
    in Σ×-≡,≡,≡→≡ (≡-refl , ≡-refl , ⊆-trans-unit-left i)

  ⊆k-trans-unit-right : {k : K w} {k' : K w'} (is : k ⊆k k')
    → ⊆k-trans is ⊆k-refl[ k' ] ≋[⊆k] is
  ⊆k-trans-unit-right is p = let (_ , _ , i) = is p
    in Σ×-≡,≡,≡→≡ (≡-refl , ≡-refl , ⊆-trans-unit-right i)

  ⊆k-trans-assoc : {k : K u} {k' : K v} {k'' : K w} {k''' : K w'}
    → (is : k ⊆k k') (is' : k' ⊆k k'') (is'' : k'' ⊆k k''')
    → ⊆k-trans (⊆k-trans is is') is'' ≋[⊆k] ⊆k-trans is (⊆k-trans is' is'')
  ⊆k-trans-assoc is is' is'' p''' = let
    (_ , p'' , i'') = is'' p'''
    (_ , p' , i')   = is' p''
    (_ , _ , i)     = is p'
    in Σ×-≡,≡,≡→≡ (≡-refl , ≡-refl , ⊆-trans-assoc i i' i'')

  -- functions mapping a coverage k to a "larger" cover k'
  _⇒k_ : W → W → Set
  w ⇒k v = (k : K w) → Σ (K v) λ k' → k ⊆k k'

  _$k_ : (w ⇒k w') → K w → K w'
  h $k k = h k .fst

  _$⊆_ : (h : w ⇒k w') → (k : K w) → k ⊆k (h $k k)
  h $⊆ k = h k .snd

  ⇒k-refl[_] : ∀ w → w ⇒k w
  ⇒k-refl[ w ] = λ k → k , ⊆k-refl[ k ]

  ⇒k-trans : w ⇒k w' → w' ⇒k w'' → w ⇒k w''
  ⇒k-trans h h' = λ k → (h' $k (h $k k)) , ⊆k-trans (h $⊆ k) (h' $⊆ (h $k k))

  -- extensional equality for ⇒k
  record _≋[⇒k]_ (h h' : w ⇒k w') : Set where
    constructor proof
    field
      pw : (k : K w) → let (k1 , is1) = h k ; (k2 , is2) = h' k
        in Σ (k1 ≡ k2) λ k1≡k2 → ≡-subst (k ⊆k_) k1≡k2 is1 ≋[⊆k] is2

  -- TODO: ≋[⇒k]-refl, ≋[⇒k]-sym, ≋[⇒k]-trans

  ⇒k-trans-unit-left : (h : w ⇒k w') → ⇒k-trans ⇒k-refl[ w ] h ≋[⇒k] h
  ⇒k-trans-unit-left h = proof λ k → ≡-refl , ⊆k-trans-unit-left (h $⊆ k)

  ⇒k-trans-unit-right : (h : w ⇒k w') → ⇒k-trans h ⇒k-refl[ w' ] ≋[⇒k] h
  ⇒k-trans-unit-right h = proof λ k → ≡-refl , ⊆k-trans-unit-right (h $⊆ k)

  ⇒k-trans-assoc : (h : u ⇒k v) (h' : v ⇒k w) (h'' : w ⇒k w')
    → ⇒k-trans (⇒k-trans h h') h'' ≋[⇒k] ⇒k-trans h (⇒k-trans h' h'')
  ⇒k-trans-assoc h h' h'' = proof λ k
    → ≡-refl , ⊆k-trans-assoc (h $⊆ k) (h' $⊆ (h $k k)) (h'' $⊆ (h' $k (h $k k) ))


  record CFrame : Set₁ where

    field

      factor : w ⊆ w' → w ⇒k w'

      factor-pres-refl :
          factor ⊆-refl ≋[⇒k] ⇒k-refl[ w ]

      factor-pres-trans : {w w' : W} (i : w ⊆ w') (i' : w' ⊆ w'')
        → factor (⊆-trans i i') ≋[⇒k] ⇒k-trans (factor i) (factor i')

  module _ (CF : CFrame) where

    open CFrame CF

    record Coverage : Set₁ where

      field

        -- a cover of w is a family of (w ⊆_) proofs
        family        : (k : K w) → ForAllW k (w ⊆_)

      strFam : {k : K w} (i : v ⊆ v') → ForAllW k (v' ⊆_) → ForAllW k (v ⊆_)
      strFam i fam x = ⊆-trans i (fam x)

      wkFam : {k : K w} {k' : K w'} → k ⊆k k' → ForAllW k (w ⊆_) → ForAllW k' (w ⊆_)
      wkFam is fam x = let (_ , x' , i) = is x in ⊆-trans (fam x') i

      field
        -- factorisation square commutes
        family-stable : (i : w ⊆ w') (k : K w)
          → ForAllW≋ _ (wkFam (factor i $⊆ k) (family k)) (strFam i (family (factor i $k k)))
