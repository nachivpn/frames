{-# OPTIONS --safe --without-K #-}
open import Frame.IFrame

module Frame.CFrame {W : Set} {_⊆_ : W → W → Set} (IF : IFrame W _⊆_) where

open IFrame IF public
open Collection IF

open import Data.List using ([] ; [_] ; _++_)

open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; cong to ≡-cong)
open import Data.Product using (Σ ; ∃; _×_; _,_; -,_)
  renaming (proj₁ to fst; proj₂ to snd)

private
  variable
    w w' w'' u u' v v' : W
    ws ws' ws'' us us' vs vs' : W⋆

-- Covering Frame on a covering relation `R⋆`
record CFrame (_R⋆_   : W → W⋆ → Set) : Set₁ where

  field
    factor : w ⊆ w' → w R⋆ vs → ∃ λ vs' → (w' R⋆ vs') × (vs ⋆⊆⋆ vs')

  -- worlds witnessing the factorisation
  factorW⋆ : (i : w ⊆ w') (r : w R⋆ vs) → W⋆
  factorW⋆ i r = factor i r .fst

  -- R⋆ witnessing the factorisation
  factorR⋆ : (i : w ⊆ w') (r : w R⋆ vs) → w' R⋆ factorW⋆ i r
  factorR⋆ i r = factor i r .snd .fst

  factor⋆⊆⋆ : (i : w ⊆ w') (r : w R⋆ vs) → vs ⋆⊆⋆ factorW⋆ i r
  factor⋆⊆⋆ i r = factor i r .snd .snd

  field
    factor-pres-⊆-refl  :
      (m : w R⋆ vs) → factor ⊆-refl m ≡ (vs , m , ⋆⊆⋆-refl)
    factor-pres-⊆-trans : (i : w ⊆ w') (i' : w' ⊆ w'') (m : w R⋆ vs)
      → factor (⊆-trans i i') m ≡ (-, (factorR⋆ i' (factorR⋆ i m) , (⋆⊆⋆-trans (factor⋆⊆⋆ i m) (factor⋆⊆⋆ i' (factorR⋆ i m)))))

  -- think "coverage" of a world `w`
  K : (w : W) → Set
  K w = ∃ λ vs → w R⋆ vs

  -- `K w` intuitively represents a family of morphisms with domain `w`
  -- this is later enforced in the definition of `Coverage` by the `family` field

  -- worlds accessible from a coverage of `w`
  cod : {w : W} → K w → W⋆
  cod = fst

  -- paths/morphisms contained in a coverage of `w`
  rel : {w : W} → (k : K w) → w R⋆ (cod k)
  rel = snd

  -- worlds accessible from a collection of covers
  cods : Coll ws K → W⋆
  cods []       = []
  cods (k ∷ ks) = cod k ++ cods ks

  -- generalize?
  module _ (pasteOnce : ∀ {w us} → (r : w R⋆ us) → (ks : Coll us K) → w R⋆ (cods ks)) where

    paste : (ks : Coll ws K) (qs : Coll (cods ks) K) → Coll ws K
    paste []              [] = []
    paste ((us , r) ∷ ks) qs = let (qs1 , qs2) = split qs in (-, pasteOnce r qs1) ∷ paste ks qs2

    -- observe: it should be the case that
    --   (ks : Coll ws K) (qs : Coll (cods ks) K) → cods (paste ks qs) ≡ cods qs
    -- but having to rely on this to state coherence laws isn't going to be pretty

-- Coverages with various properties
module _ {_R⋆_ : W → W⋆ → Set} (CF : CFrame _R⋆_) where
  open CFrame CF

  record Coverage : Set where
    field

      -- covering family
      family    : w R⋆ vs → Coll vs (w ⊆_)

    field
      -- the squares determined by factor commute pointwise
      stability : (i : w ⊆ w') (r : w R⋆ vs)
        → i ᵢ∙ (family (factorR⋆ i r)) ≡ (family r) ∙ᵢ⋆ (factor⋆⊆⋆ i r)

  record ReflexiveCFrame : Set where
    field
      R⋆-refl             : w R⋆ [ w ]
      factor-pres-R⋆-refl : (i : w ⊆ w') → factor i R⋆-refl ≡ (-, R⋆-refl , [ i ]⋆)

    R⋆-refl[_] : (w : W) → w R⋆ [ w ] ; R⋆-refl[ w ] = R⋆-refl {w}

  record ReflexiveCoverage (C : Coverage) (RCF : ReflexiveCFrame) : Set where
    open Coverage C
    open ReflexiveCFrame RCF

    -- identity condition
    field
      family-pres-refl : family R⋆-refl ≡ [ ⊆-refl[ w ] ]'

  record TransitiveCFrame : Set where

    field
      R⋆-trans : (r : w R⋆ ws) → (ks : Coll ws K) → w R⋆ (cods ks)

      -- TODO: R⋆-trans-assoc, factor-pres-R⋆-trans
