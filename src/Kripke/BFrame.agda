{-# OPTIONS --safe --without-K #-}

open import Kripke.IFrame

-- Bimodule frame
module Kripke.BFrame {W : Set} {_⊆_ : W → W → Set} (IF : IFrame W _⊆_) (_R_ : W → W → Set) where

open IFrame IF public
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

_⊇_ : W → W → Set
w' ⊇ w = w ⊆ w'

record BFrame : Set where

  -- R is a ⊇-⊇ bimodule (see https://en.wikipedia.org/wiki/Bimodule#Definition)
  field

    -- left absorption
    _ᵢ∙_    : {w w' v : W} → w ⊆ w' → w R v → w' R v

    -- right absorption
    _∙ᵢ_    : {w v v' : W} → w R v' → v ⊆ v' → w R v

    -- associativity of absorption
    ∙-assoc : {w w' v' v : W} (i : w ⊆ w') (r : w R v') (i' : v ⊆ v') → (i ᵢ∙ r) ∙ᵢ i' ≡ i ᵢ∙ (r ∙ᵢ i')

  -- absorption respects structure of underlying IFrame
  field
    ᵢ∙-pres-⊆-refl  : {w v : W} (r : w R v) → ⊆-refl ᵢ∙ r ≡ r
    ∙ᵢ-pres-⊆-refl  : {w v : W} (r : w R v) → r ∙ᵢ ⊆-refl ≡ r
    ᵢ∙-pres-⊆-trans : {w w' w'' v : W} (i : w ⊆ w') (i' : w' ⊆ w'') (r : w R v) → (⊆-trans i i') ᵢ∙ r ≡ i' ᵢ∙ (i ᵢ∙ r)
    ∙ᵢ-pres-⊆-trans : {w v v' v'' : W} (r : w R v'') (i : v' ⊆ v'') (i' : v ⊆ v') → r ∙ᵢ (⊆-trans i' i) ≡ (r ∙ᵢ i) ∙ᵢ i'

  record ReflexiveBFrame : Set where
    field
      R-refl[_] : (w : W) → w R w
      ∙-pres-R-refl : {w w' : W} (i : w ⊆ w') → i ᵢ∙ R-refl[ w ] ≡ R-refl[ w' ] ∙ᵢ i

    R-refl : {w : W} → w R w
    R-refl = R-refl[ _ ]

  record TransitiveBFrame : Set where
    field
      R-trans : {w w' w'' : W} → w R w' → w' R w'' → w R w''

      R-trans-assoc : {v0 v1 v2 v3 : W} → (r : v0 R v1) (r' : v1 R v2) (r'' : v2 R v3)
        → R-trans (R-trans r r') r'' ≡ R-trans r (R-trans r' r'')

      ᵢ∙-pres-R-trans : {w w' u v : W} (i : w ⊆ w') (r : w R v) (r' : v R u)
        → i ᵢ∙ (R-trans r r') ≡ R-trans (i ᵢ∙ r) r'

      ∙ᵢ-pres-R-trans : {w v u u' : W} (r : w R v) (r' : v R u') (i : u ⊆ u')
        → (R-trans r r') ∙ᵢ i ≡ R-trans r (r' ∙ᵢ i)
