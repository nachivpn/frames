{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_)

module Kripke.IFrame where

-- Intuitionistic Frame
record IFrame (W : Set) (_⊆_ : W → W → Set) : Set where
  field
    ⊆-trans            : {w w' w'' : W} → (i : w ⊆ w') → (i' : w' ⊆ w'') → w ⊆ w''
    ⊆-trans-assoc      : {w w' w'' w''' : W} (i : w ⊆ w') (i' : w' ⊆ w'') (i'' : w'' ⊆ w''') → ⊆-trans (⊆-trans i i') i'' ≡ ⊆-trans i (⊆-trans i' i'')
    ⊆-refl             : {w : W} → w ⊆ w
    ⊆-trans-unit-left  : {w w' : W} (i : w ⊆ w') → ⊆-trans ⊆-refl i ≡ i
    ⊆-trans-unit-right : {w w' : W} (i : w ⊆ w') → ⊆-trans i ⊆-refl ≡ i

  ⊆-refl[_] : (w : W) → w ⊆ w
  ⊆-refl[ _ ] = ⊆-refl
