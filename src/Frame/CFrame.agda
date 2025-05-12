{-# OPTIONS --safe --without-K #-}
open import Frame.IFrame

module Frame.CFrame {W : Set} {_⊆_ : W → W → Set} (IF : IFrame W _⊆_) where

open IFrame IF public

open import Data.Unit

open import Function using (const)

open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; cong to ≡-cong)
open import Data.Product using (Σ ; ∃; _×_; _,_; -,_ ; uncurry)
  renaming (proj₁ to fst; proj₂ to snd)

private
  variable
    w w' w'' u u' v v' : W

-- worlds indexed by a set
Ws : Set → Set
Ws I = I → W

--
⊆s-syn : (I : Set) → Ws I → Ws I → Set
⊆s-syn I ws ws' = ∀ i → ws i ⊆ ws' i

syntax ⊆s-syn I ws ws' = ws ⊆s[ I ] ws'

-- Covering Frame on a covering relation `_⊲_`
record CFrame (_⊲_ : {I : Set} → W → Ws I → Set) : Set₁ where

  ⊲-syn : (I : Set) → W → Ws I → Set
  ⊲-syn I w vs = _⊲_ {I} w vs

  syntax ⊲-syn I w vs = w ⊲[ I ] vs

  field

    -- worlds witnessing the factorisation
    factorWs : {I : Set} {vs : Ws I} → w ⊆ w' → w ⊲[ I ] vs → (Ws I)

    -- ⊲ witnessing the factorisation
    factor⊲ : {I : Set} {vs : Ws I} (o : w ⊆ w') (r : w ⊲[ I ] vs) → w' ⊲[ I ] factorWs o r

    -- ⊆s witnessing the factorisation
    factor⊆s : {I : Set} {vs : Ws I} (o : w ⊆ w') (r : w ⊲[ I ] vs) → vs ⊆s[ I ] factorWs o r

  factor : {I : Set} {vs : Ws I} → w ⊆ w' →  w ⊲[ I ] vs
      → ∃ λ (vs' : Ws I) → w' ⊲[ I ] vs' × (vs ⊆s[ I ] vs')
  factor o r = factorWs o r , factor⊲ o r , factor⊆s o r

module _ {_⊲_ : {I : Set} → W → (Ws I) → Set} (CF : CFrame _⊲_) where
  open CFrame CF

  record Coverage : Set₁ where
    field
      -- covering family
      family : {I : Set} {vs : Ws I} → w ⊲ vs → ∀ i → w ⊆ vs i

  record Identity : Set where
    field
      -- identity condition
      ⊲-iden : w ⊲[ ⊤ ] (const w)

  record Transitivity : Set₁ where

    field
      -- transitivity condition
      ⊲-trans : {I : Set} {vs : Ws I} {Js : I → Set} {vs' : ∀ i → Ws (Js i)}
        → w ⊲[ I ] vs
        → (∀ i → vs i ⊲[ Js i ] (vs' i))
        → w ⊲[ Σ I Js ] (uncurry vs')
