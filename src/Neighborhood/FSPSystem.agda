{-# OPTIONS --safe --without-K #-}

open import Level using (0ℓ ; suc)
open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans
  ; cong to ≡-cong ; cong₂ to ≡-cong₂ ; subst to ≡-subst)

module Neighborhood.FSPSystem
  {W : Set}
  (_⊲_ : W → (W → Set) → Set)
  where

open import Relation.Unary using ()
  renaming (_⊆_ to _⊆ᵖ_) public
open import Relation.Unary.Properties
  renaming (⊆-refl to ⊆ᵖ-refl ; ⊆-trans to ⊆ᵖ-trans) public
  
variable
  w w'  : W
  X Y Z : W → Set

-- proof-relevant "subsets" of W
Sub : Set₁
Sub = W → Set

_⊲⋆_ : (X Y : Sub) → Set
X ⊲⋆ Y = {w : W} → X w → w ⊲ Y

_∈_ : W → Sub → Set
w ∈ X = X w

_⊆_ : Sub → Sub → Set
X ⊆ Y = X ⊆ᵖ Y

⊆-refl[_] : ∀ X → X ⊆ X
⊆-refl[ X ] = ⊆ᵖ-refl {0ℓ} {W} {0ℓ} {X}

⊆-trans : {X Y Z : Sub} → X ⊆ Y → Y ⊆ Z → X ⊆ Z
⊆-trans {Y = Y} f g = ⊆ᵖ-trans {A = W} {j = Y} f g

-- Cover system for Finite Sum-Product (FSP) logic
record FSPSystem : Set₁ where
  field
    ⊲-mon   : X ⊆ Y → w ⊲ X → w ⊲ Y 
    ⊲-iden  : w ∈ X → w ⊲ X
    ⊲-trans : w ⊲ X → X ⊲⋆ Y → w ⊲ Y

  ⊲⋆-mon : Y ⊆ Z → X ⊲⋆ Y → X ⊲⋆ Z
  ⊲⋆-mon f p x = ⊲-mon f (p x)
  
  ⊲⋆-refl : X ⊲⋆ X
  ⊲⋆-refl = λ x → ⊲-iden x

  ⊲⋆-trans : X ⊲⋆ Y → Y ⊲⋆ Z → X ⊲⋆ Z
  ⊲⋆-trans p q = λ x → ⊲-trans (p x) q

  field
    -- functoriality
    ⊲-mon-pres-⊆-refl : (p : w ⊲ X)
      → ⊲-mon ⊆-refl[ X ] p ≡ p
    ⊲-mon-pres-⊆-trans : (f : X ⊆ Y) (g : Y ⊆ Z) (p : w ⊲ X)
      → ⊲-mon (⊆-trans {X} {Y} {Z} f g) p ≡ ⊲-mon g (⊲-mon f p)

    -- naturality
    ⊲-iden-natural : (f : X ⊆ Y) (x : w ∈ X) 
      → ⊲-mon {X} {Y} f (⊲-iden x) ≡ ⊲-iden (f x)
    ⊲-trans-natural : (f : Y ⊆ Z) (p : w ⊲ X) (q : X ⊲⋆ Y) 
      → ⊲-mon f (⊲-trans p q) ≡ ⊲-trans p (⊲⋆-mon f q)
    
    -- monad laws
    ⊲-trans-right-unit : (p : w ⊲ X)
      → ⊲-trans p ⊲-iden ≡ p
    ⊲-trans-left-unit : (x : X w) (p : X ⊲⋆ Y)
      → ⊲-trans (⊲-iden x) p ≡ p x
    ⊲-trans-assoc : (p : w ⊲ X) (q : X ⊲⋆ Y) (r : Y ⊲⋆ Z)
      → ⊲-trans (⊲-trans p q) r ≡ ⊲-trans p (⊲⋆-trans q r)
