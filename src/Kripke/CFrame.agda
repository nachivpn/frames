open import Relation.Binary.PropositionalEquality using (_≡_)

open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans) 
open import Data.Product using (Σ ; ∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

open import Kripke.IFrame

module Kripke.CFrame {W : Set} {_⊆_ : W → W → Set} (IF : IFrame W _⊆_) where

open IFrame IF public

open import Data.List
open import Data.List.Relation.Binary.Pointwise
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any

variable
  w w' w'' v v' : W
  ws ws' ws'' vs vs' : List W

W⋆ = List W

_⊆⋆_ : W⋆ → W⋆ → Set
_⊆⋆_ = Pointwise _⊆_

⊆⋆-refl[_] : ∀ ws → ws ⊆⋆ ws
⊆⋆-refl[ [] ]     = []
⊆⋆-refl[ x ∷ ws ] = ⊆-refl ∷ ⊆⋆-refl[ ws ]

⊆⋆-refl : ws ⊆⋆ ws
⊆⋆-refl = ⊆⋆-refl[ _ ]

⊆⋆-trans : ws ⊆⋆ ws' → ws' ⊆⋆ ws'' → ws ⊆⋆ ws''
⊆⋆-trans [] is'              = is'
⊆⋆-trans (i ∷ is) (i' ∷ is') = ⊆-trans i i' ∷ ⊆⋆-trans is is'

_∈⋆ᵣ_ : v' ∈ vs' → vs ⊆⋆ vs' → ∃ λ v  → v ∈ vs × (v ⊆ v')
(here ≡-refl) ∈⋆ᵣ (i ∷ is) = (-, here ≡-refl , i)
(there n)     ∈⋆ᵣ (i ∷ is) = let (_ , n' , i' ) = n ∈⋆ᵣ is in (-, there n' , i')

-- Covering Frame
record CFrame (_R⋆_   : W → W⋆ → Set) : Set₁ where

  field
    factor : w ⊆ w' → w R⋆ vs → ∃ λ vs' → (w' R⋆ vs') × (vs ⊆⋆ vs')

  factorW⋆ : (i : w ⊆ w') (r : w R⋆ vs) → W⋆
  factorW⋆ i r = factor i r .fst
  
  factorR⋆ : (i : w ⊆ w') (r : w R⋆ vs) → w' R⋆ _
  factorR⋆ i r = factor i r .snd .fst

  factor⊆⋆ : (i : w ⊆ w') (r : w R⋆ vs) → vs ⊆⋆ _
  factor⊆⋆ i r = factor i r .snd .snd

  factorW : (i : w ⊆ w') (r : w R⋆ vs) → ∀ {v'} → (n' : v' ∈ factorW⋆ i r) → W
  factorW i r n' = fst (n' ∈⋆ᵣ (factor⊆⋆ i r))

  factor∈ : (i : w ⊆ w') (r : w R⋆ vs) → ∀ {v'} → (n' : v' ∈ factorW⋆ i r) → factorW i r n' ∈ vs
  factor∈ i r n' = fst (snd (n' ∈⋆ᵣ (factor⊆⋆ i r)))

  factor⊆ : (i : w ⊆ w') (r : w R⋆ vs) → ∀ {v'} → (n' : v' ∈ factorW⋆ i r) → factorW i r n' ⊆ v'
  factor⊆ i r n' = snd (snd (n' ∈⋆ᵣ (factor⊆⋆ i r)))
  
  field
    factor-pres-⊆-refl  : 
      (m : w R⋆ vs) → factor ⊆-refl m ≡ (vs , m , ⊆⋆-refl)
    factor-pres-⊆-trans : (i : w ⊆ w') (i' : w' ⊆ w'') (m : w R⋆ vs)
      → factor (⊆-trans i i') m ≡ (-, (factorR⋆ i' (factorR⋆ i m) , (⊆⋆-trans (factor⊆⋆ i m) (factor⊆⋆ i' (factorR⋆ i m))))) 

-- Coverages with various properties
module _ {_R⋆_   : W → W⋆ → Set} (CF : CFrame _R⋆_) where
  open CFrame CF

  -- Coverage
  record Cov : Set where
    field
    
      -- covering family
      family    : w R⋆ vs → ∀ {v} → v ∈ vs → w ⊆ v
      
      -- stability condition
      stability : (i : w ⊆ w') → (m : w R⋆ vs) → ∀ {v'} → (n' : v' ∈ factorW⋆ i m)
        → ⊆-trans i (family (factorR⋆ i m) n') ≡ ⊆-trans (family m (factor∈ i m n')) (factor⊆ i m n')

--
-- Special covering frames
--

data emptyR⋆ : W → W⋆ → Set where
  none : emptyR⋆ w []

emptyCFrame : CFrame emptyR⋆
emptyCFrame = record
  { factor              = λ { x none → [] , none , [] }
  ; factor-pres-⊆-refl  = λ { none → ≡-refl }
  ; factor-pres-⊆-trans = λ { i i' none → ≡-refl }
  }

emptyCov : Cov emptyCFrame
emptyCov = record
  { family    = λ { none () }
  ; stability = λ { i none () }
  }

data idR⋆ : W → W⋆ → Set where
  id : idR⋆ w [ w ]

idCFrame : CFrame idR⋆
idCFrame = record
  { factor              = λ { i id → (-, id , i ∷ [] )}
  ; factor-pres-⊆-refl  = λ { id → ≡-refl }
  ; factor-pres-⊆-trans = λ { i i' id → ≡-refl }
  }

idCov : Cov idCFrame
idCov = record
  { family    = λ { id (here ≡-refl) → ⊆-refl }
  ; stability = λ { i id (here ≡-refl) → ≡-trans (⊆-trans-unit-right i) (≡-sym (⊆-trans-unit-left i)) }
  }
