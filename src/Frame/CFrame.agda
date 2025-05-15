{-# OPTIONS --safe --without-K #-}
open import Frame.IFrame

module Frame.CFrame {W : Set} {_⊆_ : W → W → Set} (IF : IFrame W _⊆_) where

open IFrame IF public

open import Data.Unit using (⊤)
open import Function using (const)

open import Relation.Binary using (IsEquivalence)

open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; cong to ≡-cong
           ; subst to ≡-subst ; subst₂ to ≡-subst₂)
open import Data.Product using (Σ ; ∃; _×_; _,_; -,_ ; uncurry)
  renaming (proj₁ to fst; proj₂ to snd)

-- families of worlds, indexed by a type
Wₛ : Set → Set
Wₛ I = I → W

private
  variable
    w w' w'' u u' v v' : W
    I I' : Set
    ws vs ws' vs' ws'' vs'' : Wₛ I

-- lift a relation on worlds to families of worlds
LiftR : (W → W → Set) → Wₛ I → Wₛ I → Set
LiftR {I} R ws ws' = ∀ i → R (ws i) (ws' i)

-- lift _≡_ on worlds
_≋_ : Wₛ I → Wₛ I → Set
_≋_ = LiftR _≡_

≋-refl[_] : (ws : Wₛ I) → ws ≋ ws
≋-refl[ ws ] = λ i → ≡-refl {x = ws i}

≋-sym : ws ≋ ws' → ws' ≋ ws
≋-sym ws≋ws' = λ i → ≡-sym (ws≋ws' i)

≋-trans : ws ≋ ws' → ws' ≋ ws'' → ws ≋ ws''
≋-trans ws≋ws' ws'≋ws'' = λ i → ≡-trans (ws≋ws' i) (ws'≋ws'' i)

≋-isequiv : IsEquivalence (_≋_ {I})
≋-isequiv = record { refl = ≋-refl[ _ ] ; sym = ≋-sym ; trans = ≋-trans }

≋-subst₂-LiftR : {R : W → W → Set} → ws ≋ ws' → vs ≋ vs' → LiftR R ws vs → LiftR R ws' vs'
≋-subst₂-LiftR {R = R} ws≋ws' vs≋vs' r = λ i → ≡-subst₂ R (ws≋ws' i) (vs≋vs' i) (r i)

_⊆ₛ_ : Wₛ I → Wₛ I → Set
_⊆ₛ_ = LiftR _⊆_

_≋ₒ_ : ws ⊆ₛ ws' → ws ⊆ₛ ws' → Set
_≋ₒ_ os os' = ∀ i → os i ≡ os' i

≋ₒ-refl[_] : (os : ws ⊆ₛ ws') → os ≋ₒ os
≋ₒ-refl[ os ] = λ i → ≡-refl {x = os i}

≋ₒ-sym : {os os' : ws ⊆ₛ ws'} → os ≋ₒ os' → os' ≋ₒ os
≋ₒ-sym os≋os' = λ i → ≡-sym (os≋os' i)

≋ₒ-trans : {os os' os'' : ws ⊆ₛ ws'} → os ≋ₒ os' → os' ≋ₒ os'' → os ≋ₒ os''
≋ₒ-trans os≋os' os'≋os'' = λ i → ≡-trans (os≋os' i) (os'≋os'' i)

≋ₒ-isequiv : IsEquivalence (_≋ₒ_ {I} {ws} {ws'})
≋ₒ-isequiv = record { refl = ≋ₒ-refl[ _ ] ; sym = ≋ₒ-sym ; trans = ≋ₒ-trans }

⊆ₛ-refl[_] : (ws : Wₛ I) → ws ⊆ₛ ws
⊆ₛ-refl[ ws ] = λ i → ⊆-refl[ ws i ]

⊆ₛ-trans : ws ⊆ₛ ws' → ws' ⊆ₛ ws'' → ws ⊆ₛ ws''
⊆ₛ-trans os os' = λ i → ⊆-trans (os i) (os' i)

⊆ₛ-trans-unit-left : (os : ws ⊆ₛ ws') → ⊆ₛ-trans (⊆ₛ-refl[ ws ]) os ≋ₒ os
⊆ₛ-trans-unit-left os = λ i → ⊆-trans-unit-left (os i)

⊆ₛ-trans-unit-right : (os : ws ⊆ₛ ws') → ⊆ₛ-trans os (⊆ₛ-refl[ ws' ]) ≋ₒ os
⊆ₛ-trans-unit-right os = λ i → ⊆-trans-unit-right (os i)

≋-subst₂-⊆ₛ : ws ≋ ws' → vs ≋ vs' → ws ⊆ₛ vs → ws' ⊆ₛ vs'
≋-subst₂-⊆ₛ = ≋-subst₂-LiftR {R = _⊆_}

≋-subst-⊆ₛ-right : vs ≋ vs' → ws ⊆ₛ vs → ws ⊆ₛ vs'
≋-subst-⊆ₛ-right {ws = ws} = ≋-subst₂-⊆ₛ ≋-refl[ ws ]

module Core
  (_⊲_             : {I : Set} → W → Wₛ I → Set)
  (≋-subst-⊲       : {I : Set} {w : W} {ws ws' : Wₛ I} → ws ≋ ws' → w ⊲ ws → w ⊲ ws')
  (≋-subst-⊲-refl  : {I : Set} {w : W} {ws : Wₛ I} {r : w ⊲ ws} → ≋-subst-⊲ ≋-refl[ ws ] r ≡ r)
  (≋-subst-⊲-trans : {I : Set} {w : W} {ws ws' ws'' : Wₛ I} {p : ws ≋ ws'} {p' : ws' ≋ ws''} {r : w ⊲ ws} → ≋-subst-⊲ (≋-trans p p') r ≡ ≋-subst-⊲ p' (≋-subst-⊲ p r))
  where

  -- hack for defining syntax
  ⊲-syn   = _⊲_

  syntax ⊲-syn {I} w vs = w ⊲[ I ] vs

  -- "converge"
  ⇓-syn : W → Wₛ I → Set
  ⇓-syn {I} w' vs = ∃ λ vs' → w' ⊲[ I ] vs' × (vs ⊆ₛ vs')

  syntax ⇓-syn {I} w vs = w ⇓[ I ] vs

  -- module to bring these implicit arguments into the body's scope
  module _ {w : W} {I : Set} {vs : Wₛ I} where

    -- equivalence of two proofs of convergence
    _≋⇓_ : w ⇓[ I ] vs → w ⇓[ I ] vs → Set
    (xs , r , os) ≋⇓ (xs' , r' , os') =
      Σ (xs ≋ xs') λ xs≋xs' → ≋-subst-⊲ xs≋xs' r ≡ r' × (≋-subst-⊆ₛ-right xs≋xs' os ≋ₒ os')

  -- Covering Frame on a covering relation `_⊲_`
  record CFrame : Set₁ where

  -- components of the factorisation square
    field

      -- worlds witnessing the factorisation
      factorWₛ : w ⊆ w' → w ⊲[ I ] vs → Wₛ I

      -- ⊲ witnessing the factorisation
      factor⊲ : (o : w ⊆ w') (r : w ⊲[ I ] vs) → w' ⊲[ I ] factorWₛ o r

      -- ⊆ₛ witnessing the factorisation
      factor⊆ₛ : (o : w ⊆ w') (r : w ⊲[ I ] vs) → vs ⊆ₛ factorWₛ o r

    -- factorisation square
    factor : w ⊆ w' → w ⊲[ I ] vs → w' ⇓[ I ] vs
    factor o r = factorWₛ o r , factor⊲ o r , factor⊆ₛ o r

    -- functor laws of the factorisation action
    field
      --
      factor-⊆-refl : (r : w ⊲[ I ] vs)
        → factor ⊆-refl r ≋⇓ (vs , r , ⊆ₛ-refl[ vs ])

      --
      factor-⊆-trans : (o : w ⊆ w') (o' : w' ⊆ w'') (r : w ⊲[ I ] vs)
        → let r' = factor⊲ o r
          in factor (⊆-trans o o') r ≋⇓ (factorWₛ o' r' , factor⊲ o' r' , ⊆ₛ-trans (factor⊆ₛ o r) (factor⊆ₛ o' r'))

  module _ (CF : CFrame) where

    open CFrame CF

    record Coverage : Set₁ where
      field
        -- covering family
        family : {vs : Wₛ I} → w ⊲[ I ] vs → ∀ i → w ⊆ vs i

    record Identity : Set where
      field
        -- identity condition
        ⊲-iden : w ⊲[ ⊤ ] (const w)

    record Transitivity : Set₁ where

      field
        -- transitivity condition
        ⊲-trans : {vs : Wₛ I} {Js : I → Set} {vs' : ∀ i → Wₛ (Js i)}
          → w ⊲[ I ] vs
          → (∀ i → vs i ⊲[ Js i ] (vs' i))
          → w ⊲[ Σ I Js ] (uncurry vs')
