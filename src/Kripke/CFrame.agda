open import Relation.Binary.PropositionalEquality using (_≡_)

open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans)
open import Data.Product using (Σ ; ∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

open import Kripke.IFrame

module Kripke.CFrame {W : Set} {_⊆_ : W → W → Set} (IF : IFrame W _⊆_) where

open IFrame IF public

open import Data.List
open import Data.List.Relation.Binary.Pointwise as Pointwise
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any

open import Data.List.Relation.Binary.Subset.Propositional renaming (_⊆_ to _≤_)
variable
  w w' w'' u u' v v' : W
  ws ws' ws'' us us' vs vs' : List W

W⋆ = List W

_⋆⊆⋆_ : W⋆ → W⋆ → Set
_⋆⊆⋆_ = Pointwise _⊆_

⋆⊆⋆-refl[_] : ∀ ws → ws ⋆⊆⋆ ws
⋆⊆⋆-refl[ [] ]     = []
⋆⊆⋆-refl[ x ∷ ws ] = ⊆-refl ∷ ⋆⊆⋆-refl[ ws ]

⋆⊆⋆-refl : ws ⋆⊆⋆ ws
⋆⊆⋆-refl = ⋆⊆⋆-refl[ _ ]

⋆⊆⋆-trans : ws ⋆⊆⋆ ws' → ws' ⋆⊆⋆ ws'' → ws ⋆⊆⋆ ws''
⋆⊆⋆-trans [] is'              = is'
⋆⊆⋆-trans (i ∷ is) (i' ∷ is') = ⊆-trans i i' ∷ ⋆⊆⋆-trans is is'

[_]⋆ : w ⊆ w' → [ w ] ⋆⊆⋆ [ w' ]
[ i ]⋆ = i ∷ []

∈⋆-refl : w ∈ [ w ]
∈⋆-refl = here ≡-refl

-- an collection of elements
-- one `A w` for every `w` in `ws`
data Collection' (A : W → Set) : W⋆ → Set where
  []   : Collection' A []
  _∷_  : A w → Collection' A ws → Collection' A (w ∷ ws)

Collection : W⋆ → (W → Set) → Set
Collection ws A = Collection' A ws

[_]' : {A : W → Set} → A w → Collection [ w ] A
[ x ]' = x ∷ []

mapCollection : {A B : W → Set} → (∀ {w} → A w → B w) → Collection ws A → Collection ws B
mapCollection f [] = []
mapCollection f (x ∷ xs) = f x ∷ mapCollection f xs

split : {A : W → Set} → Collection (ws ++ us) A → Collection ws A × Collection us A
split {[]}     ps       = [] , ps
split {w ∷ ws} (p ∷ ps) = let (qs , rs) = split {ws = ws} ps in (p ∷ qs) , rs

-- Covering Frame on a covering relation `R⋆`
record CFrame (_R⋆_   : W → W⋆ → Set) : Set₁ where

  field
    factor : w ⊆ w' → w R⋆ vs → ∃ λ vs' → (w' R⋆ vs') × (vs ⋆⊆⋆ vs')

  factorW⋆ : (i : w ⊆ w') (r : w R⋆ vs) → W⋆
  factorW⋆ i r = factor i r .fst

  factorR⋆ : (i : w ⊆ w') (r : w R⋆ vs) → w' R⋆ factorW⋆ i r
  factorR⋆ i r = factor i r .snd .fst

  factor⋆⊆⋆ : (i : w ⊆ w') (r : w R⋆ vs) → vs ⋆⊆⋆ factorW⋆ i r
  factor⋆⊆⋆ i r = factor i r .snd .snd

  field
    factor-pres-⊆-refl  :
      (m : w R⋆ vs) → factor ⊆-refl m ≡ (vs , m , ⋆⊆⋆-refl)
    factor-pres-⊆-trans : (i : w ⊆ w') (i' : w' ⊆ w'') (m : w R⋆ vs)
      → factor (⊆-trans i i') m ≡ (-, (factorR⋆ i' (factorR⋆ i m) , (⋆⊆⋆-trans (factor⋆⊆⋆ i m) (factor⋆⊆⋆ i' (factorR⋆ i m)))))

  -- think "coverage" of a world
  K : (w : W) → Set
  K w = ∃ λ vs → w R⋆ vs

  cod : {w : W} → K w → W⋆
  cod = fst

  rel : {w : W} → (k : K w) → w R⋆ (cod k)
  rel = snd

  cods : Collection ws K → W⋆
  cods []       = []
  cods (k ∷ ks) = cod k ++ cods ks

  -- generalize?
  module _ (pasteOnce : ∀ {w us} → (r : w R⋆ us) → (ks : Collection us K) → w R⋆ (cods ks)) where

    paste : (ks : Collection ws K) (qs : Collection (cods ks) K) → Collection ws K
    paste []              qs = qs
    paste ((us , r) ∷ ks) qs = let (qs1 , qs2) = split qs in ((-, pasteOnce r qs1)) ∷ paste ks qs2

-- Coverages with various properties
module _ {_R⋆_ : W → W⋆ → Set} (CF : CFrame _R⋆_) where
  open CFrame CF

  record Coverage : Set where
    field

      -- covering family
      family    : w R⋆ vs → Collection vs (w ⊆_)

      -- TODO: stability condition

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
      R⋆-trans : (r : w R⋆ ws) → (ks : Collection ws K) → w R⋆ (cods ks)

      -- TODO: R⋆-trans-assoc, factor-pres-R⋆-trans

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

emptyCov : Coverage emptyCFrame
emptyCov = record
  { family        = λ { none → [] }
--  ; family-stable = ?
  }

data idR⋆ : W → W⋆ → Set where
  id : idR⋆ w [ w ]

idCFrame : CFrame idR⋆
idCFrame = record
  { factor              = λ { i id → (-, id , i ∷ [] )}
  ; factor-pres-⊆-refl  = λ { id → ≡-refl }
  ; factor-pres-⊆-trans = λ { i i' id → ≡-refl }
  }

idCov : Coverage idCFrame
idCov = record
  { family        = λ { id → [ ⊆-refl ]' }
--  ; family-stable = ?
  }

idRCFrame : ReflexiveCFrame idCFrame
idRCFrame = record
  { R⋆-refl             = id
  ; factor-pres-R⋆-refl = λ _ → ≡-refl
  }

idRCov : ReflexiveCoverage idCFrame idCov idRCFrame
idRCov = record { family-pres-refl = ≡-refl }
