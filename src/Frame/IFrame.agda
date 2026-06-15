{-# OPTIONS --safe --without-K #-}

module Frame.IFrame where

open import Relation.Binary.PropositionalEquality
  using (_≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)

--
record Preorder (W : Set) (_⊑_ : W → W → Set) : Set where
  field
    ⊑-trans            : {w w' w'' : W} → (i : w ⊑ w') → (i' : w' ⊑ w'') → w ⊑ w''
    ⊑-refl             : {w : W} → w ⊑ w

  ⊑-refl[_] : (w : W) → w ⊑ w
  ⊑-refl[ _ ] = ⊑-refl

-- Intuitionistic Frame
record IFrame (W : Set) (_⊑_ : W → W → Set) : Set where
  field
    ⊑-trans            : {w w' w'' : W} → (i : w ⊑ w') → (i' : w' ⊑ w'') → w ⊑ w''
    ⊑-trans-assoc      : {w w' w'' w''' : W} (i : w ⊑ w') (i' : w' ⊑ w'') (i'' : w'' ⊑ w''') → ⊑-trans (⊑-trans i i') i'' ≡ ⊑-trans i (⊑-trans i' i'')
    ⊑-refl             : {w : W} → w ⊑ w
    ⊑-trans-unit-left  : {w w' : W} (i : w ⊑ w') → ⊑-trans ⊑-refl i ≡ i
    ⊑-trans-unit-right : {w w' : W} (i : w ⊑ w') → ⊑-trans i ⊑-refl ≡ i

  ⊑-refl[_] : (w : W) → w ⊑ w
  ⊑-refl[ _ ] = ⊑-refl

  ⊑-trans-unit : {w w' : W} (i : w ⊑ w') → ⊑-trans ⊑-refl i ≡ ⊑-trans i ⊑-refl
  ⊑-trans-unit i = ≡-trans (⊑-trans-unit-left i) (≡-sym (⊑-trans-unit-right i))

module Collection {W : Set} {_⊑_ : W → W → Set} (IF : IFrame W _⊑_) where

  open IFrame IF

  open import Data.List
  open import Data.List.Relation.Binary.Pointwise
  open import Data.List.Membership.Propositional
  open import Data.List.Relation.Unary.Any

  open import Relation.Binary.PropositionalEquality using (_≡_)
    renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; cong to ≡-cong)
  open import Data.Product using (Σ ; ∃; _×_; _,_; -,_)
    renaming (proj₁ to fst; proj₂ to snd)

  private
    variable
      w w' w'' u u' v v' : W
      ws ws' ws'' us us' vs vs' : List W

  W⋆ = List W

  _⋆⊑⋆_ : W⋆ → W⋆ → Set
  _⋆⊑⋆_ = Pointwise _⊑_

  ⋆⊑⋆-refl[_] : ∀ ws → ws ⋆⊑⋆ ws
  ⋆⊑⋆-refl[ [] ]     = []
  ⋆⊑⋆-refl[ w ∷ ws ] = ⊑-refl {w} ∷ ⋆⊑⋆-refl[ ws ]

  ⋆⊑⋆-refl : ws ⋆⊑⋆ ws
  ⋆⊑⋆-refl = ⋆⊑⋆-refl[ _ ]

  ⋆⊑⋆-trans : ws ⋆⊑⋆ ws' → ws' ⋆⊑⋆ ws'' → ws ⋆⊑⋆ ws''
  ⋆⊑⋆-trans [] is'              = is'
  ⋆⊑⋆-trans (i ∷ is) (i' ∷ is') = ⊑-trans i i' ∷ ⋆⊑⋆-trans is is'

  [_]⋆ : w ⊑ w' → [ w ] ⋆⊑⋆ [ w' ]
  [ i ]⋆ = i ∷ []

  ∈⋆-refl : w ∈ [ w ]
  ∈⋆-refl = here ≡-refl

  -- a collection of elements [ A w | w ∈ ws ]
  -- one `A w` for every `w` in `ws`
  data Coll' (A : W → Set) : W⋆ → Set where
    []   : Coll' A []
    _∷_  : A w → Coll' A ws → Coll' A (w ∷ ws)

  Coll : W⋆ → (W → Set) → Set
  Coll ws A = Coll' A ws

  -- singleton collection
  [_]' : {A : W → Set} → A w → Coll [ w ] A
  [ x ]' = x ∷ []

  -- map over a collection
  mapColl : {A B : W → Set} → (∀ {w} → A w → B w) → Coll ws A → Coll ws B
  mapColl f []       = []
  mapColl f (x ∷ xs) = f x ∷ mapColl f xs

  -- split a collection into two
  split : {A : W → Set} → Coll (ws ++ us) A → Coll ws A × Coll us A
  split {[]}     ps       = [] , ps
  split {w ∷ ws} (p ∷ ps) = let (qs , rs) = split {ws = ws} ps in (p ∷ qs) , rs

  -- join two collection into one
  join : {A : W → Set} → Coll ws A → Coll us A → Coll (ws ++ us) A
  join []      c' = c'
  join (x ∷ c) c' = x ∷ join c c'

  zipWithColl : {A B C : W → Set} → ({w : W} → A w → B w → C w) → Coll ws A → Coll ws B → Coll ws C
  zipWithColl f []       []       = []
  zipWithColl f (a ∷ as) (b ∷ bs) = f a b ∷ zipWithColl f as bs

  -- if w ⊑ w' and [ w' ⊑ x | x ∈ ws ], then [ w ⊑ x | x ∈ ws ]
  _ᵢ∙_ : w ⊑ w' → Coll ws (w' ⊑_) → Coll ws (w ⊑_)
  i ᵢ∙ c = mapColl (⊑-trans i) c

  wkColl : {A : W → Set}
    → ({w w' : W} → w ⊑ w' → A w → A w')
    → ws ⋆⊑⋆ ws' → Coll ws A → Coll ws' A
  wkColl wkA []       []       = []
  wkColl wkA (i ∷ is) (x ∷ xs) = wkA i x ∷ wkColl wkA is xs

  -- if [ w ⊑ x | x ∈ ws ] and ws ⊑ ws' pointwise, then [ w ⊑ x | x ∈ ws' ]
  _∙ᵢ⋆_ : Coll ws (w ⊑_) → ws ⋆⊑⋆ ws' → Coll ws' (w ⊑_)
  xs ∙ᵢ⋆ is = wkColl (λ i' i → ⊑-trans i i') is xs
