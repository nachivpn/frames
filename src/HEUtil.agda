{-# OPTIONS --safe --with-K #-}
module HEUtil where

open import Level using (Level)

open import Relation.Unary using (Pred)

open import Relation.Binary                       using (REL)
import      Relation.Binary.HeterogeneousEquality as HE
open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; subst ; subst₂)
  renaming (refl to ≡-refl ; trans to ≡-trans)

open HE public
  using    (_≅_ ; ≅-to-≡ ; ≡-to-≅ ; ≡-subst-removable ; ≅-to-subst-≡ ; ≅-to-type-≡)
  renaming (refl to ≅-refl ; sym to ≅-sym ; trans to ≅-trans ; cong to ≅-cong ; icong to ≅-icong ; cong-app to ≅-cong-app ; subst-removable to ≅-subst-removable)

private
  variable
    ℓ : Level
    A : Set ℓ
    B : Set ℓ

≡-subst-addable : ∀ (P : Pred A ℓ) {x y} (eq : x ≡ y) (z : P x) → z ≅ subst P eq z
≡-subst-addable P p z = ≅-sym (≡-subst-removable P p z)

-- stole it from history of master
≡-subst₂-removable : ∀ (R : REL A B ℓ) {x y u v} (eq₁ : x ≡ y) (eq₂ : u ≡ v) (z : R x u) → subst₂ R eq₁ eq₂ z ≅ z
≡-subst₂-removable P ≡-refl ≡-refl z = ≅-refl

≡-subst₂-addable : ∀ (R : REL A B ℓ) {x y u v} (eq₁ : x ≡ y) (eq₂ : u ≡ v) (z : R x u) → z ≅ subst₂ R eq₁ eq₂ z
≡-subst₂-addable P p q z = ≅-sym (≡-subst₂-removable P p q z)
