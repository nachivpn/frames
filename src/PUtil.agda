{-# OPTIONS --safe --without-K #-}
module PUtil where

open import Level using (Level)
open import Relation.Unary using (Pred)

open import Data.Product            using (Σ ; _,_ ; proj₁ ; proj₂ ; ∃ ; _×_)
open import Data.Product.Properties using (Σ-≡,≡↔≡; ×-≡,≡↔≡)

open import Function using (Inverse)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; sym ; trans ; subst)
open import PEUtil

module _ {a} {b} {A : Set a} {B : A → Set b} {p₁ p₂ : Σ A B} where
  open import Function
  open import Data.Product.Properties
  open Inverse (Σ-≡,≡↔≡ {p₁ = p₁} {p₂ = p₂}) public
    using    ()
    renaming (to to Σ-≡,≡→≡ ; from to Σ-≡,≡←≡ ; inverse to Σ-≡,≡↔≡-inverse)

private
  variable
    ℓ ℓ' : Level
    A B : Set ℓ
    P Q : Pred A ℓ

opaque
 ×-≡,≡→≡ : {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : A × B} → a₁ ≡ a₂ × b₁ ≡ b₂ → p₁ ≡ p₂
 ×-≡,≡→≡ = ×-≡,≡↔≡ .Inverse.to

 ×-≡,≡←≡ : {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : A × B} → p₁ ≡ p₂ → a₁ ≡ a₂ × b₁ ≡ b₂
 ×-≡,≡←≡ = ×-≡,≡↔≡ .Inverse.from

 ≡→×-≡,≡  : {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : A × B} → p₁ ≡ p₂ → a₁ ≡ a₂ × b₁ ≡ b₂
 ≡→×-≡,≡ = ×-≡,≡←≡

 {-# WARNING_ON_USAGE ≡→×-≡,≡ "DEPRECATED: Use ×-≡,≡←≡ instead" #-}

 Σ×-≡,≡,≡→≡ : {p₁@(a₁ , b₁ , b₁') p₂@(a₂ , b₂ , b₂') : ∃ λ (a : A) → P a × Q a} → (∃ λ (p : a₁ ≡ a₂) → subst P p b₁ ≡ b₂ × subst Q p b₁' ≡ b₂') → p₁ ≡ p₂
 Σ×-≡,≡,≡→≡ {A} {_P} {_Q} {p₁} {p₂} (p , q , q') = Σ-≡,≡→≡ (p , ×-≡,≡→≡ (˘trans (subst-application′ proj₁ p) q , ˘trans (subst-application′ proj₂ p) q'))

 Σ×-≡,≡,≡→≡˘ : {p₁@(a₁ , b₁ , b₁') p₂@(a₂ , b₂ , b₂') : ∃ λ (a : A) → P a × Q a} → (∃ λ (p : a₁ ≡ a₂) → subst P p b₁ ≡ b₂ × subst Q p b₁' ≡ b₂') → p₂ ≡ p₁
 Σ×-≡,≡,≡→≡˘ p = sym (Σ×-≡,≡,≡→≡ p)

 ≡˘→Σ-≡,≡ : {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : ∃ λ (a : A) → P a} → p₂ ≡ p₁ → ∃ λ (p : a₁ ≡ a₂) → subst P p b₁ ≡ b₂
 ≡˘→Σ-≡,≡ p = Σ-≡,≡←≡ (sym p)

 Σ×-≡,≡,≡←≡ : {p₁@(a₁ , b₁ , b₁') p₂@(a₂ , b₂ , b₂') : ∃ λ (a : A) → P a × Q a}
   → p₁ ≡ p₂ → (∃ λ (p : a₁ ≡ a₂) → subst P p b₁ ≡ b₂ × subst Q p b₁' ≡ b₂')
 Σ×-≡,≡,≡←≡ {A} {_P} {_Q} {p₁} {p₂} p = let (q , r) = Σ-≡,≡←≡ p ; (r1 , r2) = ×-≡,≡←≡ r
   in q , trans (subst-application′ proj₁ q) r1 , trans (subst-application′ proj₂ q) r2

 Σ-≡,≡↔≡-inverseˡ : {a₁ a₂ : A} {b₁ : P a₁} {b₂ : P a₂}
   → (p : Σ (a₁ ≡ a₂) (λ p₁ → subst (λ v → P v) p₁ b₁ ≡ b₂)) → Σ-≡,≡←≡ (Σ-≡,≡→≡ p) ≡ p
 Σ-≡,≡↔≡-inverseˡ p = Σ-≡,≡↔≡-inverse .proj₂ refl

 Σ-≡,≡↔≡-inverseʳ : {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : ∃ λ (a : A) → P a}
   → (p : p₁ ≡ p₂) → Σ-≡,≡→≡ (Σ-≡,≡←≡ p) ≡ p
 Σ-≡,≡↔≡-inverseʳ p = Σ-≡,≡↔≡-inverse .proj₁ refl
