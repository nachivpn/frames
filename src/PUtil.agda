{-# OPTIONS --safe --without-K #-}
module PUtil where

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

opaque
 ×-≡,≡→≡ : {A B : Set} {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : A × B} → a₁ ≡ a₂ × b₁ ≡ b₂ → p₁ ≡ p₂
 ×-≡,≡→≡ = ×-≡,≡↔≡ .Inverse.to

 ≡→×-≡,≡ : {A B : Set} {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : A × B} → p₁ ≡ p₂ → a₁ ≡ a₂ × b₁ ≡ b₂
 ≡→×-≡,≡ = ×-≡,≡↔≡ .Inverse.from

 Σ×-≡,≡,≡→≡ : {A : Set} {B B' : A → Set} {p₁@(a₁ , b₁ , b₁') p₂@(a₂ , b₂ , b₂') : ∃ λ (a : A) → B a × B' a} → (∃ λ (p : a₁ ≡ a₂) → subst B p b₁ ≡ b₂ × subst B' p b₁' ≡ b₂') → p₁ ≡ p₂
 Σ×-≡,≡,≡→≡ {A} {_B} {_B'} {p₁} {p₂} (p , q , q') = Σ-≡,≡→≡ (p , ×-≡,≡→≡ (˘trans (subst-application′ proj₁ p) q , ˘trans (subst-application′ proj₂ p) q'))

 Σ×-≡,≡,≡→≡˘ : {A : Set} {B B' : A → Set} {p₁@(a₁ , b₁ , b₁') p₂@(a₂ , b₂ , b₂') : ∃ λ (a : A) → B a × B' a} → (∃ λ (p : a₁ ≡ a₂) → subst B p b₁ ≡ b₂ × subst B' p b₁' ≡ b₂') → p₂ ≡ p₁
 Σ×-≡,≡,≡→≡˘ p = sym (Σ×-≡,≡,≡→≡ p)

 ≡˘→Σ-≡,≡ : {A : Set} {B : A → Set} {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : ∃ λ (a : A) → B a} → p₂ ≡ p₁ → ∃ λ (p : a₁ ≡ a₂) → subst B p b₁ ≡ b₂
 ≡˘→Σ-≡,≡ p = Σ-≡,≡←≡ (sym p)

 Σ×-≡,≡,≡←≡ : {A : Set} {B B' : A → Set} {p₁@(a₁ , b₁ , b₁') p₂@(a₂ , b₂ , b₂') : ∃ λ (a : A) → B a × B' a} → p₁ ≡ p₂ → (∃ λ (p : a₁ ≡ a₂) → subst B p b₁ ≡ b₂ × subst B' p b₁' ≡ b₂')
 Σ×-≡,≡,≡←≡ {A} {_B} {_B'} {p₁} {p₂} p = let (q , r) = Σ-≡,≡←≡ p ; (r1 , r2) = ≡→×-≡,≡ r in q , trans (subst-application′ proj₁ q) r1 , trans (subst-application′ proj₂ q) r2

 Σ-≡,≡↔≡-inverseˡ : {A : Set} {B : A → Set} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} (p : Σ (a₁ ≡ a₂) (λ p₁ → subst (λ v → B v) p₁ b₁ ≡ b₂)) → Σ-≡,≡←≡ (Σ-≡,≡→≡ p) ≡ p
 Σ-≡,≡↔≡-inverseˡ p = Σ-≡,≡↔≡-inverse .proj₂ refl

 Σ-≡,≡↔≡-inverseʳ : {A : Set} {B : A → Set} {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : ∃ λ (a : A) → B a} (p : p₁ ≡ p₂) → Σ-≡,≡→≡ (Σ-≡,≡←≡ p) ≡ p
 Σ-≡,≡↔≡-inverseʳ p = Σ-≡,≡↔≡-inverse .proj₁ refl
