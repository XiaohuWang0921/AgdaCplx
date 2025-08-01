{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module Cplx (ext : ∀ {a b} → Extensionality a b) where
  open import Level
  open import Relation.Binary.PropositionalEquality
  open import Function.Base

  private
    variable
      a b c u v x y : Level
      A : Set a
      B : Set b
      C : Set c

  join : (A → A → B) → A → B
  join f x = f x x

  module Single {X : Set x} {Y : Set y} (ι : X → Y) where
    record Cplx (A : Set a) : Set (a ⊔ x ⊔ y) where
      field
        ϕ : (X → A) → Y → A
        sec : ∀ {h x} → ϕ h (ι x) ≡ h x
        proj : ∀ {a x} → ϕ (const a) x ≡ a
        diag : ∀ {hh y} → ϕ (λ x → ϕ (hh x) y) y ≡ ϕ (join hh) y
        braid : ∀ {hh y y'} → ϕ (λ x → ϕ (hh x) y') y ≡ ϕ (λ x → ϕ (flip hh x) y) y'
