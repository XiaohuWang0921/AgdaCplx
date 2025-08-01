{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module Cplx (ext : ∀ {a b} → Extensionality a b) where
  open import Level
  open import Relation.Binary.PropositionalEquality
  open import Function.Base
  open import Data.Unit.Base
  open import Data.Product.Base
  
  private
    variable
      a b c u v x y : Level
      A : Set a
      B : Set b
      C : Set c

  join : {B : A → A → Set b} → (∀ x y → B x y) → ∀ x → B x x
  join f = λ x → f x x

  {-# NOINLINE const #-}
  {-# NOINLINE flip #-}
  {-# NOINLINE _∘_ #-}
  {-# NOINLINE join #-}

  record Equaliser {A : Set a} {B : A → Set b} (f g : ∀ x → B x) : Set (a ⊔ b) where
    constructor eql
    field
      val : A
      eq : f val ≡ g val

  module Single {X : Set x} {Y : Set y} (ι : X → Y) where
    record Cplx (A : Set a) : Set (a ⊔ x ⊔ y) where
      field
        ϕ : (X → A) → Y → A
        sec : ∀ {h x} → ϕ h (ι x) ≡ h x
        proj : ∀ {a x} → ϕ (const a) x ≡ a
        diag : ∀ {hh y} → ϕ (λ x → ϕ (hh x) y) y ≡ ϕ (join hh) y
        braid : ∀ {hh y y'} → ϕ (λ x → ϕ (hh x) y') y ≡ ϕ (λ x → ϕ (flip hh x) y) y'
