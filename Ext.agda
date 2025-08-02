{-# OPTIONS --without-K --safe --prop #-}

open import Level
open import Equality

Extensionality : (a b : Level) → Prop _
Extensionality a b = {A : Set a} {B : A → Set b} {f g : ∀ x → B x} → (∀ x → f x ≐ g x) → f ≐ g
