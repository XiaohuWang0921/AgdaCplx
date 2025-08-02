{-# OPTIONS --without-K --safe --prop #-}

module Equaliser where

open import Level
open import Combinator
open import Equality

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c
    
record Equaliser {A : Set a} {B : A → Set b} (f g : ∀ x → B x) : Set (a ⊔ b) where
  constructor eql
  field
    val : A
    eq : f val ≐ g val

open Equaliser public

factor : {f g : B → C} → Equaliser {A = A → B} (f ∘_) (g ∘_) → A → Equaliser f g
factor (eql h f∘h≐g∘h) x = eql (h x) (cong (λ f → f x) f∘h≐g∘h)
