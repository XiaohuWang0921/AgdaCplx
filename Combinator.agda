{-# OPTIONS --without-K --safe #-}

module Combinator where

open import Level
open import Function.Base public

private
  variable
    a b : Level
    A : Set a
    
join : {B : A → A → Set b} → (∀ x y → B x y) → ∀ x → B x x
join f = λ x → f x x

{-# NOINLINE id #-}
{-# NOINLINE const #-}
{-# NOINLINE flip #-}
{-# NOINLINE _∘_ #-}
{-# NOINLINE join #-}
