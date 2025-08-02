{-# OPTIONS --without-K --safe --prop #-}

module Prod where

open import Level
open import Data.Product.Base public
open import Equality

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c
    x y : A
    u v : B

×-≐,≐→≐ : x ≐ y → u ≐ v → (x ,′ u) ≐ (y , v)
×-≐,≐→≐ refl refl = refl
