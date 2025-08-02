{-# OPTIONS --without-K --safe --prop #-}

module Equality where

open import Level

private
  variable
    a b : Level
    A : Set a
    B : Set b
    x y z : A

infix 4 _≐_
data _≐_ {A : Set a} (x : A) : A → Prop a where
  instance refl : x ≐ x

subst : {P : A → Prop b} → x ≐ y → P x → P y
subst refl p = p

cong : (f : A → B) → x ≐ y → f x ≐ f y
cong _ refl = refl

sym : x ≐ y → y ≐ x
sym refl = refl

trans : x ≐ y → y ≐ z → x ≐ z
trans refl p = p
