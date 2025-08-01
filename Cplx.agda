{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module Cplx where

open import Level
open import Relation.Binary.PropositionalEquality
open import Function.Base
open import Data.Unit.Base
open import Data.Product.Base
open import Data.Product.Properties
open ≡-Reasoning

private
  variable
    a b c u v x y : Level
    A : Set a
    B : Set b
    C : Set c

join : {B : A → A → Set b} → (∀ x y → B x y) → ∀ x → B x x
join f = λ x → f x x

{-# NOINLINE id #-}
{-# NOINLINE const #-}
{-# NOINLINE flip #-}
{-# NOINLINE _∘_ #-}
{-# NOINLINE join #-}
{-# NOINLINE <_,_> #-}

record Equaliser {A : Set a} {B : A → Set b} (f g : ∀ x → B x) : Set (a ⊔ b) where
  constructor eql
  field
    val : A
    .eq : f val ≡ g val

open Equaliser public

factor : {f g : B → C} → Equaliser {A = A → B} (f ∘_) (g ∘_) → A → Equaliser f g
factor (eql h f∘h≡g∘h) x = eql (h x) (cong (_$ x) f∘h≡g∘h)

module Ext (ext : ∀ {a b} → Extensionality a b) where

  module Single {X : Set x} {Y : Set y} (ι : X → Y) where
    record Cplx (A : Set a) : Set (a ⊔ x ⊔ y) where
      field
        ϕ : (X → A) → Y → A
        sec : ∀ {h x} → ϕ h (ι x) ≡ h x
        proj : ∀ {a x} → ϕ (const a) x ≡ a
        diag : ∀ {hh y} → ϕ (λ x → ϕ (hh x) y) y ≡ ϕ (join hh) y
        braid : ∀ {hh y y'} → ϕ (λ x → ϕ (hh x) y') y ≡ ϕ (λ x → ϕ (flip hh x) y) y'

    open Cplx {{...}} public

    record Coh {A : Set a} {B : Set b} {{_ : Cplx A}} {{_ : Cplx B}} (f : A → B) : Set (a ⊔ b ⊔ x ⊔ y) where
      field
        coh : ∀ {h y} → ϕ (f ∘ h) y ≡ f (ϕ h y)

    open Coh {{...}} public

    instance
      ⊤-Cplx : Cplx ⊤
      ⊤-Cplx = record
        { ϕ = λ _ _ → tt
        ; sec = λ {h} {x = x₁} → refl
        ; proj = λ {a} {x = x₁} → refl
        ; diag = λ {hh} {y = y₁} → refl
        ; braid = λ {hh} {y = y₁} {y'} → refl
        }

      ×-Cplx : {{Cplx A}} → {{Cplx B}} → Cplx (A × B)
      ×-Cplx = record
        { ϕ = λ h y → ϕ (proj₁ ∘ h) y , ϕ (proj₂ ∘ h) y
        ; sec = ×-≡,≡→≡ (sec , sec)
        ; proj = ×-≡,≡→≡ (proj , proj)
        ; diag = ×-≡,≡→≡ (diag , diag)
        ; braid = ×-≡,≡→≡ (braid , braid)
        }

      proj₁-Coh : {{_ : Cplx A}} {{_ : Cplx B}} → Coh {A = A × B} proj₁
      {-# OVERLAPS proj₁-Coh #-}
      proj₁-Coh = record
        { coh = refl
        }

      proj₂-Coh : {{_ : Cplx A}} {{_ : Cplx B}} → Coh {A = A × B} proj₂
      {-# OVERLAPS proj₂-Coh #-}
      proj₂-Coh = record
        { coh = refl
        }

      <,>-Coh : {f : A → B} {g : A → C} {{_ : Cplx A}} {{_ : Cplx B}} {{_ : Cplx C}} → {{Coh f}} → {{Coh g}} → Coh < f , g >
      {-# OVERLAPS <,>-Coh #-}
      <,>-Coh = record
        { coh = ×-≡,≡→≡ (coh , coh)
        }

      →-Cplx : {{Cplx B}} → Cplx (A → B)
      →-Cplx = record
        { ϕ = λ h y a → ϕ (flip h a) y
        ; sec = ext (λ _ → sec)
        ; proj = ext (λ _ → proj)
        ; diag = ext (λ _ → diag)
        ; braid = ext (λ _ → braid)
        }

      id-Coh : {{_ : Cplx A}} → Coh {A = A} id
      {-# OVERLAPPING id-Coh #-}
      id-Coh = record
        { coh = refl
        }

      ∘-Coh : {f : B → C} {g : A → B} {{_ : Cplx A}} {{_ : Cplx B}} {{_ : Cplx C}} → {{Coh f}} → {{Coh g}} → Coh (f ∘ g)
      {-# OVERLAPPABLE ∘-Coh #-}
      ∘-Coh {f = f} = record
        { coh = trans coh (cong f coh)
        }

      ∀∘-Coh : {f : B → C} {{_ : Cplx B}} {{_ : Cplx C}} → {{Coh f}} → Coh {A = A → B} (f ∘_)
      {-# OVERLAPS ∀∘-Coh #-}
      ∀∘-Coh = record
        { coh = ext (λ _ → coh)
        }

      ∀flip∘-Coh : {f : A → B} {{_ : Cplx C}} → Coh (flip (_∘′_ {C = C}) f)
      {-# OVERLAPS ∀flip∘-Coh #-}
      ∀flip∘-Coh = record
        { coh = refl
        }

      ∀∀∘-Coh : {{_ : Cplx C}} → Coh (_∘′_ {B = B} {C = C} {A = A})
      {-# OVERLAPS ∀∀∘-Coh #-}
      ∀∀∘-Coh = record
        { coh = refl
        }
