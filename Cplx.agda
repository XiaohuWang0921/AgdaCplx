{-# OPTIONS --without-K --safe --prop #-}

module Cplx where

open import Level
open import Data.Unit.Base
open import Combinator
open import Equality
open import Equaliser
open import Prod
open import Ext

private
  variable
    a b c u v x y : Level
    A : Set a
    B : Set b
    C : Set c

module WithExt (ext : ∀ {a b} → Extensionality a b) where

  module Single {X : Set x} {Y : Set y} (ι : X → Y) where
    record Cplx (A : Set a) : Set (a ⊔ x ⊔ y) where
      field
        ϕ : (X → A) → Y → A
        sec : ∀ {h x} → ϕ h (ι x) ≐ h x
        proj : ∀ {a x} → ϕ (const a) x ≐ a
        diag : ∀ {hh y} → ϕ (λ x → ϕ (hh x) y) y ≐ ϕ (join hh) y
        braid : ∀ {hh y y'} → ϕ (λ x → ϕ (hh x) y') y ≐ ϕ (λ x → ϕ (flip hh x) y) y'

    open Cplx {{...}} public

    record Coh {A : Set a} {B : Set b} {{_ : Cplx A}} {{_ : Cplx B}} (f : A → B) : Prop (a ⊔ b ⊔ x ⊔ y) where
      field
        coh : ∀ {h y} → ϕ (f ∘ h) y ≐ f (ϕ h y)

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
        ; sec = ×-≐,≐→≐ sec sec
        ; proj = ×-≐,≐→≐ proj proj
        ; diag = ×-≐,≐→≐ diag diag
        ; braid = ×-≐,≐→≐ braid braid
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
      <,>-Coh {f = f} {g = g} = record
        { coh = ×-≐,≐→≐ (coh {f = f}) (coh {f = g})
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
      ∘-Coh {f = f} {g = g} = record
        { coh = trans (coh {f = f}) (cong f (coh {f = g}))
        }

      ∀∘-Coh : {f : B → C} {{_ : Cplx B}} {{_ : Cplx C}} → {{Coh f}} → Coh {A = A → B} (f ∘_)
      {-# OVERLAPS ∀∘-Coh #-}
      ∀∘-Coh {f = f} = record
        { coh = ext (λ _ → coh {f = f})
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
