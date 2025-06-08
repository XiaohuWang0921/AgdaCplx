{-# OPTIONS --without-K --safe #-}

module Cplx where

open import Relation.Binary.Bundles
open import Function.Bundles
open import Level
open import Data.Product
import Relation.Binary.Reasoning.Base.Single as Reasoning

private
  variable
    a b c d x y z r s t u v w : Level

module _ where

  private
    variable
      A : Setoid a r
      B : Setoid b s
      C : Setoid c t
      D : Setoid d u
      
  infixr 0 _⟶ˢ_
  _⟶ˢ_ : Setoid a r → Setoid b s → Setoid _ _
  From ⟶ˢ To = let open Setoid To in record
    { Carrier = From ⟶ₛ To
    ; _≈_ = λ f g → ∀ a → f ⟨$⟩ a ≈ g ⟨$⟩ a
    ; isEquivalence = record
      { refl = λ _ → refl
      ; sym = λ f≈g a → sym (f≈g a)
      ; trans = λ f≈g g≈h a → trans (f≈g a) (g≈h a)
      }
    }
  
  compose : (B ⟶ˢ C) ⟶ₛ (A ⟶ˢ B) ⟶ˢ A ⟶ˢ C
  compose = record
    { to = λ f → record
      { to = λ g → record
        { to = λ a → f ⟨$⟩ (g ⟨$⟩ a)
        ; cong = λ a → f .Func.cong (g .Func.cong a)
        }
      ; cong = λ g≈h a → f .Func.cong (g≈h a)
      }
    ; cong = λ f≈h g a → f≈h (g ⟨$⟩ a)
    }
  
  infixr 9 _∘ₛ_
  _∘ₛ_ : (B ⟶ₛ C) → (A ⟶ₛ B) → A ⟶ₛ C
  f ∘ₛ g = compose ⟨$⟩ f ⟨$⟩ g
  
  flip : (A ⟶ˢ B ⟶ˢ C) ⟶ₛ B ⟶ˢ A ⟶ˢ C
  flip = record
    { to = λ f → record
      { to = λ b → record
        { to = λ a → f ⟨$⟩ a ⟨$⟩ b
      ; cong = λ a≈a' → f .Func.cong a≈a' b
      }
      ; cong = λ b≈b' a → (f ⟨$⟩ a) .Func.cong b≈b'
      }
    ; cong = λ f≈g a b → f≈g b a
    }
  
  const : A ⟶ₛ B ⟶ˢ A
  const {A = A} = let open Setoid A in record
    { to = λ a → record
      { to = λ _ → a
      ; cong = λ _ → refl
      }
    ; cong = λ a≈a' _ → a≈a'
    }
  
  join : (A ⟶ˢ A ⟶ˢ B) ⟶ₛ A ⟶ˢ B
  join {B = B} = let open Setoid B in record
    { to = λ f → record
      { to = λ a → f ⟨$⟩ a ⟨$⟩ a
      ; cong = λ {a} {a'} a≈a' → trans
                 ((f ⟨$⟩ a) .Func.cong a≈a') (f .Func.cong a≈a' a')
      }
    ; cong = λ f≈g a → f≈g a a
    }
  
  id : A ⟶ₛ A
  id = join ⟨$⟩ const
  
  infixr 2 _×ˢ_
  _×ˢ_ : Setoid a r → Setoid b s → Setoid _ _
  A ×ˢ B = record
    { Carrier = A.Carrier × B.Carrier
    ; _≈_ = λ (a , b) (a' , b') → a A.≈ a' × b B.≈ b'
    ; isEquivalence = record
      { refl = A.refl , B.refl
        ; sym = λ (a≈a' , b≈b') → A.sym a≈a' , B.sym b≈b'
      ; trans = λ (a≈a' , b≈b') (a'≈a'' , b'≈b'') →
                  A.trans a≈a' a'≈a'' , B.trans b≈b' b'≈b''
      }
    }
    where
      module A = Setoid A
      module B = Setoid B
  
  fst : A ×ˢ B ⟶ₛ A
  fst = record
    { to = proj₁
    ; cong = proj₁
    }
  
  snd : A ×ˢ B ⟶ₛ B
  snd = record
    { to = proj₂
    ; cong = proj₂
    }
  
  combine : (A ⟶ˢ B) ⟶ₛ (A ⟶ˢ C) ⟶ˢ A ⟶ˢ B ×ˢ C
  combine {B = B} {C = C} = record
    { to = λ f → record
      { to = λ g → record
        { to = λ a → f ⟨$⟩ a , g ⟨$⟩ a
          ; cong = λ a≈a' → f .Func.cong a≈a' , g .Func.cong a≈a'
        }
      ; cong = λ g≈g' a → B.refl , g≈g' a
      }
    ; cong = λ f≈f' _ a → f≈f' a , C.refl
    }
    where
      module B = Setoid B
      module C = Setoid C
  
  <_,_>ₛ : (A ⟶ₛ B) → (A ⟶ₛ C) → A ⟶ₛ B ×ˢ C
  < f , g >ₛ = combine ⟨$⟩ f ⟨$⟩ g
    
  Equaliser : (f g : A ⟶ₛ B) → Setoid _ _
  Equaliser {A = A} {B = B} f g = record
    { Carrier = Σ Carrier λ a → f ⟨$⟩ a ≈₂ g ⟨$⟩ a
    ; _≈_ = λ (a , _) (a' , _) → a ≈₁ a'
    ; isEquivalence = record
      { refl = refl
      ; sym = sym
      ; trans = trans
      }
    }
    where
      open Setoid A renaming (_≈_ to _≈₁_)
      open Setoid B using () renaming (_≈_ to _≈₂_)
  
  defactorise : (f g : B ⟶ₛ C) →
    (A ⟶ˢ Equaliser f g) ⟶ₛ
    Equaliser (compose {A = A} ⟨$⟩ f) (compose ⟨$⟩ g)
  defactorise _ _ = record
    { to = λ h → record
      { to = λ a → (h ⟨$⟩ a) .proj₁
      ; cong = h .Func.cong
      } , λ a → (h ⟨$⟩ a) .proj₂
    ; cong = λ h≈h' → h≈h'
    }

  equaliser : (f g : A ⟶ₛ B) → Equaliser f g ⟶ₛ A
  equaliser f g = (defactorise f g ⟨$⟩ id) .proj₁
  
  equaliser-eq : (f g : A ⟶ₛ B) → let open Setoid (Equaliser f g ⟶ˢ B) in f ∘ₛ equaliser f g ≈ g ∘ₛ equaliser f g
  equaliser-eq f g = proj₂

  compose-eqlˡ : (f g : C ⟶ₛ D) →
    Equaliser (compose {A = B} ⟨$⟩ f) (compose ⟨$⟩ g) ⟶ₛ
    (A ⟶ˢ B) ⟶ˢ Equaliser (compose {A = A} ⟨$⟩ f) (compose ⟨$⟩ g)
  compose-eqlˡ f g = record
    { to = λ (h , h-eq) → record
      { to = λ j → h ∘ₛ j , λ a → h-eq (j ⟨$⟩ a)
      ; cong = λ j≈j' a → h .Func.cong (j≈j' a)
      }
    ; cong = λ h≈h' j a → h≈h' (j ⟨$⟩ a)
    }

  compose-eqlʳ : (f g : B ⟶ₛ C) (h : C ⟶ₛ D) →
    Equaliser (compose {A = A} ⟨$⟩ f) (compose ⟨$⟩ g) ⟶ₛ
    Equaliser (compose {A = A} ⟨$⟩ h ∘ₛ f) (compose ⟨$⟩ h ∘ₛ f)
  compose-eqlʳ {D = D} f g h = let open Setoid D in record
    { to = λ (j , j-eq) → j , λ a → refl
    ; cong = λ j≈j' → j≈j'
    }
  
  factorise : (f g : B ⟶ₛ C) →
              Equaliser (compose {A = A} ⟨$⟩ f) (compose ⟨$⟩ g) ⟶ₛ
              A ⟶ˢ Equaliser f g
  factorise _ _ = record
    { to = λ (h , h-eq) → record
      { to = λ z → h ⟨$⟩ z , h-eq z
      ; cong = h .Func.cong
      }
    ; cong = λ h≈h' → h≈h'
    }
  
  <_≈_for_w/_>⁼ : (f g : B ⟶ₛ C) (h : A ⟶ₛ B) →
                (let open Setoid (A ⟶ˢ C) in f ∘ₛ h ≈ g ∘ₛ h) → A ⟶ₛ Equaliser f g
  < f ≈ g for h w/ h-eq >⁼ = factorise f g ⟨$⟩ (h , h-eq)
  
module Single (X : Setoid x u) (Y : Setoid y v) (α : X ⟶ₛ Y) where
  module X = Setoid X
  module Y = Setoid Y

  record Cplx a r : Set (suc (a ⊔ r) ⊔ x ⊔ u ⊔ y ⊔ v) where
    field
      setoid : Setoid a r
      ϕ : (X ⟶ˢ setoid) ⟶ₛ (Y ⟶ˢ setoid)

    open Setoid setoid public

    fill : (X ⟶ₛ setoid) → Y.Carrier → Carrier
    fill h y = ϕ ⟨$⟩ h ⟨$⟩ y

    open Func ϕ renaming (cong to fill-cong) public

    field
      sec : ∀ h x → fill h (α ⟨$⟩ x) ≈ h ⟨$⟩ x
      proj : ∀ s y → fill (const ⟨$⟩ s) y ≈ s
      diag : ∀ hh y → fill (flip ⟨$⟩ ϕ ∘ₛ hh ⟨$⟩ y) y ≈ fill (join ⟨$⟩ hh) y
      braid : ∀ hh y y' → fill (flip ⟨$⟩ ϕ ∘ₛ hh ⟨$⟩ y') y ≈
              fill (flip ⟨$⟩ (ϕ ∘ₛ (flip ⟨$⟩ hh)) ⟨$⟩ y) y'

  Coh : Cplx a r → Cplx b s → Setoid _ _
  Coh A B = Equaliser ((flip ⟨$⟩ compose ⟨$⟩ A.ϕ) ∘ₛ compose) ((compose ⟨$⟩ B.ϕ) ∘ₛ compose)
    where
      module A = Cplx A
      module B = Cplx B

  private
    variable
      A : Cplx a r
      B : Cplx b s
      C : Cplx c t

  _×ᶜ_ : Cplx a r → Cplx a s → Cplx _ _
  A ×ᶜ B = record
    { setoid = A.setoid ×ˢ B.setoid
    ; ϕ = join ⟨$⟩ (flip ⟨$⟩ compose ⟨$⟩ B.ϕ ∘ₛ (compose ⟨$⟩ snd)) ∘ₛ combine ∘ₛ A.ϕ ∘ₛ (compose ⟨$⟩ fst)
    ; sec = λ h x →
               A.sec (compose ⟨$⟩ fst ⟨$⟩ h) x ,
               B.sec (compose ⟨$⟩ snd ⟨$⟩ h) x
    ; proj = λ s y → A.proj (proj₁ s) y , B.proj (proj₂ s) y
    ; diag = λ hh y →
      A.trans
        (A.fill-cong (λ _ → A.refl) y)
        (A.diag ((compose ⟨$⟩ fst) ∘ₛ hh) y) ,
      B.trans
        (B.fill-cong (λ _ → B.refl) y)
        (B.diag ((compose ⟨$⟩ snd) ∘ₛ hh) y)
    ; braid = λ hh y y' →
      A.trans
        (A.trans
          (A.fill-cong (λ _ → A.refl) y)
          (A.braid ((compose ⟨$⟩ fst) ∘ₛ hh) y y'))
        (A.fill-cong (λ _ → A.refl) y') ,
      B.trans
        (B.fill-cong (λ _ → B.refl) y)
        (B.trans
          (B.braid ((compose ⟨$⟩ snd) ∘ₛ hh) y y')
          (B.fill-cong (λ _ → B.refl) y'))
    }
    where
      module A = Cplx A
      module B = Cplx B
