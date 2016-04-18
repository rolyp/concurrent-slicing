module Ren.Lattice.GaloisConnection where

   open import ConcurrentSlicingCommon hiding (poset)
   open import Ext.Algebra

   import Lattice; open Lattice.Prefixes ⦃...⦄
   open import Name as ᴺ using (Name; zero; _≟_)
   open import Name.Lattice as ᴺ̃ using (sucᴹ); open ᴺ̃.↓_; open ᴺ̃._≤_
   open import Ren as ᴿ using (Ren; ᴺren); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice as ᴿ̃ using (◻≤; get; getᴹ; put; putᴹ; _*ᴹ; suc; pre) renaming (◻ to ◻′; _* to _*̃)

   id≤get∘put : ∀ {Γ Γ′} {ρ₀ : Ren Γ Γ′} (x₀ : Name Γ) (u : ↓ (ρ₀ *) x₀) → let ρ , x = put ρ₀ x₀ u in u ≤ (ρ *̃) x
   id≤get∘put _ ◻ = ◻
   id≤get∘put {ρ₀ = ρ₀} x [ ._ ] with x ≟ x
   ... | yes refl = [ ρ₀ x ]
   ... | no x≢x = ⊥-elim (x≢x refl)

   put₁∘get≤id : ∀ {Γ Γ′} {ρ₀ : Ren Γ Γ′} {x₀ : Name Γ} (x : ↓ x₀) (ρ : ↓ ρ₀) → π₁ (put ρ₀ x₀ ((ρ *̃) x)) ≤ ρ
   put₁∘get≤id ◻ _ = ◻≤
   put₁∘get≤id [ x ] ρ y with x ≟ y
   put₁∘get≤id [ x ] ρ .x | yes refl with ρ x
   ... | ◻ = ◻
   ... | [ ._ ] with x ≟ x
   ... | yes refl = [ _ ]
   ... | no x≢x = ⊥-elim (x≢x refl)
   put₁∘get≤id [ x ] ρ y | no _ with ρ x
   ... | ◻ = ◻
   ... | [ ._ ] with x ≟ y
   put₁∘get≤id [ x ] ρ .x | no x≢x | [ ._ ] | yes refl = ⊥-elim (x≢x refl)
   ... | no _ = ◻

   put₂∘get≤id : ∀ {Γ Γ′} {ρ₀ : Ren Γ Γ′} {x₀ : Name Γ} (x : ↓ x₀) (ρ : ↓ ρ₀) → π₂ (put ρ₀ x₀ ((ρ *̃) x)) ≤ x
   put₂∘get≤id ◻ ρ = ◻
   put₂∘get≤id [ x ] ρ with ρ x
   ... | ◻ = ◻
   ... | [ ._ ] = [ x ]

   put∘get≤id : ∀ {Γ Γ′} {ρ₀ : Ren Γ Γ′} {x₀ : Name Γ} (x : ↓ x₀) (ρ : ↓ ρ₀) →
                let u = (ρ *̃) x; ρ′ , x′ = put ρ₀ x₀ u in ρ′ ≤ ρ × x′ ≤ x
   put∘get≤id x ρ = put₁∘get≤id x ρ , put₂∘get≤id x ρ

   import Ext.Algebra.Properties.Lattice.Product
   module Lattice′ {Γ Γ′} {ρx : Ren Γ Γ′ × Name Γ} = Ext.Algebra.Properties.Lattice.Product
      (isLattice {a = π₁ ρx}) (isLattice {a = π₂ ρx})

   gc : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) (x : Name Γ) → GaloisConnection (Lattice′.poset {ρx = ρ , x}) (poset {a = (ρ *) x})
   gc ρ x = ⟪ get {ρ = ρ} {x = x}, put ρ x ~ isGC ⟫
      where
         isGC = record {
               f-mono = λ { _ _ (ρ , x) → ≤⇒≤ᴸ (getᴹ (≤ᴸ⇒≤ ρ , ≤ᴸ⇒≤ x)) };
               g-mono = λ _ _ u → let ρ′ , x′ = putᴹ ρ x (≤ᴸ⇒≤ u) in ≤⇒≤ᴸ ρ′ , ≤⇒≤ᴸ x′;
               id≤f∘g = ≤⇒≤ᴸ ∘ᶠ id≤get∘put x;
               g∘f≤id = λ { (ρ , x) → let ρ′ , x′ = put∘get≤id x ρ in ≤⇒≤ᴸ ρ′ , ≤⇒≤ᴸ x′ }
            }

   -- (suc, pre) is a degenerate Galois connection.
   id≤suc∘pre : ∀ {Γ Γ′} {ρ₀ : Ren Γ Γ′} (ρ : ↓ ᴿ.suc ρ₀) → ρ ≤ suc (pre ρ)
   id≤suc∘pre ρ zero with ρ zero
   ... | ◻ = ◻
   ... | [ .zero ] = [ zero ]
   id≤suc∘pre {ρ₀ = ρ₀} ρ (ᴺ.suc x) with ρ (ᴺ.suc x)
   ... | ◻ = ◻
   ... | [ ._ ] = [ ᴺ.suc (ρ₀ x) ]

   pre∘suc≡id : ∀ {Γ Γ′} {ρ₀ : Ren Γ Γ′} (ρ : ↓ ρ₀) → pre (suc ρ) ≃ₑ ρ
   pre∘suc≡id ρ x with pre (suc ρ) x | ρ x
   ... | ◻ | ◻ = refl
   ... | ◻ | [ ._ ] = refl
   ... | [ ._ ] | ◻ = refl
   ... | [ ._ ] | [ ._ ] = refl
