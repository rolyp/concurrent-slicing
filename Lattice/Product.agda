open import Lattice using (Prefixes)

module Lattice.Product
   (A : Set)
   (B : A → Set)
   ⦃ ᴬprefixes : Prefixes A ⦄
   ⦃ ᴮprefixes : {a : A} → Prefixes (B a) ⦄ where

   open import ConcurrentSlicingCommon hiding (_-×-_)
   open import Ext
   import Ext.Algebra.Properties.Lattice.Product

   open Lattice using (module Prefixes); open Prefixes ⦃...⦄

   ×-prefixes : Prefixes (Σ[ a ∈ A ] B a)
   ×-prefixes = record {
         lattices = record {
               ↓_ = λ { (a , b) → ↓ a × ↓ b };
               ↓⁻_ = λ { (a , b) → ↓⁻ a × ↓⁻ b };
               _⊔⁻_ = Lattice⁻._∨_;
               _⊔_ = Lattice′._∨_;
               _⊓⁻_ = Lattice⁻._∧_;
               _⊓_ = Lattice′._∧_;
               isLattice⁻ = Lattice⁻.isLattice;
               isLattice = Lattice′.isLattice
            };
         _≤_ = _≤_ -×- _≤_;
         _≤⁻_ = _≤⁻_ -×- _≤⁻_;
         ≤⁻ᴸ⇒≤⁻ = ≤⁻ᴸ⇒≤⁻ ⟨ map ⟩ ≤⁻ᴸ⇒≤⁻;
         ≤ᴸ⇒≤ = ≤ᴸ⇒≤ ⟨ map ⟩ ≤ᴸ⇒≤;
         ≤⁻⇒≤⁻ᴸ = ≤⁻⇒≤⁻ᴸ ⟨ map ⟩ ≤⁻⇒≤⁻ᴸ;
         ≤⇒≤ᴸ = ≤⇒≤ᴸ ⟨ map ⟩ ≤⇒≤ᴸ
      }
      where
         module Lattice⁻ {ab : Σ[ a ∈ A ] B a} = Ext.Algebra.Properties.Lattice.Product
            (isLattice⁻ {a = π₁ ab}) (isLattice⁻ {a = π₂ ab})

         module Lattice′ {ab : Σ[ a ∈ A ] B a} = Ext.Algebra.Properties.Lattice.Product
            (isLattice {a = π₁ ab}) (isLattice {a = π₂ ab})
