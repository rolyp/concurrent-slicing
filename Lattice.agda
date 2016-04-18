module Lattice where

   open import ConcurrentSlicingCommon hiding (preorder)
   import Relation.Binary.PreorderReasoning as PreorderReasoning
   import Level

   import Ext.Algebra.Properties.Lattice

   record Lattices {𝑎} {𝑙} (A : Set 𝑎) : Set (Level.suc 𝑎 Level.⊔ Level.suc 𝑙) where
      infixr 6 _⊔⁻_ _⊔_
      infixr 7 _⊓⁻_ _⊓_
      field
         -- Finite lattices of prefixes.
         ↓_ : A → Set
         -- Variant which can be convenient to introduce a case distinction for ε at the top level.
         ↓⁻_ : A → Set
         -- Compatible join and meet.
         _⊔⁻_ : ∀ {a₀ : A} (a a′ : ↓⁻ a₀) → ↓⁻ a₀
         _⊔_ : ∀ {a₀ : A} (a a′ : ↓ a₀) → ↓ a₀
         _⊓⁻_ : ∀ {a₀ : A} (a a′ : ↓⁻ a₀) → ↓⁻ a₀
         _⊓_ : ∀ {a₀ : A} (a a′ : ↓ a₀) → ↓ a₀
         {_≈⁻_} : ∀ {a : A} → Rel (↓⁻ a) 𝑙
         {_≈_} : ∀ {a : A} → Rel (↓ a) 𝑙
         isLattice⁻ : ∀ {a : A} → IsLattice _≈⁻_ (_⊔⁻_ {a₀ = a}) (_⊓⁻_ {a₀ = a})
         isLattice : ∀ {a : A} → IsLattice _≈_ (_⊔_ {a₀ = a}) (_⊓_ {a₀ = a})

      private
         open module LatticeProps⁻ {a : A} = Ext.Algebra.Properties.Lattice
            (record { isLattice = isLattice⁻ {a = a} }) public
            using () renaming (
               ∨ˡ to ∨⁻ˡ; ∨ʳ to ∨⁻ʳ; _≤_ to _≤⁻ᴸ_; reflexive to reflexive⁻ᴸ; ≤-refl to ≤⁻-reflᴸ; trans to trans⁻ᴸ
            )

         open module LatticeProps {a : A} = Ext.Algebra.Properties.Lattice
            (record { isLattice = isLattice {a = a} }) public
            using (∨ˡ; ∨ʳ; _∨-lub_; _∨-compatible_; poset)
            renaming (
               _≤_ to _≤ᴸ_; reflexive to reflexiveᴸ; ≤-refl to ≤-reflᴸ; trans to transᴸ;
               ∨-idempotent to ⊔-idem; ∧-idempotent to ⊓-idem
            )

   record Prefixes {𝑎} (A : Set 𝑎) : Set (Level.suc 𝑎) where
      field
         lattices : Lattices A
      open Lattices lattices public

      infix 4 _≤⁻_ _≤_
      field
         -- Additional definition of the partial order (e.g. an inductive one, if useful) implied by meet/join.
         _≤_ : ∀ {a : A} → ↓ a → ↓ a → Set
         _≤⁻_ : ∀ {a : A} → ↓⁻ a → ↓⁻ a → Set

      field
         -- Partial order induced by ⊓ agrees with our "convenient" (typically inductive) definition.
         ≤⁻ᴸ⇒≤⁻ : ∀ {a : A} → _≤⁻ᴸ_ {a = a} ⇒ _≤⁻_
         ≤ᴸ⇒≤ : ∀ {a : A} → _≤ᴸ_ {a = a} ⇒ _≤_
         ≤⁻⇒≤⁻ᴸ : ∀ {a : A} → _≤⁻_ ⇒ _≤⁻ᴸ_ {a = a}
         ≤⇒≤ᴸ : ∀ {a : A} → _≤_ ⇒ _≤ᴸ_ {a = a}

      preorder⁻ : ∀ {a : A} → Preorder _ _ _
      preorder⁻ {a = a} = record {
            _≈_ = _≈⁻_;
            _∼_ = _≤⁻_ {a = a};
            isPreorder = record {
                  isEquivalence = IsLattice.isEquivalence isLattice⁻;
                  reflexive = ≤⁻ᴸ⇒≤⁻ ∘ᶠ reflexive⁻ᴸ;
                  trans = λ x≤ᴸy y≤ᴸz → ≤⁻ᴸ⇒≤⁻ (trans⁻ᴸ (≤⁻⇒≤⁻ᴸ x≤ᴸy) (≤⁻⇒≤⁻ᴸ y≤ᴸz))
               }
         }

      preorder : ∀ {a : A} → Preorder _ _ _
      preorder {a = a} = record {
            _≈_ = _≈_;
            _∼_ = _≤_ {a = a};
            isPreorder = record {
                  isEquivalence = IsLattice.isEquivalence isLattice;
                  reflexive = ≤ᴸ⇒≤ ∘ᶠ reflexiveᴸ;
                  trans = λ x≤ᴸy y≤ᴸz → ≤ᴸ⇒≤ (transᴸ (≤⇒≤ᴸ x≤ᴸy) (≤⇒≤ᴸ y≤ᴸz))
               }
         }

      private
         open module Preorder⁻ {a : A} = Preorder (preorder⁻ {a = a}) public
            using () renaming (reflexive to ≤⁻-reflexive; trans to ≤⁻-trans)

         open module Preorder′ {a : A} = Preorder (preorder {a = a}) public
            using () renaming (reflexive to ≤-reflexive; trans to ≤-trans)

      -- This naming convention arises because one can think of reflexivity as nullary monotonicity.
      ⁻ᴹ : ∀ {a₀ : A} (a : ↓⁻ a₀) → a ≤⁻ a
      ⁻ᴹ P = Preorder⁻.refl

      ᴹ : ∀ {a₀ : A} (a : ↓ a₀) → a ≤ a
      ᴹ P = Preorder′.refl

      -- Extension of substitutability to the partial order.
      substᴹ : {a a′ : A} {P P′ : ↓ a} → P ≤ P′ → (q : a ≡ a′) → subst ↓_ q P ≤ subst ↓_ q P′
      substᴹ P refl = P

      module ≤⁻-Reasoning {a : A} = PreorderReasoning (preorder⁻ {a = a}) renaming (_∼⟨_⟩_ to _≤⁻⟨_⟩_)
      module ≤-Reasoning {a : A} = PreorderReasoning (preorder {a = a}) renaming (_∼⟨_⟩_ to _≤⟨_⟩_)

      infixr 6 _⊔⁻ˡ_ _⊔ˡ_ _⊔⁻ʳ_ _⊔ʳ_ _⊔-lub_ _⊔ᴹ_

      _⊔⁻ˡ_ : ∀ {a₀ : A} (a′ a : ↓⁻ a₀) → a ≤⁻ a′ ⊔⁻ a
      a′ ⊔⁻ˡ _ = ≤⁻ᴸ⇒≤⁻ (∨⁻ˡ {y = a′}) -- for some reason Agda needs some help in this case

      _⊔ˡ_ : ∀ {a₀ : A} (a′ a : ↓ a₀) → a ≤ a′ ⊔ a
      _ ⊔ˡ _ = ≤ᴸ⇒≤ ∨ˡ

      _⊔⁻ʳ_ : ∀ {a₀ : A} (a a′ : ↓⁻ a₀) → a ≤⁻ a ⊔⁻ a′
      _ ⊔⁻ʳ _ = ≤⁻ᴸ⇒≤⁻ ∨⁻ʳ

      _⊔ʳ_ : ∀ {a₀ : A} (a a′ : ↓ a₀) → a ≤ a ⊔ a′
      _ ⊔ʳ _ = ≤ᴸ⇒≤ ∨ʳ

      _⊔-lub_ : ∀ {a₀ : A} {a₁ a₂ a : ↓ a₀} → a₁ ≤ a → a₂ ≤ a → a₁ ⊔ a₂ ≤ a
      a₁ ⊔-lub a₂ = ≤ᴸ⇒≤ (≤⇒≤ᴸ a₁ ∨-lub ≤⇒≤ᴸ a₂)

      _⊔ᴹ_ : ∀ {a₀ : A} {a₁ a₂ a₁′ a₂′ : ↓ a₀} → a₁ ≤ a₁′ → a₂ ≤ a₂′ → a₁ ⊔ a₂ ≤ a₁′ ⊔ a₂′
      a ⊔ᴹ a′ = ≤ᴸ⇒≤ (≤⇒≤ᴸ a ∨-compatible ≤⇒≤ᴸ a′)
