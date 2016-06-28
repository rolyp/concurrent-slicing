module Name.Lattice where

   open import ConcurrentSlicingCommon hiding (preorder)
   import Relation.Binary.PreorderReasoning as PreorderReasoning

   import Ext.Algebra.Properties.Lattice hiding (module Eq)

   open import Lattice using (Lattices; module Lattices; Prefixes)
   open import Name as ᴺ using (Name)

   data ↓_ {Γ} : Name Γ → Set where
      ◻ : {x : Name Γ} → ↓ x
      [_] : (x : Name Γ) → ↓ x

   data _≤_ {Γ} : {x : Name Γ} → ↓ x → ↓ x → Set where
      ◻ : {x : Name Γ} {u : ↓ x} → ◻ ≤ u
      [_] : (x : Name Γ) → [ x ] ≤ [ x ]

   -- Probably overkill.
   to-↓ : ∀ {Γ} (x : Name Γ) → ↓ x
   to-↓ = [_]

   infixr 6 _⊔_
   _⊔_ : ∀ {Γ} {x₀ : Name Γ} → (x x′ : ↓ x₀) → ↓ x₀
   ◻ ⊔ x = x
   x ⊔ ◻ = x
   [ x ] ⊔ [ .x ] = [ x ]

   infixr 7 _⊓_
   _⊓_ : ∀ {Γ} {x₀ : Name Γ} → (x x′ : ↓ x₀) → ↓ x₀
   ◻ ⊓ x = ◻
   x ⊓ ◻ = ◻
   [ x ] ⊓ [ .x ] = [ x ]

   ⊓-comm : ∀ {Γ} {x : Name Γ} → Commutative _≡_ (_⊓_ {x₀ = x})
   ⊓-comm ◻ ◻ = refl
   ⊓-comm ◻ [ _ ] = refl
   ⊓-comm [ _ ] ◻ = refl
   ⊓-comm [ x ] [ .x ] = refl

   ⊔-comm : ∀ {Γ} {x : Name Γ} → Commutative _≡_ (_⊔_ {x₀ = x})
   ⊔-comm ◻ ◻ = refl
   ⊔-comm ◻ [ _ ] = refl
   ⊔-comm [ _ ] ◻ = refl
   ⊔-comm [ x ] [ .x ] = refl

   ⊓-assoc : ∀ {Γ} {x : Name Γ} → Associative _≡_ (_⊓_ {x₀ = x})
   ⊓-assoc ◻ _ _ = refl
   ⊓-assoc [ _ ] ◻ _ = refl
   ⊓-assoc [ _ ] [ ._ ] ◻ = refl
   ⊓-assoc [ _ ] [ ._ ] [ ._ ] = refl

   ⊔-assoc : ∀ {Γ} {x : Name Γ} → Associative _≡_ (_⊔_ {x₀ = x})
   ⊔-assoc ◻ _ _ = refl
   ⊔-assoc [ _ ] ◻ _ = refl
   ⊔-assoc [ _ ] [ ._ ] ◻ = refl
   ⊔-assoc [ _ ] [ ._ ] [ ._ ] = refl

   ⊔-absorbs-⊓ : ∀ {Γ} {x : Name Γ} → _Absorbs_ _≡_ (_⊔_ {x₀ = x}) _⊓_
   ⊔-absorbs-⊓ ◻ ◻ = refl
   ⊔-absorbs-⊓ ◻ [ _ ] = refl
   ⊔-absorbs-⊓ [ _ ] ◻ = refl
   ⊔-absorbs-⊓ [ _ ] [ ._ ] = refl

   ⊓-absorbs-⊔ : ∀ {Γ} {x : Name Γ} → _Absorbs_ _≡_ (_⊓_ {x₀ = x}) _⊔_
   ⊓-absorbs-⊔ ◻ ◻ = refl
   ⊓-absorbs-⊔ ◻ [ _ ] = refl
   ⊓-absorbs-⊔ [ _ ] ◻ = refl
   ⊓-absorbs-⊔ [ _ ] [ ._ ] = refl

   isLattice : ∀ {Γ} {x : Name Γ} → IsLattice _≡_ (_⊔_ {x₀ = x}) _⊓_
   isLattice = record {
         isEquivalence = isEquivalence;
         ∨-comm = ⊔-comm;
         ∨-assoc = ⊔-assoc;
         ∨-cong = cong₂ _⊔_;
         ∧-comm = ⊓-comm;
         ∧-assoc = ⊓-assoc;
         ∧-cong = cong₂ _⊓_;
         absorptive = ⊔-absorbs-⊓ , ⊓-absorbs-⊔
      }

   private
      lattices : ∀ {Γ} → Lattices (Name Γ)
      lattices = record {
            ↓_ = ↓_; ↓⁻_ = ↓_; _⊔⁻_ = _⊔_; _⊔_ = _⊔_; _⊓⁻_ = _⊓_; _⊓_ = _⊓_; isLattice⁻ = isLattice; isLattice = isLattice
         }

      open Lattices using (_≤ᴸ_)

   ≤ᴸ⇒≤ : ∀ {Γ} {x : Name Γ} → _≤ᴸ_ lattices {a = x} ⇒ _≤_
   ≤ᴸ⇒≤ {i = ◻} x = ◻
   ≤ᴸ⇒≤ {i = [ x ]} {[ .x ]} refl = [ x ]
   ≤ᴸ⇒≤ {i = [ x ]} {◻} ()

   ≤⇒≤ᴸ : ∀ {Γ} {x : Name Γ} → _≤_ ⇒ _≤ᴸ_ lattices {a = x}
   ≤⇒≤ᴸ ◻ = refl
   ≤⇒≤ᴸ [ x ] = refl

   instance
      prefixes : ∀ {Γ} → Prefixes (Name Γ)
      prefixes = record {
            lattices = lattices; _≤_ = _≤_; _≤⁻_ = _≤_; ≤⁻ᴸ⇒≤⁻ = ≤ᴸ⇒≤; ≤ᴸ⇒≤ = ≤ᴸ⇒≤; ≤⁻⇒≤⁻ᴸ = ≤⇒≤ᴸ; ≤⇒≤ᴸ = ≤⇒≤ᴸ
         }

   zero : ∀ {Γ} → ↓ (ᴺ.zero {Γ})
   zero = [ ᴺ.zero ]

   suc : ∀ {Γ} {x : Name Γ} → ↓ x → ↓ ᴺ.suc x
   suc ◻ = ◻
   suc [ x ] = [ ᴺ.suc x ]

   sucᴹ : ∀ {Γ} {x : Name Γ} {x′ x″ : ↓ x} → x′ ≤ x″ → suc x′ ≤ suc x″
   sucᴹ ◻ = ◻
   sucᴹ [ x ] = [ ᴺ.suc x ]
