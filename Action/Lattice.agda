module Action.Lattice where

   open import ConcurrentSlicingCommon hiding (preorder)
   import Relation.Binary.EqReasoning as EqReasoning
   import Relation.Binary.PreorderReasoning as PreorderReasoning

   import Ext.Algebra.Properties.Lattice

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ; _ᵇ; _ᶜ); open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Lattice using (Lattices; module Lattices; Prefixes; module Prefixes);
      open Prefixes ⦃...⦄ using () renaming (
            ↓_ to ↓′_; ↓⁻_ to ↓⁻′_; _≤⁻_ to _≤⁻′_; _≤_ to _≤′_; ≤ᴸ⇒≤ to ≤′ᴸ⇒≤′; ≤⇒≤ᴸ to ≤′⇒≤′ᴸ;
            _⊓_ to _⊓′_; _⊓⁻_ to _⊓⁻′_; _⊔_ to _⊔′_; _⊔⁻_ to _⊔⁻′_; ⊓-idem to ⊓′-idem; ⊔-idem to ⊔′-idem
         )
   open import Name as ᴺ using (Cxt; Name)
   open import Name.Lattice as ᴺ̃ using ([_])

   data ↓ᵇ_ {Γ : Cxt} : Actionᵇ Γ → Set where
      _• : (x : Name Γ) → ↓ᵇ x •
      •_ : (x : Name Γ) → ↓ᵇ • x

   data ↓ᶜ_ {Γ : Cxt} : Actionᶜ Γ → Set where
      •_〈_〉 : (x : Name Γ) {y : Name Γ} → ↓′ y → ↓ᶜ • x 〈 y 〉
      τ : ↓ᶜ τ {Γ}

   data ↓_ {Γ : Cxt} : Action Γ → Set where
      _ᵇ : {a : Actionᵇ Γ} → ↓ᵇ a → ↓ a ᵇ
      _ᶜ : {a : Actionᶜ Γ} → ↓ᶜ a → ↓ a ᶜ

   data _≤ᵇ_ {Γ : Cxt} : {a : Actionᵇ Γ} → ↓ᵇ a → ↓ᵇ a → Set where
      _• : (x : Name Γ) → x • ≤ᵇ x •
      •_ : (x : Name Γ) → • x ≤ᵇ • x

   data _≤ᶜ_ {Γ : Cxt} : {a : Actionᶜ Γ} → ↓ᶜ a → ↓ᶜ a → Set where
      •_〈_〉 : (x : Name Γ) {y : Name Γ} {y′ y″ : ↓′ y} → y′ ≤′ y″ → • x 〈 y′ 〉 ≤ᶜ • x 〈 y″ 〉
      τ : τ ≤ᶜ τ

   data _≤_ {Γ : Cxt} : ∀ {a : Action Γ} → ↓ a → ↓ a → Set where
      _ᵇ : {a : Actionᵇ Γ} {a′ a″ : ↓ᵇ a} → a′ ≤ᵇ a″ → a′ ᵇ ≤ a″ ᵇ
      _ᶜ : {a : Actionᶜ Γ} {a′ a″ : ↓ᶜ a} → a′ ≤ᶜ a″ → a′ ᶜ ≤ a″ ᶜ

   -- a is the greatest prefix of itself.
   to-↓ : ∀ {Γ} (a : Action Γ) → ↓ a
   to-↓ (x • ᵇ) = x • ᵇ
   to-↓ ((• x) ᵇ) = (• x) ᵇ
   to-↓ (• x 〈 y 〉 ᶜ) = • x 〈 [ y ] 〉 ᶜ
   to-↓ (τ ᶜ) = τ ᶜ

   -- Least prefix of a.
   ᴬ◻ : ∀ {Γ} {a : Action Γ} → ↓ a
   ᴬ◻ {a = (x •) ᵇ} = x • ᵇ
   ᴬ◻ {a = (• x) ᵇ} = (• x) ᵇ
   ᴬ◻ {a = • x 〈 y 〉 ᶜ} = • x 〈 ᴺ̃.◻ 〉 ᶜ
   ᴬ◻ {a = τ ᶜ} = τ ᶜ

   top : ∀ {Γ} (a : Action Γ) {a′ : ↓ a} → a′ ≤ to-↓ a
   top (x • ᵇ) {.x • ᵇ} = x • ᵇ
   top ((• x) ᵇ) {(• .x) ᵇ} = (• x) ᵇ
   top (• x 〈 y 〉 ᶜ) {• .x 〈 ᴺ̃.◻ 〉 ᶜ} = • x 〈 ᴺ̃.◻ 〉 ᶜ
   top (• x 〈 y 〉 ᶜ) {• .x 〈 [ .y ] 〉 ᶜ} = • x 〈 [ y ] 〉 ᶜ
   top (τ ᶜ) {τ ᶜ} = τ ᶜ

   _⊓_ : ∀ {Γ} {a₀ : Action Γ} → (a a′ : ↓ a₀) → ↓ a₀
   x • ᵇ ⊓ .x • ᵇ = x • ᵇ
   (• x) ᵇ ⊓ (• .x) ᵇ = (• x) ᵇ
   • x 〈 y 〉 ᶜ ⊓ • .x 〈 y′ 〉 ᶜ = • x 〈 y ⊓′ y′ 〉 ᶜ
   τ ᶜ ⊓ τ ᶜ = τ ᶜ

   _⊔_ : ∀ {Γ} {a₀ : Action Γ} → (a a′ : ↓ a₀) → ↓ a₀
   x • ᵇ ⊔ .x • ᵇ = x • ᵇ
   (• x) ᵇ ⊔ (• .x) ᵇ = (• x) ᵇ
   • x 〈 y 〉 ᶜ ⊔ • .x 〈 y′ 〉 ᶜ = • x 〈 y ⊔′ y′ 〉 ᶜ
   τ ᶜ ⊔ τ ᶜ = τ ᶜ

   ⊓-comm : ∀ {Γ} {a : Action Γ} → Commutative _≡_ (_⊓_ {a₀ = a})
   ⊓-comm (x • ᵇ) (.x • ᵇ) = refl
   ⊓-comm ((• x) ᵇ) ((• .x) ᵇ) = refl
   ⊓-comm (• x 〈 y 〉 ᶜ) (• .x 〈 y′ 〉 ᶜ) = cong (λ y → • x 〈 y 〉 ᶜ) (ᴺ̃.⊓-comm y y′)
   ⊓-comm (τ ᶜ) (τ ᶜ) = refl

   ⊓-assoc : ∀ {Γ} {a : Action Γ} → Associative _≡_ (_⊓_ {a₀ = a})
   ⊓-assoc (x • ᵇ) (.x • ᵇ) (.x • ᵇ) = refl
   ⊓-assoc ((• x) ᵇ) ((• .x) ᵇ) ((• .x) ᵇ) = refl
   ⊓-assoc (• x 〈 y₁ 〉 ᶜ) (• .x 〈 y₂ 〉 ᶜ) (• .x 〈 y₃ 〉 ᶜ) = cong (λ y → • x 〈 y 〉 ᶜ) (ᴺ̃.⊓-assoc y₁ y₂ y₃)
   ⊓-assoc (τ ᶜ) (τ ᶜ) (τ ᶜ) = refl

   ⊔-comm : ∀ {Γ} {a : Action Γ} → Commutative _≡_ (_⊔_ {a₀ = a})
   ⊔-comm (x • ᵇ) (.x • ᵇ) = refl
   ⊔-comm ((• x) ᵇ) ((• .x) ᵇ) = refl
   ⊔-comm (• x 〈 y 〉 ᶜ) (• .x 〈 y′ 〉 ᶜ) = cong (λ y → • x 〈 y 〉 ᶜ) (ᴺ̃.⊔-comm y y′)
   ⊔-comm (τ ᶜ) (τ ᶜ) = refl

   ⊔-assoc : ∀ {Γ} {a : Action Γ} → Associative _≡_ (_⊔_ {a₀ = a})
   ⊔-assoc (x • ᵇ) (.x • ᵇ) (.x • ᵇ) = refl
   ⊔-assoc ((• x) ᵇ) ((• .x) ᵇ) ((• .x) ᵇ) = refl
   ⊔-assoc (• x 〈 y₁ 〉 ᶜ) (• .x 〈 y₂ 〉 ᶜ) (• .x 〈 y₃ 〉 ᶜ) = cong (λ y → • x 〈 y 〉 ᶜ) (ᴺ̃.⊔-assoc y₁ y₂ y₃)
   ⊔-assoc (τ ᶜ) (τ ᶜ) (τ ᶜ) = refl

   ⊔-idem : ∀ {Γ} {a : Action Γ} → Idempotent _≡_ (_⊔_ {a₀ = a})
   ⊔-idem (x • ᵇ) = refl
   ⊔-idem ((• x) ᵇ) = refl
   ⊔-idem (• x 〈 y 〉 ᶜ) = cong (λ y → • x 〈 y 〉 ᶜ) (⊔′-idem y)
   ⊔-idem (τ ᶜ) = refl

   ⊔-absorbs-⊓ : ∀ {Γ} {a : Action Γ} → _Absorbs_ _≡_ (_⊔_ {a₀ = a}) _⊓_
   ⊔-absorbs-⊓ (x • ᵇ) (.x • ᵇ) = refl
   ⊔-absorbs-⊓ ((• x) ᵇ) ((• .x) ᵇ) = refl
   ⊔-absorbs-⊓ (• x 〈 y 〉 ᶜ) (• .x 〈 y′ 〉 ᶜ) = cong (λ y → • x 〈 y 〉 ᶜ) (ᴺ̃.⊔-absorbs-⊓ y y′)
   ⊔-absorbs-⊓ (τ ᶜ) (τ ᶜ) = refl

   ⊓-idem : ∀ {Γ} {a : Action Γ} → Idempotent _≡_ (_⊓_ {a₀ = a})
   ⊓-idem (x • ᵇ) = refl
   ⊓-idem ((• x) ᵇ) = refl
   ⊓-idem (• x 〈 y 〉 ᶜ) = cong (λ y → • x 〈 y 〉 ᶜ) (⊓′-idem y)
   ⊓-idem (τ ᶜ) = refl

   ⊓-absorbs-⊔ : ∀ {Γ} {a : Action Γ} → _Absorbs_ _≡_ (_⊓_ {a₀ = a}) _⊔_
   ⊓-absorbs-⊔ ((x •) ᵇ) ((.x •) ᵇ) = refl
   ⊓-absorbs-⊔ ((• x) ᵇ) ((• .x) ᵇ) = refl
   ⊓-absorbs-⊔ (• x 〈 y 〉 ᶜ) (• .x 〈 y′ 〉 ᶜ) = cong (λ y → • x 〈 y 〉 ᶜ) (ᴺ̃.⊓-absorbs-⊔ y y′)
   ⊓-absorbs-⊔ (τ ᶜ) (τ ᶜ) = refl

   isLattice : ∀ {Γ} {a : Action Γ} → IsLattice _≡_ (_⊔_ {a₀ = a}) _⊓_
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
      lattices : ∀ {Γ} → Lattices (Action Γ)
      lattices = record {
            ↓_ = ↓_; ↓⁻_ = ↓_; _⊔⁻_ = _⊔_; _⊔_ = _⊔_; _⊓⁻_ = _⊓_; _⊓_ = _⊓_;
            isLattice⁻ = isLattice; isLattice = isLattice
         }

   open Lattices using (_≤⁻ᴸ_; _≤ᴸ_)

   ≤ᴸ⇒≤ : ∀ {Γ} {a : Action Γ} → _≤⁻ᴸ_ lattices {a = a} ⇒ _≤_
   ≤ᴸ⇒≤ {i = x • ᵇ} {.x • ᵇ} _ = (x •) ᵇ
   ≤ᴸ⇒≤ {i = (• x) ᵇ} {(• .x) ᵇ} _ = (• x) ᵇ
   ≤ᴸ⇒≤ {i = • x 〈 y 〉 ᶜ} {• .x 〈 y′ 〉 ᶜ} _ with y ⊓′ y′ | inspect (_⊓′_ y) y′
   ≤ᴸ⇒≤ {i = • x 〈 y 〉 ᶜ} {• .x 〈 y′ 〉 ᶜ} refl | .y | [ y≤ᴸy′ ] = • x 〈 ≤′ᴸ⇒≤′ (sym y≤ᴸy′) 〉 ᶜ
   ≤ᴸ⇒≤ {i = τ ᶜ} {τ ᶜ} _ = τ ᶜ

   ≤⇒≤ᴸ : ∀ {Γ} {a : Action Γ} → _≤_ ⇒ _≤ᴸ_ lattices {a = a}
   ≤⇒≤ᴸ (x • ᵇ) = refl
   ≤⇒≤ᴸ ((• x) ᵇ) = refl
   ≤⇒≤ᴸ (• x 〈 y 〉 ᶜ) = cong (λ y → • x 〈 y 〉 ᶜ) (≤′⇒≤′ᴸ y)
   ≤⇒≤ᴸ (τ ᶜ) = refl

   instance
      prefixes : ∀ {Γ} → Prefixes (Action Γ)
      prefixes = record {
            lattices = lattices; _≤_ = _≤_; _≤⁻_ = _≤_; ≤⁻ᴸ⇒≤⁻ = ≤ᴸ⇒≤; ≤ᴸ⇒≤ = ≤ᴸ⇒≤; ≤⁻⇒≤⁻ᴸ = ≤⇒≤ᴸ; ≤⇒≤ᴸ = ≤⇒≤ᴸ
         }
