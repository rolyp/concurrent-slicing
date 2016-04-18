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

   data ↓ᵇ⁻_ {Γ : Cxt} : Actionᵇ Γ → Set where
      _• : {x : Name Γ} → ↓′ x → ↓ᵇ⁻ x •
      •_ : {x : Name Γ} → ↓′ x → ↓ᵇ⁻ • x

   data ↓ᶜ⁻_ {Γ : Cxt} : Actionᶜ Γ → Set where
      •_〈_〉 : {x y : Name Γ} → ↓′ x → ↓′ y → ↓ᶜ⁻ • x 〈 y 〉
      τ : ↓ᶜ⁻ τ {Γ}

   data ↓⁻_ {Γ : Cxt} : Action Γ → Set where
      _ᵇ : {a : Actionᵇ Γ} → ↓ᵇ⁻ a → ↓⁻ a ᵇ
      _ᶜ : {a : Actionᶜ Γ} → ↓ᶜ⁻ a → ↓⁻ a ᶜ

   data ↓_ {Γ : Cxt} : Action Γ → Set where
      ◻ : {a : Action Γ} → ↓ a
      [_] : ∀ {a : Action Γ} → ↓⁻ a → ↓ a

   data _≤ᵇ⁻_ {Γ : Cxt} : {a : Actionᵇ Γ} → ↓ᵇ⁻ a → ↓ᵇ⁻ a → Set where
      _• : {x : Name Γ} {x′ x″ : ↓′ x} → x′ ≤′ x″ → x′ • ≤ᵇ⁻ x″ •
      •_ : {x : Name Γ} {x′ x″ : ↓′ x} → x′ ≤′ x″ → • x′ ≤ᵇ⁻ • x″

   data _≤ᶜ⁻_ {Γ : Cxt} : {a : Actionᶜ Γ} → ↓ᶜ⁻ a → ↓ᶜ⁻ a → Set where
      •_〈_〉 : {x y : Name Γ} {x′ x″ : ↓′ x} {y′ y″ : ↓′ y} → x′ ≤′ x″ → y′ ≤′ y″ → • x′ 〈 y′ 〉 ≤ᶜ⁻ • x″ 〈 y″ 〉
      τ : τ ≤ᶜ⁻ τ

   data _≤⁻_ {Γ : Cxt} : ∀ {a : Action Γ} → ↓⁻ a → ↓⁻ a → Set where
      _ᵇ : {a : Actionᵇ Γ} {a′ a″ : ↓ᵇ⁻ a} → a′ ≤ᵇ⁻ a″ → a′ ᵇ ≤⁻ a″ ᵇ
      _ᶜ : {a : Actionᶜ Γ} {a′ a″ : ↓ᶜ⁻ a} → a′ ≤ᶜ⁻ a″ → a′ ᶜ ≤⁻ a″ ᶜ

   data _≤_ {Γ : Cxt} : ∀ {a : Action Γ} → ↓ a → ↓ a → Set where
      ◻ : {a : Action Γ} {a′ : ↓ a} → ◻ ≤ a′
      [_] : ∀ {a : Action Γ} {a′ a″ : ↓⁻ a} → a′ ≤⁻ a″ → [ a′ ] ≤ [ a″ ]

   -- a is the greatest prefix of itself.
   to-↓ : ∀ {Γ} (a : Action Γ) → ↓ a
   to-↓ (x • ᵇ) = [ [ x ] • ᵇ ]
   to-↓ ((• x) ᵇ) = [ (• [ x ]) ᵇ ]
   to-↓ (• x 〈 y 〉 ᶜ) = [ • [ x ] 〈 [ y ] 〉 ᶜ ]
   to-↓ (τ ᶜ) = [ τ ᶜ ]

   top : ∀ {Γ} (a : Action Γ) {a′ : ↓ a} → a′ ≤ to-↓ a
   top _ {◻} = ◻
   top (_ • ᵇ) {[ ᴺ̃.◻ • ᵇ ]} = [ ᴺ̃.◻ • ᵇ ]
   top (x • ᵇ) {[ [ .x ] • ᵇ ]} = [ [ x ] • ᵇ ]
   top ((• _) ᵇ) {[ (• ᴺ̃.◻) ᵇ ]} = [ (• ᴺ̃.◻) ᵇ ]
   top ((• x) ᵇ) {[ (• [ .x ]) ᵇ ]} = [ (• [ x ]) ᵇ ]
   top (• x 〈 y 〉 ᶜ) {[ • ᴺ̃.◻ 〈 ᴺ̃.◻ 〉 ᶜ ]} = [ • ᴺ̃.◻ 〈 ᴺ̃.◻ 〉 ᶜ ]
   top (• x 〈 y 〉 ᶜ) {[ • ᴺ̃.◻ 〈 [ .y ] 〉 ᶜ ]} = [ • ᴺ̃.◻ 〈 [ y ] 〉 ᶜ ]
   top (• x 〈 y 〉 ᶜ) {[ • [ .x ] 〈 ᴺ̃.◻ 〉 ᶜ ]} = [ • [ x ] 〈 ᴺ̃.◻ 〉 ᶜ ]
   top (• x 〈 y 〉 ᶜ) {[ • [ .x ] 〈 [ .y ] 〉 ᶜ ]} = [ • [ x ] 〈 [ y ] 〉 ᶜ ]
   top (τ ᶜ) {[ τ ᶜ ]} = [ τ ᶜ ]

   _⊓⁻_ : ∀ {Γ} {a₀ : Action Γ} → (a a′ : ↓⁻ a₀) → ↓⁻ a₀
   x • ᵇ ⊓⁻ x′ • ᵇ = (x ⊓′ x′) • ᵇ
   (• x)ᵇ ⊓⁻ (• x′)ᵇ = (• (x ⊓′ x′))ᵇ
   • x 〈 y 〉 ᶜ ⊓⁻ • x′ 〈 y′ 〉 ᶜ = • x ⊓′ x′ 〈 y ⊓′ y′ 〉 ᶜ
   τ ᶜ ⊓⁻ τ ᶜ = τ ᶜ

   _⊓_ : ∀ {Γ} {a₀ : Action Γ} → (a a′ : ↓ a₀) → ↓ a₀
   ◻ ⊓ _ = ◻
   _ ⊓ ◻ = ◻
   [ a ] ⊓ [ a′ ] = [ a ⊓⁻ a′ ]

   _⊔⁻_ : ∀ {Γ} {a₀ : Action Γ} → (a a′ : ↓⁻ a₀) → ↓⁻ a₀
   x • ᵇ ⊔⁻ x′ • ᵇ = (x ⊔′ x′) • ᵇ
   (• x) ᵇ ⊔⁻ (• x′) ᵇ = (• (x ⊔′ x′))ᵇ
   • x 〈 y 〉 ᶜ ⊔⁻ • x′ 〈 y′ 〉 ᶜ = • x ⊔′ x′ 〈 y ⊔′ y′ 〉 ᶜ
   τ ᶜ ⊔⁻ τ ᶜ = τ ᶜ

   _⊔_ : ∀ {Γ} {a₀ : Action Γ} → (a a′ : ↓ a₀) → ↓ a₀
   ◻ ⊔ a = a
   a ⊔ ◻ = a
   [ a ] ⊔ [ a′ ] = [ a ⊔⁻ a′ ]

   ◻-⊔-rightId : ∀ {Γ} {a : Action Γ} → RightIdentity _≡_ ◻ (_⊔_ {a₀ = a})
   ◻-⊔-rightId ◻ = refl
   ◻-⊔-rightId [ _ ] = refl

   ◻-⊓-rightZ : ∀ {Γ} {a : Action Γ} → RightZero _≡_ ◻ (_⊓_ {a₀ = a})
   ◻-⊓-rightZ ◻ = refl
   ◻-⊓-rightZ [ _ ] = refl

   ⊓⁻-comm : ∀ {Γ} {a : Action Γ} → Commutative _≡_ (_⊓⁻_ {a₀ = a})
   ⊓⁻-comm (x • ᵇ) (x′ • ᵇ) = cong (λ x → x • ᵇ) (ᴺ̃.⊓-comm x x′)
   ⊓⁻-comm ((• x)ᵇ) ((• x′)ᵇ) = cong (λ x → (• x)ᵇ) (ᴺ̃.⊓-comm x x′)
   ⊓⁻-comm (• x 〈 y 〉 ᶜ) (• x′ 〈 y′ 〉 ᶜ) = cong₂ (λ x y → • x 〈 y 〉 ᶜ) (ᴺ̃.⊓-comm x x′) (ᴺ̃.⊓-comm y y′)
   ⊓⁻-comm (τ ᶜ) (τ ᶜ) = refl

   ⊓-comm : ∀ {Γ} {a : Action Γ} → Commutative _≡_ (_⊓_ {a₀ = a})
   ⊓-comm ◻ a = sym (◻-⊓-rightZ a)
   ⊓-comm a ◻ = ◻-⊓-rightZ a
   ⊓-comm [ a ] [ a′ ] = cong [_] (⊓⁻-comm a a′)

   ⊓⁻-assoc : ∀ {Γ} {a : Action Γ} → Associative _≡_ (_⊓⁻_ {a₀ = a})
   ⊓⁻-assoc (x₁ • ᵇ) (x₂ • ᵇ) (x₃ • ᵇ) = cong (λ x → x • ᵇ) (ᴺ̃.⊓-assoc x₁ x₂ x₃)
   ⊓⁻-assoc ((• x₁)ᵇ) ((• x₂)ᵇ) ((• x₃)ᵇ) = cong (λ x → (• x)ᵇ) (ᴺ̃.⊓-assoc x₁ x₂ x₃)
   ⊓⁻-assoc (• x₁ 〈 y₁ 〉 ᶜ) (• x₂ 〈 y₂ 〉 ᶜ) (• x₃ 〈 y₃ 〉 ᶜ) =
      cong₂ (λ x y → • x 〈 y 〉 ᶜ) (ᴺ̃.⊓-assoc x₁ x₂ x₃) (ᴺ̃.⊓-assoc y₁ y₂ y₃)
   ⊓⁻-assoc (τ ᶜ) (τ ᶜ) (τ ᶜ) = refl

   ⊓-assoc : ∀ {Γ} {a : Action Γ} → Associative _≡_ (_⊓_ {a₀ = a})
   ⊓-assoc ◻ _ _ = refl
   ⊓-assoc a ◻ a′ =
      begin (a ⊓ ◻) ⊓ a′ ≡⟨ cong (flip _⊓_ a′) (◻-⊓-rightZ a) ⟩ ◻ ⊓ a′ ≡⟨ sym (◻-⊓-rightZ a) ⟩ a ⊓ ◻ ∎
      where open EqReasoning (setoid _)
   ⊓-assoc a a′ ◻ =
      begin
         (a ⊓ a′) ⊓ ◻
      ≡⟨ ◻-⊓-rightZ (a ⊓ a′) ⟩
         ◻
      ≡⟨ sym (◻-⊓-rightZ a) ⟩
         a ⊓ ◻
      ≡⟨ cong (_⊓_ a) (sym (◻-⊓-rightZ a′)) ⟩
         a ⊓ (a′ ⊓ ◻)
      ∎
      where open EqReasoning (setoid _)
   ⊓-assoc [ a₁ ] [ a₂ ] [ a₃ ] = cong [_] (⊓⁻-assoc a₁ a₂ a₃)

   ⊔⁻-comm : ∀ {Γ} {a : Action Γ} → Commutative _≡_ (_⊔⁻_ {a₀ = a})
   ⊔⁻-comm (x • ᵇ) (x′ • ᵇ) = cong (λ x → x • ᵇ) (ᴺ̃.⊔-comm x x′)
   ⊔⁻-comm ((• x)ᵇ) ((• x′)ᵇ) = cong (λ x → (• x)ᵇ) (ᴺ̃.⊔-comm x x′)
   ⊔⁻-comm (• x 〈 y 〉 ᶜ) (• x′ 〈 y′ 〉 ᶜ) = cong₂ (λ x y → • x 〈 y 〉 ᶜ) (ᴺ̃.⊔-comm x x′) (ᴺ̃.⊔-comm y y′)
   ⊔⁻-comm (τ ᶜ) (τ ᶜ) = refl

   ⊔-comm : ∀ {Γ} {a : Action Γ} → Commutative _≡_ (_⊔_ {a₀ = a})
   ⊔-comm ◻ _ = sym (◻-⊔-rightId _)
   ⊔-comm _ ◻ = ◻-⊔-rightId _
   ⊔-comm [ a ] [ a′ ] = cong [_] (⊔⁻-comm a a′)

   ⊔⁻-assoc : ∀ {Γ} {a : Action Γ} → Associative _≡_ (_⊔⁻_ {a₀ = a})
   ⊔⁻-assoc (x₁ • ᵇ) (x₂ • ᵇ) (x₃ • ᵇ) = cong (λ x → x • ᵇ) (ᴺ̃.⊔-assoc x₁ x₂ x₃)
   ⊔⁻-assoc ((• x₁) ᵇ) ((• x₂) ᵇ) ((• x₃) ᵇ) = cong (λ x → (• x)ᵇ) (ᴺ̃.⊔-assoc x₁ x₂ x₃)
   ⊔⁻-assoc (• x₁ 〈 y₁ 〉 ᶜ) (• x₂ 〈 y₂ 〉 ᶜ) (• x₃ 〈 y₃ 〉 ᶜ) =
      cong₂ (λ x y → • x 〈 y 〉 ᶜ) (ᴺ̃.⊔-assoc x₁ x₂ x₃) (ᴺ̃.⊔-assoc y₁ y₂ y₃)
   ⊔⁻-assoc (τ ᶜ) (τ ᶜ) (τ ᶜ) = refl

   ⊔-assoc : ∀ {Γ} {a : Action Γ} → Associative _≡_ (_⊔_ {a₀ = a})
   ⊔-assoc ◻ _ _ = refl
   ⊔-assoc x ◻ y = cong (flip _⊔_ y) (◻-⊔-rightId x)
   ⊔-assoc x y ◻ =
      begin (x ⊔ y) ⊔ ◻ ≡⟨ ◻-⊔-rightId (x ⊔ y) ⟩ x ⊔ y ≡⟨ cong (_⊔_ x) (sym (◻-⊔-rightId y)) ⟩ x ⊔ (y ⊔ ◻) ∎
      where open EqReasoning (setoid _)
   ⊔-assoc [ a₁ ] [ a₂ ] [ a₃ ] = cong [_] (⊔⁻-assoc a₁ a₂ a₃)

   ⊔⁻-idem : ∀ {Γ} {a : Action Γ} → Idempotent _≡_ (_⊔⁻_ {a₀ = a})
   ⊔⁻-idem (x • ᵇ) = cong (λ x → x • ᵇ) (⊔′-idem x)
   ⊔⁻-idem ((• x) ᵇ) = cong (λ x → (• x) ᵇ) (⊔′-idem x)
   ⊔⁻-idem (• x 〈 y 〉 ᶜ) = cong₂ (λ x y → • x 〈 y 〉 ᶜ) (⊔′-idem x) (⊔′-idem y)
   ⊔⁻-idem (τ ᶜ) = refl

   ⊔-idem : ∀ {Γ} {a : Action Γ} → Idempotent _≡_ (_⊔_ {a₀ = a})
   ⊔-idem ◻ = refl
   ⊔-idem [ a ] = cong [_] (⊔⁻-idem a)

   ⊔⁻-absorbs-⊓⁻ : ∀ {Γ} {a : Action Γ} → _Absorbs_ _≡_ (_⊔⁻_ {a₀ = a}) _⊓⁻_
   ⊔⁻-absorbs-⊓⁻ (x • ᵇ) (x′ • ᵇ) = cong (λ x → x • ᵇ) (ᴺ̃.⊔-absorbs-⊓ x x′)
   ⊔⁻-absorbs-⊓⁻ ((• x)ᵇ) ((• x′)ᵇ) = cong (λ x → (• x)ᵇ) (ᴺ̃.⊔-absorbs-⊓ x x′)
   ⊔⁻-absorbs-⊓⁻ (• x 〈 y 〉 ᶜ) (• x′ 〈 y′ 〉 ᶜ) =
      cong₂ (λ x y → • x 〈 y 〉 ᶜ) (ᴺ̃.⊔-absorbs-⊓ x x′) (ᴺ̃.⊔-absorbs-⊓ y y′)
   ⊔⁻-absorbs-⊓⁻ (τ ᶜ) (τ ᶜ) = refl

   ⊔-absorbs-⊓ : ∀ {Γ} {a : Action Γ} → _Absorbs_ _≡_ (_⊔_ {a₀ = a}) _⊓_
   ⊔-absorbs-⊓ ◻ _ = refl
   ⊔-absorbs-⊓ a ◻ =
      begin a ⊔ (a ⊓ ◻) ≡⟨ cong (_⊔_ a) (◻-⊓-rightZ a) ⟩ a ⊔ ◻ ≡⟨ ◻-⊔-rightId a ⟩ a ∎
      where open EqReasoning (setoid _)
   ⊔-absorbs-⊓ [ a ] [ a′ ] = cong [_] (⊔⁻-absorbs-⊓⁻ a a′)

   ⊓⁻-idem : ∀ {Γ} {a : Action Γ} → Idempotent _≡_ (_⊓⁻_ {a₀ = a})
   ⊓⁻-idem (x • ᵇ) = cong (λ x → x • ᵇ) (⊓′-idem x)
   ⊓⁻-idem ((• x)ᵇ) = cong (λ x → (• x)ᵇ) (⊓′-idem x)
   ⊓⁻-idem (• x 〈 y 〉 ᶜ) = cong₂ (λ x y → • x 〈 y 〉 ᶜ) (⊓′-idem x) (⊓′-idem y)
   ⊓⁻-idem (τ ᶜ) = refl

   ⊓-idem : ∀ {Γ} {a : Action Γ} → Idempotent _≡_ (_⊓_ {a₀ = a})
   ⊓-idem ◻ = refl
   ⊓-idem [ a ] = cong [_] (⊓⁻-idem a)

   ⊓⁻-absorbs-⊔⁻ : ∀ {Γ} {a : Action Γ} → _Absorbs_ _≡_ (_⊓⁻_ {a₀ = a}) _⊔⁻_
   ⊓⁻-absorbs-⊔⁻ ((x •) ᵇ) ((x′ •) ᵇ) = cong (λ x → x • ᵇ) (ᴺ̃.⊓-absorbs-⊔ x x′)
   ⊓⁻-absorbs-⊔⁻ ((• x) ᵇ) ((• x′) ᵇ) = cong (λ x → (• x)ᵇ) (ᴺ̃.⊓-absorbs-⊔ x x′)
   ⊓⁻-absorbs-⊔⁻ (• x 〈 y 〉 ᶜ) (• x′ 〈 y′ 〉 ᶜ) =
      cong₂ (λ x y → • x 〈 y 〉 ᶜ) (ᴺ̃.⊓-absorbs-⊔ x x′) (ᴺ̃.⊓-absorbs-⊔ y y′)
   ⊓⁻-absorbs-⊔⁻ (τ ᶜ) (τ ᶜ) = refl

   ⊓-absorbs-⊔ : ∀ {Γ} {a : Action Γ} → _Absorbs_ _≡_ (_⊓_ {a₀ = a}) _⊔_
   ⊓-absorbs-⊔ ◻ _ = refl
   ⊓-absorbs-⊔ a ◻ =
      begin a ⊓ (a ⊔ ◻) ≡⟨ cong (_⊓_ a) (◻-⊔-rightId a) ⟩ a ⊓ a ≡⟨ ⊓-idem a ⟩ a ∎ where open EqReasoning (setoid _)
   ⊓-absorbs-⊔ [ a ] [ a′ ] = cong [_] (⊓⁻-absorbs-⊔⁻ a a′)

   isLattice⁻ : ∀ {Γ} {a : Action Γ} → IsLattice _≡_ (_⊔⁻_ {a₀ = a}) _⊓⁻_
   isLattice⁻ = record {
         isEquivalence = isEquivalence;
         ∨-comm = ⊔⁻-comm;
         ∨-assoc = ⊔⁻-assoc;
         ∨-cong = cong₂ _⊔⁻_;
         ∧-comm = ⊓⁻-comm;
         ∧-assoc = ⊓⁻-assoc;
         ∧-cong = cong₂ _⊓⁻_;
         absorptive = ⊔⁻-absorbs-⊓⁻ , ⊓⁻-absorbs-⊔⁻
      }

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
            ↓_ = ↓_; ↓⁻_ = ↓⁻_; _⊔⁻_ = _⊔⁻_; _⊔_ = _⊔_; _⊓⁻_ = _⊓⁻_; _⊓_ = _⊓_;
            isLattice⁻ = isLattice⁻; isLattice = isLattice
         }

   open Lattices using (_≤⁻ᴸ_; _≤ᴸ_)

   ≤⁻ᴸ⇒≤⁻ : ∀ {Γ} {a : Action Γ} → _≤⁻ᴸ_ lattices {a = a} ⇒ _≤⁻_
   ≤⁻ᴸ⇒≤⁻ {i = x • ᵇ} {x′ • ᵇ} _ with x ⊓′ x′ | inspect (_⊓′_ x) x′
   ≤⁻ᴸ⇒≤⁻ {i = x • ᵇ} {x′ • ᵇ} refl | .x | [ x≤ᴸx′ ] = ≤′ᴸ⇒≤′ (sym x≤ᴸx′) • ᵇ
   ≤⁻ᴸ⇒≤⁻ {i = (• x)ᵇ} {(• x′)ᵇ} _ with x ⊓′ x′ | inspect (_⊓′_ x) x′
   ≤⁻ᴸ⇒≤⁻ {i = (• x)ᵇ} {(• x′)ᵇ} refl | .x | [ x≤ᴸx′ ] = (• (≤′ᴸ⇒≤′ (sym x≤ᴸx′)))ᵇ
   ≤⁻ᴸ⇒≤⁻ {i = • x 〈 y 〉 ᶜ} {• x′ 〈 y′ 〉 ᶜ} _
      with x ⊓′ x′ | inspect (_⊓′_ x) x′ | y ⊓′ y′ | inspect (_⊓′_ y) y′
   ≤⁻ᴸ⇒≤⁻ {i = • x 〈 y 〉 ᶜ} {• x′ 〈 y′ 〉 ᶜ} refl | .x | [ x≤ᴸx′ ] | .y | [ y≤ᴸy′ ] =
      • ≤′ᴸ⇒≤′ (sym x≤ᴸx′) 〈 ≤′ᴸ⇒≤′ (sym y≤ᴸy′) 〉 ᶜ
   ≤⁻ᴸ⇒≤⁻ {i = τ ᶜ} {τ ᶜ} _ = τ ᶜ

   ≤ᴸ⇒≤ : ∀ {Γ} {a : Action Γ} → _≤ᴸ_ lattices {a = a} ⇒ _≤_
   ≤ᴸ⇒≤ {i = ◻} _ = ◻
   ≤ᴸ⇒≤ {i = [ a ]} {[ a′ ]} _ with a ⊓⁻ a′ | inspect (_⊓⁻_ a) a′
   ≤ᴸ⇒≤ {i = [ a ]} {[ a′ ]} refl | .a | [ a≤⁻ᴸa′ ] = [ ≤⁻ᴸ⇒≤⁻ (sym a≤⁻ᴸa′) ]
   ≤ᴸ⇒≤ {i = [ _ ]} {◻} ()

   ≤⁻⇒≤⁻ᴸ : ∀ {Γ} {a : Action Γ} → _≤⁻_ ⇒ _≤⁻ᴸ_ lattices {a = a}
   ≤⁻⇒≤⁻ᴸ (x • ᵇ) = cong (λ x → x • ᵇ) (≤′⇒≤′ᴸ x)
   ≤⁻⇒≤⁻ᴸ ((• x)ᵇ) = cong (λ x → (• x)ᵇ) (≤′⇒≤′ᴸ x)
   ≤⁻⇒≤⁻ᴸ (• x 〈 y 〉 ᶜ) = cong₂ (λ x y → • x 〈 y 〉 ᶜ) (≤′⇒≤′ᴸ x) (≤′⇒≤′ᴸ y)
   ≤⁻⇒≤⁻ᴸ (τ ᶜ) = refl

   ≤⇒≤ᴸ : ∀ {Γ} {a : Action Γ} → _≤_ ⇒ _≤ᴸ_ lattices {a = a}
   ≤⇒≤ᴸ ◻ = refl
   ≤⇒≤ᴸ [ a ] = cong [_] (≤⁻⇒≤⁻ᴸ a)

   instance
      prefixes : ∀ {Γ} → Prefixes (Action Γ)
      prefixes = record {
            lattices = lattices; _≤_ = _≤_; _≤⁻_ = _≤⁻_; ≤⁻ᴸ⇒≤⁻ = ≤⁻ᴸ⇒≤⁻; ≤ᴸ⇒≤ = ≤ᴸ⇒≤; ≤⁻⇒≤⁻ᴸ = ≤⁻⇒≤⁻ᴸ; ≤⇒≤ᴸ = ≤⇒≤ᴸ
         }
