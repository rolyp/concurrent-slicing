module Proc.Lattice where

   open import ConcurrentSlicingCommon hiding (preorder)
   import Relation.Binary.EqReasoning as EqReasoning
   import Relation.Binary.PreorderReasoning as PreorderReasoning

   open import Ext
   import Ext.Algebra.Properties.Lattice

   open import Lattice using (Prefixes; module Prefixes; Lattices; module Lattices);
      open Prefixes ⦃...⦄ using () renaming (
            ↓⁻_ to ↓⁻′_; ↓_ to ↓′_; _≤⁻_ to _≤⁻′_; _≤_ to _≤′_; _⊔⁻_ to _⊔⁻′_; _⊔_ to _⊔′_; _⊓⁻_ to _⊓⁻′_; _⊓_ to _⊓′_;
            ≤ᴸ⇒≤ to ≤′ᴸ⇒≤′; ≤⇒≤ᴸ to ≤′⇒≤′ᴸ; ⊓-idem to ⊓′-idem
         )
   open import Name as ᴺ using (Cxt; _+_)
   import Name.Lattice as ᴺ̃
   open import Proc as ᴾ using (Proc); open ᴾ.Proc

   mutual
      infixl 6 _➕_ _│_
      infixr 7 _•∙_ •_〈_〉∙_
      data ↓⁻_ {Γ} : Proc Γ → Set where
         Ο : ↓⁻ Ο
         _•∙_ : ∀ x {P} → ↓ P → ↓⁻ (x •∙ P)
         •_〈_〉∙_ : ∀ x {y P} → ↓′ y → ↓ P → ↓⁻ (• x 〈 y 〉∙ P)
         _➕_ : ∀ {P Q} → ↓ P → ↓ Q → ↓⁻ (P ➕ Q)
         _│_ : ∀ {P Q} → ↓ P → ↓ Q → ↓⁻ (P │ Q)
         ν_ : ∀ {P} → ↓ P → ↓⁻ (ν P)
         !_ : ∀ {P} → ↓ P → ↓⁻ (! P)

      data ↓_ {Γ} : Proc Γ → Set where
         ◻ : {P : Proc Γ} → ↓ P
         [_] : {P : Proc Γ} → ↓⁻ P → ↓ P

   mutual
      infix 4 _≤⁻_ _≤_
      data _≤⁻_ {Γ} : {P : Proc Γ} → ↓⁻ P → ↓⁻ P → Set where
         Ο : Ο ≤⁻ Ο
         _•∙_ : ∀ x {P₀} {P P′ : ↓ P₀} → P ≤ P′ → x •∙ P ≤⁻ x •∙ P′
         •_〈_〉∙_ : ∀ x {y₀ P₀} {y y′ : ↓′ y₀} {P P′ : ↓ P₀} → y ≤′ y′ → P ≤ P′ → • x 〈 y 〉∙ P ≤⁻ • x 〈 y′ 〉∙ P′
         _➕_ : ∀ {P₀ Q₀} {P P′ : ↓ P₀} {Q Q′ : ↓ Q₀} → P ≤ P′ → Q ≤ Q′ → P ➕ Q ≤⁻ P′ ➕ Q′
         _│_ : ∀ {P₀ Q₀} {P P′ : ↓ P₀} {Q Q′ : ↓ Q₀} → P ≤ P′ → Q ≤ Q′ → P │ Q ≤⁻ P′ │ Q′
         ν_ : ∀ {P₀} {P P′ : ↓ P₀} → P ≤ P′ → ν P ≤⁻ ν P′
         !_ : ∀ {P₀} {P P′ : ↓ P₀} → P ≤ P′ → ! P ≤⁻ ! P′

      data _≤_ {Γ} : {P₀ : Proc Γ} → ↓ P₀ → ↓ P₀ → Set where
         ◻ : {P₀ : Proc Γ} {P : ↓ P₀} → ◻ ≤ P
         [_] : {P₀ : Proc Γ} {P P′ : ↓⁻ P₀} → P ≤⁻ P′ → [ P ] ≤ [ P′ ]

   to-↓ : ∀ {Γ} (P : Proc Γ) → ↓ P
   to-↓⁻ : ∀ {Γ} (P : Proc Γ) → ↓⁻ P

   to-↓ P = [ to-↓⁻ P ]

   to-↓⁻ Ο = Ο
   to-↓⁻ (x •∙ P) = x •∙ to-↓ P
   to-↓⁻ (• x 〈 y 〉∙ P) = • x 〈 ᴺ̃.to-↓ y 〉∙ to-↓ P
   to-↓⁻ (P ➕ Q) = to-↓ P ➕ to-↓ Q
   to-↓⁻ (P │ Q) = to-↓ P │ to-↓ Q
   to-↓⁻ (ν P) = ν to-↓ P
   to-↓⁻ (! P) = ! to-↓ P

   _⊔⁻_ : ∀ {Γ} {P₀ : Proc Γ} (P P′ : ↓⁻ P₀) → ↓⁻ P₀
   _⊔_ : ∀ {Γ} {P₀ : Proc Γ} (P P′ : ↓ P₀) → ↓ P₀

   Ο ⊔⁻ Ο = Ο
   x •∙ P ⊔⁻ .x •∙ P′ = x •∙ (P ⊔ P′)
   • x 〈 y 〉∙ P ⊔⁻ • .x 〈 y′ 〉∙ P′ = • x 〈 y ⊔′ y′ 〉∙ (P ⊔ P′)
   (P ➕ Q) ⊔⁻ (P′ ➕ Q′) = (P ⊔ P′) ➕ (Q ⊔ Q′)
   (P │ Q) ⊔⁻ (P′ │ Q′) = (P ⊔ P′) │ (Q ⊔ Q′)
   ν P ⊔⁻ ν P′ = ν (P ⊔ P′)
   ! P ⊔⁻ ! P′ = ! (P ⊔ P′)

   ◻ ⊔ P = P
   P ⊔ ◻ = P
   [ P ] ⊔ [ P′ ] = [ P ⊔⁻ P′ ]

   infixr 6 _⊔⁻_ _⊔_

   _⊓⁻_ : ∀ {Γ} {P₀ : Proc Γ} (P P′ : ↓⁻ P₀) → ↓⁻ P₀
   _⊓_ : ∀ {Γ} {P₀ : Proc Γ} (P P′ : ↓ P₀) → ↓ P₀

   Ο ⊓⁻ Ο = Ο
   (x •∙ P) ⊓⁻ (.x •∙ P′) = x •∙ (P ⊓ P′)
   • x 〈 y 〉∙ P ⊓⁻ • .x 〈 y′ 〉∙ P′ = • x 〈 y ⊓′ y′ 〉∙ (P ⊓ P′)
   (P ➕ Q) ⊓⁻ (P′ ➕ Q′) = (P ⊓ P′) ➕ (Q ⊓ Q′)
   (P │ Q) ⊓⁻ (P′ │ Q′) = (P ⊓ P′) │ (Q ⊓ Q′)
   ν P ⊓⁻ ν P′ = ν (P ⊓ P′)
   ! P ⊓⁻ ! P′ = ! (P ⊓ P′)

   ◻ ⊓ P = ◻
   P ⊓ ◻ = ◻
   [ P ] ⊓ [ P′ ] = [ P ⊓⁻ P′ ]

   infixr 7 _⊓⁻_ _⊓_

   ◻-⊔-rightId : ∀ {Γ} {P : Proc Γ} → RightIdentity _≡_ ◻ (_⊔_ {P₀ = P})
   ◻-⊔-rightId ◻ = refl
   ◻-⊔-rightId [ _ ] = refl

   ◻-⊓-rightZ : ∀ {Γ} {P : Proc Γ} → RightZero _≡_ ◻ (_⊓_ {P₀ = P})
   ◻-⊓-rightZ ◻ = refl
   ◻-⊓-rightZ [ _ ] = refl

   ⊔⁻-comm : ∀ {Γ} {P : Proc Γ} → Commutative _≡_ (_⊔⁻_ {P₀ = P})
   ⊔-comm : ∀ {Γ} {P : Proc Γ} → Commutative _≡_ (_⊔_ {P₀ = P})

   ⊔⁻-comm Ο Ο = refl
   ⊔⁻-comm (x •∙ P) (.x •∙ P′) = cong (λ P† → x •∙ P†) (⊔-comm P P′)
   ⊔⁻-comm (• x 〈 y 〉∙ P) (• .x 〈 y′ 〉∙ P′) = cong₂ (λ y† P† → • x 〈 y† 〉∙ P†) (ᴺ̃.⊔-comm y y′) (⊔-comm P P′)
   ⊔⁻-comm (P ➕ Q) (P′ ➕ Q′) = cong₂ _➕_ (⊔-comm P P′) (⊔-comm Q Q′)
   ⊔⁻-comm (P │ Q) (P′ │ Q′) = cong₂ _│_ (⊔-comm P P′) (⊔-comm Q Q′)
   ⊔⁻-comm (ν P) (ν P′) = cong ν_ (⊔-comm P P′)
   ⊔⁻-comm (! P) (! P′) = cong !_ (⊔-comm P P′)

   ⊔-comm ◻ _ = sym (◻-⊔-rightId _)
   ⊔-comm _ ◻ = ◻-⊔-rightId _
   ⊔-comm [ P ] [ P′ ] = cong [_] (⊔⁻-comm P P′)

   ⊓⁻-comm : ∀ {Γ} {P : Proc Γ} → Commutative _≡_ (_⊓⁻_ {P₀ = P})
   ⊓-comm : ∀ {Γ} {P : Proc Γ} → Commutative _≡_ (_⊓_ {P₀ = P})

   ⊓⁻-comm Ο Ο = refl
   ⊓⁻-comm (x •∙ P) (.x •∙ P′) = cong (λ P† → x •∙ P†) (⊓-comm P P′)
   ⊓⁻-comm (• x 〈 y 〉∙ P) (• .x 〈 y′ 〉∙ P′) = cong₂ (λ y† P† → • x 〈 y† 〉∙ P†) (ᴺ̃.⊓-comm y y′) (⊓-comm P P′)
   ⊓⁻-comm (P ➕ Q) (P′ ➕ Q′) = cong₂ _➕_ (⊓-comm P P′) (⊓-comm Q Q′)
   ⊓⁻-comm (P │ Q) (P′ │ Q′) = cong₂ _│_ (⊓-comm P P′) (⊓-comm Q Q′)
   ⊓⁻-comm (ν P) (ν P′) = cong ν_ (⊓-comm P P′)
   ⊓⁻-comm (! P) (! P′) = cong !_ (⊓-comm P P′)

   ⊓-comm ◻ P = sym (◻-⊓-rightZ P)
   ⊓-comm P ◻ = ◻-⊓-rightZ P
   ⊓-comm [ P ] [ P′ ] = cong [_] (⊓⁻-comm P P′)

   ⊔⁻-assoc : ∀ {Γ} {P : Proc Γ} → Associative _≡_ (_⊔⁻_ {P₀ = P})
   ⊔-assoc : ∀ {Γ} {P : Proc Γ} → Associative _≡_ (_⊔_ {P₀ = P})

   ⊔⁻-assoc Ο Ο Ο = refl
   ⊔⁻-assoc (x •∙ P₁) (.x •∙ P₂) (.x •∙ P₃) = cong (λ P† → x •∙ P†) (⊔-assoc P₁ P₂ P₃)
   ⊔⁻-assoc (• x 〈 y₁ 〉∙ P₁) (• .x 〈 y₂ 〉∙ P₂) (• .x 〈 y₃ 〉∙ P₃) =
      cong₂ (λ y† P† → • x 〈 y† 〉∙ P†) (ᴺ̃.⊔-assoc y₁ y₂ y₃) (⊔-assoc P₁ P₂ P₃)
   ⊔⁻-assoc (P₁ ➕ Q₁) (P₂ ➕ Q₂) (P₃ ➕ Q₃) = cong₂ _➕_ (⊔-assoc P₁ P₂ P₃) (⊔-assoc Q₁ Q₂ Q₃)
   ⊔⁻-assoc (P₁ │ Q₁) (P₂ │ Q₂) (P₃ │ Q₃) = cong₂ _│_ (⊔-assoc P₁ P₂ P₃) (⊔-assoc Q₁ Q₂ Q₃)
   ⊔⁻-assoc (ν P₁) (ν P₂) (ν P₃) = cong ν_ (⊔-assoc P₁ P₂ P₃)
   ⊔⁻-assoc (! P₁) (! P₂) (! P₃) = cong !_ (⊔-assoc P₁ P₂ P₃)

   ⊔-assoc ◻ _ _ = refl
   ⊔-assoc P ◻ P′ =
      begin (P ⊔ ◻) ⊔ P′ ≡⟨ cong (flip _⊔_ P′) (◻-⊔-rightId P) ⟩ P ⊔ P′ ∎
      where open EqReasoning (setoid _)
   ⊔-assoc P P′ ◻ =
      begin (P ⊔ P′) ⊔ ◻ ≡⟨ ◻-⊔-rightId _ ⟩ P ⊔ P′ ≡⟨ cong (_⊔_ P) (sym (◻-⊔-rightId _)) ⟩ P ⊔ (P′ ⊔ ◻) ∎
      where open EqReasoning (setoid _)
   ⊔-assoc [ P₁ ] [ P₂ ] [ P₃ ] = cong [_] (⊔⁻-assoc P₁ P₂ P₃)

   ⊓⁻-assoc : ∀ {Γ} {P : Proc Γ} → Associative _≡_ (_⊓⁻_ {P₀ = P})
   ⊓-assoc : ∀ {Γ} {P : Proc Γ} → Associative _≡_ (_⊓_ {P₀ = P})

   ⊓-assoc ◻ _ _ = refl
   ⊓-assoc P ◻ P′ =
      begin (P ⊓ ◻) ⊓ P′ ≡⟨ cong (flip _⊓_ P′) (◻-⊓-rightZ P) ⟩ ◻ ⊓ P′ ≡⟨ refl ⟩ ◻ ≡⟨ sym (◻-⊓-rightZ P) ⟩ P ⊓ ◻ ∎
      where open EqReasoning (setoid _)
   ⊓-assoc P P′ ◻ =
      begin
         (P ⊓ P′) ⊓ ◻
      ≡⟨ ◻-⊓-rightZ (P ⊓ P′) ⟩
         ◻
      ≡⟨ sym (◻-⊓-rightZ P) ⟩
         P ⊓ ◻
      ≡⟨ cong (_⊓_ P) (sym (◻-⊓-rightZ P′)) ⟩
         P ⊓ (P′ ⊓ ◻)
      ∎ where open EqReasoning (setoid _)
   ⊓-assoc [ P₁ ] [ P₂ ] [ P₃ ] = cong [_] (⊓⁻-assoc P₁ P₂ P₃)

   ⊓⁻-assoc Ο Ο Ο = refl
   ⊓⁻-assoc (x •∙ P₁) (.x •∙ P₂) (.x •∙ P₃) = cong (λ P† → x •∙ P†) (⊓-assoc P₁ P₂ P₃)
   ⊓⁻-assoc (• x 〈 y₁ 〉∙ P₁) (• .x 〈 y₂ 〉∙ P₂) (• .x 〈 y₃ 〉∙ P₃) =
      cong₂ (λ y† P† → • x 〈 y† 〉∙ P†) (ᴺ̃.⊓-assoc y₁ y₂ y₃) (⊓-assoc P₁ P₂ P₃)
   ⊓⁻-assoc (P₁ ➕ Q₁) (P₂ ➕ Q₂) (P₃ ➕ Q₃) = cong₂ _➕_ (⊓-assoc P₁ P₂ P₃) (⊓-assoc Q₁ Q₂ Q₃)
   ⊓⁻-assoc (P₁ │ Q₁) (P₂ │ Q₂) (P₃ │ Q₃) = cong₂ _│_ (⊓-assoc P₁ P₂ P₃) (⊓-assoc Q₁ Q₂ Q₃)
   ⊓⁻-assoc (ν P₁) (ν P₂) (ν P₃) = cong ν_ (⊓-assoc P₁ P₂ P₃)
   ⊓⁻-assoc (! P₁) (! P₂) (! P₃) = cong !_ (⊓-assoc P₁ P₂ P₃)

   ⊔⁻-absorbs-⊓ : ∀ {Γ} {P : Proc Γ} → _Absorbs_ _≡_ (_⊔⁻_ {P₀ = P}) _⊓⁻_
   ⊔-absorbs-⊓ : ∀ {Γ} {P : Proc Γ} → _Absorbs_ _≡_ (_⊔_ {P₀ = P}) _⊓_

   ⊔⁻-absorbs-⊓ Ο Ο = refl
   ⊔⁻-absorbs-⊓ (x •∙ P) (.x •∙ P′) = cong (λ P† → x •∙ P†) (⊔-absorbs-⊓ P P′)
   ⊔⁻-absorbs-⊓ (• x 〈 y 〉∙ P) (• .x 〈 y′ 〉∙ P′) =
      cong₂ (λ y† P† → • x 〈 y† 〉∙ P†) (ᴺ̃.⊔-absorbs-⊓ y y′) (⊔-absorbs-⊓ P P′)
   ⊔⁻-absorbs-⊓ (P ➕ Q) (P′ ➕ Q′) = cong₂ _➕_ (⊔-absorbs-⊓ P P′) (⊔-absorbs-⊓ Q Q′)
   ⊔⁻-absorbs-⊓ (P │ Q) (P′ │ Q′) = cong₂ _│_ (⊔-absorbs-⊓ P P′) (⊔-absorbs-⊓ Q Q′)
   ⊔⁻-absorbs-⊓ (ν P) (ν P′) = cong ν_ (⊔-absorbs-⊓ P P′)
   ⊔⁻-absorbs-⊓ (! P) (! P′) = cong !_ (⊔-absorbs-⊓ P P′)

   ⊔-absorbs-⊓ ◻ _ = refl
   ⊔-absorbs-⊓ P ◻ =
      begin P ⊔ (P ⊓ ◻) ≡⟨ cong (_⊔_ P) (◻-⊓-rightZ P) ⟩ P ⊔ ◻ ≡⟨ ◻-⊔-rightId P ⟩ P ∎
      where open EqReasoning (setoid _)
   ⊔-absorbs-⊓ [ P ] [ P′ ] = cong [_] (⊔⁻-absorbs-⊓ P P′)

   -- Idempotence follows from absorption but convenient to use it to prove absorption.
   ⊓⁻-idem : ∀ {Γ} {P : Proc Γ} → Idempotent _≡_ (_⊓⁻_ {P₀ = P})
   ⊓-idem : ∀ {Γ} {P : Proc Γ} → Idempotent _≡_ (_⊓_ {P₀ = P})

   ⊓⁻-idem Ο = refl
   ⊓⁻-idem (x •∙ P) = cong (λ P† → x •∙ P†) (⊓-idem P)
   ⊓⁻-idem (• x 〈 y 〉∙ P) = cong₂ (λ y† P† → • x 〈 y† 〉∙ P†) (⊓′-idem y) (⊓-idem P)
   ⊓⁻-idem (P ➕ Q) = cong₂ _➕_ (⊓-idem P) (⊓-idem Q)
   ⊓⁻-idem (P │ Q) = cong₂ _│_ (⊓-idem P) (⊓-idem Q)
   ⊓⁻-idem (ν P) = cong ν_ (⊓-idem P)
   ⊓⁻-idem (! P) = cong !_ (⊓-idem P)

   ⊓-idem ◻ = refl
   ⊓-idem [ P ] = cong [_] (⊓⁻-idem P)

   ⊓⁻-absorbs-⊔⁻ : ∀ {Γ} {P : Proc Γ} → _Absorbs_ _≡_ (_⊓⁻_ {P₀ = P}) _⊔⁻_
   ⊓-absorbs-⊔ : ∀ {Γ} {P : Proc Γ} → _Absorbs_ _≡_ (_⊓_ {P₀ = P}) _⊔_

   ⊓⁻-absorbs-⊔⁻ Ο Ο = refl
   ⊓⁻-absorbs-⊔⁻ (x •∙ P) (.x •∙ P′) = cong (λ P† → x •∙ P†) (⊓-absorbs-⊔ P P′)
   ⊓⁻-absorbs-⊔⁻ (• x 〈 y 〉∙ P) (• .x 〈 y′ 〉∙ P′) =
      cong₂ (λ y† P† → • x 〈 y† 〉∙ P†) (ᴺ̃.⊓-absorbs-⊔ y y′) (⊓-absorbs-⊔ P P′)
   ⊓⁻-absorbs-⊔⁻ (P ➕ Q) (P′ ➕ Q′) = cong₂ _➕_ (⊓-absorbs-⊔ P P′) (⊓-absorbs-⊔ Q Q′)
   ⊓⁻-absorbs-⊔⁻ (P │ Q) (P′ │ Q′) = cong₂ _│_ (⊓-absorbs-⊔ P P′) (⊓-absorbs-⊔ Q Q′)
   ⊓⁻-absorbs-⊔⁻ (ν P) (ν P′) = cong ν_ (⊓-absorbs-⊔ P P′)
   ⊓⁻-absorbs-⊔⁻ (! P) (! P′) = cong !_ (⊓-absorbs-⊔ P P′)

   ⊓-absorbs-⊔ ◻ _ = refl
   ⊓-absorbs-⊔ P ◻ =
      begin P ⊓ (P ⊔ ◻) ≡⟨ cong (_⊓_ P) (◻-⊔-rightId P) ⟩ P ⊓ P ≡⟨ ⊓-idem P ⟩ P ∎
      where open EqReasoning (setoid _)
   ⊓-absorbs-⊔ [ P ] [ P′ ] = cong [_] (⊓⁻-absorbs-⊔⁻ P P′)

   isLattice⁻ : ∀ {Γ} {P : Proc Γ} → IsLattice _≡_ (_⊔⁻_ {P₀ = P}) (_⊓⁻_ {P₀ = P})
   isLattice⁻ = record {
         isEquivalence = isEquivalence;
         ∨-comm = ⊔⁻-comm;
         ∨-assoc = ⊔⁻-assoc;
         ∨-cong = cong₂ _⊔⁻_;
         ∧-comm = ⊓⁻-comm;
         ∧-assoc = ⊓⁻-assoc;
         ∧-cong = cong₂ _⊓⁻_;
         absorptive = ⊔⁻-absorbs-⊓ , ⊓⁻-absorbs-⊔⁻
      }

   isLattice : ∀ {Γ} {P : Proc Γ} → IsLattice _≡_ (_⊔_ {P₀ = P}) (_⊓_ {P₀ = P})
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
      lattices : ∀ {Γ} → Lattices (Proc Γ)
      lattices = record {
            ↓_ = ↓_; ↓⁻_ = ↓⁻_; _⊔⁻_ = _⊔⁻_; _⊔_ = _⊔_; _⊓⁻_ = _⊓⁻_; _⊓_ = _⊓_; isLattice⁻ = isLattice⁻; isLattice = isLattice
         }

   open Lattices using (_≤⁻ᴸ_; _≤ᴸ_)

   ≤⁻ᴸ⇒≤⁻ : ∀ {Γ} {P : Proc Γ} → _≤⁻ᴸ_ lattices {a = P} ⇒ _≤⁻_
   ≤ᴸ⇒≤ : ∀ {Γ} {P : Proc Γ} → _≤ᴸ_ lattices {a = P} ⇒ _≤_

   ≤⁻ᴸ⇒≤⁻ {i = Ο} {Ο} _ = Ο
   ≤⁻ᴸ⇒≤⁻ {i = x •∙ P} {.x •∙ P′} _ with P ⊓ P′ | inspect (_⊓_ P) P′
   ≤⁻ᴸ⇒≤⁻ {i = x •∙ P} {.x •∙ P′} refl | .P | [ P≤⁻ᴸP′ ] = x •∙ ≤ᴸ⇒≤ (sym P≤⁻ᴸP′)
   ≤⁻ᴸ⇒≤⁻ {i = • x 〈 y 〉∙ P} {• .x 〈 y′ 〉∙ P′} _ with y ⊓′ y′ | P ⊓ P′ | inspect (_⊓′_ y) y′ | inspect (_⊓_ P) P′
   ≤⁻ᴸ⇒≤⁻ {i = • x 〈 y 〉∙ P} {• .x 〈 y′ 〉∙ P′} refl | .y | .P | [ y≤⁻ᴸy′ ] | [ P≤⁻ᴸP′ ] =
      • x 〈 ≤′ᴸ⇒≤′ (sym y≤⁻ᴸy′) 〉∙ ≤ᴸ⇒≤ (sym P≤⁻ᴸP′)
   ≤⁻ᴸ⇒≤⁻ {i = P ➕ Q} {P′ ➕ Q′} _ with P ⊓ P′ | Q ⊓ Q′ |
      inspect (_⊓_ P) P′ | inspect (_⊓_ Q) Q′
   ≤⁻ᴸ⇒≤⁻ {i = P ➕ Q} {P′ ➕ Q′} refl | .P | .Q | [ P≤⁻ᴸP′ ] | [ Q≤⁻ᴸQ′ ] = ≤ᴸ⇒≤ (sym P≤⁻ᴸP′) ➕ ≤ᴸ⇒≤ (sym Q≤⁻ᴸQ′)
   ≤⁻ᴸ⇒≤⁻ {i = P │ Q} {P′ │ Q′} _ with P ⊓ P′ | Q ⊓ Q′ |
      inspect (_⊓_ P) P′ | inspect (_⊓_ Q) Q′
   ≤⁻ᴸ⇒≤⁻ {i = P │ Q} {P′ │ Q′} refl | .P | .Q | [ P≤⁻ᴸP′ ] | [ Q≤⁻ᴸQ′ ] = ≤ᴸ⇒≤ (sym P≤⁻ᴸP′) │ ≤ᴸ⇒≤ (sym Q≤⁻ᴸQ′)
   ≤⁻ᴸ⇒≤⁻ {i = ν P} {ν P′} _ with P ⊓ P′ | inspect (_⊓_ P) P′
   ≤⁻ᴸ⇒≤⁻ {i = ν P} {ν P′} refl | .P | [ P≤⁻ᴸP′ ] = ν ≤ᴸ⇒≤ (sym P≤⁻ᴸP′)
   ≤⁻ᴸ⇒≤⁻ {i = ! P} { ! P′} _ with P ⊓ P′ | inspect (_⊓_ P) P′
   ≤⁻ᴸ⇒≤⁻ {i = ! P} { ! P′} refl | .P | [ P≤⁻ᴸP′ ] = ! ≤ᴸ⇒≤ (sym P≤⁻ᴸP′)

   ≤ᴸ⇒≤ {i = ◻} {◻} _ = ◻
   ≤ᴸ⇒≤ {i = ◻} {[ _ ]} _ = ◻
   ≤ᴸ⇒≤ {i = [ P ]} {[ P′ ]} _ with P ⊓⁻ P′ | inspect (_⊓⁻_ P) P′
   ≤ᴸ⇒≤ {i = [ P ]} {[ P′ ]} refl | .P | [ P≤⁻ᴸP′ ] = [ ≤⁻ᴸ⇒≤⁻ (sym P≤⁻ᴸP′) ]
   ≤ᴸ⇒≤ {i = [ _ ]} {◻} ()

   ≤⁻⇒≤⁻ᴸ : ∀ {Γ} {P : Proc Γ} → _≤⁻_ ⇒ _≤⁻ᴸ_ lattices {a = P}
   ≤⇒≤ᴸ : ∀ {Γ} {P : Proc Γ} → _≤_ ⇒ _≤ᴸ_ lattices {a = P}

   ≤⁻⇒≤⁻ᴸ Ο = refl
   ≤⁻⇒≤⁻ᴸ (x •∙ P) = cong (λ P† → x •∙ P†) (≤⇒≤ᴸ P)
   ≤⁻⇒≤⁻ᴸ (• x 〈 y 〉∙ P) = cong₂ (λ y† P† → • x 〈 y† 〉∙ P†) (≤′⇒≤′ᴸ y) (≤⇒≤ᴸ P)
   ≤⁻⇒≤⁻ᴸ (P ➕ Q) = cong₂ _➕_ (≤⇒≤ᴸ P) (≤⇒≤ᴸ Q)
   ≤⁻⇒≤⁻ᴸ (P │ Q) = cong₂ _│_ (≤⇒≤ᴸ P) (≤⇒≤ᴸ Q)
   ≤⁻⇒≤⁻ᴸ (ν P) = cong ν_ (≤⇒≤ᴸ P)
   ≤⁻⇒≤⁻ᴸ (! P) = cong !_ (≤⇒≤ᴸ P)

   ≤⇒≤ᴸ ◻ = refl
   ≤⇒≤ᴸ [ P ] = cong [_] (≤⁻⇒≤⁻ᴸ P)

   instance
      prefixes : ∀ {Γ} → Prefixes (Proc Γ)
      prefixes = record {
            lattices = lattices; _≤_ = _≤_; _≤⁻_ = _≤⁻_; ≤⁻ᴸ⇒≤⁻ = ≤⁻ᴸ⇒≤⁻; ≤ᴸ⇒≤ = ≤ᴸ⇒≤; ≤⁻⇒≤⁻ᴸ = ≤⁻⇒≤⁻ᴸ; ≤⇒≤ᴸ = ≤⇒≤ᴸ
         }
