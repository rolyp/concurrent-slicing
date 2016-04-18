module Transition.Lattice where

   open import ConcurrentSlicingCommon

   open import Action as ᴬ using (Action; module Action; Actionᵇ; module Actionᵇ; Actionᶜ; module Actionᶜ);
      open Action; open Actionᵇ; open Actionᶜ
   import Action.Lattice as ᴬ̃;
      open ᴬ̃.↓_; open ᴬ̃.↓⁻_; open ᴬ̃.↓ᵇ⁻_; open ᴬ̃.↓ᶜ⁻_; open ᴬ̃._≤_; open ᴬ̃._≤⁻_; open ᴬ̃._≤ᵇ⁻_; open ᴬ̃._≤ᶜ⁻_
   open import Action.Ren
   open import Lattice using (Lattices; Prefixes);
      open Lattice.Prefixes ⦃...⦄
         using (ᴹ; _⊔ᴹ_; _⊔ʳ_; ≤-trans)
         renaming (↓_ to ↓′_; ↓⁻_ to ↓⁻′_; _≤_ to _≤′_; _≤⁻_ to _≤⁻′_; _⊔_ to _⊔′_; _⊔⁻_ to _⊔⁻′_)
   import Lattice.Product
   open import Name using (Name; _+_; zero; suc)
   import Name.Lattice as ᴺ̃; open ᴺ̃.↓_; open ᴺ̃._≤_
   open import Proc using (Proc; module Proc); open Proc.Proc
   import Proc.Lattice as ᴾ̃; open ᴾ̃.↓_; open ᴾ̃.↓⁻_; open ᴾ̃._≤_; open ᴾ̃._≤⁻_
   open import Proc.Ren.Lattice renaming (_* to _*̃)
   open import Ren as ᴿ using (module Renameable); open Renameable ⦃...⦄
   open import Ren.Lattice as ᴿ̃ using (pop; popᴹ; push; swap)
   open import Transition as ᵀ using (_—[_-_]→_; module _—[_-_]→_); open _—[_-_]→_

   infixl 6 _➕₁_ _ᵇ│_ _ᶜ│_ _│ᵇ_ _│ᶜ_ _│•_ _│ᵥ_
   mutual
      data ↓⁻_ {Γ} : ∀ {P} {a : Action Γ} {R} → P —[ a - _ ]→ R → Set where
         _•∙_ : ∀ {x : Name Γ} {P : Proc (Γ + 1)} → ↓′ x → ↓′ P → ↓⁻ (x •∙ P)
         •_〈_〉∙_ : ∀ {x y : Name Γ} {P : Proc Γ} → ↓′ x → ↓′ y → ↓′ P → ↓⁻ (• x 〈 y 〉∙ P)
         _➕₁_ : ∀ {P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} {Q : Proc Γ} → ↓ E → ↓′ Q → ↓⁻ (E ➕₁ Q)
         _ᵇ│_ : ∀ {P} {a : Actionᵇ Γ} {R} {E : P —[ a ᵇ - _ ]→ R} {Q : Proc Γ} → ↓ E → ↓′ Q → ↓⁻ (E ᵇ│ Q)
         _ᶜ│_ : ∀ {P} {a : Actionᶜ Γ} {R} {E : P —[ a ᶜ - _ ]→ R} {Q : Proc Γ} → ↓ E → ↓′ Q → ↓⁻ (E ᶜ│ Q)
         _│ᵇ_ : ∀ {Q} {a : Actionᵇ Γ} {S} {P : Proc Γ} {F : Q —[ a ᵇ - _ ]→ S} → ↓′ P → ↓ F → ↓⁻ (P │ᵇ F)
         _│ᶜ_ : ∀ {Q} {a : Actionᶜ Γ} {S} {P : Proc Γ} {F : Q —[ a ᶜ - _ ]→ S} → ↓′ P → ↓ F → ↓⁻ (P │ᶜ F)
         _│•_ : ∀ {P R Q S} {x : Name Γ} {y : Name Γ} {E : P —[ x • ᵇ - _ ]→ R} {F : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S} →
                ↓ E → ↓ F → ↓⁻ (E │• F)
         _│ᵥ_ : ∀ {P R Q S} {x : Name Γ} {E : P —[ x • ᵇ - _ ]→ R} {F : Q —[ (• x) ᵇ - _ ]→ S} →
                ↓ E → ↓ F → ↓⁻ (E │ᵥ F)
         ν•_ : ∀ {P R} {x : Name Γ} {E : P —[ • suc x 〈 zero 〉 ᶜ - _ ]→ R} → ↓ E → ↓⁻ ν• E
         νᵇ_ : ∀ {P} {a : Actionᵇ Γ} {R} {E : P —[ (ᴿ.push *) a ᵇ - _ ]→ R} → ↓ E → ↓⁻ νᵇ E
         νᶜ_ : ∀ {P} {a : Actionᶜ Γ} {R} {E : P —[ (ᴿ.push *) a ᶜ - _ ]→ R} → ↓ E → ↓⁻ νᶜ E
         !_ : ∀ {P} {a : Action Γ} {R} {E : P │ ! P —[ a - _ ]→ R} → ↓ E → ↓⁻ ! E

      data ↓_ {Γ} : ∀ {P} {a : Action Γ} {R} → P —[ a - _ ]→ R → Set where
         ◻ : ∀ {P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → ↓ E
         [_] : ∀ {P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → ↓⁻ E → ↓ E

   infix 4 _≤⁻_ _≤_
   mutual
      data _≤⁻_ {Γ} : ∀ {P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → ↓⁻ E → ↓⁻ E → Set where
         _•∙_ : ∀ {x₀ : Name Γ} {P₀} {x x′ : ↓′ x₀} {P P′ : ↓′ P₀} → x ≤′ x′ → P ≤′ P′ → x •∙ P ≤⁻ x′ •∙ P′
         •_〈_〉∙_ : ∀ {x₀ y₀ : Name Γ} {P₀} {x x′ : ↓′ x₀} {y y′ : ↓′ y₀} {P P′ : ↓′ P₀} →
                   x ≤′ x′ → y ≤′ y′ → P ≤′ P′ → • x 〈 y 〉∙ P ≤⁻ • x′ 〈 y′ 〉∙ P′
         _➕₁_ : ∀ {P} {a : Action Γ} {R} {E₀ : P —[ a - _ ]→ R} {Q₀ : Proc Γ} {E E′ : ↓ E₀} {Q Q′ : ↓′ Q₀} →
                 E ≤ E′ → Q ≤′ Q′ → E ➕₁ Q ≤⁻ E′ ➕₁ Q′
         _ᵇ│_ : ∀ {P} {a : Actionᵇ Γ} {R} {E₀ : P —[ a ᵇ - _ ]→ R} {Q₀ : Proc Γ} {E E′ : ↓ E₀} {Q Q′ : ↓′ Q₀} →
                E ≤ E′ → Q ≤′ Q′ → E ᵇ│ Q ≤⁻ E′ ᵇ│ Q′
         _ᶜ│_ : ∀ {P} {a : Actionᶜ Γ} {R} {E₀ : P —[ a ᶜ - _ ]→ R} {Q₀ : Proc Γ} {E E′ : ↓ E₀} {Q Q′ : ↓′ Q₀} →
                E ≤ E′ → Q ≤′ Q′ → E ᶜ│ Q ≤⁻ E′ ᶜ│ Q′
         _│ᵇ_ : ∀ {Q} {a : Actionᵇ Γ} {S} {P₀ : Proc Γ} {F₀ : Q —[ a ᵇ - _ ]→ S} {P P′ : ↓′ P₀} {F F′ : ↓ F₀} →
                P ≤′ P′ → F ≤ F′ → P │ᵇ F ≤⁻ P′ │ᵇ F′
         _│ᶜ_ : ∀ {Q} {a : Actionᶜ Γ} {S} {P₀ : Proc Γ} {F₀ : Q —[ a ᶜ - _ ]→ S} {P P′ : ↓′ P₀} {F F′ : ↓ F₀} →
                P ≤′ P′ → F ≤ F′ → P │ᶜ F ≤⁻ P′ │ᶜ F′
         _│•_ : ∀ {P R Q S} {x : Name Γ} {y : Name Γ} {E₀ : P —[ x • ᵇ - _ ]→ R} {F₀ : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S}
                {E E′ : ↓ E₀} {F F′ : ↓ F₀} → E ≤ E′ → F ≤ F′ → E │• F ≤⁻ E′ │• F′
         _│ᵥ_ : ∀ {P R Q S} {x : Name Γ} {E₀ : P —[ x • ᵇ - _ ]→ R} {F₀ : Q —[ (• x) ᵇ - _ ]→ S}
                {E E′ : ↓ E₀} {F F′ : ↓ F₀} → E ≤ E′ → F ≤ F′ → E │ᵥ F ≤⁻ E′ │ᵥ F′
         ν•_ : ∀ {P R} {x : Name Γ} {E₀ : P —[ • suc x 〈 zero 〉 ᶜ - _ ]→ R} {E E′ : ↓ E₀} → E ≤ E′ → ν• E ≤⁻ ν• E′
         νᵇ_ : ∀ {P R} {a : Actionᵇ Γ} {E₀ : P —[ (ᴿ.push *) a ᵇ - _ ]→ R} {E E′ : ↓ E₀} → E ≤ E′ → νᵇ E ≤⁻ νᵇ E′
         νᶜ_ : ∀ {P R} {a : Actionᶜ Γ} {E₀ : P —[ (ᴿ.push *) a ᶜ - _ ]→ R} {E E′ : ↓ E₀} → E ≤ E′ → νᶜ E ≤⁻ νᶜ E′
         !_ : ∀ {P} {a : Action Γ} {R} {E₀ : P │ ! P —[ a - _ ]→ R} {E E′ : ↓ E₀} → E ≤ E′ → ! E ≤⁻ ! E′

      data _≤_ {Γ} : ∀ {P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → ↓ E → ↓ E → Set where
         ◻ : ∀ {P} {a : Action Γ} {R} {E₀ : P —[ a - _ ]→ R} {E : ↓ E₀} → ◻ ≤ E
         [_] : ∀ {P} {a : Action Γ} {R} {E₀ : P —[ a - _ ]→ R} {E E′ : ↓⁻ E₀} → E ≤⁻ E′ → [ E ] ≤ [ E′ ]

   -- Keep as postulates; too trivial to justify amount of boilerplate involved in proving them.
   postulate
      _⊔⁻_ : ∀ {Γ P} {a : Action Γ} {R} {E₀ : P —[ a - _ ]→ R} (E E′ : ↓⁻ E₀) → ↓⁻ E₀
      _⊓⁻_ : ∀ {Γ P} {a : Action Γ} {R} {E₀ : P —[ a - _ ]→ R} (E E′ : ↓⁻ E₀) → ↓⁻ E₀
      ⊔⁻-comm : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → Commutative _≡_ (_⊔⁻_ {E₀ = E})
      ⊔⁻-assoc : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → Associative _≡_ (_⊔⁻_ {E₀ = E})
      ⊓⁻-comm : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → Commutative _≡_ (_⊓⁻_ {E₀ = E})
      ⊓⁻-assoc : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → Associative _≡_ (_⊓⁻_ {E₀ = E})
      ⊓⁻-idem : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a  - _ ]→ R} → Idempotent _≡_ (_⊓⁻_ {E₀ = E})
      ⊔⁻-absorbs-⊓⁻ : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → _Absorbs_ _≡_ (_⊔⁻_ {E₀ = E}) _⊓⁻_
      ⊓⁻-absorbs-⊔⁻ : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → _Absorbs_ _≡_ (_⊓⁻_ {E₀ = E}) _⊔⁻_

   -- TODO: should do these though, as they're not verbose.
   postulate
      _⊔_ : ∀ {Γ P} {a : Action Γ} {R} {E₀ : P —[ a - _ ]→ R} (E E′ : ↓ E₀) → ↓ E₀
      _⊓_ : ∀ {Γ P} {a : Action Γ} {R} {E₀ : P —[ a - _ ]→ R} (E E′ : ↓ E₀) → ↓ E₀
      ⊔-comm : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → Commutative _≡_ (_⊔_ {E₀ = E})
      ⊔-assoc : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → Associative _≡_ (_⊔_ {E₀ = E})
      ⊓-comm : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → Commutative _≡_ (_⊓_ {E₀ = E})
      ⊓-assoc : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → Associative _≡_ (_⊓_ {E₀ = E})
      ⊓-idem : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → Idempotent _≡_ (_⊓_ {E₀ = E})
      ⊔-absorbs-⊓ : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → _Absorbs_ _≡_ (_⊔_ {E₀ = E}) _⊓_
      ⊓-absorbs-⊔ : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → _Absorbs_ _≡_ (_⊓_ {E₀ = E}) _⊔_

   isLattice⁻ : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → IsLattice _≡_ (_⊔⁻_ {E₀ = E}) _⊓⁻_
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

   isLattice : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → IsLattice _≡_ (_⊔_ {E₀ = E}) _⊓_
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
      lattices : ∀ {Γ P} {a : Action Γ} {R} → Lattices (P —[ a - _ ]→ R)
      lattices = record {
            ↓_ = ↓_; ↓⁻_ = ↓⁻_; _⊔⁻_ = _⊔⁻_; _⊔_ = _⊔_; _⊓⁻_ = _⊓⁻_; _⊓_ = _⊓_;
            isLattice⁻ = isLattice⁻; isLattice = isLattice
         }

   open Lattice.Lattices using (_≤⁻ᴸ_; _≤ᴸ_)

   -- Omitted (trivial and boilerplate-heavy).
   postulate
      ≤⁻ᴸ⇒≤⁻ : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → _≤⁻ᴸ_ lattices {a = E} ⇒ _≤⁻_
      ≤⁻⇒≤⁻ᴸ : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → _≤⁻_ ⇒ _≤⁻ᴸ_ lattices {a = E}

   -- TODO.
   postulate
      ≤ᴸ⇒≤ : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → _≤ᴸ_ lattices {a = E} ⇒ _≤_
      ≤⇒≤ᴸ : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → _≤_ ⇒ _≤ᴸ_ lattices {a = E}

   instance
      prefixes : ∀ {Γ P} {a : Action Γ} {R} → Prefixes (P —[ a - _ ]→ R)
      prefixes = record {
            lattices = lattices; _≤_ = _≤_; _≤⁻_ = _≤⁻_; ≤⁻ᴸ⇒≤⁻ = ≤⁻ᴸ⇒≤⁻; ≤ᴸ⇒≤ = ≤ᴸ⇒≤; ≤⁻⇒≤⁻ᴸ = ≤⁻⇒≤⁻ᴸ; ≤⇒≤ᴸ = ≤⇒≤ᴸ
         }

   source⁻ : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → ↓⁻ E → ↓⁻′ ᵀ.source E
   source : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → ↓ E → ↓′ ᵀ.source E

   source⁻ (x •∙ P) = x •∙ P
   source⁻ (• x 〈 y 〉∙ P) = • x 〈 y 〉∙ P
   source⁻ (E ➕₁ Q) = source E ➕ Q
   source⁻ (E ᵇ│ Q) = source E │ Q
   source⁻ (E ᶜ│ Q) = source E │ Q
   source⁻ (P │ᵇ F) = P │ source F
   source⁻ (P │ᶜ F) = P │ source F
   source⁻ (E │• F) = source E │ source F
   source⁻ (E │ᵥ F) = source E │ source F
   source⁻ (ν• E) = ν source E
   source⁻ (νᵇ E) = ν source E
   source⁻ (νᶜ E) = ν source E
   source⁻ (! E) with source E
   ... | ◻ = ! ◻
   ... | [ P │ ◻ ] = ! P
   ... | [ P │ [ P′ ] ] = ! P ⊔⁻′ P′

   source ◻ = ◻
   source [ E ] = [ source⁻ E ]

   source⁻ᴹ : ∀ {Γ P} {a : Action Γ} {R} {E₀ : P —[ a - _ ]→ R} {E E′ : ↓⁻ E₀} → E ≤⁻ E′ → source⁻ E ≤⁻′ source⁻ E′
   sourceᴹ : ∀ {Γ P} {a : Action Γ} {R} {E₀ : P —[ a - _ ]→ R} {E E′ : ↓ E₀} → E ≤ E′ → source E ≤′ source E′

   source⁻ᴹ (x •∙ P) = x •∙ P
   source⁻ᴹ (• x 〈 y 〉∙ P) = • x 〈 y 〉∙ P
   source⁻ᴹ (E ➕₁ Q) = sourceᴹ E ➕ Q
   source⁻ᴹ (E ᵇ│ Q) = sourceᴹ E │ Q
   source⁻ᴹ (E ᶜ│ Q) = sourceᴹ E │ Q
   source⁻ᴹ (P │ᵇ F) = P │ sourceᴹ F
   source⁻ᴹ (P │ᶜ F) = P │ sourceᴹ F
   source⁻ᴹ (E │• F) = sourceᴹ E │ sourceᴹ F
   source⁻ᴹ (E │ᵥ F) = sourceᴹ E │ sourceᴹ F
   source⁻ᴹ (ν• E) = ν sourceᴹ E
   source⁻ᴹ (νᵇ E) = ν sourceᴹ E
   source⁻ᴹ (νᶜ E) = ν sourceᴹ E
   source⁻ᴹ {E = ! E′} { ! E″} (! E) with source E′ | source E″ | sourceᴹ E
   ... | ◻ | ◻ | ◻ = ! ◻
   ... | ◻ | [ _ │ ◻ ] | ◻ = ! ◻
   ... | ◻ | [ _ │ [ ! _ ] ] | ◻ = ! ◻
   ... | [ _ │ ◻ ] | [ _ │ ◻ ] | [ P │ ◻ ] = ! P
   ... | [ _ │ ◻ ] | [ P │ [ ! P′ ] ] | [ P† │ _ ] = ! ≤-trans P† (P ⊔ʳ P′)
   ... | [ _ │ [ ! _ ] ] | [ _ │ ◻ ] | [ _ │ () ]
   ... | [ _ │ [ ! _ ] ] | [ _ │ [ ! _ ] ] | [ P │ [ ! P′ ] ] = ! (P ⊔ᴹ P′)

   sourceᴹ ◻ = ◻
   sourceᴹ [ E ] = [ source⁻ᴹ E ]

   open module Action×Proc {Γ} = Lattice.Product (Action Γ) (Proc ∘ᶠ ᴬ.target) using (×-prefixes)

   -- Seem to need this to coerce product lattice to more specific type.
   instance
      ᴬᴾ-prefixes : ∀ {Γ} → Lattice.Prefixes (Σ[ a ∈ Action Γ ] Proc (ᴬ.target a))
      ᴬᴾ-prefixes = ×-prefixes

   out : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → ↓ E → ↓′ ᵀ.out E
   out ◻ = ◻ , ◻
   out [ x •∙ P ] = [ x • ᵇ ] , P
   out [ • x 〈 y 〉∙ P ] = [ • x 〈 y 〉 ᶜ ] , P
   out [ E ➕₁ Q ] = out E
   out [ E ᵇ│ Q ] with out E; ... | a , P = a , [ P │ (push *̃) Q ]
   out [ E ᶜ│ Q ] with out E; ... | a , P = a , [ P │ Q ]
   out [ P │ᵇ F ] with out F; ... | a , Q = a , [ (push *̃) P │ Q ]
   out [ P │ᶜ F ] with out F; ... | a , Q = a , [ P │ Q ]
   out [ E │• F ] with out E | out F
   ... | _ , P | ◻ , Q = [ τ ᶜ ] , [ (pop ◻ *̃) P │ Q ]
   ... | _ , P | [ • _ 〈 y 〉 ᶜ ] , Q = [ τ ᶜ ] , [ (pop y *̃) P │ Q ]
   out [ E │ᵥ F ] with out E | out F
   ... | _ , P | _ , Q = [ τ ᶜ ] , [ ν [ P │ Q ] ]
   out [ ν•_ {x = x} E ] with out E
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , P = [ (• [ x ]) ᵇ ] , P
   ... | _ , P = ◻ , P
   out {a = x • ᵇ} [ νᵇ E ] with out E
   ... | [ ([ ._ ] •) ᵇ ] , P = [ [ x ] • ᵇ ] , [ ν (swap *̃) P ]
   ... | _ , P = ◻ , [ ν (swap *̃) P ]
   out {a = (• x) ᵇ} [ νᵇ E ] with out E
   ... | [ (• [ ._ ]) ᵇ ] , P = [ (• [ x ]) ᵇ ] ,  [ ν (swap *̃) P ]
   ... | _ , P = ◻ , [ ν (swap *̃) P ]
   out {a = • x 〈 y 〉 ᶜ} [ νᶜ E ] with out E
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , P = [ • [ x ] 〈 [ y ] 〉 ᶜ ] , [ ν P ]
   ... | _ , P = ◻ , [ ν P ]
   out {a = τ ᶜ} [ νᶜ E ] with out E
   ... | [ τ ᶜ ] , P = [ τ ᶜ ] , [ ν P ]
   ... | _ , P = ◻ , [ ν P ]
   out [ ! E ] = out E

   -- See Transition module for why we bundle these properties together. The case-explosion is a consequence.
   outᴹ : ∀ {Γ P} {a : Action Γ} {R} {E₀ : P —[ a - _ ]→ R} {E E′ : ↓ E₀} → E ≤ E′ → out E ≤′ out E′
   outᴹ ◻ = ◻ , ◻
   outᴹ [ x •∙ P ] = [ (x •) ᵇ ] , P
   outᴹ [ • x 〈 y 〉∙ P ] = [ • x 〈 y 〉 ᶜ ] , P
   outᴹ [ E ➕₁ Q ] = outᴹ E
   outᴹ [ E ᵇ│ Q ] with outᴹ E; ... | a , P = a , [ P │ (ᴹ push *ᴹ) Q ]
   outᴹ [ E ᶜ│ Q ] with outᴹ E; ... | a , P = a , [ P │ Q ]
   outᴹ [ P │ᵇ F ] with outᴹ F; ... | a , Q = a , [ (ᴹ push *ᴹ) P │ Q ]
   outᴹ [ P │ᶜ F ] with outᴹ F; ... | a , Q = a , [ P │ Q ]
   outᴹ {E = [ _ │• F′ ]} {[ _ │• F″ ]} [ E │• F ] with outᴹ E | out F′ | out F″ | outᴹ F
   ... | _ , P | ◻ , _ | ◻ , _ | ◻ , Q = [ τ ᶜ ] , [ (popᴹ ◻ *ᴹ) P │ Q ]
   ... | _ , P | ◻ , _ | [ • _ 〈 _ 〉 ᶜ ] , _ | ◻ , Q = [ τ ᶜ ] , [ (popᴹ ◻ *ᴹ) P │ Q ]
   ... | _ , P | [ • _ 〈 _ 〉 ᶜ ] , _ | [ • _ 〈 _ 〉 ᶜ ] , _ | [ • _ 〈 y 〉 ᶜ ] , Q = [ τ ᶜ ] , [ (popᴹ y *ᴹ) P │ Q ]
   outᴹ [ E │ᵥ F ] with outᴹ E | outᴹ F
   ... | _ , P | _ , Q = [ τ ᶜ ] , [ ν [ P │ Q ] ]
   outᴹ {E = [ ν• E′ ]} {[ ν• E″ ]} [ ν•_ {x = x} E ] with out E′ | out E″ | outᴹ E
   ... | ◻ , _ | ◻ , _ | _ , P = ◻ , P
   ... | ◻ , _ | [ • ◻ 〈 _ 〉 ᶜ ] , _ | _ , P = ◻ , P
   ... | ◻ , _ | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | _ , P = ◻ , P
   ... | ◻ , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | _ , P = ◻ , P
   ... | [ • ◻ 〈 _ 〉 ᶜ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , P = ◻ , P
   ... | [ • ◻ 〈 _ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , P = ◻ , P
   ... | [ • ◻ 〈 _ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , P = ◻ , P
   ... | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , P = ◻ , P
   ... | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , P = ◻ , P
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , P =
      [ (• [ x ]) ᵇ ] , P
   outᴹ {a = x • ᵇ} {E = [ νᵇ E′ ]} {[ νᵇ E″ ]} [ νᵇ E ] with out E′ | out E″ | outᴹ E
   ... | ◻ , _ | ◻ , _ | _ , P = ◻ , [ ν (ᴹ swap *ᴹ) P ]
   ... | ◻ , _ | [ (◻ •) ᵇ ] , _ | _ , P = ◻ , [ ν (ᴹ swap *ᴹ) P ]
   ... | ◻ , _ | [ ([ ._ ] •) ᵇ ] , _ | _ , P = ◻ , [ ν (ᴹ swap *ᴹ) P ]
   ... | [ (◻ •) ᵇ ] , _ | [ (◻ •) ᵇ ] , _ | [ (◻ •) ᵇ ] , P = ◻ , [ ν (ᴹ swap *ᴹ) P ]
   ... | [ (◻ •) ᵇ ] , _ | [ ([ ._ ] •) ᵇ ] , _ | [ (◻ •) ᵇ ] , P = ◻ , [ ν (ᴹ swap *ᴹ) P ]
   ... | [ [ ._ ] • ᵇ ] , _ | [ [ ._ ] • ᵇ ] , _ | [ [ ._ ] • ᵇ ] , P = [ [ x ] • ᵇ ] , [ ν (ᴹ swap *ᴹ) P ]
   outᴹ {a = (• x) ᵇ} {E = [ νᵇ E′ ]} {[ νᵇ E″ ]} [ νᵇ E ] with out E′ | out E″ | outᴹ E
   ... | ◻ , _ | ◻ , _ | _ , P = ◻ , [ ν (ᴹ swap *ᴹ) P ]
   ... | ◻ , _ | [ (• ◻) ᵇ ] , _ | _ , P = ◻ , [ ν (ᴹ swap *ᴹ) P ]
   ... | ◻ , _ | [ (• [ ._ ]) ᵇ ] , _ | _ , P = ◻ , [ ν (ᴹ swap *ᴹ) P ]
   ... | [ (• ◻) ᵇ ] , _ | [ (• ◻) ᵇ ] , _ | [ (• ◻) ᵇ ] , P = ◻ , [ ν (ᴹ swap *ᴹ) P ]
   ... | [ (• ◻) ᵇ ] , _ | [ (• [ ._ ]) ᵇ ] , _ | [ (• ◻) ᵇ ] , P = ◻ , [ ν (ᴹ swap *ᴹ) P ]
   ... | [ (• [ ._ ]) ᵇ ] , _ | [ (• [ ._ ]) ᵇ ] , _ | [ (• [ ._ ]) ᵇ ] , P = [ (• [ x ]) ᵇ ] , [ ν (ᴹ swap *ᴹ) P ]
   outᴹ {a = • x 〈 y 〉 ᶜ} {E = [ νᶜ E′ ]} {[ νᶜ E″ ]} [ νᶜ E ] with out E′ | out E″ | outᴹ E
   ... | ◻ , _ | ◻ , _ | _ , P = ◻ , [ ν P ]
   ... | ◻ , _ | [ • ◻ 〈 _ 〉 ᶜ ] , _ | _ , P = ◻ , [ ν P ]
   ... | ◻ , _ | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | _ , P = ◻ , [ ν P ]
   ... | ◻ , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | _ , P = ◻ , [ ν P ]
   ... | [ • ◻ 〈 _ 〉 ᶜ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , P = ◻ , [ ν P ]
   ... | [ • ◻ 〈 _ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , P = ◻ , [ ν P ]
   ... | [ • ◻ 〈 _ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , P = ◻ , [ ν P ]
   ... | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , P = ◻ , [ ν P ]
   ... | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , P = ◻ , [ ν P ]
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , P =
      [ • [ x ] 〈 [ y ] 〉 ᶜ ] , [ ν P ]
   outᴹ {a = τ ᶜ} {E = [ νᶜ E′ ]} {[ νᶜ E″ ]} [ νᶜ E ] with out E′ | out E″ | outᴹ E
   ... | ◻ , _ | ◻ , _ | _ , P = ◻ , [ ν P ]
   ... | ◻ , _ | [ τ ᶜ ] , _ | _ , P = ◻ , [ ν P ]
   ... | [ τ ᶜ ] , _ | [ τ ᶜ ] , _ | [ τ ᶜ ] , P = [ τ ᶜ ] , [ ν P ]
   outᴹ [ ! E ] = outᴹ E

   action : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → ↓ E → ↓′ ᵀ.action E
   action = π₁ ∘ᶠ out

   actionᴹ : ∀ {Γ P} {a : Action Γ} {R} {E₀ : P —[ a - _ ]→ R} {E E′ : ↓ E₀} → E ≤ E′ → action E ≤′ action E′
   actionᴹ = π₁ ∘ᶠ outᴹ

   target : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → ↓ E → ↓′ ᵀ.target E
   target = π₂ ∘ᶠ out

   targetᴹ : ∀ {Γ P} {a : Action Γ} {R} {E₀ : P —[ a - _ ]→ R} {E E′ : ↓ E₀} → E ≤ E′ → target E ≤′ target E′
   targetᴹ = π₂ ∘ᶠ outᴹ
