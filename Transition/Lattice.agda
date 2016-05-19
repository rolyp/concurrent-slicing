module Transition.Lattice where

   open import ConcurrentSlicingCommon

   open import Action as ᴬ using (Action; module Action; Actionᵇ; module Actionᵇ; Actionᶜ; module Actionᶜ);
      open Action; open Actionᵇ; open Actionᶜ
   import Action.Lattice as ᴬ̃;
      open ᴬ̃.↓_; open ᴬ̃.↓⁻_; open ᴬ̃.↓ᵇ⁻_; open ᴬ̃.↓ᶜ⁻_; open ᴬ̃._≤_; open ᴬ̃._≤⁻_; open ᴬ̃._≤ᵇ⁻_; open ᴬ̃._≤ᶜ⁻_
   open import Action.Ren
   open import Lattice using (Lattices; Prefixes);
      open Lattice.Prefixes ⦃...⦄
         using (ᴹ; ⁻ᴹ; _⊔ᴹ_; _⊔ʳ_; ≤-trans; ≤⁻-trans)
         renaming (↓_ to ↓′_; ↓⁻_ to ↓⁻′_; _≤_ to _≤′_; _≤⁻_ to _≤⁻′_; _⊔_ to _⊔′_; _⊔⁻_ to _⊔⁻′_)
   import Lattice.Product
   open import Name as ᴺ using (Name; _+_)
   open import Name.Lattice as ᴺ̃ using (zero; suc; sucᴹ); open ᴺ̃.↓_; open ᴺ̃._≤_
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
         ν•_ : ∀ {P R} {x : Name Γ} {E : P —[ • ᴺ.suc x 〈 ᴺ.zero 〉 ᶜ - _ ]→ R} → ↓ E → ↓⁻ ν• E
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
         ν•_ : ∀ {P R} {x : Name Γ} {E₀ : P —[ • ᴺ.suc x 〈 ᴺ.zero 〉 ᶜ - _ ]→ R} {E E′ : ↓ E₀} → E ≤ E′ → ν• E ≤⁻ ν• E′
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

   step : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓′ P → ↓ E
   step⁻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓⁻′ P → ↓ E

   step E [ P ] = step⁻ E P
   step E ◻ = ◻

   step⁻ (_ •∙ _) (x •∙ P) = [ x •∙ P ]
   step⁻ (• _ 〈 _ 〉∙ _) (• x 〈 y 〉∙ P) = [ • x 〈 y 〉∙ P ]
   step⁻ (E ➕₁ _) (P ➕ Q) = [ step E P ➕₁ Q ]
   step⁻ {a = _ ᵇ} (E ᵇ│ _) (P │ Q) = [ step E P ᵇ│ Q ]
   step⁻ {a = _ ᶜ} (E ᶜ│ _) (P │ Q) = [ step E P ᶜ│ Q ]
   step⁻ {a = _ ᵇ} (_ │ᵇ E) (P │ Q) = [ P │ᵇ step E Q ]
   step⁻ {a = _ ᶜ} (_ │ᶜ E) (P │ Q) = [ P │ᶜ step E Q ]
   step⁻ (E │• F) (P │ Q) with action (step E P) | action (step F Q)
   ... | [ [ x ] • ᵇ ] | [ • [ .x ] 〈 y 〉 ᶜ ] = [ step E P │• step F Q ]
   ... | _ | _ = ◻
   step⁻ (E │ᵥ F) (P │ Q) with action (step E P) | action (step F Q)
   ... | [ [ x ] • ᵇ ] | [ (• [ .x ]) ᵇ ] = [ step E P │ᵥ step F Q ]
   ... | _ | _ = ◻
   step⁻ (ν• E) (ν P) with action (step E P)
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] = [ ν• (step E P) ]
   ... | _ = ◻
   step⁻ {a = _ • ᵇ} (νᵇ E) (ν P) with action (step E P)
   ... | [ [ ._ ] • ᵇ ] = [ νᵇ (step E P) ]
   ... | _ = ◻
   step⁻ {a = (• _) ᵇ} (νᵇ E) (ν P) with action (step E P)
   ... | [ (• [ ._ ]) ᵇ ] = [ νᵇ (step E P) ]
   ... | _ = ◻
   step⁻ {a = • _ 〈 _ 〉 ᶜ} (νᶜ E) (ν P) with action (step E P)
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] = [ νᶜ (step E P) ]
   ... | _ = ◻
   step⁻ {a = τ ᶜ} (νᶜ E) (ν P) with action (step E P)
   ... | [ τ ᶜ ] = [ νᶜ (step E P) ]
   ... | _ = ◻
   step⁻ (! E) (! P) = [ ! (step E [ P │ [ ! P ] ]) ]

   stepᴹ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) {R R′ : ↓′ P} → R ≤′ R′ → step E R ≤ step E R′
   step⁻ᴹ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) {R R′ : ↓⁻′ P} → R ≤⁻′ R′ → step⁻ E R ≤ step⁻ E R′

   stepᴹ E [ P ] = step⁻ᴹ E P
   stepᴹ E ◻ = ◻

   step⁻ᴹ (_ •∙ _) (x •∙ P) = [ x •∙ P ]
   step⁻ᴹ (• _ 〈 _ 〉∙ _) (• x 〈 y 〉∙ P) = [ • x 〈 y 〉∙ P ]
   step⁻ᴹ (E ➕₁ _) (P ➕ Q) = [ stepᴹ E P ➕₁ Q ]
   step⁻ᴹ {a = _ ᵇ} (E ᵇ│ _) (P │ Q) = [ stepᴹ E P ᵇ│ Q ]
   step⁻ᴹ {a = _ ᶜ} (E ᶜ│ _) (P │ Q) = [ stepᴹ E P ᶜ│ Q ]
   step⁻ᴹ {a = _ ᵇ} (_ │ᵇ E) (P │ Q) = [ P │ᵇ stepᴹ E Q ]
   step⁻ᴹ {a = _ ᶜ} (_ │ᶜ E) (P │ Q) = [ P │ᶜ stepᴹ E Q ]
   step⁻ᴹ (E │• F) {R = R │ S} {R′ │ S′} (P │ Q) with action (step E R) | action (step E R′) | actionᴹ (stepᴹ E P)
   ... | .◻ | _ | ◻ = ◻
   ... | ._ | ._ | [ ◻ • ᵇ ] = ◻
   ... | [ [ x ] • ᵇ ] | [ [ .x ] • ᵇ ] | [ [ .x ] • ᵇ ]
      with action (step F S) | action (step F S′) | actionᴹ (stepᴹ F Q)
   ... | ◻ | _ | _ = ◻
   ... | [ • ◻ 〈 _ 〉 ᶜ ] | [ • _ 〈 _ 〉 ᶜ ] | [ • ◻ 〈 _ 〉 ᶜ ] = ◻
   ... | [ • [ .x ] 〈 _ 〉 ᶜ ] | [ • [ .x ] 〈 _ 〉 ᶜ ] | [ • [ .x ] 〈 _ 〉 ᶜ ] = [ stepᴹ E P │• stepᴹ F Q ]
   step⁻ᴹ (E │ᵥ F) {R = R │ S} {R′ │ S′} (P │ Q) with action (step E R) | action (step E R′) | actionᴹ (stepᴹ E P)
   ... | ◻ | _ | _ = ◻
   ... | [ ◻ • ᵇ ] | [ _ • ᵇ ] | [ ◻ • ᵇ ] = ◻
   ... | [ ([ x ] •) ᵇ ] | [ ([ .x ] •) ᵇ ] | [ ([ .x ] •) ᵇ ]
      with action (step F S) | action (step F S′) | actionᴹ (stepᴹ F Q)
   ... | ◻ | _ | _ = ◻
   ... | [ (• ◻) ᵇ ] | [ (• _) ᵇ ] | [ (• ◻) ᵇ ] = ◻
   ... | [ (• [ .x ]) ᵇ ] | [ (• [ .x ]) ᵇ ] | [ (• [ .x ]) ᵇ ] = [ stepᴹ E P │ᵥ stepᴹ F Q ]
   step⁻ᴹ (ν• E) {R = ν R} {ν R′} (ν P) with action (step E R) | action (step E R′) | actionᴹ (stepᴹ E P)
   ... | ◻ | _ | _ = ◻
   ... | [ • ◻ 〈 _ 〉 ᶜ ] | [ • _ 〈 _ 〉 ᶜ ] | [ • ◻ 〈 _ 〉 ᶜ ] = ◻
   ... | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] | [ • [ ._ ] 〈 _ 〉 ᶜ ] | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] = ◻
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] = [ ν• (stepᴹ E P) ]
   step⁻ᴹ {a = (• x) ᵇ} (νᵇ E) {R = ν R} {ν R′} (ν P) with action (step E R) | action (step E R′) | actionᴹ (stepᴹ E P)
   ... | ◻ | _ | _ = ◻
   ... | [ (• ◻) ᵇ ] | [ (• _) ᵇ ] | [ (• ◻) ᵇ ] = ◻
   ... | [ (• [ ._ ]) ᵇ ] | [ (• [ ._ ]) ᵇ ] | [ (• [ ._ ]) ᵇ ] = [ νᵇ (stepᴹ E P) ]
   step⁻ᴹ {a = x • ᵇ} (νᵇ E) {R = ν R} {ν R′} (ν P) with action (step E R) | action (step E R′) | actionᴹ (stepᴹ E P)
   ... | ◻ | _ | _ = ◻
   ... | [ ◻ • ᵇ ] | [ _ • ᵇ ] | [ ◻ • ᵇ ] = ◻
   ... | [ [ ._ ] • ᵇ ] | [ [ ._ ] • ᵇ ] | [ [ ._ ] • ᵇ ] = [ νᵇ (stepᴹ E P) ]
   step⁻ᴹ {a = • x 〈 y 〉 ᶜ} (νᶜ E) {R = ν R} {ν R′} (ν P)
      with action (step E R) | action (step E R′) | actionᴹ (stepᴹ E P)
   ... | ◻ | _ | _ = ◻
   ... | [ • ◻ 〈 _ 〉 ᶜ ] | [ • _ 〈 _ 〉 ᶜ ] | [ • ◻ 〈 _ 〉 ᶜ ] = ◻
   ... | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] | [ • [ ._ ] 〈 _ 〉 ᶜ ] | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] = ◻
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] = [ νᶜ (stepᴹ E P) ]
   ... | [ • [ ._ ] 〈 _ 〉 ᶜ ] | [ • ◻ 〈 _ 〉 ᶜ ] | [ • () 〈 _ 〉 ᶜ ]
   step⁻ᴹ {a = τ ᶜ} (νᶜ E) {R = ν R} {ν R′} (ν P) with action (step E R) | action (step E R′) | actionᴹ (stepᴹ E P)
   ... | ◻ | _ | _ = ◻
   ... | [ τ ᶜ ] | [ τ ᶜ ] | [ τ ᶜ ] = [ νᶜ (stepᴹ E P) ]
   step⁻ᴹ (! E) (! P) = [ ! stepᴹ E [ P │ [ ! P ] ] ]

   -- unstep reflects ◻. The unstep-◻ variant slices with a ◻ process and a non-◻ action. The recursion case
   -- is simpler than in the paper, because we don't specify here the slice of the source process.
   unstep : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) → ↓′ a → ↓′ P′ → ↓ E
   unstep-◻ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) → ↓⁻′ a → ↓⁻ E
   unstep⁻ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) → ↓′ a → ↓⁻′ P′ → ↓⁻ E

   unstep E a [ R ] = [ unstep⁻ E a R ]
   unstep E [ a ] ◻ = [ unstep-◻ E a ]
   unstep _ ◻ ◻ = ◻

   unstep-◻ (_ •∙ P) (x • ᵇ) = x •∙ ◻
   unstep-◻ (• _ 〈 _ 〉∙ _) (• x 〈 y 〉 ᶜ) = • x 〈 y 〉∙ ◻
   unstep-◻ (E ➕₁ Q) a = [ unstep-◻ E a ] ➕₁ ◻
   unstep-◻ (E ᵇ│ Q) a = [ unstep-◻ E a ] ᵇ│ ◻
   unstep-◻ (E ᶜ│ Q) a = [ unstep-◻ E a ] ᶜ│ ◻
   unstep-◻ (P │ᵇ E) a = ◻ │ᵇ [ unstep-◻ E a ]
   unstep-◻ (P │ᶜ E) a = ◻ │ᶜ [ unstep-◻ E a ]
   unstep-◻ (E │• F) (τ ᶜ) = [ unstep-◻ E ([ _ ] • ᵇ) ] │• [ unstep-◻ F (• [ _ ] 〈 ◻ 〉 ᶜ) ]
   unstep-◻ (E │ᵥ F) (τ ᶜ) = [ unstep-◻ E ([ _ ] • ᵇ) ] │ᵥ [ unstep-◻ F ((• [ _ ]) ᵇ) ]
   unstep-◻ (ν• E) ((• _) ᵇ) = ν• [ unstep-◻ E (• suc [ _ ] 〈 zero 〉 ᶜ) ]
   unstep-◻ {a = x • ᵇ} (νᵇ E) _ = νᵇ [ unstep-◻ E ([ (ᴿ.push *) x ] • ᵇ) ]
   unstep-◻ {a = (• x) ᵇ} (νᵇ E) _ = νᵇ [ unstep-◻ E ((• [ (ᴿ.push *) x ]) ᵇ) ]
   unstep-◻ {a = • x 〈 y 〉 ᶜ} (νᶜ E) _ = νᶜ [ unstep-◻ E (• [ (ᴿ.push *) x ] 〈 [ (ᴿ.push *) y ] 〉 ᶜ) ]
   unstep-◻ {a = τ ᶜ} (νᶜ E) _ = νᶜ [ unstep-◻ E (τ ᶜ) ]
   unstep-◻ (! E) a = ! [ unstep-◻ E a ]

   unstep⁻ (_ •∙ _) ◻ R = ◻ •∙ [ R ]
   unstep⁻ (_ •∙ _) [ x • ᵇ ] R = x •∙ [ R ]
   unstep⁻ (• _ 〈 _ 〉∙ ._) ◻ R = • ◻ 〈 ◻ 〉∙ [ R ]
   unstep⁻ (• _ 〈 _ 〉∙ ._) [ • x 〈 y 〉 ᶜ ] R = • x 〈 y 〉∙ [ R ]
   unstep⁻ (E ➕₁ _) a R = [ unstep⁻ E a R ] ➕₁ ◻
   unstep⁻ {a = _ ᵇ} (E ᵇ│ Q) a (R │ S) = unstep E a R ᵇ│ π₂ ((ᴿ.push †) Q S)
   unstep⁻ {a = _ ᶜ} (E ᶜ│ Q) a (R │ S) = unstep E a R ᶜ│ S
   unstep⁻ {a = _ ᵇ} (P │ᵇ E) a (R │ S) = π₂ ((ᴿ.push †) P R) │ᵇ unstep E a S
   unstep⁻ {a = _ ᶜ} (P │ᶜ E) a (R │ S) = R │ᶜ unstep E a S
   unstep⁻ (_│•_ {R = P′} {x = x} {y} E F) _ (R │ S) with (ᴿ.pop y †) P′ R
   ... | pop-y , R′ = unstep E [ [ _ ] • ᵇ ] R′ │• unstep F [ • [ _ ] 〈 pop-y ᴺ.zero 〉 ᶜ ] S
   unstep⁻ (E │ᵥ F) _ (ν ◻) = [ unstep-◻ E ([ _ ] • ᵇ) ] │ᵥ [ unstep-◻ F ((• [ _ ]) ᵇ) ]
   unstep⁻ (E │ᵥ F) _ (ν [ R │ S ]) = unstep E [ [ _ ] • ᵇ ] R │ᵥ unstep F [ (• [ _ ]) ᵇ ] S
   unstep⁻ (ν• E) _ R = ν• [ unstep⁻ E [ • suc [ _ ] 〈 zero 〉 ᶜ ] R ]
   unstep⁻ {a = x • ᵇ} (νᵇ_ {R = P′} E) _ (ν R) = νᵇ unstep E [ [ (ᴿ.push *) x ] • ᵇ ] (π₂ ((ᴿ.swap †) P′ R))
   unstep⁻ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) _ (ν R) = νᵇ unstep E [ (• [ (ᴿ.push *) x ]) ᵇ ] (π₂ ((ᴿ.swap †) P′ R))
   unstep⁻ {a = • x 〈 y 〉 ᶜ} (νᶜ_ {R = P′} E) _ (ν R) = νᶜ unstep E [ (• [ (ᴿ.push *) x ] 〈 [ (ᴿ.push *) y ] 〉) ᶜ ] R
   unstep⁻ {a = τ ᶜ} (νᶜ_ {R = P′} E) _ (ν R) = νᶜ unstep E [ τ ᶜ ] R
   unstep⁻ (! E) a R = ! [ unstep⁻ E a R ]

   unstep-◻ᴹ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) {a′ a″ : ↓⁻′ a} →
               a′ ≤⁻′ a″ → unstep-◻ E a′ ≤⁻ unstep-◻ E a″
   unstep-◻ᴹ (_ •∙ _) (x • ᵇ) = x •∙ ◻
   unstep-◻ᴹ (• _ 〈 _ 〉∙ _) (• x 〈 y 〉 ᶜ) = • x 〈 y 〉∙ ◻
   unstep-◻ᴹ (E ➕₁ _) a = [ unstep-◻ᴹ E a ] ➕₁ ◻
   unstep-◻ᴹ (E ᵇ│ _) a = [ unstep-◻ᴹ E a ] ᵇ│ ◻
   unstep-◻ᴹ (E ᶜ│ _) a = [ unstep-◻ᴹ E a ] ᶜ│ ◻
   unstep-◻ᴹ (_ │ᵇ E) a = ◻ │ᵇ [ unstep-◻ᴹ E a ]
   unstep-◻ᴹ (_ │ᶜ E) a = ◻ │ᶜ [ unstep-◻ᴹ E a ]
   unstep-◻ᴹ (E │• F) (τ ᶜ) = [ unstep-◻ᴹ E ([ _ ] • ᵇ) ] │• [ unstep-◻ᴹ F (• [ _ ] 〈 ◻ 〉 ᶜ) ]
   unstep-◻ᴹ (ν• E) ((• _) ᵇ) = ν• [ unstep-◻ᴹ E (• sucᴹ [ _ ] 〈 ᴹ zero 〉 ᶜ) ]
   unstep-◻ᴹ (E │ᵥ F) (τ ᶜ) = [ unstep-◻ᴹ E ([ _ ] • ᵇ) ] │ᵥ [ unstep-◻ᴹ F ((• [ _ ]) ᵇ) ]
   unstep-◻ᴹ {a = x • ᵇ} (νᵇ E) (_ • ᵇ) = νᵇ [ unstep-◻ᴹ E ([ (ᴿ.push *) x ] • ᵇ) ]
   unstep-◻ᴹ {a = (• x) ᵇ} (νᵇ E) ((• _) ᵇ) = νᵇ [ unstep-◻ᴹ E ((• [ (ᴿ.push *) x ]) ᵇ) ]
   unstep-◻ᴹ {a = • x 〈 y 〉 ᶜ} (νᶜ E) (• _ 〈 _ 〉 ᶜ) = νᶜ [ unstep-◻ᴹ E (• [ (ᴿ.push *) x ] 〈 [ (ᴿ.push *) y ] 〉 ᶜ) ]
   unstep-◻ᴹ {a = τ ᶜ} (νᶜ E) (τ ᶜ) = νᶜ [ unstep-◻ᴹ E (τ ᶜ) ]
   unstep-◻ᴹ (! E) a = ! [ unstep-◻ᴹ E a ]

   -- Auxiliary lemmas needed for monotonicity.
   unstep-◻-min : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) (a′ : ↓⁻′ a) (R : ↓′ P′) →
                  [ unstep-◻ E a′ ] ≤ unstep E [ a′ ] R
   unstep-◻-min⁻ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) (a′ : ↓⁻′ a) (R : ↓⁻′ P′) →
                   unstep-◻ E a′ ≤⁻ unstep⁻ E [ a′ ] R

   unstep-◻-min E a ◻ = [ ⁻ᴹ (unstep-◻ E a) ]
   unstep-◻-min E a [ R ] = [ unstep-◻-min⁻ E a R ]

   unstep-◻-min⁻ (_ •∙ _) (x • ᵇ) _ = ᴹ x •∙ ◻
   unstep-◻-min⁻ (• _ 〈 _ 〉∙ _) (• x 〈 y 〉 ᶜ) _ = • ᴹ x 〈 ᴹ y 〉∙ ◻
   unstep-◻-min⁻ (E ➕₁ _) a P = [ unstep-◻-min⁻ E a P ] ➕₁ ◻
   unstep-◻-min⁻ (E ᵇ│ _) a (P │ Q) = unstep-◻-min E a P ᵇ│ ◻
   unstep-◻-min⁻ (E ᶜ│ _) a (P │ Q) = unstep-◻-min E a P ᶜ│ ◻
   unstep-◻-min⁻ (_ │ᵇ E) a (P │ Q) = ◻ │ᵇ unstep-◻-min E a Q
   unstep-◻-min⁻ (_ │ᶜ E) a (P │ Q) = ◻ │ᶜ unstep-◻-min E a Q
   unstep-◻-min⁻ (_│•_ {R = P′} {y = y} E F) (τ ᶜ) (P │ Q) with (ᴿ.pop y †) P′ P
   ... | pop-y , R =
      unstep-◻-min E ([ _ ] • ᵇ) R │•
      ≤-trans [ unstep-◻ᴹ F (• [ _ ] 〈 ◻ 〉 ᶜ) ] (unstep-◻-min F (• [ _ ] 〈 pop-y ᴺ.zero 〉 ᶜ) Q)
   unstep-◻-min⁻ (ν• E) ((• _) ᵇ) P = ν• [ unstep-◻-min⁻ E (• suc [ _ ] 〈 zero 〉 ᶜ) P ]
   unstep-◻-min⁻ (E │ᵥ F) (τ ᶜ) (ν ◻) = [ ⁻ᴹ (unstep-◻ E ([ _ ] • ᵇ)) ] │ᵥ [ ⁻ᴹ (unstep-◻ F ((• [ _ ]) ᵇ)) ]
   unstep-◻-min⁻ (E │ᵥ F) (τ ᶜ) (ν [ P │ Q ]) = unstep-◻-min E ([ _ ] • ᵇ) P │ᵥ unstep-◻-min F ((• [ _ ]) ᵇ) Q
   unstep-◻-min⁻ {a = x • ᵇ} (νᵇ_ {R = P′} E) _ (ν P) = νᵇ unstep-◻-min E ([ (ᴿ.push *) x ] • ᵇ) (π₂ ((ᴿ.swap †) P′ P))
   unstep-◻-min⁻ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) _ (ν P) = νᵇ unstep-◻-min E ((• [ (ᴿ.push *) x ]) ᵇ) (π₂ ((ᴿ.swap †) P′ P))
   unstep-◻-min⁻ {a = • x 〈 y 〉 ᶜ} (νᶜ_ {R = P′} E) _ (ν P) = νᶜ unstep-◻-min E (• [ (ᴿ.push *) x ] 〈 [ (ᴿ.push *) y ] 〉 ᶜ) P
   unstep-◻-min⁻ {a = τ ᶜ} (νᶜ_ {R = P′} E) _ (ν P) = νᶜ unstep-◻-min E (τ ᶜ) P
   unstep-◻-min⁻ (! E) a R = ! [ unstep-◻-min⁻ E a R ]

   unstepᴹ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) {a′ a″ : ↓′ a} {R R′ : ↓′ P′} →
                a′ ≤′ a″ → R ≤′ R′ → unstep E a′ R ≤ unstep E a″ R′
   unstep⁻ᴹ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) {a′ a″ : ↓′ a} {R R′ : ↓⁻′ P′} →
              a′ ≤′ a″ → R ≤⁻′ R′ → unstep⁻ E a′ R ≤⁻ unstep⁻ E a″ R′

   unstepᴹ E a [ R ] = [ unstep⁻ᴹ E a R ]
   unstepᴹ E {[ _ ]} {[ _ ]} {◻} {◻} [ a ] ◻ = [ unstep-◻ᴹ E a ]
   unstepᴹ E {[ _ ]} {[ _ ]} {◻} {[ R ]} [ a ] ◻ = [ ≤⁻-trans (unstep-◻ᴹ E a) (unstep-◻-min⁻ E _ R) ]
   unstepᴹ E {◻} ◻ ◻ = ◻

   unstep⁻ᴹ (_ •∙ _) {◻} {◻} ◻ R = ◻ •∙ [ R ]
   unstep⁻ᴹ (_ •∙ _) {◻} {[ _ • ᵇ ]} ◻ R = ◻ •∙ [ R ]
   unstep⁻ᴹ (_ •∙ _) {[ _ • ᵇ ]} {[ _ • ᵇ ]} [ u • ᵇ ] R = u •∙ [ R ]
   unstep⁻ᴹ (• _ 〈 _ 〉∙ _) {◻} {◻} ◻ R = • ◻ 〈 ◻ 〉∙ [ R ]
   unstep⁻ᴹ (• _ 〈 _ 〉∙ _) {◻} {[ • _ 〈 _ 〉 ᶜ ]} ◻ R = • ◻ 〈 ◻ 〉∙ [ R ]
   unstep⁻ᴹ (• _ 〈 _ 〉∙ _) {[ • _ 〈 _ 〉 ᶜ ]} {[ • _ 〈 _ 〉 ᶜ ]} [ • x 〈 y 〉 ᶜ ] R = • x 〈 y 〉∙ [ R ]
   unstep⁻ᴹ (E ➕₁ Q) a R = [ unstep⁻ᴹ E a R ] ➕₁ ◻
   unstep⁻ᴹ (E ᵇ│ Q) a′ (R │ S) = unstepᴹ E a′ R ᵇ│ π₂ ((ᴿ.push †ᴹ) Q S)
   unstep⁻ᴹ (E ᶜ│ Q) a′ (R │ S) = unstepᴹ E a′ R ᶜ│ S
   unstep⁻ᴹ (P │ᵇ E) a′ (R │ S) = π₂ ((ᴿ.push †ᴹ) P R) │ᵇ unstepᴹ E a′ S
   unstep⁻ᴹ (P │ᶜ E) a′ (R │ S) = R │ᶜ unstepᴹ E a′ S
   unstep⁻ᴹ (_│•_ {R = P″} {y = y} E F) {R = P │ _} {P′ │ _} a (R │ S) with (ᴿ.pop y †ᴹ) P″ R
   ... | pop-y , R′ = unstepᴹ E [ [ _ ] • ᵇ ] R′ │• unstepᴹ F [ • [ _ ] 〈 pop-y ᴺ.zero 〉 ᶜ ] S
   unstep⁻ᴹ (ν• E) _ R = ν• [ unstep⁻ᴹ E [ • sucᴹ [ _ ] 〈 ᴹ zero 〉 ᶜ ] R ]
   unstep⁻ᴹ (E │ᵥ F) {R = ν ◻} {ν ◻} _ (ν ◻) = [ ⁻ᴹ (unstep-◻ E ([ _ ] • ᵇ)) ] │ᵥ [ ⁻ᴹ (unstep-◻ F ((• _) ᵇ)) ]
   unstep⁻ᴹ (E │ᵥ F) {R = ν ◻} {ν [ P │ Q ]} _ (ν ◻) = unstep-◻-min E ([ _ ] • ᵇ) P │ᵥ unstep-◻-min F ((• _) ᵇ) Q
   unstep⁻ᴹ (E │ᵥ F) {R = ν [ _ │ _ ]} {ν [ _ │ _ ]} _ (ν [ R │ S ]) =
      unstepᴹ E [ [ _ ] • ᵇ ] R │ᵥ unstepᴹ F [ (• [ _ ]) ᵇ ] S
   unstep⁻ᴹ {a = x • ᵇ} (νᵇ_ {R = P′} E) _ (ν R) = νᵇ unstepᴹ E [ [ (ᴿ.push *) x ] • ᵇ ] (π₂ ((ᴿ.swap †ᴹ) P′ R))
   unstep⁻ᴹ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) _ (ν R) = νᵇ unstepᴹ E [ (• [ (ᴿ.push *) x ]) ᵇ ] (π₂ ((ᴿ.swap †ᴹ) P′ R))
   unstep⁻ᴹ {a = • x 〈 y 〉 ᶜ} (νᶜ_ {R = P′} E) _ (ν R) = νᶜ unstepᴹ E [ • [ (ᴿ.push *) x ] 〈 [ (ᴿ.push *) y ] 〉 ᶜ ] R
   unstep⁻ᴹ {a = τ ᶜ} (νᶜ_ {R = P′} E) _ (ν R) = νᶜ unstepᴹ E [ τ ᶜ ] R
   unstep⁻ᴹ (! E) a R = ! [ unstep⁻ᴹ E a R ]

   fwd : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓′ P → ↓′ (a , R)
   fwd E = out ∘ᶠ step E

   fwd⁻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓⁻′ P → ↓′ (a , R)
   fwd⁻ E = out ∘ᶠ step⁻ E

   fwdᴹ : ∀ {Γ P₀} {a : Action Γ} {R} (E : P₀ —[ a - _ ]→ R) {P P′ : ↓′ P₀} → P ≤′ P′ → fwd E P ≤′ fwd E P′
   fwdᴹ E = outᴹ ∘ᶠ stepᴹ E

   fwd⁻ᴹ : ∀ {Γ P₀} {a : Action Γ} {R} (E : P₀ —[ a - _ ]→ R) {P P′ : ↓⁻′ P₀} → P ≤⁻′ P′ → fwd⁻ E P ≤′ fwd⁻ E P′
   fwd⁻ᴹ E = outᴹ ∘ᶠ step⁻ᴹ E

   bwd : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓′ (a , R) → ↓′ P
   bwd E (a , R) = source (unstep E a R)

   bwdᴹ : ∀ {Γ P} {a₀ : Action Γ} {R₀} (E : P —[ a₀ - _ ]→ R₀) {a a′ : ↓′ a₀} {R R′ : ↓′ R₀} →
          (a , R) ≤′ (a′ , R′) → bwd E (a , R) ≤′ bwd E (a′ , R′)
   bwdᴹ E (a , R) = sourceᴹ (unstepᴹ E a R)

   bwd-◻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓⁻′ a → ↓⁻′ P
   bwd-◻ E a = source⁻ (unstep-◻ E a)

   bwd⁻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓′ a → ↓⁻′ R → ↓⁻′ P
   bwd⁻ E a R = source⁻ (unstep⁻ E a R)

   bwd⁻ᴹ : ∀ {Γ P} {a₀ : Action Γ} {R₀} (E : P —[ a₀ - _ ]→ R₀) {a a′ : ↓′ a₀} {R R′ : ↓⁻′ R₀} →
           a ≤′ a′ → R ≤⁻′ R′ → bwd⁻ E a R ≤⁻′ bwd⁻ E a′ R′
   bwd⁻ᴹ E a R = source⁻ᴹ (unstep⁻ᴹ E a R)
