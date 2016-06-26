module Transition.Seq.Lattice where

   open import ConcurrentSlicingCommon
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action; Actionᵇ; module Actionᵇ; Actionᶜ; module Actionᶜ); open ᴬ.Action
   open import Action.Seq as ᴬ⋆ using (Action⋆; inc⋆); open ᴬ⋆.Action⋆
   open import Lattice using (Lattices; Prefixes);
      open Lattice.Prefixes ⦃...⦄
         using (ᴹ; _⊔ᴹ_; _⊔ʳ_; ≤-trans)
         renaming (↓_ to ↓′_; ↓⁻_ to ↓⁻′_; _≤_ to _≤′_; _≤⁻_ to _≤⁻′_; _⊔_ to _⊔′_; _⊓_ to _⊓′_; ≤ᴸ⇒≤ to ≤′ᴸ⇒≤′; ≤⇒≤ᴸ to ≤′⇒≤′ᴸ)
   open import Name using (+-assoc)
   open import Proc using (Proc; Proc↱; Proc↲)
   import Proc.Lattice as ᴾ̃; open ᴾ̃.↓_; open ᴾ̃.↓⁻_
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_
   open import Transition.Lattice as ᵀ̃ using (tgt)
   open import Transition.Seq as ᵀ⋆ using (_—[_]→⋆_); open ᵀ⋆._—[_]→⋆_

{-
   -- Not sure it makes sense to allow a trace slice to have ◻ as a constitutent transition.
   mutual
      infixr 5 _ᵇ∷_ _ᶜ∷_
      -- An empty trace slice really is a proxy for a process slice, so make the index explicit.
      data ↓⁻_ {Γ} : ∀ {P} {a⋆ : Action⋆ Γ} {R} → P —[ a⋆ ]→⋆ R → Set where
         []﹙_﹚ : ∀ {P} → ↓′ P → ↓⁻ ([] {P = P})
         _ᵇ∷_ : ∀ {P a R a⋆ S} {E : P —[ a ᵇ - _ ]→ R} {E⋆ : R —[ a⋆ ]→⋆ S} → ↓′ E → ↓ E⋆ → ↓⁻ (E ᵇ∷ E⋆)
         _ᶜ∷_ : ∀ {P a R a⋆ S} {E : P —[ a ᶜ - _ ]→ R} {E⋆ : R —[ a⋆ ]→⋆ S} → ↓′ E → ↓ E⋆ → ↓⁻ (E ᶜ∷ E⋆)

      data ↓_ {Γ} : ∀ {P} {a⋆ : Action⋆ Γ} {R} → P —[ a⋆ ]→⋆ R → Set where
         ◻ : ∀ {P} {a⋆ : Action⋆ Γ} {R} {E⋆ : P —[ a⋆ ]→⋆ R} → ↓ E⋆
         [_] : ∀ {P} {a⋆ : Action⋆ Γ} {R} {E⋆ : P —[ a⋆ ]→⋆ R} → ↓⁻ E⋆ → ↓ E⋆

   infix 4 _≤⁻_ _≤_
   mutual
      data _≤⁻_ {Γ} : ∀ {P} {a⋆ : Action⋆ Γ} {R} {E⋆ : P —[ a⋆ ]→⋆ R} → ↓⁻ E⋆ → ↓⁻ E⋆ → Set where
         []﹙_﹚ : ∀ {P₀} {P P′ : ↓′ P₀} → P ≤′ P′  → []﹙ P ﹚ ≤⁻ []﹙ P′ ﹚
         _ᵇ∷_ : ∀ {P a R a⋆ S} {E₀ : P —[ a ᵇ - _ ]→ R} {E₀⋆ : R —[ a⋆ ]→⋆ S} {E E′ : ↓′ E₀} {E⋆ E′⋆ : ↓ E₀⋆} →
                E ≤′ E′ → E⋆ ≤ E′⋆ → E ᵇ∷ E⋆ ≤⁻ E′ ᵇ∷ E′⋆
         _ᶜ∷_ : ∀ {P a R a⋆ S} {E₀ : P —[ a ᶜ - _ ]→ R} {E₀⋆ : R —[ a⋆ ]→⋆ S} {E E′ : ↓′ E₀} {E⋆ E′⋆ : ↓ E₀⋆} →
                E ≤′ E′ → E⋆ ≤ E′⋆ → E ᶜ∷ E⋆ ≤⁻ E′ ᶜ∷ E′⋆

      data _≤_ {Γ} : ∀ {P} {a⋆ : Action⋆ Γ} {R} {E : P —[ a⋆ ]→⋆ R} → ↓ E → ↓ E → Set where
         ◻ : ∀ {P} {a⋆ : Action⋆ Γ} {R} {E₀⋆ : P —[ a⋆ ]→⋆ R} {E⋆ : ↓ E₀⋆} → ◻ ≤ E⋆
         [_] : ∀ {P} {a⋆ : Action⋆ Γ} {R} {E₀⋆ : P —[ a⋆ ]→⋆ R} {E⋆ E′⋆ : ↓⁻ E₀⋆} → E⋆ ≤⁻ E′⋆ → [ E⋆ ] ≤ [ E′⋆ ]


   _⊔⁻_ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E₀⋆ : P —[ a⋆ ]→⋆ R} (E⋆ E′⋆ : ↓⁻ E₀⋆) → ↓⁻ E₀⋆
   _⊔_ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E₀⋆ : P —[ a⋆ ]→⋆ R} (E E′ : ↓ E₀⋆) → ↓ E₀⋆

   []﹙ P ﹚ ⊔⁻ []﹙ P′ ﹚ = []﹙ P ⊔′ P′ ﹚
   (E ᵇ∷ E⋆) ⊔⁻ (E′ ᵇ∷ E′⋆) = E ⊔′ E′ ᵇ∷ E⋆ ⊔ E′⋆
   (E ᶜ∷ E⋆) ⊔⁻ (E′ ᶜ∷ E′⋆) = E ⊔′ E′ ᶜ∷ E⋆ ⊔ E′⋆

   ◻ ⊔ ◻ = ◻
   ◻ ⊔ [ E⋆ ] = [ E⋆ ]
   [ E⋆ ] ⊔ ◻ = [ E⋆ ]
   [ E⋆ ] ⊔ [ E′⋆ ] = [ E⋆ ⊔⁻ E′⋆ ]

   _⊓⁻_ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E₀⋆ : P —[ a⋆ ]→⋆ R} (E⋆ E′⋆ : ↓⁻ E₀⋆) → ↓⁻ E₀⋆
   _⊓_ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E₀⋆ : P —[ a⋆ ]→⋆ R} (E E′ : ↓ E₀⋆) → ↓ E₀⋆

   []﹙ P ﹚ ⊓⁻ []﹙ P′ ﹚ = []﹙ P ⊓′ P′ ﹚
   (E ᵇ∷ E⋆) ⊓⁻ (E′ ᵇ∷ E′⋆) = E ⊓′ E′ ᵇ∷ E⋆ ⊓ E′⋆
   (E ᶜ∷ E⋆) ⊓⁻ (E′ ᶜ∷ E′⋆) = E ⊓′ E′ ᶜ∷ E⋆ ⊓ E′⋆

   ◻ ⊓ ◻ = ◻
   ◻ ⊓ [ E⋆ ] = ◻
   [ E⋆ ] ⊓ ◻ = ◻
   [ E⋆ ] ⊓ [ E′⋆ ] = [ E⋆ ⊓⁻ E′⋆ ]

   ⊔⁻-comm : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E⋆ : P —[ a⋆ ]→⋆ R} → Commutative _≡_ (_⊔⁻_ {E₀⋆ = E⋆})
   ⊔-comm : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E : P —[ a⋆ ]→⋆ R} → Commutative _≡_ (_⊔_ {E₀⋆ = E})

   ⊔⁻-comm []﹙ P ﹚ []﹙ P′ ﹚ = cong []﹙_﹚ (ᴾ̃.⊔-comm P P′)
   ⊔⁻-comm (E ᵇ∷ E⋆) (E′ ᵇ∷ E′⋆) = cong₂ _ᵇ∷_ (ᵀ̃.⊔-comm E E′) (⊔-comm E⋆ E′⋆)
   ⊔⁻-comm (E ᶜ∷ E⋆) (E′ ᶜ∷ E′⋆) = cong₂ _ᶜ∷_ (ᵀ̃.⊔-comm E E′) (⊔-comm E⋆ E′⋆)

   ⊔-comm ◻ ◻ = refl
   ⊔-comm ◻ [ _ ] = refl
   ⊔-comm [ _ ] ◻ = refl
   ⊔-comm [ E⋆ ] [ E′⋆ ] = cong [_] (⊔⁻-comm E⋆ E′⋆)

   ⊓⁻-comm : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E⋆ : P —[ a⋆ ]→⋆ R} → Commutative _≡_ (_⊓⁻_ {E₀⋆ = E⋆})
   ⊓-comm : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E : P —[ a⋆ ]→⋆ R} → Commutative _≡_ (_⊓_ {E₀⋆ = E})

   ⊓⁻-comm []﹙ P ﹚ []﹙ P′ ﹚ = cong []﹙_﹚ (ᴾ̃.⊓-comm P P′)
   ⊓⁻-comm (E ᵇ∷ E⋆) (E′ ᵇ∷ E′⋆) = cong₂ _ᵇ∷_ (ᵀ̃.⊓-comm E E′) (⊓-comm E⋆ E′⋆)
   ⊓⁻-comm (E ᶜ∷ E⋆) (E′ ᶜ∷ E′⋆) = cong₂ _ᶜ∷_ (ᵀ̃.⊓-comm E E′) (⊓-comm E⋆ E′⋆)

   ⊓-comm ◻ ◻ = refl
   ⊓-comm ◻ [ _ ] = refl
   ⊓-comm [ _ ] ◻ = refl
   ⊓-comm [ E⋆ ] [ E′⋆ ] = cong [_] (⊓⁻-comm E⋆ E′⋆)

   ⊔⁻-assoc : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E⋆ : P —[ a⋆ ]→⋆ R} → Associative _≡_ (_⊔⁻_ {E₀⋆ = E⋆})
   ⊔-assoc : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E : P —[ a⋆ ]→⋆ R} → Associative _≡_ (_⊔_ {E₀⋆ = E})

   ⊔⁻-assoc []﹙ P ﹚ []﹙ P′ ﹚ []﹙ P″ ﹚ = cong []﹙_﹚ (ᴾ̃.⊔-assoc P P′ P″)
   ⊔⁻-assoc (E ᵇ∷ E⋆) (E′ ᵇ∷ E′⋆) (E″ ᵇ∷ E″⋆) = cong₂ _ᵇ∷_ (ᵀ̃.⊔-assoc E E′ E″) (⊔-assoc E⋆ E′⋆ E″⋆)
   ⊔⁻-assoc (E ᶜ∷ E⋆) (E′ ᶜ∷ E′⋆) (E″ ᶜ∷ E″⋆) = cong₂ _ᶜ∷_ (ᵀ̃.⊔-assoc E E′ E″) (⊔-assoc E⋆ E′⋆ E″⋆)

   ⊔-assoc ◻ ◻ ◻ = refl
   ⊔-assoc ◻ ◻ [ _ ] = refl
   ⊔-assoc ◻ [ _ ] ◻ = refl
   ⊔-assoc ◻ [ _ ] [ _ ] = refl
   ⊔-assoc [ _ ] ◻ ◻ = refl
   ⊔-assoc [ _ ] ◻ [ _ ] = refl
   ⊔-assoc [ _ ] [ _ ] ◻ = refl
   ⊔-assoc [ E⋆ ] [ E′⋆ ] [ E″⋆ ] = cong [_] (⊔⁻-assoc E⋆ E′⋆ E″⋆)

   ⊓⁻-assoc : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E⋆ : P —[ a⋆ ]→⋆ R} → Associative _≡_ (_⊓⁻_ {E₀⋆ = E⋆})
   ⊓-assoc : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E : P —[ a⋆ ]→⋆ R} → Associative _≡_ (_⊓_ {E₀⋆ = E})

   ⊓⁻-assoc []﹙ P ﹚ []﹙ P′ ﹚ []﹙ P″ ﹚ = cong []﹙_﹚ (ᴾ̃.⊓-assoc P P′ P″)
   ⊓⁻-assoc (E ᵇ∷ E⋆) (E′ ᵇ∷ E′⋆) (E″ ᵇ∷ E″⋆) = cong₂ _ᵇ∷_ (ᵀ̃.⊓-assoc E E′ E″) (⊓-assoc E⋆ E′⋆ E″⋆)
   ⊓⁻-assoc (E ᶜ∷ E⋆) (E′ ᶜ∷ E′⋆) (E″ ᶜ∷ E″⋆) = cong₂ _ᶜ∷_ (ᵀ̃.⊓-assoc E E′ E″) (⊓-assoc E⋆ E′⋆ E″⋆)

   ⊓-assoc ◻ ◻ ◻ = refl
   ⊓-assoc ◻ ◻ [ _ ] = refl
   ⊓-assoc ◻ [ _ ] ◻ = refl
   ⊓-assoc ◻ [ _ ] [ _ ] = refl
   ⊓-assoc [ _ ] ◻ ◻ = refl
   ⊓-assoc [ _ ] ◻ [ _ ] = refl
   ⊓-assoc [ _ ] [ _ ] ◻ = refl
   ⊓-assoc [ E⋆ ] [ E′⋆ ] [ E″⋆ ] = cong [_] (⊓⁻-assoc E⋆ E′⋆ E″⋆)

   -- Idempotence follows from absorption but convenient to use it to prove absorption.
   ⊓⁻-idem : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E⋆ : P —[ a⋆ ]→⋆ R} → Idempotent _≡_ (_⊓⁻_ {E₀⋆ = E⋆})
   ⊓-idem : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E⋆ : P —[ a⋆ ]→⋆ R} → Idempotent _≡_ (_⊓_ {E₀⋆ = E⋆})

   ⊓⁻-idem []﹙ P ﹚ = cong []﹙_﹚ (ᴾ̃.⊓-idem P)
   ⊓⁻-idem (E ᵇ∷ E⋆) = cong₂ _ᵇ∷_ (ᵀ̃.⊓-idem E) (⊓-idem E⋆)
   ⊓⁻-idem (E ᶜ∷ E⋆) = cong₂ _ᶜ∷_ (ᵀ̃.⊓-idem E) (⊓-idem E⋆)

   ⊓-idem ◻ = refl
   ⊓-idem [ E⋆ ] = cong [_] (⊓⁻-idem E⋆)

   ⊔⁻-absorbs-⊓⁻ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E⋆ : P —[ a⋆ ]→⋆ R} → _Absorbs_ _≡_ (_⊔⁻_ {E₀⋆ = E⋆}) _⊓⁻_
   ⊔-absorbs-⊓ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E : P —[ a⋆ ]→⋆ R} → _Absorbs_ _≡_ (_⊔_ {E₀⋆ = E}) _⊓_

   ⊔⁻-absorbs-⊓⁻ []﹙ P ﹚ []﹙ P′ ﹚ = cong []﹙_﹚ (ᴾ̃.⊔-absorbs-⊓ P P′)
   ⊔⁻-absorbs-⊓⁻ (E ᵇ∷ E⋆) (E′ ᵇ∷ E′⋆) = cong₂ _ᵇ∷_ (ᵀ̃.⊔-absorbs-⊓ E E′) (⊔-absorbs-⊓ E⋆ E′⋆)
   ⊔⁻-absorbs-⊓⁻ (E ᶜ∷ E⋆) (E′ ᶜ∷ E′⋆) = cong₂ _ᶜ∷_ (ᵀ̃.⊔-absorbs-⊓ E E′) (⊔-absorbs-⊓ E⋆ E′⋆)

   ⊔-absorbs-⊓ ◻ ◻ = refl
   ⊔-absorbs-⊓ ◻ [ _ ] = refl
   ⊔-absorbs-⊓ [ _ ] ◻ = refl
   ⊔-absorbs-⊓ [ E⋆ ] [ E′⋆ ] = cong [_] (⊔⁻-absorbs-⊓⁻ E⋆ E′⋆)

   ⊓⁻-absorbs-⊔⁻ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E⋆ : P —[ a⋆ ]→⋆ R} → _Absorbs_ _≡_ (_⊓⁻_ {E₀⋆ = E⋆}) _⊔⁻_
   ⊓-absorbs-⊔ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E : P —[ a⋆ ]→⋆ R} → _Absorbs_ _≡_ (_⊓_ {E₀⋆ = E}) _⊔_

   ⊓⁻-absorbs-⊔⁻ []﹙ P ﹚ []﹙ P′ ﹚ = cong []﹙_﹚ (ᴾ̃.⊓-absorbs-⊔ P P′)
   ⊓⁻-absorbs-⊔⁻ (E ᵇ∷ E⋆) (E′ ᵇ∷ E′⋆) = cong₂ _ᵇ∷_ (ᵀ̃.⊓-absorbs-⊔ E E′) (⊓-absorbs-⊔ E⋆ E′⋆)
   ⊓⁻-absorbs-⊔⁻ (E ᶜ∷ E⋆) (E′ ᶜ∷ E′⋆) = cong₂ _ᶜ∷_ (ᵀ̃.⊓-absorbs-⊔ E E′) (⊓-absorbs-⊔ E⋆ E′⋆)

   ⊓-absorbs-⊔ ◻ ◻ = refl
   ⊓-absorbs-⊔ ◻ [ _ ] = refl
   ⊓-absorbs-⊔ [ E⋆ ] ◻ = cong [_] (⊓⁻-idem E⋆)
   ⊓-absorbs-⊔ [ E⋆ ] [ E′⋆ ] = cong [_] (⊓⁻-absorbs-⊔⁻ E⋆ E′⋆)

   isLattice⁻ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E⋆ : P —[ a⋆ ]→⋆ R} → IsLattice _≡_ (_⊔⁻_ {E₀⋆ = E⋆}) _⊓⁻_
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

   isLattice : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E⋆ : P —[ a⋆ ]→⋆ R} → IsLattice _≡_ (_⊔_ {E₀⋆ = E⋆}) _⊓_
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
      lattices : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} → Lattices (P —[ a⋆ ]→⋆ R)
      lattices = record {
            ↓_ = ↓_; ↓⁻_ = ↓⁻_; _⊔⁻_ = _⊔⁻_; _⊔_ = _⊔_; _⊓⁻_ = _⊓⁻_; _⊓_ = _⊓_;
            isLattice⁻ = isLattice⁻; isLattice = isLattice
         }

   open Lattice.Lattices using (_≤⁻ᴸ_; _≤ᴸ_)

   ≤⁻ᴸ⇒≤⁻ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E⋆ : P —[ a⋆ ]→⋆ R} → _≤⁻ᴸ_ lattices {a = E⋆} ⇒ _≤⁻_
   ≤ᴸ⇒≤ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E⋆ : P —[ a⋆ ]→⋆ R} → _≤ᴸ_ lattices {a = E⋆} ⇒ _≤_

   ≤⁻ᴸ⇒≤⁻ {i = []﹙ P ﹚} {[]﹙ P′ ﹚} _ with P ⊓′ P′ | inspect (_⊓′_ P) P′
   ≤⁻ᴸ⇒≤⁻ {i = []﹙ P ﹚} {[]﹙ P′ ﹚} refl | .P | [ P≤⁻ᴸP′ ] = []﹙ ≤′ᴸ⇒≤′ (sym P≤⁻ᴸP′) ﹚
   ≤⁻ᴸ⇒≤⁻ {i = E ᵇ∷ E⋆} {E′ ᵇ∷ E′⋆} _ with E ⊓′ E′ | E⋆ ⊓ E′⋆ | inspect (_⊓′_ E) E′ | inspect (_⊓_ E⋆) E′⋆
   ≤⁻ᴸ⇒≤⁻ {i = E ᵇ∷ E⋆} {E′ ᵇ∷ E′⋆} refl | .E | .E⋆ | [ E≤⁻ᴸE′ ] | [ E⋆≤⁻ᴸE′⋆ ] = ≤′ᴸ⇒≤′ (sym E≤⁻ᴸE′) ᵇ∷ ≤ᴸ⇒≤ (sym E⋆≤⁻ᴸE′⋆)
   ≤⁻ᴸ⇒≤⁻ {i = E ᶜ∷ E⋆} {E′ ᶜ∷ E′⋆} _ with E ⊓′ E′ | E⋆ ⊓ E′⋆ | inspect (_⊓′_ E) E′ | inspect (_⊓_ E⋆) E′⋆
   ≤⁻ᴸ⇒≤⁻ {i = E ᶜ∷ E⋆} {E′ ᶜ∷ E′⋆} refl | .E | .E⋆ | [ E≤⁻ᴸE′ ] | [ E⋆≤⁻ᴸE′⋆ ] = ≤′ᴸ⇒≤′ (sym E≤⁻ᴸE′) ᶜ∷ ≤ᴸ⇒≤ (sym E⋆≤⁻ᴸE′⋆)

   ≤ᴸ⇒≤ {i = ◻} _ = ◻
   ≤ᴸ⇒≤ {i = [ _ ]} {◻} ()
   ≤ᴸ⇒≤ {i = [ E⋆ ]} {[ E′⋆ ]} _ with E⋆ ⊓⁻ E′⋆ | inspect (_⊓⁻_ E⋆) E′⋆
   ≤ᴸ⇒≤ {i = [ E⋆ ]} {[ E′⋆ ]} refl | .E⋆ | [ E⋆≤⁻ᴸE′⋆ ] = [ ≤⁻ᴸ⇒≤⁻ (sym E⋆≤⁻ᴸE′⋆) ]

   ≤⁻⇒≤⁻ᴸ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E⋆ : P —[ a⋆ ]→⋆ R} → _≤⁻_ ⇒ _≤⁻ᴸ_ lattices {a = E⋆}
   ≤⇒≤ᴸ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E⋆ : P —[ a⋆ ]→⋆ R} → _≤_ ⇒ _≤ᴸ_ lattices {a = E⋆}

   ≤⁻⇒≤⁻ᴸ []﹙ P ﹚ = cong []﹙_﹚ (≤′⇒≤′ᴸ P)
   ≤⁻⇒≤⁻ᴸ (E ᵇ∷ E⋆) = cong₂ _ᵇ∷_ (≤′⇒≤′ᴸ E) (≤⇒≤ᴸ E⋆)
   ≤⁻⇒≤⁻ᴸ (E ᶜ∷ E⋆) = cong₂ _ᶜ∷_ (≤′⇒≤′ᴸ E) (≤⇒≤ᴸ E⋆)

   -- Maybe introduce a typeclass for lattices where join/meet are monoids rather than proper semigroups.
   ◻-⊓-leftZ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E⋆ : P —[ a⋆ ]→⋆ R} → LeftZero _≡_ ◻ (_⊓_ {E₀⋆ = E⋆})
   ◻-⊓-leftZ ◻ = refl
   ◻-⊓-leftZ [ _ ] = refl

   ≤⇒≤ᴸ {j = E⋆} ◻ = sym (◻-⊓-leftZ E⋆)
   ≤⇒≤ᴸ [ E⋆ ] = cong [_] (≤⁻⇒≤⁻ᴸ E⋆)

   instance
      prefixes : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} → Prefixes (P —[ a⋆ ]→⋆ R)
      prefixes = record {
            lattices = lattices; _≤_ = _≤_; _≤⁻_ = _≤⁻_; ≤⁻ᴸ⇒≤⁻ = ≤⁻ᴸ⇒≤⁻; ≤ᴸ⇒≤ = ≤ᴸ⇒≤; ≤⁻⇒≤⁻ᴸ = ≤⁻⇒≤⁻ᴸ; ≤⇒≤ᴸ = ≤⇒≤ᴸ
         }

   -- I can't write these just by peeking at the relevant index, as I do in the non-lattice versions.
   source⋆ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E⋆ : P —[ a⋆ ]→⋆ R} → ↓ E⋆ → ↓′ ᵀ⋆.source⋆ E⋆
   source⋆ ◻ = ◻
   source⋆ [ []﹙ P ﹚ ] = P
   source⋆ [ E ᵇ∷ _ ] = ᵀ̃.source E
   source⋆ [ E ᶜ∷ _ ] = ᵀ̃.source E

   target⋆ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E⋆ : P —[ a⋆ ]→⋆ R} → ↓ E⋆ → ↓′ ᵀ⋆.target⋆ E⋆
   target⋆ ◻ = ◻
   target⋆ [ []﹙ P ﹚ ] = P
   target⋆ {Γ} {a⋆ = a ᵇ∷ a⋆} {E⋆ = E ᵇ∷ E⋆} [ _ ᵇ∷ E′⋆ ] =
      ≅-subst✴ Proc ↓′_ (+-assoc Γ 1 (inc⋆ a⋆)) (≅-sym (Proc↲ (+-assoc Γ 1 (inc⋆ a⋆)) (ᵀ⋆.target⋆ E⋆))) (target⋆ E′⋆)
   target⋆ {Γ} {a⋆ = a ᶜ∷ a⋆} {E⋆ = E ᶜ∷ E⋆} [ _ ᶜ∷ E′⋆ ] =
      ≅-subst✴ Proc ↓′_ (+-assoc Γ 0 (inc⋆ a⋆)) (≅-sym (Proc↲ (+-assoc Γ 0 (inc⋆ a⋆)) (ᵀ⋆.target⋆ E⋆))) (target⋆ E′⋆)

   postulate
      target⋆ᴹ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} {E₀⋆ : P —[ a⋆ ]→⋆ R} {E⋆ E′⋆ : ↓ E₀⋆} → E⋆ ≤ E′⋆ → target⋆ E⋆ ≤′ target⋆ E′⋆
-}

   source⋆ : ∀ {Γ P} {a⋆ : Action⋆ Γ} {R} (E⋆ : P —[ a⋆ ]→⋆ R) → ↓′ R → ↓′ P
   source⋆ [] P = P
   source⋆ (E ᵇ∷ E⋆) R = {!source ?!}
   source⋆ (E ᶜ∷ E⋆) R = {!!}
