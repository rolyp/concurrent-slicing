-- Lift transition renamings to prefix lattices.
module Transition.Ren.Lattice where

   open import ConcurrentSlicingCommon
   open import Action using (Actionᵇ; Actionᶜ; _ᵇ; _ᶜ)
   open import Action.Ren.Lattice renaming (_* to _ᴬ*̃)
   import Lattice; open Lattice.Prefixes ⦃...⦄ using (↓_)
   open import Proc.Ren
   open import Proc.Ren.Lattice renaming (_* to _*̃)
   open import Ren as ᴿ using (Ren; push)
   open import Ren.Lattice using (_*; suc; _ᴿ+_)
   open import Ren.Properties
   open import Transition using (_—[_-_]→_)
   open import Transition.Lattice as ᵀ̃ using (step); open ᵀ̃.↓_; open ᵀ̃.↓⁻_
   open import Transition.Ren renaming (_*ᶜ to _*ᶜ′; _*ᵇ to _*ᵇ′)

   infixr 8 _*ᵇ _*ᶜ

   _*ᶜ : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {P R} {a : Actionᶜ Γ} {E : P —[ a ᶜ - _ ]→ R} → ↓ ρ → ↓ E → ↓ (ρ *ᶜ′) E
   _*ᵇ : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {P R} {a : Actionᵇ Γ} {E : P —[ a ᵇ - _ ]→ R} → ↓ ρ → ↓ E → ↓ (ρ *ᵇ′) E

   (ρ *ᶜ) ◻ = ◻
   (ρ *ᶜ) [ • x 〈 y 〉∙ P ] = [ • (ρ *) x 〈 (ρ *) y 〉∙ (ρ *̃) P ]
   (ρ *ᶜ) [ E ➕₁ Q ] = [ (ρ *ᶜ) E ➕₁ (ρ *̃) Q ]
   (ρ *ᶜ) [ E ᶜ│ Q ] = [ (ρ *ᶜ) E ᶜ│ (ρ *̃) Q ]
   (ρ *ᶜ) [ P │ᶜ F ] = [ (ρ *̃) P │ᶜ (ρ *ᶜ) F ]
   (ρ *ᶜ) [ ! E ] = [ ! (ρ *ᶜ) E ]
   (_*ᶜ {ρ = ρ₀} ρ) [ _│•_ {R = R} {y = y} E F ] rewrite pop-comm ρ₀ y R = [ (ρ *ᵇ) E │• (ρ *ᶜ) F ]
   (ρ *ᶜ) [ E │ᵥ F ] = [ (ρ *ᵇ) E │ᵥ (ρ *ᵇ) F ]
   (_*ᶜ {ρ = ρ₀} ρ) [ νᶜ_ {a = a} {E = E₀} E ] with (ᴿ.suc ρ₀ *ᶜ′) E₀ | (suc ρ *ᶜ) E
   ... | E₀′ | E′ rewrite ᴿ+-comm 1 ρ₀ a = [ νᶜ E′ ]

   (ρ *ᵇ) ◻ = ◻
   (ρ *ᵇ) [ x •∙ P ] = [ (ρ *) x •∙ (suc ρ *̃) P ]
   (ρ *ᵇ) [ E ➕₁ Q ] = [ (ρ *ᵇ) E ➕₁ (ρ *̃) Q ]
   (ρ *ᵇ) [ ! E ] = [ ! (ρ *ᵇ) E ]
   (_*ᵇ {ρ = ρ₀} ρ) [ _ᵇ│_ {Q = Q₀} E Q ] rewrite ᴿ+-comm 1 ρ₀ Q₀ = [ (ρ *ᵇ) E ᵇ│ (ρ *̃) Q ]
   (_*ᵇ {ρ = ρ₀} ρ) [ _│ᵇ_ {P = P₀} P F ] rewrite ᴿ+-comm 1 ρ₀ P₀ = [ (ρ *̃) P │ᵇ (ρ *ᵇ) F ]
   (ρ *ᵇ) [ ν• E ] = [ ν• (suc ρ *ᶜ) E ]
   (_*ᵇ {ρ = ρ₀} ρ) [ νᵇ_ {a = a} {R} {E₀} E ] with (ᴿ.suc ρ₀ *ᵇ′) E₀ | (suc ρ *ᵇ) E
   ... | E₀′ | E′ rewrite ᴿ+-comm 1 ρ₀ a | sym (swap-suc-suc ρ₀ R) = [ νᵇ E′ ]

   postulate
      -- Convenient to have separate lemmas for the actions and the target processes.
      renᶜ-step-comm : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {P₀ a R₀} (E : P₀ —[ a ᶜ - _ ]→ R₀) →
                       (ρ′ : ↓ ρ) (P : ↓ P₀) → (ρ′ *̃) (π₂ (step E P)) ≡ π₂ (step ((ρ *ᶜ′) E) ((ρ′ *̃) P))
      ᴬrenᶜ-step-comm : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {P₀ a R₀} (E : P₀ —[ a ᶜ - _ ]→ R₀) →
                       (ρ′ : ↓ ρ) (P : ↓ P₀) → (ρ′ ᴬ*̃) (π₁ (step E P)) ≡ π₁ (step ((ρ *ᶜ′) E) ((ρ′ *̃) P))
      renᵇ-step-comm : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {P₀ a R₀} (E : P₀ —[ a ᵇ - _ ]→ R₀) →
                       (ρ′ : ↓ ρ) (P : ↓ P₀) → ((ρ′ ᴿ+ 1) *̃) (π₂ (step E P)) ≡ π₂ (step ((ρ *ᵇ′) E) ((ρ′ *̃) P))
      ᴬrenᵇ-step-comm : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} {P₀ a R₀} (E : P₀ —[ a ᵇ - _ ]→ R₀) →
                       (ρ′ : ↓ ρ) (P : ↓ P₀) → (ρ′ ᴬ*̃) (π₁ (step E P)) ≡ π₁ (step ((ρ *ᵇ′) E) ((ρ′ *̃) P))
