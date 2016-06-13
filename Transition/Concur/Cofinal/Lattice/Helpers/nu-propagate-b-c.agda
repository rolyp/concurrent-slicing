module Transition.Concur.Cofinal.Lattice.Helpers.nu-propagate-b-c where

   open import ConcurrentSlicingCommon
   import Ren as ᴿ
   open import Transition.Concur.Cofinal.Lattice.Common

   module x•-•x〈y〉
      {Γ P₀ R₀ R′₀} {x x′ y : Name Γ} {E : P₀ —[ (• ᴿ.push x) ᵇ - _ ]→ R₀}
      {E′ : P₀ —[ • ᴿ.push x′ 〈 ᴿ.push y 〉 ᶜ - _ ]→ R′₀} (𝐸 : E ⌣₁[ ᵇ∇ᶜ ] E′) (P : ↓ P₀)
      (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂ (⊖₁ 𝐸))
      (IH : braiding (ᵇ∇ᶜ {a = • ᴿ.push x} {• ᴿ.push x′ 〈 ᴿ.push y 〉}) {0} (γ₁ 𝐸)
            (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      private
         module sub
            (R : ↓ R₀) (R′ : ↓ R′₀) (≡R : tgt E P ≡ R) (≡R′ : tgt E′ P ≡ R′) where

            postulate
             case′ :
               braiding (ᵇ∇ᶜ {a = • x} {• x′ 〈 y 〉}) {0} (cong ν_ (cong (ᴿ.swap *) (γ₁ 𝐸)))
               (π₂ (step⁻ (νᶜ (ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) (ν (swap *̃) R))) ≡ π₂ (step⁻ (νᵇ E/E′ (⊖₁ 𝐸)) (ν R′))

      open sub

      case :
         braiding (ᵇ∇ᶜ {a = • x} {• x′ 〈 y 〉}) {0} (γ₁ (νᵇᶜ 𝐸))
         (tgt (E′/E (⊖₁ (νᵇᶜ 𝐸))) (tgt (νᵇ E) [ ν P ])) ≡ tgt (E/E′ (⊖₁ (νᵇᶜ 𝐸))) (tgt (νᶜ E′) [ ν P ])
      case
         with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
      ... | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | ◻ , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
