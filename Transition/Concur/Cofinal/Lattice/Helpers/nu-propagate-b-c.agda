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

      case :
         braiding (ᵇ∇ᶜ {a = • x} {• x′ 〈 y 〉}) {0} (γ₁ (νᵇᶜ 𝐸))
         (tgt (E′/E (⊖₁ (νᵇᶜ 𝐸))) (tgt (νᵇ E) [ ν P ]))  ≡
         tgt (E/E′ (⊖₁ (νᵇᶜ 𝐸))) (tgt (νᶜ E′) [ ν P ])
      case
         with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
      ... | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = {!!}
      ... | ◻ , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ] = {!!}
      ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = {!!}
      ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = {!!}
      ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ] = {!!}
      ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ] = {!!}
{-
      case
         with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
      ... | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] =
         case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | ◻ , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] =
         case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | ◻ , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] =
         case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] =
         case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] =
         case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] =
         case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] =
         case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] =
         case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] =
         case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
-}
