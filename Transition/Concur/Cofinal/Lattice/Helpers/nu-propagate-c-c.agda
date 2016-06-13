module Transition.Concur.Cofinal.Lattice.Helpers.nu-propagate-c-c where

   open import ConcurrentSlicingCommon
   import Ren as ᴿ
   open import Transition.Concur.Cofinal.Lattice.Common

   module νᶜᶜ
      {Γ P₀ R₀ R′₀} {x y x′ y′ : Name Γ} {E : P₀ —[ • ᴿ.push x 〈 ᴿ.push y 〉 ᶜ - _ ]→ R₀}
      {E′ : P₀ —[ • ᴿ.push x′ 〈 ᴿ.push y′ 〉 ᶜ - _ ]→ R′₀} (𝐸 : E ⌣₁[ ᶜ∇ᶜ ] E′) (P : ↓ P₀)
      (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂ (⊖₁ 𝐸))
      where

      module sub
         (R : ↓ R₀) (R′ : ↓ R′₀) (≡R : tgt E P ≡ R) (≡R′ : tgt E′ P ≡ R′) where

         case′ :
            braiding (ᶜ∇ᶜ {a = • x 〈 y 〉} {• x′ 〈 y′ 〉}) {0} (cong ν_ (γ₁ 𝐸))
            (π₂ (step⁻ (νᶜ E′/E (⊖₁ 𝐸)) (ν R))) ≡
            π₂ (step⁻ (νᶜ E/E′ (⊖₁ 𝐸)) (ν R′))
         case′
            with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′
         case′ | ◻ , P′ | ◻ , P″ = {!!}
         case′ | ◻ , P′ | [ • ._ 〈 ◻ 〉 ᶜ ] , P″ = {!!}
         case′ | ◻ , P′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , P″ = {!!}
         case′ | [ • ._ 〈 ◻ 〉 ᶜ ] , P′ | ◻ , P″ = {!!}
         case′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , P′ | ◻ , P″ = {!!}
         case′ | [ • ._ 〈 ◻ 〉 ᶜ ] , P′ | [ • ._ 〈 ◻ 〉 ᶜ ] , P″ = {!!}
         case′ | [ • ._ 〈 ◻ 〉 ᶜ ] , P′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , P″ = {!!}
         case′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , P′ | [ • ._ 〈 ◻ 〉 ᶜ ] , P″ = {!!}
         case′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , P′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , P″ = {!!}

      case :
         braiding (ᶜ∇ᶜ {a = • x 〈 y 〉} {• x′ 〈 y′ 〉}) {0} (cong ν_ (γ₁ 𝐸))
         (tgt (νᶜ E′/E (⊖₁ 𝐸)) (tgt (νᶜ E) [ ν P ])) ≡
         tgt (νᶜ E/E′ (⊖₁ 𝐸)) (tgt (νᶜ E′) [ ν P ])
      case
         with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
      ... | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] =
         let open sub R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′) in case′
      ... | ◻ , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] =
         let open sub R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′) in case′
      ... | ◻ , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] =
         let open sub R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′) in case′
      ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] =
         let open sub R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′) in case′
      ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] =
         let open sub R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′) in case′
      ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] =
         let open sub R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′) in case′
      ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] =
         let open sub R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′) in case′
      ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] =
         let open sub R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′) in case′
      ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] =
         let open sub R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′) in case′
