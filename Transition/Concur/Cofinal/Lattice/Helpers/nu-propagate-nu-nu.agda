module Transition.Concur.Cofinal.Lattice.Helpers.nu-propagate-nu-nu where

   open import ConcurrentSlicingCommon
   open import Transition.Concur.Cofinal.Lattice.Common
   import Relation.Binary.EqReasoning as EqReasoning
   import Ren as ᴿ

   base : ∀ {Γ} {P₀ : Proc (Γ + 1)} {R₀ R′₀} {E : P₀ —[ τ ᶜ - _ ]→ R₀} {E′ : P₀ —[ τ ᶜ - _ ]→ R′₀}
          (𝐸 : E ⌣₁[ ᵛ∇ᵛ ] E′) (P : ↓ P₀) (R : ↓ R₀) (R′ : ↓ R′₀) (S† : ↓ tgt₁ (⊖₁ 𝐸)) (S‡ : ↓ tgt₂ (⊖₁ 𝐸)) →
          tgt E P ≡ R → tgt E′ P ≡ R′ → tgt (E′/E (⊖₁ 𝐸)) R ≡ S† → tgt (E/E′ (⊖₁ 𝐸)) R′ ≡ S‡ →
          braid̂ (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P) →
          _≡_ {A = ↓_ {A = Proc Γ} (ν Proc↱ refl (tgt₂ (⊖₁ 𝐸)))} [ ν braid̂ (γ₁ 𝐸) S† ] [ ν S‡ ]
   base {E = E} {E′} 𝐸 P R R′ S† S‡ ≡R ≡R′ ≡S† ≡S‡ IH = cong [_] (cong ν_ (
      let open EqReasoning (setoid _) in
      begin
         braid̂ (γ₁ 𝐸) S†
      ≡⟨ cong (braid̂ (γ₁ 𝐸)) (trans (sym ≡S†) (cong (tgt (E′/E (⊖₁ 𝐸))) (sym ≡R))) ⟩
         braid̂ (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
      ≡⟨ IH ⟩
         tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)
      ≡⟨ cong (tgt (E/E′ (⊖₁ 𝐸))) ≡R′ ⟩
         tgt (E/E′ (⊖₁ 𝐸)) R′
      ≡⟨ ≡S‡ ⟩
         S‡
      ∎))

   module ⋆
      {Γ} {P₀ : Proc (Γ + 1)} {R₀ R′₀} {E : P₀ —[ τ ᶜ - _ ]→ R₀} {E′ : P₀ —[ τ ᶜ - _ ]→ R′₀} (𝐸 : E ⌣₁[ ᵛ∇ᵛ ] E′)
      (P : ↓ P₀) (IH : braid̂ (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      private
         module sub
            (R : ↓ R₀) (R′ : ↓ R′₀) (≡R : tgt E P ≡ R) (≡R′ : tgt E′ P ≡ R′) where

            case′ :
               braid̂ (ν γ₁ 𝐸)
               (tgt (νᶜ E′/E (⊖₁ 𝐸)) [ ν R ]) ≡ tgt (νᶜ E/E′ (⊖₁ 𝐸)) [ ν R′ ]
            case′
               with step (E/E′ (⊖₁ 𝐸)) R′ | step (E′/E (⊖₁ 𝐸)) R |
                    inspect (step (E/E′ (⊖₁ 𝐸))) R′ | inspect (step (E′/E (⊖₁ 𝐸))) R
            ... | ◻ , S‡ | ◻ , S† | [ ≡S‡ ] | [ ≡S† ] =
               base 𝐸 P R R′ S† S‡ ≡R ≡R′ (,-inj₂ ≡S†) (,-inj₂ ≡S‡) IH
            ... | ◻ , S‡ | [ τ ᶜ ] , S† | [ ≡S‡ ] | [ ≡S† ] =
               base 𝐸 P R R′ S† S‡ ≡R ≡R′ (,-inj₂ ≡S†) (,-inj₂ ≡S‡) IH
            ... | [ τ ᶜ ] , S‡ | ◻ , S† | [ ≡S‡ ] | [ ≡S† ] =
               base 𝐸 P R R′ S† S‡ ≡R ≡R′ (,-inj₂ ≡S†) (,-inj₂ ≡S‡) IH
            ... | [ τ ᶜ ] , S‡ | [ τ ᶜ ] , S† | [ ≡S‡ ] | [ ≡S† ] =
               base 𝐸 P R R′ S† S‡ ≡R ≡R′ (,-inj₂ ≡S†) (,-inj₂ ≡S‡) IH

      open sub

      case :
         braid̂ (ν γ₁ 𝐸)
         (tgt (νᶜ E′/E (⊖₁ 𝐸)) (tgt (νᶜ E) [ ν P ])) ≡ tgt (νᶜ E/E′ (⊖₁ 𝐸)) (tgt (νᶜ E′) [ ν P ])
      case
         with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
      ... | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | ◻ , R′ | [ τ ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ τ ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ τ ᶜ ] , R′ | [ τ ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
