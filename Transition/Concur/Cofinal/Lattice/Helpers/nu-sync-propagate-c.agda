module Transition.Concur.Cofinal.Lattice.Helpers.nu-sync-propagate-c
   {Γ P₀ Q₀}
   where

   open import ConcurrentSlicingCommon
   open import Transition.Concur.Cofinal.Lattice.Common

   module τ
      {x : Name Γ} {R₀ R′₀ S₀} {E : P₀ —[ τ ᶜ - _ ]→ R₀} {E′ : P₀ —[ x • ᵇ - _ ]→ R′₀}
      (𝐸 : E ⌣₁[ ᶜ∇ᵇ ] E′) (F : Q₀ —[ (• x) ᵇ - _ ]→ S₀) (P : ↓ P₀) (Q : ↓ Q₀)
      (IH : braiding (ᶜ∇ᵇ {a = τ} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      case :
         braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (γ₁ (𝐸 │ᵥᶜ F))
         (tgt (E′/E (⊖₁ (𝐸 │ᵥᶜ F))) (tgt (E ᶜ│ Q₀) [ P │ Q ]))
         ≡
         tgt (E/E′ (⊖₁ (𝐸 │ᵥᶜ F))) (tgt (E′ │ᵥ F) [ P │ Q ])
      case
         with (idᶠ *ᶜ) (E/E′ (⊖₁ 𝐸)) | step E′ P | step F Q | step (E′/E (⊖₁ 𝐸)) (tgt E P) |
              inspect (idᶠ *ᶜ) (E/E′ (⊖₁ 𝐸)) | inspect (step E′) P | inspect (step F) Q |
              inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P)
      ... | id*E/E | ◻ , R′ | _ , S | [ ._ • ᵇ ] , P′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
         ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡R′)) (trans (sym (π₁ (ᴬgamma₁ 𝐸 P))) (,-inj₁ ≡P′))))
      ... | id*E/E | [ ._ • ᵇ ] , R′ | _ , S | ◻ , P′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
         ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P′)) (trans (π₁ (ᴬgamma₁ 𝐸 P)) (,-inj₁ ≡R′))))
      ... | id*E/E | ◻ , R′ | ◻ , S | ◻ , P′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
         {!!} -- let open │ᵥᶜ-τ 𝐸 F P Q P′ id*E/E S R′ ◻ ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in case
      ... | id*E/E | ◻ , R′ | [ (• ._) ᵇ ] , S | ◻ , P′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
         {!!} -- let open │ᵥᶜ-τ 𝐸 F P Q P′ id*E/E S R′ ◻ ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in case
      ... | id*E/E | [ ._ • ᵇ ] , R′ | ◻ , S | [ ._ • ᵇ ] , P′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
         {!!} -- let open │ᵥᶜ-τ 𝐸 F P Q P′ id*E/E S R′ ◻ ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in case
      ... | id*E/E | [ ._ • ᵇ ] , R′ | [ (• ._) ᵇ ] , S | [ ._ • ᵇ ] , P′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
         {!!} -- let open │ᵥᶜ-τ 𝐸 F P Q P′ id*E/E S R′ [ ᴺ.zero ] ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in case
