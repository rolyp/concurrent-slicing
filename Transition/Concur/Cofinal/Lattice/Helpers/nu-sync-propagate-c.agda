module Transition.Concur.Cofinal.Lattice.Helpers.nu-sync-propagate-c
   {Γ P₀ Q₀}
   where

   open import ConcurrentSlicingCommon
   open import Transition.Concur.Cofinal.Lattice.Common
   import Name as ᴺ

   module τ
      {x : Name Γ} {R₀ R′₀ S₀} {E : P₀ —[ τ ᶜ - _ ]→ R₀} {E′ : P₀ —[ x • ᵇ - _ ]→ R′₀}
      (𝐸 : E ⌣₁[ ᶜ∇ᵇ ] E′) (F : Q₀ —[ (• x) ᵇ - _ ]→ S₀) (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂ (⊖₁ 𝐸))
      (P : ↓ P₀) (Q : ↓ Q₀) (P′ : ↓ P′₀)
      (IH : braiding (ᶜ∇ᵇ {a = τ} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      module _
         (id*E/E′ : (idᶠ *) R′₀ —[ τ ᶜ - _ ]→ (idᶠ *) P″₀) (S : ↓ S₀) (R′ : ↓ R′₀) (y : ↓ ᴺ.zero)
         (≡id*E/E′ : (idᶠ *ᶜ) (E/E′ (⊖₁ 𝐸)) ≡ id*E/E′) (≡P′ : tgt (E′/E (⊖₁ 𝐸)) (tgt E P) ≡ P′) (≡S : tgt F Q ≡ S)
         (≡R′ : tgt E′ P ≡ R′)
         where

         base :
            (P″ : ↓ (idᶠ *) P″₀) (≡P″ : tgt id*E/E′ ((repl y *̃) R′) ≡ P″) →
            braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (cong ν_ (cong₂ _│_ (cong (idᶠ *) (γ₁ 𝐸)) refl))
            [ ν [ (repl y *̃) P′ │ S ] ] ≡
            [ ν [ P″ │ S ] ]
         base P″ ≡P″ = ≅-to-≡ (
            let α : (repl y *̃) P′ ≅ P″
                α = let open ≅-Reasoning in
                   begin
                      (repl y *̃) P′
                   ≡⟨ cong (repl y *̃) (sym ≡P′) ⟩
                      (repl y *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
                   ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐸) ((repl y *̃)) (≅-sym (reduce-ᶜ∇ᵇ (γ₁ 𝐸) _)) ⟩
                      (repl y *̃) (braiding (ᶜ∇ᵇ {a = τ} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))
                   ≡⟨ cong (repl y *̃) IH ⟩
                      (repl y *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
                   ≡⟨ renᶜ-tgt-comm (E/E′ (⊖₁ 𝐸)) (repl y) (tgt E′ P) ⟩
                      tgt ((idᶠ *ᶜ) (E/E′ (⊖₁ 𝐸))) ((repl y *̃) (tgt E′ P))
                   ≡⟨ cong (λ E† → tgt E† ((repl y *̃) (tgt E′ P))) ≡id*E/E′ ⟩
                      tgt id*E/E′ ((repl y *̃) (tgt E′ P))
                   ≡⟨ cong (tgt id*E/E′ ∘ᶠ (repl y *̃)) ≡R′  ⟩
                      tgt id*E/E′ ((repl y *̃) R′)
                   ≡⟨ ≡P″ ⟩
                      P″
                   ∎
                open ≅-Reasoning in
            begin
               braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (cong ν_ (cong₂ _│_ (cong (idᶠ *) (γ₁ 𝐸)) refl))
               [ ν [ (repl y *̃) P′ │ S ] ]
            ≅⟨ reduce-ᶜ∇ᶜ (cong ν_ (cong₂ _│_ (cong (idᶠ *) (γ₁ 𝐸)) refl)) _ ⟩
               [ ν [ (repl y *̃) P′ │ S ] ]
            ≅⟨ [ν-]-cong (cong₂ _│_ (cong (idᶠ *) (γ₁ 𝐸)) refl) ([-│]-cong S (cong (idᶠ *) (γ₁ 𝐸)) α) ⟩
               [ ν [ P″ │ S ] ]
            ∎)

         subcase :
            braiding (ᶜ∇ᶜ {a = τ} {τ}) {0}
            (cong ν_ (cong₂ _│_ (cong (idᶠ *) (γ₁ 𝐸)) refl))
            [ ν [ (repl y *̃) P′ │ S ] ] ≡
            π₂ (step⁻ (νᶜ (id*E/E′ ᶜ│ S₀)) (ν [ (repl y *̃) R′ │ S ]))
         subcase
            with step id*E/E′ ((repl y *̃) R′) | inspect (step id*E/E′) ((repl y *̃) R′)
         ... | ◻ , P″ | [ ≡P″ ] = base P″ (,-inj₂ ≡P″)
         ... | [ τ ᶜ ] , P″ | [ ≡P″ ] = base P″ (,-inj₂ ≡P″)

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
