open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common

module Transition.Concur.Cofinal.Lattice.case.nu-sync-propagate-c
   {Γ} {x : Name Γ} {P₀ Q₀ R₀ R′₀ S₀}
   where

   import Name as ᴺ

   module τ
      {E : P₀ —[ τ ᶜ - _ ]→ R₀} {E′ : P₀ —[ x • ᵇ - _ ]→ R′₀}
      (𝐸 : E ⌣₁[ ᶜ∇ᵇ ] E′) (F : Q₀ —[ (• x) ᵇ - _ ]→ S₀) (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂ (⊖₁ 𝐸))
      (P : ↓ P₀) (Q : ↓ Q₀)
      (IH : braiding (ᶜ∇ᵇ {a = τ} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      module _
         (P′ : ↓ P′₀) (S : ↓ S₀) (R′ : ↓ R′₀) (≡P′ : tgt (E′/E (⊖₁ 𝐸)) (tgt E P) ≡ P′) (≡S : tgt F Q ≡ S)
         (≡R′ : tgt E′ P ≡ R′)
         where

         base :
            (P″ : ↓ P″₀) (≡P″ : tgt (E/E′ (⊖₁ 𝐸)) R′ ≡ P″) →
            braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (cong ν_ (cong₂ _│_ (γ₁ 𝐸) refl))
            [ ν [ P′ │ S ] ]
            ≡
            [ ν [ P″ │ S ] ]
         base P″ ≡P″ = ≅-to-≡ (
            let α : P′ ≅ P″
                α = let open ≅-Reasoning in
                   begin
                      P′
                   ≡⟨ sym ≡P′ ⟩
                      tgt (E′/E (⊖₁ 𝐸)) (tgt E P)
                   ≅⟨ ≅-sym (reduce-ᶜ∇ᵇ (γ₁ 𝐸) _) ⟩
                      braiding (ᶜ∇ᵇ {a = τ} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
                   ≡⟨ IH ⟩
                      tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)
                   ≡⟨ cong (tgt (E/E′ (⊖₁ 𝐸))) ≡R′  ⟩
                      tgt (E/E′ (⊖₁ 𝐸)) R′
                   ≡⟨ ≡P″ ⟩
                      P″
                   ∎
                open ≅-Reasoning in
            begin
               braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (cong ν_ (cong₂ _│_ (γ₁ 𝐸) refl))
               [ ν [ P′ │ S ] ]
            ≅⟨ reduce-ᶜ∇ᶜ (cong ν_ (cong₂ _│_ (γ₁ 𝐸) refl)) _ ⟩
               [ ν [ P′ │ S ] ]
            ≅⟨ [ν-]-cong (cong₂ _│_ (γ₁ 𝐸) refl) ([-│]-cong S (γ₁ 𝐸) α) ⟩
               [ ν [ P″ │ S ] ]
            ∎)

         subcase :
            braiding (ᶜ∇ᶜ {a = τ} {τ}) {0}
            (cong ν_ (cong₂ _│_ (γ₁ 𝐸) refl))
            [ ν [ P′ │ S ] ]
            ≡
            π₂ (step⁻ (νᶜ (E/E′ (⊖₁ 𝐸) ᶜ│ S₀)) (ν [ R′ │ S ]))
         subcase
            with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
         ... | ◻ , P″ | [ ≡P″ ] = base P″ (,-inj₂ ≡P″)
         ... | [ τ ᶜ ] , P″ | [ ≡P″ ] = base P″ (,-inj₂ ≡P″)

      case :
         braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (γ₁ (𝐸 │ᵥᶜ F))
         (tgt (E′/E (⊖₁ (𝐸 │ᵥᶜ F))) (tgt (E ᶜ│ Q₀) [ P │ Q ]))
         ≡
         tgt (E/E′ (⊖₁ (𝐸 │ᵥᶜ F))) (tgt (E′ │ᵥ F) [ P │ Q ])
      case
         with step E′ P | step F Q | step (E′/E (⊖₁ 𝐸)) (tgt E P) |
              inspect (step E′) P | inspect (step F) Q | inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P)
      ... | ◻ , R′ | _ , S | [ ._ • ᵇ ] , P′ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
         ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡R′)) (trans (sym (π₁ (ᴬgamma₁ 𝐸 P))) (,-inj₁ ≡P′))))
      ... | [ ._ • ᵇ ] , R′ | _ , S | ◻ , P′ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
         ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P′)) (trans (π₁ (ᴬgamma₁ 𝐸 P)) (,-inj₁ ≡R′))))
      ... | ◻ , R′ | ◻ , S | ◻ , P′ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
         subcase P′ S R′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡R′)
      ... | ◻ , R′ | [ (• ._) ᵇ ] , S | ◻ , P′ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
         subcase P′ S R′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡R′)
      ... | [ ._ • ᵇ ] , R′ | ◻ , S | [ ._ • ᵇ ] , P′ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
         subcase P′ S R′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡R′)
      ... | [ ._ • ᵇ ] , R′ | [ (• ._) ᵇ ] , S | [ ._ • ᵇ ] , P′ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
         subcase P′ S R′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡R′)

   module •x〈y〉
      {x′ y₀ : Name Γ} {E : P₀ —[ • x′ 〈 y₀ 〉 ᶜ - _ ]→ R₀} {E′ : P₀ —[ x • ᵇ - _ ]→ R′₀}
      (𝐸 : E ⌣₁[ ᶜ∇ᵇ ] E′) (F : Q₀ —[ (• x) ᵇ - _ ]→ S₀) (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂ (⊖₁ 𝐸))
      (P : ↓ P₀) (Q : ↓ Q₀)
      (IH : braiding (ᶜ∇ᵇ {a = • x′ 〈 y₀ 〉} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      module _
         (P′ : ↓ P′₀) (S : ↓ S₀) (R′ : ↓ R′₀) (≡P′ : tgt (E′/E (⊖₁ 𝐸)) (tgt E P) ≡ P′) (≡S : tgt F Q ≡ S)
         (≡R′ : tgt E′ P ≡ R′)
         where

         base :
            (P″ : ↓ P″₀) (≡P″ : tgt (E/E′ (⊖₁ 𝐸)) R′ ≡ P″) →
            braiding (ᶜ∇ᶜ {a = • x′ 〈 y₀ 〉} {τ}) {0} (cong ν_ (cong₂ _│_ (γ₁ 𝐸) refl))
            [ ν [ P′ │ S ] ]
            ≡
            [ ν [ P″ │ S ] ]
         base P″ ≡P″ = ≅-to-≡ (
            let α : P′ ≅ P″
                α = let open ≅-Reasoning in
                   begin
                      P′
                   ≡⟨ sym ≡P′ ⟩
                      tgt (E′/E (⊖₁ 𝐸)) (tgt E P)
                   ≅⟨ ≅-sym (reduce-ᶜ∇ᵇ (γ₁ 𝐸) _) ⟩
                      braiding (ᶜ∇ᵇ {a = • x′ 〈 y₀ 〉} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
                   ≡⟨ IH ⟩
                      tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)
                   ≡⟨ cong (tgt (E/E′ (⊖₁ 𝐸))) ≡R′  ⟩
                      tgt (E/E′ (⊖₁ 𝐸)) R′
                   ≡⟨ ≡P″ ⟩
                      P″
                   ∎
                open ≅-Reasoning in
            begin
               braiding (ᶜ∇ᶜ {a = • x′ 〈 y₀ 〉} {τ}) {0} (cong ν_ (cong₂ _│_ (γ₁ 𝐸) refl))
               [ ν [ P′ │ S ] ]
            ≅⟨ reduce-ᶜ∇ᶜ (cong ν_ (cong₂ _│_ (γ₁ 𝐸) refl)) _ ⟩
               [ ν [ P′ │ S ] ]
            ≅⟨ [ν-]-cong (cong₂ _│_ (γ₁ 𝐸) refl) ([-│]-cong S (γ₁ 𝐸) α) ⟩
               [ ν [ P″ │ S ] ]
            ∎)

         subcase :
            braiding (ᶜ∇ᶜ {a = • x′ 〈 y₀ 〉} {τ}) {0}
            (cong ν_ (cong₂ _│_ (γ₁ 𝐸) refl))
            [ ν [ P′ │ S ] ]
            ≡
            tgt (νᶜ (E/E′ (⊖₁ 𝐸) ᶜ│ S₀)) [ ν [ R′ │ S ] ]
         subcase
            with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
         ... | ◻ , P″ | [ ≡P″ ] = base P″ (,-inj₂ ≡P″)
         ... | [ • ._ 〈 ◻ 〉 ᶜ ] , P″ | [ ≡P″ ] = base P″ (,-inj₂ ≡P″)
         ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , P″ | [ ≡P″ ] = base P″ (,-inj₂ ≡P″)

      case :
         braiding (ᶜ∇ᶜ {a = • x′ 〈 y₀ 〉} {τ}) {0} (γ₁ (𝐸 │ᵥᶜ F))
         (tgt (E′/E (⊖₁ (𝐸 │ᵥᶜ F))) (tgt (E ᶜ│ Q₀) [ P │ Q ]))
         ≡
         tgt (E/E′ (⊖₁ (𝐸 │ᵥᶜ F))) (tgt (E′ │ᵥ F) [ P │ Q ])
      case
         with step E′ P | step F Q | step (E′/E (⊖₁ 𝐸)) (tgt E P) |
              inspect (step E′) P | inspect (step F) Q | inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P)
      ... | ◻ , R′ | _ , S | [ ._ • ᵇ ] , P′ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
         ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡R′)) (trans (sym (π₁ (ᴬgamma₁ 𝐸 P))) (,-inj₁ ≡P′))))
      ... | [ ._ • ᵇ ] , R′ | _ , S | ◻ , P′ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
         ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P′)) (trans (π₁ (ᴬgamma₁ 𝐸 P)) (,-inj₁ ≡R′))))
      ... | ◻ , R′ | ◻ , S | ◻ , P′ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
         subcase P′ S R′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡R′)
      ... | ◻ , R′ | [ (• ._) ᵇ ] , S | ◻ , P′ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
         subcase P′ S R′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡R′)
      ... | [ ._ • ᵇ ] , R′ | ◻ , S | [ ._ • ᵇ ] , P′ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
         subcase P′ S R′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡R′)
      ... | [ ._ • ᵇ ] , R′ | [ (• ._) ᵇ ] , S | [ ._ • ᵇ ] , P′ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] =
         subcase P′ S R′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡R′)
