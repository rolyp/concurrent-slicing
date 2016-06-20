open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common

module Transition.Concur.Cofinal.Lattice.Helpers.nu-sync-propagate-b
   {Γ} {x : Name Γ} {P₀ Q₀ R₀ R′₀ S₀}
   where

   import Relation.Binary.EqReasoning as EqReasoning
   import Name as ᴺ
   import Ren as ᴿ
   import Ren.Lattice as ᴿ̃

   module x•
      {x′ : Name Γ} {E : P₀ —[ x′ • ᵇ - _ ]→ R₀} {E′ : P₀ —[ x • ᵇ - _ ]→ R′₀}
      (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (F : Q₀ —[ (• x) ᵇ - _ ]→ S₀) (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂ (⊖₁ 𝐸))
      (P : ↓ P₀) (Q : ↓ Q₀)
      (IH : braiding (ᵇ∇ᵇ {a = x′ •} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      module _
         (P′ : ↓ P′₀) (S′ : ↓ (ᴿ.suc ᴿ.push *) S₀) (id*E/E′ : (idᶠ *) R′₀ —[ ᴺ.suc x′ • ᵇ - _ ]→ (ᴿ.suc idᶠ *) P″₀)
         (S : ↓ S₀) (R′ : ↓ R′₀) (y : ↓ ᴺ.zero) (≡id*E/E′ : (idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) ≡ id*E/E′)
         (≡P′ : tgt (E′/E (⊖₁ 𝐸)) (tgt E P) ≡ P′) (≡S : tgt F Q ≡ S) (≡S′ : tgt ((ᴿ.push *ᵇ) F) ((push *̃) Q) ≡ S′)
         (≡R′ : tgt E′ P ≡ R′)
         (let α : (idᶠ *) P′₀ ≡ (ᴿ.swap *) ((ᴿ.suc idᶠ *) P″₀)
              α = (let open EqReasoning (setoid _) in
                begin
                   (idᶠ *) P′₀
                ≡⟨ *-preserves-id P′₀ ⟩
                   P′₀
                ≡⟨ swap-swap (γ₁ 𝐸) ⟩
                   (ᴿ.swap *) P″₀
                ≡⟨ cong (ᴿ.swap *) (sym (+-id-elim 1 P″₀)) ⟩
                   (ᴿ.swap *) ((ᴿ.suc idᶠ *) P″₀)
                ∎))
         where

         base :
            (P″ : ↓ (ᴿ.suc idᶠ *) P″₀) (≡P″ : tgt id*E/E′ ((repl y *̃) R′) ≡ P″) →
            braiding (ᵇ∇ᶜ {a = x′ •} {τ}) {0} (cong ν_ (cong₂ _│_ α (swap∘push S₀)))
            [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P′ │ S′ ] ] ≡
            [ ν [ (swap *̃) P″ │ (swap *̃) ((push *̃) S) ] ]
         base P″ ≡P″ = ≅-to-≡ (
            let β = (repl ((weaken ᴿ̃.*) y) *̃) P′ ≅ (swap *̃) P″
                β = let open ≅-Reasoning in
                   begin
                      (repl ((weaken ᴿ̃.*) y) *̃) P′
                   ≡⟨ cong (repl ((weaken ᴿ̃.*) y) *̃) (sym ≡P′) ⟩
                      (repl ((weaken ᴿ̃.*) y) *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
                   ≅⟨ ≅-cong✴ ↓_ (sym ((swap-involutive P′₀)))
                              (repl ((weaken ᴿ̃.*) y) *̃) (≅-sym (swap-involutivẽ (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))) ⟩
                      (repl ((weaken ᴿ̃.*) y) *̃) ((swap *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                   ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐸) ((repl ((weaken ᴿ̃.*) y) *̃) ∘ᶠ (swap *̃)) (≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐸) _)) ⟩
                      (repl ((weaken ᴿ̃.*) y) *̃)
                      ((swap *̃) (braiding (ᵇ∇ᵇ {a = x′ •} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                   ≡⟨ cong ((repl ((weaken ᴿ̃.*) y) *̃) ∘ᶠ (swap *̃)) IH ⟩
                      (repl ((weaken ᴿ̃.*) y) *̃) ((swap *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)))
                   ≅⟨ id-swap̃ y (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)) ⟩
                      (swap *̃) ((suc (repl y) *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)))
                   ≡⟨ cong (swap *̃) (renᵇ-tgt-comm (E/E′ (⊖₁ 𝐸)) (repl y) (tgt E′ P)) ⟩
                      (swap *̃) (tgt ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸))) ((repl y *̃) (tgt E′ P)))
                   ≡⟨ cong (λ E† → (swap *̃) (tgt E† ((repl y *̃) (tgt E′ P)))) ≡id*E/E′ ⟩
                      (swap *̃) (tgt id*E/E′ ((repl y *̃) (tgt E′ P)))
                   ≡⟨ cong ((swap *̃) ∘ᶠ tgt id*E/E′ ∘ᶠ (repl y *̃)) ≡R′ ⟩
                      (swap *̃) (tgt id*E/E′ ((repl y *̃) R′))
                   ≡⟨ cong (swap *̃) ≡P″ ⟩
                      (swap *̃) P″
                   ∎
                δ : S′ ≅ (swap *̃) ((push *̃) S)
                δ = let open ≅-Reasoning in
                   begin
                      S′
                   ≡⟨ sym ≡S′ ⟩
                      tgt ((ᴿ.push *ᵇ) F) ((push *̃) Q)
                   ≡⟨ sym (renᵇ-tgt-comm F push Q) ⟩
                      (suc push *̃) (tgt F Q)
                   ≅⟨ swap∘push̃ _ ⟩
                      (swap *̃) ((push *̃) (tgt F Q))
                   ≡⟨ cong ((swap *̃) ∘ᶠ (push *̃)) ≡S ⟩
                      (swap *̃) ((push *̃) S)
                   ∎
                open ≅-Reasoning in
            begin
               braiding ᵇ∇ᶜ (cong ν_ (cong₂ _│_ α (swap∘push S₀)))
               [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P′ │ S′ ] ]
            ≅⟨ reduce-ᵇ∇ᶜ (cong ν_ (cong₂ _│_ α (swap∘push S₀))) _ ⟩
               [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P′ │ S′ ] ]
            ≅⟨ [ν-]-cong (cong₂ _│_ α (swap∘push S₀)) ([-│-]-cong α β (swap∘push S₀) δ) ⟩
               [ ν [ (swap *̃) P″ │ (swap *̃) ((push *̃) S) ] ]
            ∎)

         subcase :
            braiding (ᵇ∇ᶜ {a = x′ •} {τ}) {0} (cong ν_ (cong₂ _│_ α (swap∘push S₀)))
            [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P′ │ S′ ] ] ≡
            π₂ (step⁻ (νᵇ (id*E/E′ ᵇ│ S₀)) (ν [ (repl y *̃) R′ │ S ]))
         subcase
            with step id*E/E′ ((repl y *̃) R′) | inspect (step id*E/E′) ((repl y *̃) R′)
         ... | ◻ , P″ | [ ≡P″ ] = base P″ (,-inj₂ ≡P″)
         ... | [ ._ • ᵇ ] , P″ | [ ≡P″ ] = base P″ (,-inj₂ ≡P″)

      case :
         braiding (ᵇ∇ᶜ {a = x′ •} {τ}) {0} (γ₁ (𝐸 │ᵥᵇ F))
         (tgt (E′/E (⊖₁ (𝐸 │ᵥᵇ F))) (tgt (E ᵇ│ Q₀) [ P │ Q ]))
         ≡
         tgt (E/E′ (⊖₁ (𝐸 │ᵥᵇ F))) (tgt (E′ │ᵥ F) [ P │ Q ])
      case
         with (idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) | step E′ P | step F Q | step (E′/E (⊖₁ 𝐸)) (tgt E P) |
              step ((ᴿ.push *ᵇ) F) ((push *̃) Q) | inspect (idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) | inspect (step E′) P |
              inspect (step F) Q | inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P) | inspect (step ((ᴿ.push *ᵇ) F)) ((push *̃) Q)
      ... | id*E/E′ | [ ._ • ᵇ ] , R′ | _ , S | ◻ , P′ | _ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P′)) (trans (π₁ (ᴬgamma₁ 𝐸 P)) (cong (push ᴬ*̃) (,-inj₁ ≡R′)))))
      ... | id*E/E′ | ◻ , R′ | _ , S | [ ._ • ᵇ ] , P′ | _ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R′))) (trans (sym (π₁ (ᴬgamma₁ 𝐸 P))) (,-inj₁ ≡P′))))
      ... | id*E/E′ | _ , R′ | [ (• ._) ᵇ ] , S | _ , P′ | ◻ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡S′)) (trans (sym (renᵇ-action-comm F push Q)) (cong (push ᴬ*̃) (,-inj₁ ≡S)))))
      ... | id*E/E′ | _ , R′ | ◻ , S | _ , P′ | [ (• ._) ᵇ ] , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡S))) (trans (renᵇ-action-comm F push Q) (,-inj₁ ≡S′))))
      ... | id*E/E′ | ◻ , R′ | ◻ , S | ◻ , P′ | ◻ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         subcase P′ S′ id*E/E′ S R′ ◻ ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′)
      ... | id*E/E′ | ◻ , R′ | [ (• ._) ᵇ ] , S | ◻ , P′ | [ (• ._) ᵇ ] , S′ |
         [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         subcase P′ S′ id*E/E′ S R′ ◻ ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′)
      ... | id*E/E′ | [ ._ • ᵇ ] , R′ | ◻ , S | [ ._ • ᵇ ] , P′ | ◻ , S′ |
         [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         subcase P′ S′ id*E/E′ S R′ ◻ ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′)
      ... | id*E/E′ | [ ._ • ᵇ ] , R′ | [ (• ._) ᵇ ] , S | [ ._ • ᵇ ] , P′ | [ (• ._) ᵇ ] , S′ |
         [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         subcase P′ S′ id*E/E′ S R′ zero ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′)

   module •x
      {x′ : Name Γ} {E : P₀ —[ (• x′) ᵇ - _ ]→ R₀} {E′ : P₀ —[ x • ᵇ - _ ]→ R′₀}
      (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (F : Q₀ —[ (• x) ᵇ - _ ]→ S₀) (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂ (⊖₁ 𝐸))
      (P : ↓ P₀) (Q : ↓ Q₀)
      (IH : braiding (ᵇ∇ᵇ {a = • x′} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      module _
         (P′ : ↓ P′₀) (S′ : ↓ (ᴿ.suc ᴿ.push *) S₀) (id*E/E′ : (idᶠ *) R′₀ —[ (• ᴺ.suc x′) ᵇ - _ ]→ (ᴿ.suc idᶠ *) P″₀)
         (S : ↓ S₀) (R′ : ↓ R′₀) (y : ↓ ᴺ.zero) (≡id*E/E′ : (idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) ≡ id*E/E′) (≡P′ : tgt (E′/E (⊖₁ 𝐸))
         (tgt E P) ≡ P′) (≡S : tgt F Q ≡ S) (≡S′ : tgt ((ᴿ.push *ᵇ) F) ((push *̃) Q) ≡ S′) (≡R′ : tgt E′ P ≡ R′)
         (let α : (idᶠ *) P′₀ ≡ (ᴿ.swap *) ((ᴿ.suc idᶠ *) P″₀)
              α = let open EqReasoning (setoid _) in
                 begin
                    (idᶠ *) P′₀
                 ≡⟨ *-preserves-id P′₀ ⟩
                    P′₀
                 ≡⟨ swap-swap (γ₁ 𝐸) ⟩
                    (ᴿ.swap *) P″₀
                 ≡⟨ cong (ᴿ.swap *) (sym (+-id-elim 1 P″₀)) ⟩
                    (ᴿ.swap *) ((ᴿ.suc idᶠ *) P″₀)
                 ∎)
         where

         base :
            (P″ : ↓ (ᴿ.suc idᶠ *) P″₀) (≡P″ : tgt id*E/E′ ((repl y *̃) R′) ≡ P″) →
            braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} (cong ν_ (cong₂ _│_ α (swap∘push S₀)))
            [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P′ │ S′ ] ] ≡
            [ ν [ (swap *̃) P″ │ (swap *̃) ((push *̃) S) ] ]
         base P″ ≡P″ = ≅-to-≡ (
            let β = (repl ((weaken ᴿ̃.*) y) *̃) P′ ≅ (swap *̃) P″
                β = let open ≅-Reasoning in
                   begin
                      (repl ((weaken ᴿ̃.*) y) *̃) P′
                   ≡⟨ cong (repl ((weaken ᴿ̃.*) y) *̃) (sym ≡P′) ⟩
                      (repl ((weaken ᴿ̃.*) y) *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
                   ≅⟨ ≅-cong✴ ↓_ (sym ((swap-involutive P′₀)))
                              (repl ((weaken ᴿ̃.*) y) *̃) (≅-sym (swap-involutivẽ (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))) ⟩
                      (repl ((weaken ᴿ̃.*) y) *̃) ((swap *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                   ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐸) ((repl ((weaken ᴿ̃.*) y) *̃) ∘ᶠ (swap *̃)) (≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐸) _)) ⟩
                      (repl ((weaken ᴿ̃.*) y) *̃)
                      ((swap *̃) (braiding (ᵇ∇ᵇ {a = • x′} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                   ≡⟨ cong ((repl ((weaken ᴿ̃.*) y) *̃) ∘ᶠ (swap *̃)) IH ⟩
                      (repl ((weaken ᴿ̃.*) y) *̃) ((swap *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)))
                   ≅⟨ id-swap̃ y (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)) ⟩
                      (swap *̃) ((suc (repl y) *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)))
                   ≡⟨ cong (swap *̃) (renᵇ-tgt-comm (E/E′ (⊖₁ 𝐸)) (repl y) (tgt E′ P)) ⟩
                      (swap *̃) (tgt ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸))) ((repl y *̃) (tgt E′ P)))
                   ≡⟨ cong (λ E† → (swap *̃) (tgt E† ((repl y *̃) (tgt E′ P)))) ≡id*E/E′ ⟩
                      (swap *̃) (tgt id*E/E′ ((repl y *̃) (tgt E′ P)))
                   ≡⟨ cong ((swap *̃) ∘ᶠ tgt id*E/E′ ∘ᶠ (repl y *̃)) ≡R′ ⟩
                      (swap *̃) (tgt id*E/E′ ((repl y *̃) R′))
                   ≡⟨ cong (swap *̃) ≡P″ ⟩
                      (swap *̃) P″
                   ∎
                δ : S′ ≅ (swap *̃) ((push *̃) S)
                δ = let open ≅-Reasoning in
                   begin
                      S′
                   ≡⟨ sym ≡S′ ⟩
                      tgt ((ᴿ.push *ᵇ) F) ((push *̃) Q)
                   ≡⟨ sym (renᵇ-tgt-comm F push Q) ⟩
                      (suc push *̃) (tgt F Q)
                   ≅⟨ swap∘push̃ _ ⟩
                      (swap *̃) ((push *̃) (tgt F Q))
                   ≡⟨ cong ((swap *̃) ∘ᶠ (push *̃)) ≡S ⟩
                      (swap *̃) ((push *̃) S)
                   ∎
                open ≅-Reasoning in
            begin
               braiding ᵇ∇ᶜ (cong ν_ (cong₂ _│_ α (swap∘push S₀)))
               [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P′ │ S′ ] ]
            ≅⟨ reduce-ᵇ∇ᶜ (cong ν_ (cong₂ _│_ α (swap∘push S₀))) _ ⟩
               [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P′ │ S′ ] ]
            ≅⟨ [ν-]-cong (cong₂ _│_ α (swap∘push S₀)) ([-│-]-cong α β (swap∘push S₀) δ) ⟩
               [ ν [ (swap *̃) P″ │ (swap *̃) ((push *̃) S) ] ]
            ∎)

         subcase :
            braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} (cong ν_ (cong₂ _│_ α (swap∘push S₀)))
            [ ν [ (repl ((weaken ᴿ̃.*) y) *̃) P′ │ S′ ] ] ≡
            π₂ (step⁻ (νᵇ (id*E/E′ ᵇ│ S₀)) (ν [ (repl y *̃) R′ │ S ]))
         subcase
            with step id*E/E′ ((repl y *̃) R′) | inspect (step id*E/E′) ((repl y *̃) R′)
         ... | ◻ , P″ | [ ≡P″ ] = base P″ (,-inj₂ ≡P″)
         ... | [ (• ._) ᵇ ] , P″ | [ ≡P″ ] = base P″ (,-inj₂ ≡P″)

      case :
         braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} (γ₁ (𝐸 │ᵥᵇ F))
         (tgt (E′/E (⊖₁ (𝐸 │ᵥᵇ F))) (tgt (E ᵇ│ Q₀) [ P │ Q ]))
         ≡
         tgt (E/E′ (⊖₁ (𝐸 │ᵥᵇ F))) (tgt (E′ │ᵥ F) [ P │ Q ])
      case
         with (idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) | step E′ P | step F Q | step (E′/E (⊖₁ 𝐸)) (tgt E P) |
              step ((ᴿ.push *ᵇ) F) ((push *̃) Q) | inspect (idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) | inspect (step E′) P |
              inspect (step F) Q | inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P) | inspect (step ((ᴿ.push *ᵇ) F)) ((push *̃) Q)
      ... | id*E/E′ | [ ._ • ᵇ ] , R′ | _ , S | ◻ , P′ | _ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P′)) (trans (π₁ (ᴬgamma₁ 𝐸 P)) (cong (push ᴬ*̃) (,-inj₁ ≡R′)))))
      ... | id*E/E′ | ◻ , R′ | _ , S | [ ._ • ᵇ ] , P′ | _ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R′))) (trans (sym (π₁ (ᴬgamma₁ 𝐸 P))) (,-inj₁ ≡P′))))
      ... | id*E/E′ | _ , R′ | [ (• ._) ᵇ ] , S | _ , P′ | ◻ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡S′)) (trans (sym (renᵇ-action-comm F push Q)) (cong (push ᴬ*̃) (,-inj₁ ≡S)))))
      ... | id*E/E′ | _ , R′ | ◻ , S | _ , P′ | [ (• ._) ᵇ ] , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡S))) (trans (renᵇ-action-comm F push Q) (,-inj₁ ≡S′))))
      ... | id*E/E′ | ◻ , R′ | ◻ , S | ◻ , P′ | ◻ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         subcase P′ S′ id*E/E′ S R′ ◻ ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′)
      ... | id*E/E′ | ◻ , R′ | [ (• ._) ᵇ ] , S | ◻ , P′ | [ (• ._) ᵇ ] , S′ |
         [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         subcase P′ S′ id*E/E′ S R′ ◻ ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′)
      ... | id*E/E′ | [ ._ • ᵇ ] , R′ | ◻ , S | [ ._ • ᵇ ] , P′ | ◻ , S′ |
         [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         subcase P′ S′ id*E/E′ S R′ ◻ ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′)
      ... | id*E/E′ | [ ._ • ᵇ ] , R′ | [ (• ._) ᵇ ] , S | [ ._ • ᵇ ] , P′ | [ (• ._) ᵇ ] , S′ |
         [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         subcase P′ S′ id*E/E′ S R′ zero ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′)
