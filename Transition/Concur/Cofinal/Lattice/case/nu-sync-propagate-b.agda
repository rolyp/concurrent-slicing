open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common

module Transition.Concur.Cofinal.Lattice.case.nu-sync-propagate-b
   {Γ} {x : Name Γ} {P₀ Q₀ R₀ R′₀ S₀}
   where

   import Relation.Binary.EqReasoning as EqReasoning
   import Name as ᴺ
   import Ren as ᴿ

{-
   module x•
      {x′ : Name Γ} {E : P₀ —[ x′ • ᵇ - _ ]→ R₀} {E′ : P₀ —[ x • ᵇ - _ ]→ R′₀}
      (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (F : Q₀ —[ (• x) ᵇ - _ ]→ S₀) (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂ (⊖₁ 𝐸))
      (P : ↓ P₀) (Q : ↓ Q₀)
      (IH : braiding (ᵇ∇ᵇ {a = x′ •} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      module _
         (P′ : ↓ P′₀) (S′ : ↓ (ᴿ.suc ᴿ.push *) S₀)  (S : ↓ S₀) (R′ : ↓ R′₀)
         (≡P′ : tgt (E′/E (⊖₁ 𝐸)) (tgt E P) ≡ P′) (≡S : tgt F Q ≡ S) (≡S′ : tgt ((ᴿ.push *ᵇ) F) ((push *̃) Q) ≡ S′)
         (≡R′ : tgt E′ P ≡ R′)
         (let α : P′₀ ≡ (ᴿ.swap *) P″₀
              α = swap-swap (γ₁ 𝐸))
         where

         base :
            (P″ : ↓ P″₀) (≡P″ : tgt (E/E′ (⊖₁ 𝐸)) R′ ≡ P″) →
            braiding (ᵇ∇ᶜ {a = x′ •} {τ}) {0} (cong ν_ (cong₂ _│_ α (swap∘push S₀)))
            [ ν [ P′ │ S′ ] ]
            ≡
            [ ν [ (swap *̃) P″ │ (swap *̃) ((push *̃) S) ] ]
         base P″ ≡P″ = ≅-to-≡ (
            let β = P′ ≅ (swap *̃) P″
                β = let open ≅-Reasoning in
                   begin
                      P′
                   ≡⟨ sym ≡P′ ⟩
                      tgt (E′/E (⊖₁ 𝐸)) (tgt E P)
                   ≅⟨ ≅-sym (swap-involutivẽ (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))) ⟩
                      (swap *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))
                   ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐸) (swap *̃) (≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐸) _)) ⟩
                      (swap *̃) (braiding (ᵇ∇ᵇ {a = x′ •} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))
                   ≡⟨ cong (swap *̃) IH ⟩
                      (swap *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
                   ≡⟨ cong ((swap *̃) ∘ᶠ tgt (E/E′ (⊖₁ 𝐸))) ≡R′ ⟩
                      (swap *̃) (tgt (E/E′ (⊖₁ 𝐸)) R′)
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
               [ ν [ P′ │ S′ ] ]
            ≅⟨ reduce-ᵇ∇ᶜ (cong ν_ (cong₂ _│_ α (swap∘push S₀))) _ ⟩
               [ ν [ P′ │ S′ ] ]
            ≅⟨ [ν-]-cong (cong₂ _│_ α (swap∘push S₀)) ([-│-]-cong α β (swap∘push S₀) δ) ⟩
               [ ν [ (swap *̃) P″ │ (swap *̃) ((push *̃) S) ] ]
            ∎)

         subcase :
            braiding (ᵇ∇ᶜ {a = x′ •} {τ}) {0} (cong ν_ (cong₂ _│_ α (swap∘push S₀)))
            [ ν [ P′ │ S′ ] ]
            ≡
            π₂ (step⁻ (νᵇ (E/E′ (⊖₁ 𝐸) ᵇ│ S₀)) (ν [ R′ │ S ]))
         subcase
            with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
         ... | ◻ , P″ | [ ≡P″ ] = base P″ (,-inj₂ ≡P″)
         ... | [ ._ • ᵇ ] , P″ | [ ≡P″ ] = base P″ (,-inj₂ ≡P″)

      case :
         braiding (ᵇ∇ᶜ {a = x′ •} {τ}) {0} (γ₁ (𝐸 │ᵥᵇ F))
         (tgt (E′/E (⊖₁ (𝐸 │ᵥᵇ F))) (tgt (E ᵇ│ Q₀) [ P │ Q ]))
         ≡
         tgt (E/E′ (⊖₁ (𝐸 │ᵥᵇ F))) (tgt (E′ │ᵥ F) [ P │ Q ])
      case
         with step E′ P | step F Q | step (E′/E (⊖₁ 𝐸)) (tgt E P) |
              step ((ᴿ.push *ᵇ) F) ((push *̃) Q) | inspect (step E′) P |
              inspect (step F) Q | inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P) | inspect (step ((ᴿ.push *ᵇ) F)) ((push *̃) Q)
      ... | [ ._ • ᵇ ] , R′ | _ , S | ◻ , P′ | _ , S′ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P′)) (trans (π₁ (ᴬgamma₁ 𝐸 P)) (cong (push ᴬ*̃) (,-inj₁ ≡R′)))))
      ... | ◻ , R′ | _ , S | [ ._ • ᵇ ] , P′ | _ , S′ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R′))) (trans (sym (π₁ (ᴬgamma₁ 𝐸 P))) (,-inj₁ ≡P′))))
      ... | _ , R′ | [ • ._ ﹙ _ ﹚ ᵇ ] , S | _ , P′ | ◻ , S′ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡S′)) (trans (sym (renᵇ-action-comm F push Q)) (cong (push ᴬ*̃) (,-inj₁ ≡S)))))
      ... | _ , R′ | ◻ , S | _ , P′ | [ • ._ ﹙ _ ﹚ ᵇ ] , S′ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡S))) (trans (renᵇ-action-comm F push Q) (,-inj₁ ≡S′))))
      ... | ◻ , R′ | ◻ , S | ◻ , P′ | ◻ , S′ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         {!!} -- subcase P′ S′ S R′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′)
      ... | ◻ , R′ | [ • ._ ﹙ _ ﹚ ᵇ ] , S | ◻ , P′ | [ • ._ ﹙ _ ﹚ ᵇ ] , S′ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         {!!} -- subcase P′ S′ S R′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′)
      ... | [ ._ • ᵇ ] , R′ | ◻ , S | [ ._ • ᵇ ] , P′ | ◻ , S′ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         {!!} -- subcase P′ S′ S R′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′)
      ... | [ ._ • ᵇ ] , R′ | [ • ._ ﹙ _ ﹚ ᵇ ] , S | [ ._ • ᵇ ] , P′ | [ • ._ ﹙ _ ﹚ ᵇ ] , S′ |
         [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         {!!} -- subcase P′ S′ S R′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′)
-}

   module •x
      {x′ : Name Γ} {E : P₀ —[ (• x′) ᵇ - _ ]→ R₀} {E′ : P₀ —[ x • ᵇ - _ ]→ R′₀}
      (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (F : Q₀ —[ (• x) ᵇ - _ ]→ S₀) (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂ (⊖₁ 𝐸))
      (P : ↓ P₀) (Q : ↓ Q₀)
      (IH : braiding (ᵇ∇ᵇ {a = • x′} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      module _
         (id*E/E′ : (idᶠ *) R′₀ —[ (• ᴺ.suc x′) ᵇ - _ ]→ (ᴿ.suc idᶠ *) (tgt₂ (⊖₁ 𝐸))) (P′ : ↓ P′₀)
         (S′ : ↓ (ᴿ.suc ᴿ.push *) S₀) (S : ↓ S₀) (R′ : ↓ R′₀) (y : ↓ ᴺ.zero {ᴺ.suc Γ}) (y′ : ↓ ᴺ.zero {Γ})
         (≡id*E/E′ : (idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) ≡ id*E/E′) (≡P′ : tgt (E′/E (⊖₁ 𝐸)) (tgt E P) ≡ P′) (≡S : tgt F Q ≡ S)
         (≡S′ : tgt ((ᴿ.push *ᵇ) F) ((push *̃) Q) ≡ S′) (≡R′ : tgt E′ P ≡ R′) (≡y : weaken ̃ y′ ≡ y)
         (let α = let open EqReasoning (setoid _) in
                begin
                   (idᶠ *) P′₀
                ≡⟨ *-preserves-id P′₀ ⟩
                   P′₀
                ≡⟨ swap-swap (γ₁ 𝐸) ⟩
                   (ᴿ.swap *) P″₀
                ≡⟨ cong (ᴿ.swap *) (sym (+-id-elim 1 P″₀)) ⟩
                   (ᴿ.swap *) ((ᴿ.suc idᶠ *) P″₀)
                ∎) where

         base :
            (P″ : ↓ ((ᴿ.suc idᶠ *) P″₀)) (≡P″ : tgt id*E/E′ ((repl y′ *̃) R′) ≡ P″) →
            braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} (cong ν_ (cong₂ _│_ α (swap∘push S₀)))
            [ ν [ (repl y *̃) P′ │ S′ ] ]
            ≡
            [ ν [ (swap *̃) P″ │ (swap *̃) ((push *̃) S) ] ]
         base P″ ≡P″ = ≅-to-≡ (
            let β = (repl y *̃) P′ ≅ (swap *̃) P″
                β = let open ≅-Reasoning in
                   begin
                      (repl y *̃) P′
                   ≡⟨ cong ((repl y *̃)) (sym ≡P′) ⟩
                      (repl y *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
                   ≅⟨ ≅-cong✴ ↓_ (sym (swap-involutive P′₀))
                              (repl y *̃) (≅-sym (swap-involutivẽ (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))) ⟩
                      (repl y *̃) ((swap *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                   ≡⟨ cong (λ y† → (repl y† *̃) ((swap *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))) (sym ≡y) ⟩
                      (repl (weaken ̃ y′) *̃) ((swap *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                   ≅⟨ id-swap-id̃ y′ _ ⟩
                      (swap *̃) ((suc (repl y′) *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                   ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐸) ((swap *̃) ∘ᶠ (suc (repl y′) *̃)) (≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐸) _)) ⟩
                      (swap *̃)
                      ((suc (repl y′) *̃) (braiding (ᵇ∇ᵇ {a = • x′} {x •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                   ≡⟨ cong ((swap *̃) ∘ᶠ (suc (repl y′) *̃)) IH ⟩
                      (swap *̃) ((suc (repl y′) *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)))
                   ≡⟨ cong ((swap *̃) ∘ᶠ (suc (repl y′) *̃) ∘ᶠ tgt (E/E′ (⊖₁ 𝐸))) ≡R′ ⟩
                      (swap *̃) ((suc (repl y′) *̃) (tgt (E/E′ (⊖₁ 𝐸)) R′))
                   ≡⟨ cong (swap *̃) (renᵇ-tgt-comm (E/E′ (⊖₁ 𝐸)) (repl y′) R′) ⟩
                      (swap *̃) (tgt ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸))) ((repl y′ *̃) R′))
                   ≡⟨ cong (λ E† → (swap *̃) (tgt E† ((repl y′ *̃) R′))) ≡id*E/E′ ⟩
                      (swap *̃) (tgt id*E/E′ ((repl y′ *̃) R′))
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
               [ ν [ (repl y *̃) P′ │ S′ ] ]
            ≅⟨ reduce-ᵇ∇ᶜ (cong ν_ (cong₂ _│_ α (swap∘push S₀))) _ ⟩
               [ ν [ (repl y *̃) P′ │ S′ ] ]
            ≅⟨ [ν-]-cong (cong₂ _│_ α (swap∘push S₀)) ([-│-]-cong α β (swap∘push S₀) δ) ⟩
               [ ν [ (swap *̃) P″ │ (swap *̃) ((push *̃) S) ] ]
            ∎)

         subcase :
            braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} (cong ν_ (cong₂ _│_ α (swap∘push S₀)))
            [ ν [ (repl y *̃) P′ │ S′ ] ]
            ≡
            tgt (νᵇ (id*E/E′ ᵇ│ S₀)) [ ν [ (repl y′ *̃) R′ │ S ] ]
         subcase
            with step id*E/E′ ((repl y′ *̃) R′) | inspect (step id*E/E′) ((repl y′ *̃) R′)
         ... | ◻ , P″ | [ ≡P″ ] = base P″ (,-inj₂ ≡P″)
         ... | [ • ._ ﹙ ◻ ﹚ ᵇ ] , P″ | [ ≡P″ ] = base P″ (,-inj₂ ≡P″)
         ... | [ • ._ ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , P″ | [ ≡P″ ] = base P″ (,-inj₂ ≡P″)

      case :
         braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} (γ₁ (𝐸 │ᵥᵇ F))
         (tgt (E′/E (⊖₁ (𝐸 │ᵥᵇ F))) (tgt (E ᵇ│ Q₀) [ P │ Q ]))
         ≡
         tgt (E/E′ (⊖₁ (𝐸 │ᵥᵇ F))) (tgt (E′ │ᵥ F) [ P │ Q ])
      case
         with (idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) | step E′ P | step F Q | step (E′/E (⊖₁ 𝐸)) (tgt E P) |
              step ((ᴿ.push *ᵇ) F) ((push *̃) Q) | inspect (idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) | inspect (step E′) P |
              inspect (step F) Q | inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P) | inspect (step ((ᴿ.push *ᵇ) F)) ((push *̃) Q)
      ... | _ | [ ._ • ᵇ ] , R′ | _ , S | ◻ , P′ | _ , S′ | _ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P′)) (trans (π₁ (ᴬgamma₁ 𝐸 P)) (cong (push ᴬ*̃) (,-inj₁ ≡R′)))))
      ... | _ | ◻ , R′ | _ , S | [ ._ • ᵇ ] , P′ | _ , S′ | _ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R′))) (trans (sym (π₁ (ᴬgamma₁ 𝐸 P))) (,-inj₁ ≡P′))))
      ... | _ | _ , R′ | [ • ._ ﹙ _ ﹚ ᵇ ] , S | _ , P′ | ◻ , S′ | _ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡S′)) (trans (sym (renᵇ-action-comm F push Q)) (cong (push ᴬ*̃) (,-inj₁ ≡S)))))
      ... | _ | _ , R′ | ◻ , S | _ , P′ | [ • ._ ﹙ _ ﹚ ᵇ ] , S′ | _ | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡S))) (trans (renᵇ-action-comm F push Q) (,-inj₁ ≡S′))))
      ... | id*E/E′ | ◻ , R′ | ◻ , S | ◻ , P′ | ◻ , S′ |
         [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         subcase id*E/E′ P′ S′ S R′ ◻ ◻ ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′) refl
      ... | id*E/E′ | ◻ , R′ | [ • .x ﹙ ◻ ﹚ ᵇ ] , S | ◻ , P′ | [ • .(ᴺ.suc x) ﹙ ◻ ﹚ ᵇ ] , S′ |
         [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         subcase id*E/E′ P′ S′ S R′ ◻ ◻ ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′) refl
      ... | id*E/E′ | ◻ , R′ | [ • .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , S | ◻ , P′ | [ • .(ᴺ.suc x) ﹙ ◻ ﹚ ᵇ ] , S′ |
         [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] = {!!}
         let α :  [ • ᴺ.suc x ﹙ ◻ ﹚ ᵇ ] ≡ [ • ᴺ.suc x ﹙ [ ᴺ.zero ] ﹚ ᵇ ]
             α = let open EqReasoning (setoid _) in
                begin
                   [ • ᴺ.suc x ﹙ ◻ ﹚ ᵇ ]
                ≡⟨ sym (,-inj₁ ≡S′) ⟩
                   action ((ᴿ.push *ᵇ) F) ((push *̃) Q)
                ≡⟨ sym (renᵇ-action-comm F push Q) ⟩
                   (push ᴬ*̃) (action F Q)
                ≡⟨ {!!} ⟩
                   (push ᴬ*̃) [ • x ﹙ [ ᴺ.zero ] ﹚ ᵇ ]
                ≡⟨ {!!} ⟩
                   [ • ᴺ.suc x ﹙ [ ᴺ.zero ] ﹚ ᵇ ]
                ∎ in
         {!!}
      ... | id*E/E′ | ◻ , R′ | [ • .x ﹙ ◻ ﹚ ᵇ ] , S | ◻ , P′ | [ • .(ᴺ.suc x) ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , S′ |
         [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] = {!!}
      ... | id*E/E′ | ◻ , R′ | [ • .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , S | ◻ , P′ | [ • .(ᴺ.suc x) ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , S′ |
         [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         subcase id*E/E′ P′ S′ S R′ [ ᴺ.zero ] [ ᴺ.zero ] ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′) refl
      ... | id*E/E′ | [ ._ • ᵇ ] , R′ | ◻ , S | [ ._ • ᵇ ] , P′ | ◻ , S′ |
         [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         subcase id*E/E′ P′ S′ S R′ ◻ ◻ ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′) refl
      ... | id*E/E′ | [ ._ • ᵇ ] , R′ | [ • ._ ﹙ y ﹚ ᵇ ] , S | [ ._ • ᵇ ] , P′ | [ • ._ ﹙ y′ ﹚ ᵇ ] , S′ |
         [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
         subcase id*E/E′ P′ S′ S R′ y′ y ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′) trustMe
