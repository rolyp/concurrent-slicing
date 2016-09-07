open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common

module Transition.Concur.Cofinal.Lattice.case.propagate-c-nu-sync
   {Γ} {x : Name Γ} {P₀ Q₀} where

   import Relation.Binary.EqReasoning as EqReasoning

   import Name as ᴺ
   import Ren as ᴿ
   import Ren.Lattice as ᴿ̃
   import Transition as ᵀ

   module •x〈y〉
      {R₀ S₀ S′₀} {x′ y : Name Γ} {F : Q₀ —[ • x′ 〈 y 〉 ᶜ - _ ]→ S₀} {F′ : Q₀ —[ (• x) ᵇ - _ ]→ S′₀}
      (E : P₀ —[ x • ᵇ - _ ]→ R₀) (𝐹 : F ⌣₁[ ᶜ∇ᵇ ] F′) (let Q′₀ = tgt₁ (⊖₁ 𝐹); Q″₀ = tgt₂ (⊖₁ 𝐹))
      (P : ↓ P₀) (Q : ↓ Q₀)
      (IH : braiding (ᶜ∇ᵇ {a = • x′ 〈 y 〉} {• x}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡ tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q))
      where

      module _
         (R : ↓ R₀) (S′ : ↓ S′₀) (P′ : ↓ Q′₀) (y′ y″ : ↓ ᴺ.zero {Γ}) (≡R : tgt E P ≡ R) (≡S′ : tgt F′ Q ≡ S′)
         (≡P′ : tgt (E′/E (⊖₁ 𝐹)) (tgt F Q) ≡ P′) (≡y″ : y′ ≡ y″)
         where

         base :
            (Q″ : ↓ Q″₀) (≡Q″ : tgt (E/E′ (⊖₁ 𝐹)) S′ ≡ Q″) →
            braiding (ᶜ∇ᶜ {a = • x′ 〈 y 〉} {τ}) {0} (cong ν_ (cong₂ _│_ refl (γ₁ 𝐹)))
            [ ν [ (repl y′ *̃) R │ P′ ] ]
            ≡
            [ ν [ (repl y″ *̃) R │ Q″ ] ]

         base Q″ ≡Q″ =
            let α : ν ((idᶠ *) R₀ │ tgt₁ (⊖₁ 𝐹)) ≡ ν ((idᶠ *) R₀ │ Proc↱ refl (tgt₂ (⊖₁ 𝐹)))
                α = cong ν_ (cong₂ _│_ refl (γ₁ 𝐹))
                δ : P′ ≅ Q″
                δ = let open ≅-Reasoning in
                   begin
                      P′
                   ≡⟨ sym ≡P′ ⟩
                      tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)
                   ≅⟨ ≅-sym (reduce-ᶜ∇ᵇ (γ₁ 𝐹) _) ⟩
                      braiding (ᶜ∇ᵇ {a = • x′ 〈 y 〉} {• x}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q))
                   ≡⟨ IH ⟩
                      (tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q))
                   ≡⟨ cong (tgt (E/E′ (⊖₁ 𝐹))) ≡S′ ⟩
                      (tgt (E/E′ (⊖₁ 𝐹)) S′)
                   ≡⟨ ≡Q″ ⟩
                      Q″
                   ∎
                open ≅-Reasoning in ≅-to-≡ (
            begin
               braiding (ᶜ∇ᶜ {a = • x′ 〈 y 〉} {τ}) {0} α
               [ ν [ (repl y′ *̃) R │ P′ ] ]
            ≅⟨ reduce-ᶜ∇ᶜ α _ ⟩
               [ ν [ (repl y′ *̃) R │ P′ ] ]
            ≅⟨ [ν-]-cong (cong₂ _│_ refl (γ₁ 𝐹))
                         ([-│-]-cong refl (≡-to-≅ (cong (λ y† → (repl y† *̃) R) ≡y″)) (γ₁ 𝐹) δ) ⟩
               [ ν [ (repl y″ *̃) R │ Q″ ] ]
            ∎)

         subcase :
            braiding (ᶜ∇ᶜ {a = • x′ 〈 y 〉} {τ}) {0} (cong ν_ (cong₂ _│_ refl (γ₁ 𝐹)))
            [ ν [ (repl y′ *̃) R │ P′ ] ]
            ≡
            tgt (νᶜ ((idᶠ *) R₀ │ᶜ E/E′ (⊖₁ 𝐹))) [ ν [ (repl y″ *̃) R │ S′ ] ]
         subcase
            with step (E/E′ (⊖₁ 𝐹)) S′ | inspect (step (E/E′ (⊖₁ 𝐹))) S′
         ... | ◻ , Q″ | [ ≡Q″ ] = base Q″ (,-inj₂ ≡Q″)
         ... | [ • ._ 〈 ◻ 〉 ᶜ ] , Q″ | [ ≡Q″ ] = base Q″ (,-inj₂ ≡Q″)
         ... | [ • .(ᴺ.suc x′) 〈 [ .(ᴺ.suc y) ] 〉 ᶜ ] , Q″ | [ ≡Q″ ] = base Q″ (,-inj₂ ≡Q″)

      case :
         braiding (ᶜ∇ᶜ {a = • x′ 〈 y 〉} {τ}) {0} (cong ν_ (cong₂ _│_ refl (γ₁ 𝐹)))
         (tgt (E │ᵥ E′/E (⊖₁ 𝐹)) (tgt (P₀ │ᶜ F) [ P │ Q ]))
         ≡
         tgt (νᶜ ((idᶠ *) (ᵀ.tgt E) │ᶜ E/E′ (⊖₁ 𝐹))) (tgt (E │ᵥ F′) [ P │ Q ])
      case
         with step E P | step F′ Q | step (E′/E (⊖₁ 𝐹)) (tgt F Q) |
              inspect (step E) P | inspect (step F′) Q | inspect (step (E′/E (⊖₁ 𝐹))) (tgt F Q)
      case | _ , R | ◻ , S′ | [ _ ] , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡S′)) (trans (sym (π₁ (ᴬgamma₁ 𝐹 Q))) (,-inj₁ ≡P′))))
      case | _ , R | [ _ ] , S′ | ◻ , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         ⊥-elim (◻≢[-] (trans (,-inj₁ (sym ≡P′)) (trans (π₁ (ᴬgamma₁ 𝐹 Q)) (,-inj₁ ≡S′))))
      case | _ , R | [ • .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , S′ | [ • .x ﹙ ◻ ﹚ ᵇ ] , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         let α = trans (sym (,-inj₁ ≡S′)) (trans (sym (π₁ (ᴬgamma₁ 𝐹 Q))) (,-inj₁ ≡P′)) in
         ⊥-elim ([•x﹙◻﹚ᵇ]≢[•x﹙[zero]﹚ᵇ] (sym α))
      case | _ , R | [ • .x ﹙ ◻ ﹚ ᵇ ] , S′ | [ • .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         let α = trans (sym (,-inj₁ ≡S′)) (trans (sym (π₁ (ᴬgamma₁ 𝐹 Q))) (,-inj₁ ≡P′)) in
         ⊥-elim ([•x﹙◻﹚ᵇ]≢[•x﹙[zero]﹚ᵇ] α)
      case | ◻ , R | ◻ , S′ | ◻ , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         subcase R S′ P′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P′) refl
      case | ◻ , R | [ • .x ﹙ ◻ ﹚ ᵇ ] , S′ | [ • .x ﹙ ◻ ﹚ ᵇ ] , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         subcase R S′ P′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P′) refl
      case | ◻ , R | [ • .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , S′ | [ • .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         subcase R S′ P′ [ ᴺ.zero ] [ ᴺ.zero ] (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P′) refl
      case | [ .x • ᵇ ] , R | ◻ , S′ | ◻ , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         subcase R S′ P′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P′) refl
      case | [ .x • ᵇ ] , R | [ • .x ﹙ ◻ ﹚ ᵇ ] , S′ | [ • .x ﹙ ◻ ﹚ ᵇ ] , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         subcase R S′ P′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P′) refl
      case | [ .x • ᵇ ] , R | [ • .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , S′ | [ • .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         subcase R S′ P′ [ ᴺ.zero ] [ ᴺ.zero ] (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P′) refl

   module τ
      {R₀ S₀ S′₀} {F : Q₀ —[ τ ᶜ - _ ]→ S₀} {F′ : Q₀ —[ (• x) ᵇ - _ ]→ S′₀}
      (E : P₀ —[ x • ᵇ - _ ]→ R₀) (𝐹 : F ⌣₁[ ᶜ∇ᵇ ] F′) (let Q′₀ = tgt₁ (⊖₁ 𝐹); Q″₀ = tgt₂ (⊖₁ 𝐹))
      (P : ↓ P₀) (Q : ↓ Q₀)
      (IH : braiding (ᶜ∇ᵇ {a = τ} {• x}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡ tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q))
      where

      module _
         (R : ↓ R₀) (S′ : ↓ S′₀) (P′ : ↓ Q′₀) (y′ y″ : ↓ ᴺ.zero {Γ}) (≡R : tgt E P ≡ R) (≡S′ : tgt F′ Q ≡ S′)
         (≡P′ : tgt (E′/E (⊖₁ 𝐹)) (tgt F Q) ≡ P′) (≡y″ : y′ ≡ y″)
         where

         base :
            (Q″ : ↓ Q″₀) (≡Q″ : tgt (E/E′ (⊖₁ 𝐹)) S′ ≡ Q″) →
            braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (cong ν_ (cong₂ _│_ refl (γ₁ 𝐹)))
            [ ν [ (repl y′ *̃) R │ P′ ] ]
            ≡
            [ ν [ (repl y″ *̃) R │ Q″ ] ]
         base Q″ ≡Q″ =
            let α : ν ((idᶠ *) R₀ │ tgt₁ (⊖₁ 𝐹)) ≡ ν ((idᶠ *) R₀ │ Proc↱ refl (tgt₂ (⊖₁ 𝐹)))
                α = cong ν_ (cong₂ _│_ refl (γ₁ 𝐹))
                δ : P′ ≅ Q″
                δ = let open ≅-Reasoning in
                   begin
                      P′
                   ≡⟨ sym ≡P′ ⟩
                      tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)
                   ≅⟨ ≅-sym (reduce-ᶜ∇ᵇ (γ₁ 𝐹) _) ⟩
                      braiding (ᶜ∇ᵇ {a = τ} {• x}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q))
                   ≡⟨ IH ⟩
                      (tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q))
                   ≡⟨ cong (tgt (E/E′ (⊖₁ 𝐹))) ≡S′ ⟩
                      (tgt (E/E′ (⊖₁ 𝐹)) S′)
                   ≡⟨ ≡Q″ ⟩
                      Q″
                   ∎
                open ≅-Reasoning in ≅-to-≡ (
            begin
               braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} α [ ν [ (repl y′ *̃) R │ P′ ] ]
            ≅⟨ reduce-ᶜ∇ᶜ α _ ⟩
               [ ν [ (repl y′ *̃) R │ P′ ] ]
            ≅⟨ [ν-]-cong (cong₂ _│_ refl (γ₁ 𝐹))
                         ([-│-]-cong refl (≡-to-≅ (cong (λ y† → (repl y† *̃) R) ≡y″)) (γ₁ 𝐹) δ) ⟩
               [ ν [ (repl y″ *̃) R │ Q″ ] ]
            ∎)

         subcase :
            braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (cong ν_ (cong₂ _│_ refl (γ₁ 𝐹)))
            [ ν [ (repl y′ *̃) R │ P′ ] ]
            ≡
            tgt (νᶜ ((idᶠ *) R₀ │ᶜ E/E′ (⊖₁ 𝐹))) [ ν [ (repl y″ *̃) R │ S′ ] ]
         subcase with step (E/E′ (⊖₁ 𝐹)) S′ | inspect (step (E/E′ (⊖₁ 𝐹))) S′
         ... | ◻ , Q″ | [ ≡Q″ ] = base Q″ (,-inj₂ ≡Q″)
         ... | [ τ ᶜ ] , Q″ | [ ≡Q″ ] = base Q″ (,-inj₂ ≡Q″)

      case :
         braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (cong ν_ (cong₂ _│_ refl (γ₁ 𝐹)))
         (tgt (E │ᵥ E′/E (⊖₁ 𝐹)) (tgt (P₀ │ᶜ F) [ P │ Q ]))
         ≡
         tgt (νᶜ ((idᶠ *) (ᵀ.tgt E) │ᶜ E/E′ (⊖₁ 𝐹))) (tgt (E │ᵥ F′) [ P │ Q ])
      case
         with step E P | step F′ Q | step (E′/E (⊖₁ 𝐹)) (tgt F Q) |
              inspect (step E) P | inspect (step F′) Q | inspect (step (E′/E (⊖₁ 𝐹))) (tgt F Q)
      case | ◻ , R | ◻ , S′ | [ _ ] , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡S′)) (trans (sym (π₁ (ᴬgamma₁ 𝐹 Q))) (,-inj₁ ≡P′))))
      case | ◻ , R | [ _ ] , S′ | ◻ , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         ⊥-elim (◻≢[-] (trans (,-inj₁ (sym ≡P′)) (trans (π₁ (ᴬgamma₁ 𝐹 Q)) (,-inj₁ ≡S′))))
      case | ◻ , R | [ • .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , S′ | [ • .x ﹙ ◻ ﹚ ᵇ ] , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         let α = trans (sym (,-inj₁ ≡S′)) (trans (sym (π₁ (ᴬgamma₁ 𝐹 Q))) (,-inj₁ ≡P′)) in
         ⊥-elim ([•x﹙◻﹚ᵇ]≢[•x﹙[zero]﹚ᵇ] (sym α))
      case | ◻ , R | [ • .x ﹙ ◻ ﹚ ᵇ ] , S′ | [ • .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         let α = trans (sym (,-inj₁ ≡S′)) (trans (sym (π₁ (ᴬgamma₁ 𝐹 Q))) (,-inj₁ ≡P′)) in
         ⊥-elim ([•x﹙◻﹚ᵇ]≢[•x﹙[zero]﹚ᵇ] α)
      case | [ .x • ᵇ ] , R | ◻ , S′ | [ _ ] , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡S′)) (trans (sym (π₁ (ᴬgamma₁ 𝐹 Q))) (,-inj₁ ≡P′))))
      case | [ .x • ᵇ ] , R | [ _ ] , S′ | ◻ , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         ⊥-elim (◻≢[-] (trans (,-inj₁ (sym ≡P′)) (trans (π₁ (ᴬgamma₁ 𝐹 Q)) (,-inj₁ ≡S′))))
      case | [ .x • ᵇ ] , R | [ • .x ﹙ ◻ ﹚ ᵇ ] , S′ | [ • .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         let α = trans (sym (,-inj₁ ≡S′)) (trans (sym (π₁ (ᴬgamma₁ 𝐹 Q))) (,-inj₁ ≡P′)) in
         ⊥-elim ([•x﹙◻﹚ᵇ]≢[•x﹙[zero]﹚ᵇ] α)
      case | [ .x • ᵇ ] , R | [ • .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , S′ | [ • .x ﹙ ◻ ﹚ ᵇ ] , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         let α = trans (sym (,-inj₁ ≡S′)) (trans (sym (π₁ (ᴬgamma₁ 𝐹 Q))) (,-inj₁ ≡P′)) in
         ⊥-elim ([•x﹙◻﹚ᵇ]≢[•x﹙[zero]﹚ᵇ] (sym α))
      case | ◻ , R | ◻ , S′ | ◻ , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         subcase R S′ P′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P′) refl
      case | ◻ , R | [ • .x ﹙ ◻ ﹚ ᵇ ] , S′ | [ • .x ﹙ ◻ ﹚ ᵇ ] , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         subcase R S′ P′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P′) refl
      case | ◻ , R | [ • .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , S′ | [ • .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         subcase R S′ P′ [ ᴺ.zero ] [ ᴺ.zero ] (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P′) refl
      case | [ .x • ᵇ ] , R | ◻ , S′ | ◻ , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         subcase R S′ P′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P′) refl
      case | [ .x • ᵇ ] , R | [ • .x ﹙ ◻ ﹚ ᵇ ] , S′ | [ • .x ﹙ ◻ ﹚ ᵇ ] , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         subcase R S′ P′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P′) refl
      case | [ .x • ᵇ ] , R | [ • .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , S′ | [ • .x ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] =
         subcase R S′ P′ [ ᴺ.zero ] [ ᴺ.zero ] (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P′) refl
