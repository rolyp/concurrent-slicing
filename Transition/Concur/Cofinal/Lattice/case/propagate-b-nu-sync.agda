open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common

module Transition.Concur.Cofinal.Lattice.case.propagate-b-nu-sync
   {Γ} {x x′ : Name Γ} {P₀ Q₀} where

   import Relation.Binary.EqReasoning as EqReasoning

   import Name as ᴺ
   import Ren as ᴿ
   import Ren.Lattice as ᴿ̃
   import Transition as ᵀ

{-
   module ˣ∇ˣ
      {R₀ S₀ S′₀} {F : Q₀ —[ (• x′) ᵇ - _ ]→ S₀} {F′ : Q₀ —[ (• x) ᵇ - _ ]→ S′₀} (E : P₀ —[ x • ᵇ - _ ]→ R₀)
      (𝐹 : F ⌣₁[ ˣ∇ˣ ] F′) (let Q′₀ = tgt₁ (⊖₁ 𝐹); Q″₀ = tgt₂ (⊖₁ 𝐹)) (P : ↓ P₀) (Q : ↓ Q₀)
      (IH : (braiding (ˣ∇ˣ {x = x′} {x}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡ tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)))
      (let α : (ᴿ.pop ᴺ.zero *) ((ᴿ.suc ᴿ.push *) R₀) ≡ (idᶠ *) R₀
           α = trans (pop-zero∘suc-push R₀) (sym (*-preserves-id R₀)))
      where

      module _
         (R : ↓ R₀) (R′ : ↓ (ᴿ.suc ᴿ.push *) R₀) (S′ : ↓ S′₀) (Q′ : ↓ Q′₀) (y y′ : ↓ (ᴺ.zero {Γ}))
         (≡R : tgt E P ≡ R) (≡R′ : tgt ((ᴺ.suc *ᵇ) E) ((push *̃) P) ≡ R′) (≡S′ : tgt F′ Q ≡ S′)
         (≡Q′ : tgt (E′/E (⊖₁ 𝐹)) (tgt F Q) ≡ Q′) (≡y′ : y ≡ y′) where

         base :
            (Q″ : ↓ Q″₀) (≡Q″ : tgt (E/E′ (⊖₁ 𝐹)) S′ ≡ Q″) →
            braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} (cong₂ _│_ α (γ₁ 𝐹))
            [ (pop y *̃) R′ │ Q′ ]
            ≡
            [ (repl y′ *̃) R │ Q″ ]
         base Q″ ≡Q″ =
            let β : (pop y *̃) R′ ≅ (repl y′ *̃) R
                β = let open ≅-Reasoning in
                   begin
                      (pop y *̃) R′
                   ≡⟨ cong (pop y *̃) (sym ≡R′) ⟩
                      (pop y *̃) (tgt ((ᴺ.suc *ᵇ) E) ((push *̃) P))
                   ≡⟨ cong (pop y *̃) (sym (renᵇ-tgt-comm E push P)) ⟩
                      (pop y *̃) ((suc push *̃) (tgt E P))
                   ≅⟨ pop-zero∘suc-push̃ y _ ⟩
                      (repl y *̃) (tgt E P)
                   ≡⟨ cong (λ y† → (repl y† *̃) (tgt E P)) ≡y′ ⟩
                      (repl y′ *̃) (tgt E P)
                   ≡⟨ cong (repl y′ *̃) ≡R ⟩
                      (repl y′ *̃) R
                   ∎
                δ : Q′ ≅ Q″
                δ = let open ≅-Reasoning in
                   begin
                      Q′
                   ≡⟨ sym ≡Q′ ⟩
                      tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)
                   ≅⟨ ≅-sym (reduce-ˣ∇ˣ {x = x′} {x} (γ₁ 𝐹) _) ⟩
                      braiding (ˣ∇ˣ {x = x′} {x}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q))
                   ≡⟨ IH ⟩
                      tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)
                   ≡⟨ cong (tgt (E/E′ (⊖₁ 𝐹))) ≡S′ ⟩
                      tgt (E/E′ (⊖₁ 𝐹)) S′
                   ≡⟨ ≡Q″ ⟩
                      Q″
                   ∎
                open ≅-Reasoning in ≅-to-≡(
            begin
               braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} (cong₂ _│_ α (γ₁ 𝐹))
               [ (pop y *̃) R′ │ Q′ ]
            ≅⟨ reduce-ᵇ∇ᶜ (cong₂ _│_ α (γ₁ 𝐹)) _ ⟩
               [ (pop y *̃) R′ │ Q′ ]
            ≅⟨ [-│-]-cong α β (γ₁ 𝐹) δ ⟩
               [ (repl y′ *̃) R │ Q″ ]
            ∎)

         subcase :
            braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} (cong₂ _│_ α (γ₁ 𝐹))
            [ (pop y *̃) R′ │ Q′ ] ≡
            tgt (ν• ((idᶠ *) R₀ │ᶜ E/E′ (⊖₁ 𝐹))) [ ν [ (repl y′ *̃) R │ S′ ] ]
         subcase
            with step (E/E′ (⊖₁ 𝐹)) S′ | inspect (step (E/E′ (⊖₁ 𝐹))) S′
         ... | ◻ , Q″ | [ ≡Q″ ] = base Q″ (,-inj₂ ≡Q″)
         ... | [ • ._ 〈 ◻ 〉 ᶜ ] , Q″ | [ ≡Q″ ] = base Q″ (,-inj₂ ≡Q″)
         ... | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , Q″ | [ ≡Q″ ] = base Q″ (,-inj₂ ≡Q″)

      case :
         braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} (cong₂ _│_ α (γ₁ 𝐹))
         (tgt ((ᴿ.push *ᵇ) E │• E′/E (⊖₁ 𝐹)) (tgt (P₀ │ᵇ F) [ P │ Q ]))
         ≡
         (tgt (ν• ((idᶠ *) R₀ │ᶜ E/E′ (⊖₁ 𝐹))) (tgt (E │ᵥ F′) [ P │ Q ]))
      case
         with step E P | step ((ᴿ.push *ᵇ) E) ((push *̃) P) | step F′ Q | step (E′/E (⊖₁ 𝐹)) (tgt F Q) |
              inspect (step E) P | inspect (step ((ᴿ.push *ᵇ) E)) ((push *̃) P) |
              inspect (step F′) Q | inspect (step (E′/E (⊖₁ 𝐹))) (tgt F Q)
      ... | _ , R | _ , R′ | ◻ , S′ | [ • ._ 〈 y 〉 ᶜ ] , Q′ | [ ≡R ] | [ ≡R′ ] | [ ≡S′ ] | [ ≡Q′ ] =
         ⊥-elim (◻≢[-] (trans (cong (residual ˣ∇ˣ) (sym (,-inj₁ ≡S′))) (trans (sym (π₁ (ᴬgamma₁ 𝐹 Q))) (,-inj₁ ≡Q′))))
      ... | _ , R | _ , R′ | [ • ._ ﹙ _ ﹚ ᵇ ] , S′ | ◻ , Q′ | [ ≡R ] | [ ≡R′ ] | [ ≡S′ ] | [ ≡Q′ ] =
         ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡Q′)) (trans (π₁ (ᴬgamma₁ 𝐹 Q)) (cong (residual ˣ∇ˣ) (,-inj₁ ≡S′)))))
      ... | ◻ , R | [ _ ] , R′ | _ , S′ | _ , Q′ | [ ≡R ] | [ ≡R′ ] | [ ≡S′ ] | [ ≡Q′ ] =
         ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R))) (trans (renᵇ-action-comm E push P) (,-inj₁ ≡R′))))
      ... | [ ._ • ᵇ ] , R | ◻ , R′ | _ , S′ | _ , Q′ | [ ≡R ] | [ ≡R′ ] | [ ≡S′ ] | [ ≡Q′ ] =
         ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡R′)) (trans (sym (renᵇ-action-comm E push P)) (cong (push ᴬ*̃) (,-inj₁ ≡R)))))
      ... | _ , R | _ , R′ | [ • ._ ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , S′ | [ • ._ 〈 ◻ 〉 ᶜ ] , Q′ | [ ≡R ] | [ ≡R′ ] | [ ≡S′ ] | [ ≡Q′ ] =
         let α = trans (sym (,-inj₁ ≡Q′)) (trans (π₁ (ᴬgamma₁ 𝐹 Q)) (cong (residual ˣ∇ˣ) (,-inj₁ ≡S′))) in
         ⊥-elim ([•x〈◻〉ᶜ]≢[•x〈[-]〉ᶜ] α)
      ... | _ , R | _ , R′ | [ • ._ ﹙ ◻ ﹚ ᵇ ] , S′ | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , Q′ |
         [ ≡R ] | [ ≡R′ ] | [ ≡S′ ] | [ ≡Q′ ] =
         let α = trans (sym (,-inj₁ ≡Q′)) (trans (π₁ (ᴬgamma₁ 𝐹 Q)) (cong (residual ˣ∇ˣ) (,-inj₁ ≡S′))) in
         ⊥-elim ([•x〈◻〉ᶜ]≢[•x〈[-]〉ᶜ] (sym α))
      ... | ◻ , R | ◻ , R′ | ◻ , S′ | ◻ , Q′ | [ ≡R ] | [ ≡R′ ] | [ ≡S′ ] | [ ≡Q′ ] =
         subcase R R′ S′ Q′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl
      ... | ◻ , R | ◻ , R′ | [ • ._ ﹙ ◻ ﹚ ᵇ ] , S′ | [ • ._ 〈 ◻ 〉 ᶜ ] , Q′ | [ ≡R ] | [ ≡R′ ] | [ ≡S′ ] | [ ≡Q′ ] =
         subcase R R′ S′ Q′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl
      ... | ◻ , R | ◻ , R′ | [ • ._ ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , S′ | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , Q′ |
         [ ≡R ] | [ ≡R′ ] | [ ≡S′ ] | [ ≡Q′ ] =
         subcase R R′ S′ Q′ [ ᴺ.zero ] [ ᴺ.zero ] (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl
      ... | [ ._ • ᵇ ] , R | [ ._ • ᵇ ] , R′ | ◻ , S′ | ◻ , Q′ | [ ≡R ] | [ ≡R′ ] | [ ≡S′ ] | [ ≡Q′ ] =
         subcase R R′ S′ Q′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl
      ... | [ ._ • ᵇ ] , R | [ ._ • ᵇ ] , R′ | [ • ._ ﹙ ◻ ﹚ ᵇ ] , S′ | [ • ._ 〈 ◻ 〉 ᶜ ] , Q′ |
         [ ≡R ] | [ ≡R′ ] | [ ≡S′ ] | [ ≡Q′ ] =
         subcase R R′ S′ Q′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl
      ... | [ ._ • ᵇ ] , R | [ ._ • ᵇ ] , R′ | [ • ._ ﹙ [ .ᴺ.zero ] ﹚ ᵇ ] , S′ | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , Q′ |
         [ ≡R ] | [ ≡R′ ] | [ ≡S′ ] | [ ≡Q′ ] =
         subcase R R′ S′ Q′ [ ᴺ.zero ] [ ᴺ.zero ] (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl
-}

   module ᵇ∇ᵇ-•x
      {R₀ S₀ S′₀ : Proc (Γ + 1)} {F : Q₀ —[ (• x′) ᵇ - _ ]→ S₀} {F′ : Q₀ —[ (• x) ᵇ - _ ]→ S′₀}
      (E : P₀ —[ x • ᵇ - _ ]→ R₀) (𝐹 : F ⌣₁[ ᵇ∇ᵇ ] F′) (let Q′₀ = tgt₁ (⊖₁ 𝐹); Q″₀ = tgt₂ (⊖₁ 𝐹))
      (P : ↓ P₀) (Q : ↓ Q₀)
      (IH : braiding (ᵇ∇ᵇ {a = • x′} {• x}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡ tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q))
      (let α : (idᶠ *) ((ᴿ.suc ᴿ.push *) R₀) ≡ (ᴿ.swap *) ((ᴿ.push *) ((idᶠ *) R₀))
           α = let open EqReasoning (setoid _) in
             begin
                (idᶠ *) ((ᴿ.suc ᴿ.push *) R₀)
             ≡⟨ *-preserves-id _ ⟩
                (ᴿ.suc ᴿ.push *) R₀
             ≡⟨ cong (ᴿ.suc ᴿ.push *) (sym (*-preserves-id R₀)) ⟩
                (ᴿ.suc ᴿ.push *) ((idᶠ *) R₀)
             ≡⟨ swap∘push _ ⟩
                (ᴿ.swap *) ((ᴿ.push *) ((idᶠ *) R₀))
             ∎
           β : ν ((idᶠ *) ((ᴿ.suc ᴿ.push *) R₀) │ Q′₀) ≡ ν ((ᴿ.swap *) ((ᴿ.push *) ((idᶠ *) R₀)) │ (ᴿ.swap *) Q″₀)
           β = (cong ν_ (cong₂ _│_ α (swap-swap (γ₁ 𝐹))))) where

{-
      module _
         (R : ↓ R₀) (S′ : ↓ S′₀) (P″ : ↓ (ᴿ.suc ᴿ.push *) R₀) (P′ : ↓ Q′₀)
         (≡R : tgt E P ≡ R) (≡S′ : tgt F′ Q ≡ S′) (≡P″ : tgt ((ᴺ.suc *ᵇ) E) ((push *̃) P) ≡ P″)
         (≡P′ : tgt (E′/E (⊖₁ 𝐹)) (tgt F Q) ≡ P′) where

         base :
            (Q″ : ↓ Q″₀) (≡Q″ : tgt (E/E′ (⊖₁ 𝐹)) S′ ≡ Q″) →
            braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} β
            [ ν [ P″ │ P′ ] ]
            ≡
            [ ν [ (swap *̃) ((push *̃) R) │ (swap *̃) Q″ ] ]
         base Q″ ≡Q″ =
            let γ : P″ ≅ (swap *̃) ((push *̃) R)
                γ = let open ≅-Reasoning in
                   begin
                      P″
                   ≡⟨ sym ≡P″ ⟩
                      tgt ((ᴿ.push *ᵇ) E) ((push *̃) P)
                   ≡⟨ sym (renᵇ-tgt-comm E push P) ⟩
                      (suc push *̃) (tgt E P)
                   ≅⟨ swap∘push̃ _ ⟩
                      (swap *̃) ((push *̃) (tgt E P))
                   ≡⟨ cong ((swap *̃) ∘ᶠ (push *̃)) ≡R ⟩
                      (swap *̃) ((push *̃) R)
                   ∎
                δ : P′ ≅ (swap *̃) Q″
                δ = let open ≅-Reasoning in
                   begin
                      P′
                   ≡⟨ sym ≡P′ ⟩
                      tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)
                   ≅⟨ ≅-sym (swap-involutivẽ _) ⟩
                      (swap *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)))
                   ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐹) (swap *̃) (≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐹) _)) ⟩
                      (swap *̃) (braiding (ᵇ∇ᵇ {a = • x′} {• x}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)))
                   ≡⟨ cong (swap *̃) IH ⟩
                      (swap *̃) (tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q))
                   ≡⟨ cong ((swap *̃) ∘ᶠ tgt (E/E′ (⊖₁ 𝐹))) ≡S′ ⟩
                      (swap *̃) (tgt (E/E′ (⊖₁ 𝐹)) S′)
                   ≡⟨ cong (swap *̃) ≡Q″ ⟩
                      (swap *̃) Q″
                   ∎
                open ≅-Reasoning in ≅-to-≡ (
            begin
               braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} β [ ν [ P″ │ P′ ] ]
            ≅⟨ reduce-ᵇ∇ᶜ β _ ⟩
               [ ν [ P″ │ P′ ] ]
            ≅⟨ [ν-]-cong (cong₂ _│_ α (swap-swap (γ₁ 𝐹))) ([-│-]-cong α γ (swap-swap (γ₁ 𝐹)) δ) ⟩
               [ ν [ (swap *̃) ((push *̃) R) │ (swap *̃) Q″ ] ]
            ∎)

         subcase :
            braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} β
            [ ν [ P″ │ P′ ] ]
            ≡
            tgt (νᵇ (R₀ │ᵇ E/E′ (⊖₁ 𝐹))) [ ν [ R │ S′ ] ]
         subcase
            with step (E/E′ (⊖₁ 𝐹)) S′ | inspect (step (E/E′ (⊖₁ 𝐹))) S′
         ... | ◻ , Q″ | [ ≡Q″ ] = base Q″ (,-inj₂ ≡Q″)
         ... | [ (• ._) ᵇ ] , Q″ | [ ≡Q″ ] = base Q″ (,-inj₂ ≡Q″)
-}

      case :
         braiding (ᵇ∇ᶜ {a = • x′} {τ}) {0} β
         (tgt ((ᴿ.push *ᵇ) E │ᵥ E′/E (⊖₁ 𝐹)) (tgt (P₀ │ᵇ F) [ P │ Q ]))
         ≡
         tgt (νᵇ ((idᶠ *) (ᵀ.tgt E) │ᵇ E/E′ (⊖₁ 𝐹))) (tgt (E │ᵥ F′) [ P │ Q ])
      case
         with step E P | step ((ᴿ.push *ᵇ) E) ((push *̃) P) | step F′ Q | step (E′/E (⊖₁ 𝐹)) (tgt F Q) |
              inspect (step E) P | inspect (step ((ᴺ.suc *ᵇ) E)) ((push *̃) P) | inspect (step F′) Q |
              inspect (step (E′/E (⊖₁ 𝐹))) (tgt F Q)
      ... | ◻ , R | [ ._ • ᵇ ] , P″ | _ , S′ | _ , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
         ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R))) (trans (renᵇ-action-comm E push P) (,-inj₁ ≡P″))))
      ... | [ ._ • ᵇ ] , R | ◻ , P″ | _ , S′ | _ , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
         ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P″)) (trans (sym (renᵇ-action-comm E push P)) (cong (push ᴬ*̃) (,-inj₁ ≡R)))))
      ... | _ , R | _ , P″ | ◻ , S′ | [ _ ] , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
         ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡S′))) (trans (sym (π₁ (ᴬgamma₁ 𝐹 Q))) (,-inj₁ ≡P′))))
      ... | _ , R | _ , P″ | [ • ._ ﹙ _ ﹚ ᵇ ] , S′ | ◻ , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
         ⊥-elim (◻≢[-] (trans (,-inj₁ (sym ≡P′)) (trans (π₁ (ᴬgamma₁ 𝐹 Q)) (cong (push ᴬ*̃) (,-inj₁ ≡S′)))))
      ... | ◻ , R | ◻ , P″ | ◻ , S′ | ◻ , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
         ? -- subcase R S′ P″ P′ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P″) (,-inj₂ ≡P′)
      ... | ◻ , R | ◻ , P″ | [ _ ] , S′ | [ _ ] , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
         ? -- subcase R S′ P″ P′ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P″) (,-inj₂ ≡P′)
      ... | [ ._ • ᵇ ] , R | [ ._ • ᵇ ] , P″ | ◻ , S′ | ◻ , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
         ? -- subcase R S′ P″ P′ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P″) (,-inj₂ ≡P′)
      ... | [ ._ • ᵇ ] , R | [ ._ • ᵇ ] , P″ | [ • ._ ﹙ _ ﹚ ᵇ ] , S′ | [ • ._ ﹙ _ ﹚ ᵇ ] , P′ |
         [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
         ? -- subcase R S′ P″ P′ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P″) (,-inj₂ ≡P′)

{-
   module ᵇ∇ᵇ-x•
      {R₀ S₀ S′₀ : Proc (Γ + 1)} {F : Q₀ —[ x′ • ᵇ - _ ]→ S₀} {F′ : Q₀ —[ (• x) ᵇ - _ ]→ S′₀}
      (E : P₀ —[ x • ᵇ - _ ]→ R₀) (𝐹 : F ⌣₁[ ᵇ∇ᵇ ] F′) (let Q′₀ = tgt₁ (⊖₁ 𝐹); Q″₀ = tgt₂ (⊖₁ 𝐹))
      (P : ↓ P₀) (Q : ↓ Q₀)
      (IH : braiding (ᵇ∇ᵇ {a = x′ •} {• x}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡ tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q))
      (let α : (ᴿ.suc ᴿ.push *) R₀ ≡ (ᴿ.swap *) ((ᴿ.push *) R₀)
           α = swap∘push R₀
           β : ν ((ᴿ.suc ᴿ.push *) R₀ │ Q′₀) ≡ ᵀ.tgt (νᵇ (R₀ │ᵇ E/E′ (⊖₁ 𝐹)))
           β = cong ν_ (cong₂ _│_ α (swap-swap (γ₁ 𝐹)))) where

      module _
         (R : ↓ R₀) (S′ : ↓ S′₀) (P″ : ↓ (ᴿ.suc ᴿ.push *) R₀) (P′ : ↓ Q′₀)
         (≡R : tgt E P ≡ R) (≡S′ : tgt F′ Q ≡ S′) (≡P″ : tgt ((ᴺ.suc *ᵇ) E) ((push *̃) P) ≡ P″)
         (≡P′ : tgt (E′/E (⊖₁ 𝐹)) (tgt F Q) ≡ P′) where

         base :
            (Q″ : ↓ Q″₀) (≡Q″ : tgt (E/E′ (⊖₁ 𝐹)) S′ ≡ Q″) →
            braiding (ᵇ∇ᶜ {a = x′ •} {τ}) {0} β
            [ ν [ P″ │ P′ ] ]
            ≡
            [ ν [ (swap *̃) ((push *̃) R) │ (swap *̃) Q″ ] ]
         base Q″ ≡Q″ =
            let γ : P″ ≅ (swap *̃) ((push *̃) R)
                γ = let open ≅-Reasoning in
                   begin
                      P″
                   ≡⟨ sym ≡P″ ⟩
                      tgt ((ᴿ.push *ᵇ) E) ((push *̃) P)
                   ≡⟨ sym (renᵇ-tgt-comm E push P) ⟩
                      (suc push *̃) (tgt E P)
                   ≅⟨ swap∘push̃ _ ⟩
                      (swap *̃) ((push *̃) (tgt E P))
                   ≡⟨ cong ((swap *̃) ∘ᶠ (push *̃)) ≡R ⟩
                      (swap *̃) ((push *̃) R)
                   ∎
                δ : P′ ≅ (swap *̃) Q″
                δ = let open ≅-Reasoning in
                   begin
                      P′
                   ≡⟨ sym ≡P′ ⟩
                      tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)
                   ≅⟨ ≅-sym (swap-involutivẽ _) ⟩
                      (swap *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)))
                   ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐹) (swap *̃) (≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐹) _)) ⟩
                      (swap *̃) (braiding (ᵇ∇ᵇ {a = x′ •} {• x}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)))
                   ≡⟨ cong (swap *̃) IH ⟩
                      (swap *̃) (tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q))
                   ≡⟨ cong ((swap *̃) ∘ᶠ tgt (E/E′ (⊖₁ 𝐹))) ≡S′ ⟩
                      (swap *̃) (tgt (E/E′ (⊖₁ 𝐹)) S′)
                   ≡⟨ cong (swap *̃) ≡Q″ ⟩
                      (swap *̃) Q″
                   ∎
                open ≅-Reasoning in ≅-to-≡ (
            begin
               braiding (ᵇ∇ᶜ {a = x′ •} {τ}) {0} β [ ν [ P″ │ P′ ] ]
            ≅⟨ reduce-ᵇ∇ᶜ β _ ⟩
               [ ν [ P″ │ P′ ] ]
            ≅⟨ [ν-]-cong (cong₂ _│_ α (swap-swap (γ₁ 𝐹))) ([-│-]-cong α γ (swap-swap (γ₁ 𝐹)) δ) ⟩
               [ ν [ (swap *̃) ((push *̃) R) │ (swap *̃) Q″ ] ]
            ∎)

         subcase :
            braiding (ᵇ∇ᶜ {a = x′ •} {τ}) {0} β
            [ ν [ P″ │ P′ ] ]
            ≡
            π₂ (step⁻ (νᵇ (R₀ │ᵇ E/E′ (⊖₁ 𝐹))) (ν [ R │ S′ ]))
         subcase
            with step (E/E′ (⊖₁ 𝐹)) S′ | inspect (step (E/E′ (⊖₁ 𝐹))) S′
         ... | ◻ , Q″ | [ ≡Q″ ] = base Q″ (,-inj₂ ≡Q″)
         ... | [ ._ • ᵇ ] , Q″ | [ ≡Q″ ] = base Q″ (,-inj₂ ≡Q″)

      case :
         braiding (ᵇ∇ᶜ {a = x′ •} {τ}) {0} β
         (tgt ((ᴿ.push *ᵇ) E │ᵥ E′/E (⊖₁ 𝐹)) (tgt (P₀ │ᵇ F) [ P │ Q ]))
         ≡
         tgt (νᵇ (ᵀ.tgt E │ᵇ E/E′ (⊖₁ 𝐹))) (tgt (E │ᵥ F′) [ P │ Q ])
      case
         with step E P | step ((ᴿ.push *ᵇ) E) ((push *̃) P) | step F′ Q | step (E′/E (⊖₁ 𝐹)) (tgt F Q) |
              inspect (step E) P | inspect (step ((ᴿ.push *ᵇ) E)) ((push *̃) P) | inspect (step F′) Q |
              inspect (step (E′/E (⊖₁ 𝐹))) (tgt F Q)
      ... | ◻ , R | [ ._ • ᵇ ] , P″ | _ , S′ | _ , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
         ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R))) (trans (renᵇ-action-comm E push P) (,-inj₁ ≡P″))))
      ... | [ ._ • ᵇ ] , R | ◻ , P″ | _ , S′ | _ , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
         ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P″)) (trans (sym (renᵇ-action-comm E push P)) (cong (push ᴬ*̃) (,-inj₁ ≡R)))))
      ... | _ , R | _ , P″ | ◻ , S′ | [ _ ] , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
         ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡S′))) (trans (sym (π₁ (ᴬgamma₁ 𝐹 Q))) (,-inj₁ ≡P′))))
      ... | _ , R | _ , P″ | [ (• ._) ᵇ ] , S′ | ◻ , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
         ⊥-elim (◻≢[-] (trans (,-inj₁ (sym ≡P′)) (trans (π₁ (ᴬgamma₁ 𝐹 Q)) (cong (push ᴬ*̃) (,-inj₁ ≡S′)))))
      ... | ◻ , R | ◻ , P″ | ◻ , S′ | ◻ , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
         subcase R S′ P″ P′ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P″) (,-inj₂ ≡P′)
      ... | ◻ , R | ◻ , P″ | [ _ ] , S′ | [ _ ] , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
         subcase R S′ P″ P′ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P″) (,-inj₂ ≡P′)
      ... | [ ._ • ᵇ ] , R | [ ._ • ᵇ ] , P″ | ◻ , S′ | ◻ , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
         subcase R S′ P″ P′ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P″) (,-inj₂ ≡P′)
      ... | [ ._ • ᵇ ] , R | [ ._ • ᵇ ] , P″ | [ (• ._) ᵇ ] , S′ | [ (• ._) ᵇ ] , P′ | [ ≡R ] | [ ≡P″ ] | [ ≡S′ ] | [ ≡P′ ] =
         subcase R S′ P″ P′ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡P″) (,-inj₂ ≡P′)
-}
