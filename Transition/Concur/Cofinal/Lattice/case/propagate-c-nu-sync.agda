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
         (R : ↓ R₀) (S′ : ↓ S′₀) (P′ : ↓ Q′₀) (≡R : tgt E P ≡ R) (≡S′ : tgt F′ Q ≡ S′) (≡P′ : tgt (E′/E (⊖₁ 𝐹)) (tgt F Q) ≡ P′)
         where

{-
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
-}


         postulate
          subcase :
            braiding (ᶜ∇ᶜ {a = • x′ 〈 y 〉} {τ}) {0} (cong ν_ (cong₂ _│_ refl (γ₁ 𝐹)))
            [ ν [ R │ P′ ] ]
            ≡
            tgt (νᶜ (R₀ │ᶜ E/E′ (⊖₁ 𝐹))) [ ν [ R │ S′ ] ]
{-
         subcase
            with step (E/E′ (⊖₁ 𝐹)) S′ | inspect (step (E/E′ (⊖₁ 𝐹))) S′
         ... | ◻ , Q″ | [ ≡Q″ ] = base Q″ (,-inj₂ ≡Q″)
         ... | [ (• ._) ᵇ ] , Q″ | [ ≡Q″ ] = base Q″ (,-inj₂ ≡Q″)
-}

      case :
         braiding (ᶜ∇ᶜ {a = • x′ 〈 y 〉} {τ}) {0} (cong ν_ (cong₂ _│_ refl (γ₁ 𝐹)))
         (tgt (E │ᵥ E′/E (⊖₁ 𝐹)) (tgt (P₀ │ᶜ F) [ P │ Q ]))
         ≡
         tgt (νᶜ (ᵀ.tgt E │ᶜ E/E′ (⊖₁ 𝐹))) (tgt (E │ᵥ F′) [ P │ Q ])
      case
         with step E P | step F′ Q | step (E′/E (⊖₁ 𝐹)) (tgt F Q) |
              inspect (step E) P | inspect (step F′) Q | inspect (step (E′/E (⊖₁ 𝐹))) (tgt F Q)
      case | ◻ , R | ◻ , S′ | ◻ , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] = {!!}
      case | ◻ , R | ◻ , S′ | [ _ ] , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] = {!!}
      case | ◻ , R | [ _ ] , S′ | ◻ , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] = {!!}
      case | ◻ , R | [ _ ] , S′ | [ _ ] , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] = {!!}
      case | [ (.x •) ᵇ ] , R | ◻ , S′ | ◻ , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] = {!!}
      case | [ (.x •) ᵇ ] , R | ◻ , S′ | [ (• .x) ᵇ ] , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] = {!!}
      case | [ (.x •) ᵇ ] , R | [ (• .x) ᵇ ] , S′ | ◻ , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] = {!!}
      case | [ (.x •) ᵇ ] , R | [ (• .x) ᵇ ] , S′ | [ (• .x) ᵇ ] , P′ | [ ≡R ] | [ ≡S′ ] | [ ≡P′ ] = {!!}
{-
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
