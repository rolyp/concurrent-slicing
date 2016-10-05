open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common

import Relation.Binary.EqReasoning as EqReasoning
import Ren as ᴿ

module Transition.Concur.Cofinal.Lattice.case.sync-sync
   {Γ} {x y u z : Name Γ} {P₀ Q₀ R₀ R′₀ S₀ S′₀} {E : P₀ —[ x • ᵇ - _ ]→ R₀} {E′ : P₀ —[ u • ᵇ - _ ]→ R′₀}
   {F : Q₀ —[ • x 〈 y 〉 ᶜ - _ ]→ S₀} {F′ : Q₀ —[ • u 〈 z 〉 ᶜ - _ ]→ S′₀} (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (𝐹 : F ⌣₁[ ᶜ∇ᶜ ] F′)
   (P : ↓ P₀) (Q : ↓ Q₀)
   (IH₁ : braiding (ᵇ∇ᵇ {a = x •} {u •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
   (IH₂ : braiding (ᶜ∇ᶜ {a = • x 〈 y 〉} {• u 〈 z 〉}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡ tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q))
   (let
      P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂(⊖₁ 𝐸)
      α = let open EqReasoning (setoid _) in
         begin
            (ᴿ.pop z *) ((ᴿ.suc (ᴿ.pop y) *) P′₀)
         ≡⟨ sym (pop-pop-swap y z _) ⟩
            (ᴿ.pop y *) ((ᴿ.suc (ᴿ.pop z) *) ((ᴿ.swap *) P′₀))
         ≡⟨ cong (ᴿ.pop y *) (cong (ᴿ.suc (ᴿ.pop z) *) (γ₁ 𝐸)) ⟩
            (ᴿ.pop y *) ((ᴿ.suc (ᴿ.pop z) *) P″₀)
         ∎)
   where

   module _
      (pop-y*E′/E : (ᴿ.pop y *) R₀ —[ u • ᵇ - _ ]→ (ᴿ.suc (ᴿ.pop y) *) (tgt₁ (⊖₁ 𝐸)))
      (pop-z*E/E′ : (ᴿ.pop z *) R′₀ —[ (x •) ᵇ - _ ]→ (ᴿ.suc (ᴿ.pop z) *) (tgt₂ (⊖₁ 𝐸)))
      (R : ↓ R₀) (R′ : ↓ R′₀) (S : ↓ S₀) (S′ : ↓ S′₀) (y′ : ↓ y) (z′ : ↓ z)
      (≡R : tgt E P ≡ R) (≡R′ : tgt E′ P ≡ R′) (≡S : tgt F Q ≡ S) (≡S′ : tgt F′ Q ≡ S′)
      (≡pop-y*E′/E : (ᴿ.pop y *ᵇ) (E′/E (⊖₁ 𝐸)) ≡ pop-y*E′/E)
      (≡pop-z*E/E′ : (ᴿ.pop z *ᵇ) (E/E′ (⊖₁ 𝐸)) ≡ pop-z*E/E′)
      (≡z′ : (z′ ≡ ◻ × action F′ Q ≡ ◻ → ⊥) → action F′ Q ≡ [ • u 〈 z′ 〉 ᶜ ])
      (≡y′ : (y′ ≡ ◻ × action F Q ≡ ◻ → ⊥) → action F Q ≡ [ • x 〈 y′ 〉 ᶜ ])
      where

      ≡a′/a : action (E′/E (⊖₁ 𝐹)) S ≡ action F′ Q
      ≡a′/a = trans (cong (action (E′/E (⊖₁ 𝐹))) (sym ≡S)) (π₁ (ᴬgamma₁ 𝐹 Q))

      z₁≡z₂ : (z₁ z₂ : ↓ z)
              (α : (z₁ ≡ ◻ × action F′ Q ≡ ◻ → ⊥) → action F′ Q ≡ [ • u 〈 z₁ 〉 ᶜ ])
              (β : (z₂ ≡ ◻ × action (E′/E (⊖₁ 𝐹)) S ≡ ◻ → ⊥) → action (E′/E (⊖₁ 𝐹)) S ≡ [ • u 〈 z₂ 〉 ᶜ ]) →
              z₁ ≡ z₂
      z₁≡z₂ ◻ ◻ _ _ = refl
      z₁≡z₂ [ .z ] [ .z ] _ _ = refl
      z₁≡z₂ ◻ [ .z ] α β rewrite ≡a′/a =
         let δ : action F′ Q ≡ [ • u 〈 [ z ] 〉 ᶜ ]
             δ = β (λ { (() , _) })
         in ⊥-elim ([•x〈◻〉ᶜ]≢[•x〈[-]〉ᶜ] (trans (sym (α (λ { (_ , δ′) → ◻≢[-] (trans (sym δ′) δ) }))) δ))
      z₁≡z₂ [ .z ] ◻ α β rewrite sym ≡a′/a =
         let δ : action (E′/E (⊖₁ 𝐹)) S ≡ [ • u 〈 [ z ] 〉 ᶜ ]
             δ = α (λ { (() , _) })
         in ⊥-elim ([•x〈◻〉ᶜ]≢[•x〈[-]〉ᶜ] (trans (sym (β (λ { (_ , δ′) → ◻≢[-] (trans (sym δ′) δ) }))) δ))

      ≡a/a′ : action (E/E′ (⊖₁ 𝐹)) S′ ≡ action F Q
      ≡a/a′ = trans (cong (action (E/E′ (⊖₁ 𝐹))) (sym ≡S′)) (π₂ (ᴬgamma₁ 𝐹 Q))

      y₁≡y₂ : (y₁ y₂ : ↓ y)
              (α : (y₁ ≡ ◻ × action F Q ≡ ◻ → ⊥) → action F Q ≡ [ • x 〈 y₁ 〉 ᶜ ])
              (β : (y₂ ≡ ◻ × action (E/E′ (⊖₁ 𝐹)) S′ ≡ ◻ → ⊥) → action (E/E′ (⊖₁ 𝐹)) S′ ≡ [ • x 〈 y₂ 〉 ᶜ ]) →
              y₁ ≡ y₂
      y₁≡y₂ ◻ ◻ _ _ = refl
      y₁≡y₂ [ .y ] [ .y ] _ _ = refl
      y₁≡y₂ ◻ [ .y ] α β rewrite ≡a/a′ =
         let δ : action F Q ≡ [ • x 〈 [ y ] 〉 ᶜ ]
             δ = β (λ { (() , _) })
         in ⊥-elim ([•x〈◻〉ᶜ]≢[•x〈[-]〉ᶜ] (trans (sym (α (λ { (_ , δ′) → ◻≢[-] (trans (sym δ′) δ) }))) δ))
      y₁≡y₂ [ .y ] ◻ α β rewrite sym ≡a/a′ =
         let δ : action (E/E′ (⊖₁ 𝐹)) S′ ≡ [ • x 〈 [ y ] 〉 ᶜ ]
             δ = α (λ { (() , _) })
         in ⊥-elim ([•x〈◻〉ᶜ]≢[•x〈[-]〉ᶜ] (trans (sym (β (λ { (_ , δ′) → ◻≢[-] (trans (sym δ′) δ) }))) δ))

      module _
         (P′ : ↓ (ᴿ.suc (ᴿ.pop y) *) P′₀) (Q′ : ↓ tgt₁ (⊖₁ 𝐹)) (P″ : ↓ (ᴿ.suc (ᴿ.pop z) *) P″₀)
         (Q″ : ↓ tgt₂ (⊖₁ 𝐹)) (z† : ↓ z) (y† : ↓ y)
         (≡P′ : tgt pop-y*E′/E ((pop y′ *̃) R) ≡ P′) (≡Q′ : tgt (E′/E (⊖₁ 𝐹)) S ≡ Q′)
         (≡P″ : tgt pop-z*E/E′ ((pop z′ *̃) R′) ≡ P″) (≡Q″ : tgt (E/E′ (⊖₁ 𝐹)) S′ ≡ Q″)
         (≡z† : (z† ≡ ◻ × action (E′/E (⊖₁ 𝐹)) S ≡ ◻ → ⊥) → action (E′/E (⊖₁ 𝐹)) S ≡ [ • u 〈 z† 〉 ᶜ ])
         (≡y† : (y† ≡ ◻ × action (E/E′ (⊖₁ 𝐹)) S′ ≡ ◻ → ⊥) → action (E/E′ (⊖₁ 𝐹)) S′ ≡ [ • x 〈 y† 〉 ᶜ ])
         where

         β : (pop z† *̃) P′ ≅ (pop y† *̃) P″
         β = let open ≅-Reasoning in
            begin
               (pop z† *̃) P′
            ≡⟨ cong (pop z† *̃) (sym ≡P′) ⟩
               (pop z† *̃) (tgt pop-y*E′/E ((pop y′ *̃) R))
            ≡⟨ cong ((pop z† *̃) ∘ᶠ tgt pop-y*E′/E ∘ᶠ (pop y′ *̃)) (sym ≡R) ⟩
               (pop z† *̃) (tgt pop-y*E′/E ((pop y′ *̃) (tgt E P)))
            ≡⟨ cong (λ E† → (pop z† *̃) (tgt E† ((pop y′ *̃) (tgt E P)))) (sym ≡pop-y*E′/E) ⟩
               (pop z† *̃) (tgt ((ᴿ.pop y *ᵇ) (E′/E (⊖₁ 𝐸))) ((pop y′ *̃) (tgt E P)))
            ≡⟨ cong (pop z† *̃) (sym (renᵇ-tgt-comm (E′/E (⊖₁ 𝐸)) (pop y′) (tgt E P))) ⟩
               (pop z† *̃) ((suc (pop y′) *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))
            ≡⟨ cong₂ (λ z‡ y‡ → (pop z‡ *̃) ((suc (pop y‡) *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                     (sym (z₁≡z₂ z′ z† ≡z′ ≡z†)) (y₁≡y₂ y′ y† ≡y′ ≡y†) ⟩
               (pop z′ *̃) ((suc (pop y†) *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))
            ≅⟨ ≅-cong✴ ↓_ (sym (swap-involutive P′₀))
               ((pop z′ *̃) ∘ᶠ (suc (pop y†) *̃)) (≅-sym (swap-involutivẽ (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))) ⟩
               (pop z′ *̃) ((suc (pop y†) *̃) ((swap *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))))
            ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐸) ((pop z′ *̃) ∘ᶠ (suc (pop y†) *̃) ∘ᶠ (swap *̃)) (≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐸) _)) ⟩
               (pop z′ *̃)
               ((suc (pop y†) *̃)
                ((swap *̃) (braiding (ᵇ∇ᵇ {a = x •} {u •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))))
            ≡⟨ cong ((pop z′ *̃) ∘ᶠ (suc (pop y†) *̃) ∘ᶠ (swap *̃)) IH₁ ⟩
               (pop z′ *̃) ((suc (pop y†) *̃) ((swap *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))))
            ≅⟨ pop-pop-swap̃ z′ y† _ ⟩
               (pop y† *̃) ((suc (pop z′) *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)))
            ≡⟨ cong (pop y† *̃) (renᵇ-tgt-comm (E/E′ (⊖₁ 𝐸)) (pop z′) (tgt E′ P)) ⟩
               (pop y† *̃) (tgt ((ᴿ.pop z *ᵇ) (E/E′ (⊖₁ 𝐸))) ((pop z′ *̃) (tgt E′ P)))
            ≡⟨ cong (λ E† → (pop y† *̃) (tgt E† ((pop z′ *̃) (tgt E′ P)))) ≡pop-z*E/E′ ⟩
               (pop y† *̃) (tgt pop-z*E/E′ ((pop z′ *̃) (tgt E′ P)))
            ≡⟨ cong ((pop y† *̃) ∘ᶠ tgt pop-z*E/E′ ∘ᶠ (pop z′ *̃)) ≡R′ ⟩
               (pop y† *̃) (tgt pop-z*E/E′ ((pop z′ *̃) R′))
            ≡⟨ cong (pop y† *̃) ≡P″ ⟩
               (pop y† *̃) P″
            ∎

         δ : Q′ ≅ Q″
         δ = let open ≅-Reasoning in
            begin
               Q′
            ≡⟨ sym ≡Q′ ⟩
               tgt (E′/E (⊖₁ 𝐹)) S
            ≡⟨ cong (tgt (E′/E (⊖₁ 𝐹))) (sym ≡S) ⟩
               tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)
            ≅⟨ ≅-sym (reduce-ᶜ∇ᶜ (γ₁ 𝐹) _) ⟩
               braiding (ᶜ∇ᶜ {a = • x 〈 y 〉} {• u 〈 z 〉}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q))
            ≡⟨ IH₂ ⟩
               tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)
            ≡⟨ cong (tgt (E/E′ (⊖₁ 𝐹))) ≡S′ ⟩
               tgt (E/E′ (⊖₁ 𝐹)) S′
            ≡⟨ ≡Q″ ⟩
               Q″
            ∎

         base :
            braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (cong₂ _│_ α (γ₁ 𝐹))
            [ (pop z† *̃) P′ │ Q′ ]
            ≡
            [ (pop y† *̃) P″ │ Q″ ]
         base =
            let open ≅-Reasoning in ≅-to-≡ (
            begin
               braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (cong₂ _│_ α (γ₁ 𝐹)) [ (pop z† *̃) P′ │ Q′ ]
            ≅⟨ reduce-ᶜ∇ᶜ (cong₂ _│_ α (γ₁ 𝐹)) _ ⟩
               [ (pop z† *̃) P′ │ Q′ ]
            ≅⟨ [-│-]-cong α β (γ₁ 𝐹) δ ⟩
               [ (pop y† *̃) P″ │ Q″ ]
            ∎)

      subcase :
         braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (cong₂ _│_ α (γ₁ 𝐹))
         (tgt (pop-y*E′/E │• E′/E (⊖₁ 𝐹)) [ (pop y′ *̃) R │ S ])
         ≡
         tgt (pop-z*E/E′ │• E/E′ (⊖₁ 𝐹)) [ (pop z′ *̃) R′ │ S′ ]
      subcase
         with step pop-y*E′/E ((pop y′ *̃) R) | step (E′/E (⊖₁ 𝐹)) S |
              step pop-z*E/E′ ((pop z′ *̃) R′) | step (E/E′ (⊖₁ 𝐹)) S′ |
              inspect (step pop-y*E′/E) ((pop y′ *̃) R) | inspect (step (E′/E (⊖₁ 𝐹))) S |
              inspect (step pop-z*E/E′) ((pop z′ *̃) R′) | inspect (step (E/E′ (⊖₁ 𝐹))) S′
      ... | ◻ , P′ | ◻ , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ ≢z† → ⊥-elim (≢z† (refl , ,-inj₁ ≡Q′))) (λ ≢y† → ⊥-elim (≢y† (refl , ,-inj₁ ≡Q″ )))
      ... | ◻ , P′ | ◻ , Q′ | ◻ , P″ | [ • .x 〈 y† 〉 ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ y† (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ ≢z† → ⊥-elim (≢z† (refl , ,-inj₁ ≡Q′))) (λ _ → ,-inj₁ ≡Q″)
      ... | ◻ , P′ | ◻ , Q′ | [ .x • ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ ≢z† → ⊥-elim (≢z† (refl , ,-inj₁ ≡Q′))) (λ ≢y† → ⊥-elim (≢y† (refl , ,-inj₁ ≡Q″ )))
      ... | ◻ , P′ | ◻ , Q′ | [ .x • ᵇ ] , P″ | [ • .x 〈 y† 〉 ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ y† (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ ≢z† → ⊥-elim (≢z† (refl , ,-inj₁ ≡Q′))) (λ _ → ,-inj₁ ≡Q″)
      ... | ◻ , P′ | [ • .u 〈 z† 〉 ᶜ ] , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ z† ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ _ → ,-inj₁ ≡Q′) (λ ≢y† → ⊥-elim (≢y† (refl , ,-inj₁ ≡Q″ )))
      ... | ◻ , P′ | [ • .u 〈 z† 〉 ᶜ ] , Q′ | ◻ , P″ | [ • .x 〈 y† 〉 ᶜ ] , Q″ |
         [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ z† y† (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ _ → ,-inj₁ ≡Q′) (λ _ → ,-inj₁ ≡Q″)
      ... | ◻ , P′ | [ • .u 〈 z† 〉 ᶜ ] , Q′ | [ .x • ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ z† ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ _ → ,-inj₁ ≡Q′) (λ ≢y† → ⊥-elim (≢y† (refl , ,-inj₁ ≡Q″ )))
      ... | ◻ , P′ | [ • .u 〈 z† 〉 ᶜ ] , Q′ | [ .x • ᵇ ] , P″ | [ • .x 〈 y† 〉 ᶜ ] , Q″ |
         [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ z† y† (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ _ → ,-inj₁ ≡Q′) (λ _ → ,-inj₁ ≡Q″)
      ... | [ .u • ᵇ ] , P′ | ◻ , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ ≢z† → ⊥-elim (≢z† (refl , (,-inj₁ ≡Q′)))) (λ ≢y† → ⊥-elim (≢y† (refl , ,-inj₁ ≡Q″ )))
      ... | [ .u • ᵇ ] , P′ | ◻ , Q′ | ◻ , P″ | [ • .x 〈 y† 〉 ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ y† (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ ≢z† → ⊥-elim (≢z† (refl , (,-inj₁ ≡Q′)))) (λ _ → ,-inj₁ ≡Q″)
      ... | [ .u • ᵇ ] , P′ | ◻ , Q′ | [ .x • ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ ≢z† → ⊥-elim (≢z† (refl , (,-inj₁ ≡Q′)))) (λ ≢y† → ⊥-elim (≢y† (refl , ,-inj₁ ≡Q″ )))
      ... | [ .u • ᵇ ] , P′ | ◻ , Q′ | [ .x • ᵇ ] , P″ | [ • .x 〈 y† 〉 ᶜ ] , Q″ |
         [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ y† (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ ≢z† → ⊥-elim (≢z† (refl , (,-inj₁ ≡Q′)))) (λ _ → ,-inj₁ ≡Q″)
      ... | [ .u • ᵇ ] , P′ | [ • .u 〈 z† 〉 ᶜ ] , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ z† ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ _ → ,-inj₁ ≡Q′) (λ ≢y† → ⊥-elim (≢y† (refl , ,-inj₁ ≡Q″ )))
      ... | [ .u • ᵇ ] , P′ | [ • .u 〈 z† 〉 ᶜ ] , Q′ | ◻ , P″ | [ • .x 〈 y† 〉 ᶜ ] , Q″ |
         [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ z† y† (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ _ → ,-inj₁ ≡Q′) (λ _ → ,-inj₁ ≡Q″)
      ... | [ .u • ᵇ ] , P′ | [ • .u 〈 z† 〉 ᶜ ] , Q′ | [ .x • ᵇ ] , P″ | ◻ , Q″ |
         [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ z† ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ _ → ,-inj₁ ≡Q′) (λ ≢y† → ⊥-elim (≢y† (refl , ,-inj₁ ≡Q″ )))
      ... | [ .u • ᵇ ] , P′ | [ • .u 〈 z† 〉 ᶜ ] , Q′ | [ .x • ᵇ ] , P″ | [ • .x 〈 y† 〉 ᶜ ] , Q″ |
         [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ z† y† (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ _ → ,-inj₁ ≡Q′) (λ _ → ,-inj₁ ≡Q″)

   case :
      braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (cong₂ _│_ α (γ₁ 𝐹))
      (tgt (E′/E (⊖₁ (𝐸 │• 𝐹))) (tgt (E │• F) [ P │ Q ]))
      ≡
      tgt (E/E′ (⊖₁ (𝐸 │• 𝐹))) (tgt (E′ │• F′) [ P │ Q ])
   case
      with (ᴿ.pop y *ᵇ) (E′/E (⊖₁ 𝐸)) | (ᴿ.pop z *ᵇ) (E/E′ (⊖₁ 𝐸)) |
           inspect (ᴿ.pop y *ᵇ) (E′/E (⊖₁ 𝐸)) | inspect (ᴿ.pop z *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E′/E | pop-z*E/E′ | [ ≡pop-y*E′/E ] | [ ≡pop-z*E/E′ ]
      with step E P | step F Q | step E′ P | step F′ Q |
           inspect (step E) P | inspect (step F) Q | inspect (step E′) P | inspect (step F′) Q
   ... | ◻ , R | ◻ , S | ◻ , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
              (λ ≢z′ → ⊥-elim (≢z′ (refl , ,-inj₁ ≡S′))) (λ ≢y′ → ⊥-elim (≢y′ (refl , ,-inj₁ ≡S)))
   ... | ◻ , R | ◻ , S | ◻ , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ ◻ z′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
              (λ _ → ,-inj₁ ≡S′) (λ ≢y′ → ⊥-elim (≢y′ (refl , ,-inj₁ ≡S)))
   ... | ◻ , R | ◻ , S | [ .u • ᵇ ] , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
              (λ ≢z′ → ⊥-elim (≢z′ (refl , ,-inj₁ ≡S′))) (λ ≢y′ → ⊥-elim (≢y′ (refl , ,-inj₁ ≡S)))
   ... | ◻ , R | ◻ , S | [ .u • ᵇ ] , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ ◻ z′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
              (λ _ → ,-inj₁ ≡S′) (λ ≢y′ → ⊥-elim (≢y′ (refl , ,-inj₁ ≡S)))
   ... | ◻ , R | [ • .x 〈 y′ 〉 ᶜ ] , S | ◻ , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ y′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
              (λ ≢z′ → ⊥-elim (≢z′ (refl , ,-inj₁ ≡S′))) (λ _ → ,-inj₁ ≡S)
   ... | ◻ , R | [ • .x 〈 y′ 〉 ᶜ ] , S | ◻ , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ y′ z′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
              (λ _ → ,-inj₁ ≡S′) (λ _ → ,-inj₁ ≡S)
   ... | ◻ , R | [ • .x 〈 y′ 〉 ᶜ ] , S | [ .u • ᵇ ] , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ y′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
              (λ ≢z′ → ⊥-elim (≢z′ (refl , ,-inj₁ ≡S′))) (λ _ → ,-inj₁ ≡S)
   ... | ◻ , R | [ • .x 〈 y′ 〉 ᶜ ] , S | [ .u • ᵇ ] , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ |
       [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ y′ z′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
              (λ _ → ,-inj₁ ≡S′) (λ _ → ,-inj₁ ≡S)
   ... | [ .x • ᵇ ] , R | ◻ , S | ◻ , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
              (λ ≢z′ → ⊥-elim (≢z′ (refl , ,-inj₁ ≡S′))) (λ ≢y′ → ⊥-elim (≢y′ (refl , ,-inj₁ ≡S)))
   ... | [ .x • ᵇ ] , R | ◻ , S | ◻ , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ ◻ z′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
              (λ _ → ,-inj₁ ≡S′) (λ ≢y′ → ⊥-elim (≢y′ (refl , ,-inj₁ ≡S)))
   ... | [ .x • ᵇ ] , R | ◻ , S | [ .u • ᵇ ] , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
              (λ ≢z′ → ⊥-elim (≢z′ (refl , ,-inj₁ ≡S′))) (λ ≢y′ → ⊥-elim (≢y′ (refl , ,-inj₁ ≡S)))
   ... | [ .x • ᵇ ] , R | ◻ , S | [ .u • ᵇ ] , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ |
       [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ ◻ z′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
              (λ _ → ,-inj₁ ≡S′) (λ ≢y′ → ⊥-elim (≢y′ (refl , ,-inj₁ ≡S)))
   ... | [ .x • ᵇ ] , R | [ • .x 〈 y′ 〉 ᶜ ] , S | ◻ , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ y′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
              (λ ≢z′ → ⊥-elim (≢z′ (refl , ,-inj₁ ≡S′))) (λ _ → ,-inj₁ ≡S)
   ... | [ .x • ᵇ ] , R | [ • .x 〈 y′ 〉 ᶜ ] , S | ◻ , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ |
      [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ y′ z′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
              (λ _ → ,-inj₁ ≡S′) (λ _ → ,-inj₁ ≡S)
   ... | [ .x • ᵇ ] , R | [ • .x 〈 y′ 〉 ᶜ ] , S | [ .u • ᵇ ] , R′ | ◻ , S′ |
      [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ y′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
              (λ ≢z′ → ⊥-elim (≢z′ (refl , ,-inj₁ ≡S′))) (λ _ → ,-inj₁ ≡S)
   ... | [ .x • ᵇ ] , R | [ • .x 〈 y′ 〉 ᶜ ] , S | [ .u • ᵇ ] , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ |
      [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ y′ z′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
              (λ _ → ,-inj₁ ≡S′) (λ _ → ,-inj₁ ≡S)
