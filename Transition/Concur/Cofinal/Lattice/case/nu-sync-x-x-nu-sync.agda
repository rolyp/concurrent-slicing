open import ConcurrentSlicingCommon
import Relation.Binary.EqReasoning as EqReasoning

open import Transition.Concur.Cofinal.Lattice.Common
import Name as ᴺ
import Name.Lattice as ᴺ̃
import Ren as ᴿ

module Transition.Concur.Cofinal.Lattice.case.nu-sync-x-x-nu-sync
   {Γ} {x u : Name Γ} {P₀ Q₀ R₀ R′₀ S₀ S′₀} {E : P₀ —[ x • ᵇ - _ ]→ R₀}
   {E′ : P₀ —[ u • ᵇ - _ ]→ R′₀} {F : Q₀ —[ (• x) ᵇ - _ ]→ S₀} {F′ : Q₀ —[ (• u) ᵇ - _ ]→ S′₀}
   (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (𝐹 : F ⌣₁[ ˣ∇ˣ ] F′) (P : ↓ P₀) (Q : ↓ Q₀)
   (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂(⊖₁ 𝐸); Q′₀ = tgt₁ (⊖₁ 𝐹); Q″₀ = tgt₂(⊖₁ 𝐹))
   (IH₁ : braiding (ᵇ∇ᵇ {a = x •} {u •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
   (IH₂ : braiding (ˣ∇ˣ {x = x} {u}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡ tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q))
   (let γ = let open EqReasoning (setoid _) in
          begin
             (ᴿ.pop ᴺ.zero *) ((ᴿ.suc idᶠ *) P′₀)
          ≡⟨ cong (ᴿ.pop ᴺ.zero *) (+-id-elim 1 P′₀) ⟩
             (ᴿ.pop ᴺ.zero *) P′₀
          ≡⟨ sym (pop-swap _) ⟩
             (ᴿ.pop ᴺ.zero *) ((ᴿ.swap *) P′₀)
          ≡⟨ cong (ᴿ.pop ᴺ.zero *) (γ₁ 𝐸) ⟩
             (ᴿ.pop ᴺ.zero *) P″₀
          ≡⟨ cong (ᴿ.pop ᴺ.zero *) (sym (+-id-elim 1 P″₀)) ⟩
             (ᴿ.pop ᴺ.zero *) ((ᴿ.suc idᶠ *) P″₀)
          ∎
        α : ν ((ᴿ.pop ᴺ.zero *) ((ᴿ.suc idᶠ *) P′₀) │ Q′₀) ≡ Proc↱ refl (ν ((ᴿ.pop ᴺ.zero *) ((ᴿ.suc idᶠ *) P″₀) │ Q″₀))
        α = (cong ν_ (cong₂ _│_ γ (γ₁ 𝐹))) {-γ-}) where

   module _
      (R : ↓ R₀) (R′ : ↓ R′₀) (S : ↓ S₀) (S′ : ↓ S′₀) (y y′ : ᴺ̃.↓_ {ᴺ.suc Γ} ᴺ.zero) (≡R : tgt E P ≡ R)
      (≡R′ : tgt E′ P ≡ R′) (≡S : tgt F Q ≡ S) (≡S′ : tgt F′ Q ≡ S′)
      (≡y : (y ≡ ◻ × action F Q ≡ ◻ → ⊥) → action F Q ≡ [ • x ﹙ y ﹚ ᵇ ])
      (≡y′ : (y′ ≡ ◻ × action F′ Q ≡ ◻ → ⊥) → action F′ Q ≡ [ • u ﹙ y′ ﹚ ᵇ ])
      where

      z₁≡z₂ : (z₁ z₂ : ↓ ᴺ.zero)
              (α : (z₁ ≡ ◻ × action F′ Q ≡ ◻ → ⊥) → action F′ Q ≡ [ • u ﹙ z₁ ﹚ ᵇ ])
              (β : (z₂ ≡ ◻ × action (E′/E (⊖₁ 𝐹)) S ≡ ◻ → ⊥) → action (E′/E (⊖₁ 𝐹)) S ≡ [ • ᴺ.suc u 〈 z₂ 〉 ᶜ ]) →
              z₁ ≡ z₂
      z₁≡z₂ ◻ ◻ _ _ = refl
      z₁≡z₂ [ .ᴺ.zero ] [ .ᴺ.zero ] _ _ = refl
      z₁≡z₂ ◻ [ .ᴺ.zero ] α β =
         let δ′ : residual ˣ∇ˣ (action F′ Q) ≡ [ • ᴺ.suc u 〈 [ ᴺ.zero ] 〉 ᶜ ]
             δ′ = let open EqReasoning (setoid _) in
                begin
                   residual ˣ∇ˣ (action F′ Q)
                ≡⟨ sym (π₁ (ᴬgamma₁ 𝐹 Q)) ⟩
                   action (E′/E (⊖₁ 𝐹)) (tgt F Q)
                ≡⟨ cong (action (E′/E (⊖₁ 𝐹))) ≡S ⟩
                   action (E′/E (⊖₁ 𝐹)) S
                ≡⟨ β (λ { (() , _) }) ⟩
                   [ • ᴺ.suc u 〈 [ ᴺ.zero ] 〉 ᶜ ]
                ∎
             δ : action F′ Q ≡ [ • u ﹙ [ ᴺ.zero ] ﹚ ᵇ ]
             δ = inj-residual ˣ∇ˣ (action F′ Q) _ δ′
         in ⊥-elim ([•x﹙◻﹚ᵇ]≢[•x﹙[zero]﹚ᵇ] (trans (sym (α (λ { (_ , δ′) → ◻≢[-] (trans (sym δ′) δ) }))) δ))
      z₁≡z₂ [ .ᴺ.zero ] ◻ α β =
         let δ : action (E′/E (⊖₁ 𝐹)) S ≡ [ • ᴺ.suc u 〈 [ ᴺ.zero ] 〉 ᶜ ]
             δ = let open EqReasoning (setoid _) in
                begin
                   action (E′/E (⊖₁ 𝐹)) S
                ≡⟨ cong (action (E′/E (⊖₁ 𝐹))) (sym ≡S) ⟩
                   action (E′/E (⊖₁ 𝐹)) (tgt F Q)
                ≡⟨ π₁ (ᴬgamma₁ 𝐹 Q) ⟩
                   residual ˣ∇ˣ (action F′ Q)
                ≡⟨ cong (residual ˣ∇ˣ) (α (λ { (() , _) })) ⟩
                   [ • ᴺ.suc u 〈 [ ᴺ.zero ] 〉 ᶜ ]
                ∎
         in ⊥-elim ([•x〈◻〉ᶜ]≢[•x〈[-]〉ᶜ] (trans (sym (β (λ { (_ , δ′) → ◻≢[-] (trans (sym δ′) δ) }))) δ))

      y₁≡y₂ : (y₁ : ↓ ᴺ.zero) (y₂ : ↓ ᴺ.zero)
              (α : (y₁ ≡ ◻ × action F Q ≡ ◻ → ⊥) → action F Q ≡ [ • x ﹙ y₁ ﹚ ᵇ ])
              (β : (y₂ ≡ ◻ × action (E/E′ (⊖₁ 𝐹)) S′ ≡ ◻ → ⊥) → action (E/E′ (⊖₁ 𝐹)) S′ ≡ [ • ᴺ.suc x 〈 y₂ 〉 ᶜ ]) →
              y₁ ≡ y₂
      y₁≡y₂ ◻ ◻ _ _ = refl
      y₁≡y₂ [ .ᴺ.zero ] [ .ᴺ.zero ] _ _ = refl
      y₁≡y₂ ◻ [ .ᴺ.zero ] α β =
         let δ′ : residual ˣ∇ˣ (action F Q) ≡ [ • ᴺ.suc x 〈 [ ᴺ.zero ] 〉 ᶜ ]
             δ′ = let open EqReasoning (setoid _) in
                begin
                   residual ˣ∇ˣ (action F Q)
                ≡⟨ sym (π₂ (ᴬgamma₁ 𝐹 Q)) ⟩
                   action (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)
                ≡⟨ cong (action (E/E′ (⊖₁ 𝐹))) ≡S′ ⟩
                   action (E/E′ (⊖₁ 𝐹)) S′
                ≡⟨ β (λ { (() , _) }) ⟩
                   [ • ᴺ.suc x 〈 [ ᴺ.zero ] 〉 ᶜ ]
                ∎
             δ : action F Q ≡ [ • x ﹙ [ ᴺ.zero ] ﹚ ᵇ ]
             δ = inj-residual ˣ∇ˣ (action F Q) _ δ′
         in ⊥-elim ([•x﹙◻﹚ᵇ]≢[•x﹙[zero]﹚ᵇ] (trans (sym (α (λ { (_ , δ′) → ◻≢[-] (trans (sym δ′) δ) }))) δ))
      y₁≡y₂ [ .ᴺ.zero ] ◻ α β =
         let δ : action (E/E′ (⊖₁ 𝐹)) S′ ≡ [ • ᴺ.suc x 〈 [ ᴺ.zero ] 〉 ᶜ ]
             δ = let open EqReasoning (setoid _) in
                begin
                   action (E/E′ (⊖₁ 𝐹)) S′
                ≡⟨ cong (action (E/E′ (⊖₁ 𝐹))) (sym ≡S′) ⟩
                   action (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)
                ≡⟨ π₂ (ᴬgamma₁ 𝐹 Q) ⟩
                   residual ˣ∇ˣ (action F Q)
                ≡⟨ cong (residual ˣ∇ˣ) (α (λ { (() , _) })) ⟩
                   [ • ᴺ.suc x 〈 [ ᴺ.zero ] 〉 ᶜ ]
                ∎
         in ⊥-elim ([•x〈◻〉ᶜ]≢[•x〈[-]〉ᶜ] (trans (sym (β (λ { (_ , δ′) → ◻≢[-] (trans (sym δ′) δ) }))) δ))

      base : (P′ : ↓ (ᴿ.suc idᶠ *) P′₀) (Q′ : ↓ Q′₀) (P″ : ↓ (ᴿ.suc idᶠ *) P″₀) (Q″ : ↓ Q″₀) (y† y‡ : ↓ ᴺ.zero) →
             tgt ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸))) ((repl y *̃) R) ≡ P′ → tgt (E′/E (⊖₁ 𝐹)) S ≡ Q′ →
             tgt ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸))) ((repl y′ *̃) R′) ≡ P″ → tgt (E/E′ (⊖₁ 𝐹)) S′ ≡ Q″ →
             ((y† ≡ ◻ × action (E′/E (⊖₁ 𝐹)) S ≡ ◻ → ⊥) → action (E′/E (⊖₁ 𝐹)) S ≡ [ • ᴺ.suc u 〈 y† 〉 ᶜ ]) →
             ((y‡ ≡ ◻ × action (E/E′ (⊖₁ 𝐹)) S′ ≡ ◻ → ⊥) → action (E/E′ (⊖₁ 𝐹)) S′ ≡ [ • ᴺ.suc x 〈 y‡ 〉 ᶜ ]) →
             braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} α
             [ ν [ (pop y† *̃) P′ │ Q′ ] ] ≡ [ ν [ (pop y‡ *̃) P″ │ Q″ ] ]
      base P′ Q′ P″ Q″ y† y‡ ≡P′ ≡Q′ ≡P″ ≡Q″ ≡y† ≡y‡ =
         let β : (pop y† *̃) P′ ≅ (pop y‡ *̃) P″
             β = let open ≅-Reasoning in
                begin
                   (pop y† *̃) P′
                ≡⟨ cong (pop y† *̃) (sym ≡P′) ⟩
                   (pop y† *̃) (tgt ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸))) ((repl y *̃) R))
                ≡⟨ cong (pop y† *̃) (sym (renᵇ-tgt-comm (E′/E (⊖₁ 𝐸)) (repl y) R)) ⟩
                   (pop y† *̃) ((suc (repl y) *̃) (tgt ((E′/E (⊖₁ 𝐸))) R))
                ≡⟨ cong ((pop y† *̃) ∘ᶠ (suc (repl y) *̃) ∘ᶠ tgt (E′/E (⊖₁ 𝐸))) (sym ≡R) ⟩
                   (pop y† *̃) ((suc (repl y) *̃) (tgt ((E′/E (⊖₁ 𝐸))) (tgt E P)))
                ≅⟨ ≅-sym (id-pop-swap̃ y y† (tgt ((E′/E (⊖₁ 𝐸))) (tgt E P))) ⟩
                   (pop y *̃) ((suc (repl y†) *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                ≡⟨ cong₂ (λ z z′ → (pop z *̃) ((suc (repl z′) *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))))
                         (y₁≡y₂ y y‡ ≡y ≡y‡) (sym (z₁≡z₂ y′ y† ≡y′ ≡y†)) ⟩
                   (pop y‡ *̃) ((suc (repl y′) *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐸) ((pop y‡ *̃) ∘ᶠ (suc (repl y′) *̃)) (≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐸) _)) ⟩
                   (pop y‡ *̃) ((suc (repl y′) *̃) (braiding (ᵇ∇ᵇ {a = x •} {u •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                ≡⟨ cong ((pop y‡ *̃) ∘ᶠ (suc (repl y′) *̃)) IH₁ ⟩
                   (pop y‡ *̃) ((suc (repl y′) *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)))
                ≡⟨ cong ((pop y‡ *̃) ∘ᶠ (suc (repl y′) *̃) ∘ᶠ tgt ((E/E′ (⊖₁ 𝐸)))) ≡R′ ⟩
                   (pop y‡ *̃) ((suc (repl y′) *̃) (tgt ((E/E′ (⊖₁ 𝐸))) R′))
                ≡⟨ cong (pop y‡ *̃) (renᵇ-tgt-comm (E/E′ (⊖₁ 𝐸)) (repl y′) R′) ⟩
                   (pop y‡ *̃) (tgt ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸))) ((repl y′ *̃) R′))
                ≡⟨ cong (pop y‡ *̃) ≡P″ ⟩
                   (pop y‡ *̃) P″
                ∎
             δ = Q′ ≅ Q″
             δ = let open ≅-Reasoning in
                begin
                   Q′
                ≡⟨ sym ≡Q′ ⟩
                   tgt (E′/E (⊖₁ 𝐹)) S
                ≡⟨ cong (tgt (E′/E (⊖₁ 𝐹))) (sym ≡S) ⟩
                   tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)
                ≅⟨ ≅-sym (reduce-ˣ∇ˣ {x = x} {u} (γ₁ 𝐹) _) ⟩
                   braiding (ˣ∇ˣ {x = x} {u}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q))
                ≡⟨ IH₂ ⟩
                   tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)
                ≡⟨ cong (tgt (E/E′ (⊖₁ 𝐹))) ≡S′ ⟩
                   tgt (E/E′ (⊖₁ 𝐹)) S′
                ≡⟨ ≡Q″ ⟩
                   Q″
                ∎
             open ≅-Reasoning in ≅-to-≡ (
         begin
            braiding ᶜ∇ᶜ {0} α [ ν [ (pop y† *̃) P′ │ Q′ ] ]
         ≅⟨ reduce-ᶜ∇ᶜ α _ ⟩
            [ ν [ (pop y† *̃) P′ │ Q′ ] ]
         ≅⟨ [ν-]-cong (cong₂ _│_ γ (γ₁ 𝐹)) ([-│-]-cong γ β (γ₁ 𝐹) δ) ⟩
            [ ν [ (pop y‡ *̃) P″ │ Q″ ] ]
         ∎)

      subcase :
          braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} α
          (π₂ (step⁻ (νᶜ ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸)) │• E′/E (⊖₁ 𝐹))) (ν [ (repl y *̃) R │ S ]))) ≡
          π₂ (step⁻ (νᶜ ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) │• E/E′ (⊖₁ 𝐹))) (ν [ (repl y′ *̃) R′ │ S′ ]))
      subcase
         with step ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸))) ((repl y *̃) R) | step (E′/E (⊖₁ 𝐹)) S |
              step ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸))) ((repl y′ *̃) R′) | step (E/E′ (⊖₁ 𝐹)) S′ |
              inspect (step ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸)))) ((repl y *̃) R) | inspect (step (E′/E (⊖₁ 𝐹))) S |
              inspect (step ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)))) ((repl y′ *̃) R′) | inspect (step (E/E′ (⊖₁ 𝐹))) S′
      ... | [ ._ • ᵇ ] , P′ | [ • ._ 〈 y† 〉 ᶜ ] , Q′ | [ ._ • ᵇ ] , P″ | [ • ._ 〈 y‡ 〉 ᶜ ] , Q″ |
         [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† y‡ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ _ → ,-inj₁ ≡Q′) (λ _ → ,-inj₁ ≡Q″)
      ... | ◻ , P′ | ◻ , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ ≢y† → ⊥-elim (≢y† (refl , ,-inj₁ ≡Q′))) (λ ≢y‡ → ⊥-elim (≢y‡ (refl , ,-inj₁ ≡Q″)))
      ... | ◻ , P′ | ◻ , Q′ | ◻ , P″ | [ • ._ 〈 y‡ 〉 ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ y‡ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ ≢y† → ⊥-elim (≢y† (refl , ,-inj₁ ≡Q′))) (λ _ → ,-inj₁ ≡Q″)
      ... | ◻ , P′ | ◻ , Q′ | [ (._ •) ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ ≢y† → ⊥-elim (≢y† (refl , ,-inj₁ ≡Q′))) (λ ≢y‡ → ⊥-elim (≢y‡ (refl , ,-inj₁ ≡Q″)))
      ... | ◻ , P′ | ◻ , Q′ | [ (._ •) ᵇ ] , P″ | [ • ._ 〈 y‡ 〉 ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ y‡ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ ≢y† → ⊥-elim (≢y† (refl , ,-inj₁ ≡Q′))) (λ _ → ,-inj₁ ≡Q″)
      ... | ◻ , P′ | [ • ._ 〈 y† 〉 ᶜ ] , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ _ → ,-inj₁ ≡Q′) (λ ≢y‡ → ⊥-elim (≢y‡ (refl , ,-inj₁ ≡Q″)))
      ... | ◻ , P′ | [ • ._ 〈 y† 〉 ᶜ ] , Q′ | ◻ , P″ | [ • ._ 〈 y‡ 〉 ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† y‡ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ _ → ,-inj₁ ≡Q′) (λ _ → ,-inj₁ ≡Q″)
      ... | ◻ , P′ | [ • ._ 〈 y† 〉 ᶜ ] , Q′ | [ ._ • ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ _ → ,-inj₁ ≡Q′) (λ ≢y‡ → ⊥-elim (≢y‡ (refl , ,-inj₁ ≡Q″)))
      ... | ◻ , P′ | [ • ._ 〈 y† 〉 ᶜ ] , Q′ | [ ._ • ᵇ ] , P″ | [ • ._ 〈 y‡ 〉 ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† y‡ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ _ → ,-inj₁ ≡Q′) (λ _ → ,-inj₁ ≡Q″)
      ... | [ ._ • ᵇ ] , P′ | ◻ , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ ≢y† → ⊥-elim (≢y† (refl , ,-inj₁ ≡Q′))) (λ ≢y‡ → ⊥-elim (≢y‡ (refl , ,-inj₁ ≡Q″)))
      ... | [ ._ • ᵇ ] , P′ | ◻ , Q′ | ◻ , P″ | [ • ._ 〈 y‡ 〉 ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ y‡ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ ≢y† → ⊥-elim (≢y† (refl , ,-inj₁ ≡Q′))) (λ _ → ,-inj₁ ≡Q″)
      ... | [ ._ • ᵇ ] , P′ | ◻ , Q′ | [ ._ • ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ ≢y† → ⊥-elim (≢y† (refl , ,-inj₁ ≡Q′))) (λ ≢y‡ → ⊥-elim (≢y‡ (refl , ,-inj₁ ≡Q″)))
      ... | [ ._ • ᵇ ] , P′ | ◻ , Q′ | [ ._ • ᵇ ] , P″ | [ • ._ 〈 y‡ 〉 ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ y‡ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ ≢y† → ⊥-elim (≢y† (refl , ,-inj₁ ≡Q′))) (λ _ → ,-inj₁ ≡Q″)
      ... | [ ._ • ᵇ ] , P′ | [ • ._ 〈 y† 〉 ᶜ ] , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ _ → ,-inj₁ ≡Q′) (λ ≢y‡ → ⊥-elim (≢y‡ (refl , ,-inj₁ ≡Q″)))
      ... | [ ._ • ᵇ ] , P′ | [ • ._ 〈 y† 〉 ᶜ ] , Q′ | ◻ , P″ | [ • ._ 〈 y‡ 〉 ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† y‡ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ _ → ,-inj₁ ≡Q′) (λ _ → ,-inj₁ ≡Q″)
      ... | [ ._ • ᵇ ] , P′ | [ • ._ 〈 y† 〉 ᶜ ] , Q′ | [ ._ • ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
              (λ _ → ,-inj₁ ≡Q′) (λ ≢y‡ → ⊥-elim (≢y‡ (refl , ,-inj₁ ≡Q″)))

   case :
      braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} α
      (tgt (νᶜ ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸)) │• E′/E (⊖₁ 𝐹))) (tgt (E │ᵥ F) [ P │ Q ]))
      ≡
      (tgt (νᶜ ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) │• E/E′ (⊖₁ 𝐹))) (tgt (E′ │ᵥ F′) [ P │ Q ]))
   case
      with step E′ P | step E P | step F′ Q | step F Q |
           inspect (step E′) P | inspect (step E) P | inspect (step F′) Q | inspect (step F) Q
   ... | ◻ , R′ | ◻ , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
              (λ ≢y′ → ⊥-elim (≢y′ (refl , ,-inj₁ ≡S))) (λ ≢y → ⊥-elim (≢y (refl , ,-inj₁ ≡S′)))
   ... | [ ._ • ᵇ ] , R′ | [ ._ • ᵇ ] , R | [ • ._ ﹙ y ﹚ ᵇ ] , S′ | [ • ._ ﹙ y′ ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
              (λ _ → ,-inj₁ ≡S) (λ _ → ,-inj₁ ≡S′)
   ... | ◻ , R′ | ◻ , R | ◻ , S′ | [ • ._ ﹙ y′ ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
              (λ _ → ,-inj₁ ≡S) (λ ≢y → ⊥-elim (≢y (refl , ,-inj₁ ≡S′)))
   ... | ◻ , R′ | ◻ , R | [ • ._ ﹙ y ﹚ ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
              (λ ≢y′ → ⊥-elim (≢y′ (refl , ,-inj₁ ≡S))) (λ _ → ,-inj₁ ≡S′)
   ... | ◻ , R′ | ◻ , R | [ • ._ ﹙ y ﹚ ᵇ ] , S′ | [ • ._ ﹙ y′ ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
              (λ _ → ,-inj₁ ≡S) (λ _ → ,-inj₁ ≡S′)
   ... | ◻ , R′ | [ ._ • ᵇ ] , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
              (λ ≢y′ → ⊥-elim (≢y′ (refl , ,-inj₁ ≡S))) (λ ≢y → ⊥-elim (≢y (refl , ,-inj₁ ≡S′)))
   ... | ◻ , R′ | [ ._ • ᵇ ] , R | ◻ , S′ | [ • ._ ﹙ y′ ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
              (λ _ → ,-inj₁ ≡S) (λ ≢y → ⊥-elim (≢y (refl , ,-inj₁ ≡S′)))
   ... | ◻ , R′ | [ ._ • ᵇ ] , R | [ • ._ ﹙ y ﹚ ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
              (λ ≢y′ → ⊥-elim (≢y′ (refl , ,-inj₁ ≡S)))(λ _ → ,-inj₁ ≡S′)
   ... | ◻ , R′ | [ ._ • ᵇ ] , R | [ • ._ ﹙ y ﹚ ᵇ ] , S′ | [ • ._ ﹙ y′ ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
              (λ _ → ,-inj₁ ≡S) (λ _ → ,-inj₁ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | ◻ , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
              (λ ≢y′ → ⊥-elim (≢y′ (refl , ,-inj₁ ≡S))) (λ ≢y → ⊥-elim (≢y (refl , ,-inj₁ ≡S′)))
   ... | [ ._ • ᵇ ] , R′ | ◻ , R | ◻ , S′ | [ • ._ ﹙ y′ ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
              (λ _ → ,-inj₁ ≡S) (λ ≢y → ⊥-elim (≢y (refl , ,-inj₁ ≡S′)))
   ... | [ ._ • ᵇ ] , R′ | ◻ , R | [ • ._ ﹙ y ﹚ ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
              (λ ≢y′ → ⊥-elim (≢y′ (refl , ,-inj₁ ≡S))) (λ _ → ,-inj₁ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | ◻ , R | [ • ._ ﹙ y ﹚ ᵇ ] , S′ | [ • ._ ﹙ y′ ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
              (λ _ → ,-inj₁ ≡S) (λ _ → ,-inj₁ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | [ ._ • ᵇ ] , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
              (λ ≢y′ → ⊥-elim (≢y′ (refl , ,-inj₁ ≡S))) (λ ≢y → ⊥-elim (≢y (refl , ,-inj₁ ≡S′)))
   ... | [ ._ • ᵇ ] , R′ | [ ._ • ᵇ ] , R | ◻ , S′ | [ • ._ ﹙ y′ ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
              (λ _ → ,-inj₁ ≡S) (λ ≢y → ⊥-elim (≢y (refl , ,-inj₁ ≡S′)))
   ... | [ ._ • ᵇ ] , R′ | [ ._ • ᵇ ] , R | [ • ._ ﹙ y ﹚ ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
              (λ ≢y′ → ⊥-elim (≢y′ (refl , ,-inj₁ ≡S))) (λ _ → ,-inj₁ ≡S′)
