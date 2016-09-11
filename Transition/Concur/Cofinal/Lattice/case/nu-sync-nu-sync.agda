open import ConcurrentSlicingCommon
import Relation.Binary.EqReasoning as EqReasoning
open import Transition.Concur.Cofinal.Lattice.Common
import Name as ᴺ
import Ren as ᴿ

module Transition.Concur.Cofinal.Lattice.case.nu-sync-nu-sync
   {Γ} {x u : Name Γ} {P₀ Q₀ R₀ R′₀ S₀ S′₀} {E : P₀ —[ x • ᵇ - _ ]→ R₀}
   {E′ : P₀ —[ u • ᵇ - _ ]→ R′₀} {F : Q₀ —[ (• x) ᵇ - _ ]→ S₀} {F′ : Q₀ —[ (• u) ᵇ - _ ]→ S′₀}
   (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (𝐹 : F ⌣₁[ ᵇ∇ᵇ ] F′) (P : ↓ P₀) (Q : ↓ Q₀)
   (IH₁ : braiding (ᵇ∇ᵇ {a = x •} {u •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
   (IH₂ : braiding (ᵇ∇ᵇ {a = • x} {• u}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡ tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)) where

   module _
      (R : ↓ R₀) (R′ : ↓ R′₀) (S : ↓ S₀) (S′ : ↓ S′₀) (y y′ : ↓ ᴺ.zero) (≡R : tgt E P ≡ R) (≡R′ : tgt E′ P ≡ R′)
      (≡S : tgt F Q ≡ S) (≡S′ : tgt F′ Q ≡ S′) where

      base : (P′ : ↓ (ᴿ.suc idᶠ *) (tgt₁ (⊖₁ 𝐸))) (Q′ : ↓ tgt₁ (⊖₁ 𝐹)) (P″ : ↓ (ᴿ.suc idᶠ *) (tgt₂ (⊖₁ 𝐸)))
             (Q″ : ↓ tgt₂ (⊖₁ 𝐹)) (y† y‡ : ↓ ᴺ.zero) → tgt ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸))) ((repl y′ *̃) R) ≡ P′ →
             tgt (E′/E (⊖₁ 𝐹)) S ≡ Q′ → tgt ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸))) ((repl y *̃) R′) ≡ P″ → tgt (E/E′ (⊖₁ 𝐹)) S′ ≡ Q″ →
             braid̂ (γ₁ (𝐸 │ᵥ′ 𝐹)) [ ν [ ν [ (repl y† *̃) P′ │ Q′ ] ] ] ≡ [ ν [ ν [ (repl y‡ *̃) P″ │ Q″ ] ] ]
      base P′ Q′ P″ Q″ y† y‡ ≡P′ ≡Q′ ≡P″ ≡Q″ =
         let cheat₁ : weaken ̃ y ≡ y†
             cheat₁ = trustMe
             cheat₂ : weaken ̃ y′ ≡ y‡
             cheat₂ = trustMe
             β : (swap *̃) ((repl y† *̃) P′) ≅ (repl y‡ *̃) P″
             β = let open ≅-Reasoning in
                begin
                   (swap *̃) ((repl y† *̃) P′)
                ≡⟨ cong ((swap *̃) ∘ᶠ (repl y† *̃)) (sym ≡P′) ⟩
                   (swap *̃) ((repl y† *̃) (tgt ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸))) ((repl y′ *̃) R)))
                ≡⟨ cong ((swap *̃) ∘ᶠ (repl y† *̃)) (sym (renᵇ-tgt-comm (E′/E (⊖₁ 𝐸)) (repl y′) R)) ⟩
                   (swap *̃) ((repl y† *̃) ((suc (repl y′) *̃) (tgt (E′/E (⊖₁ 𝐸)) R)))
                ≡⟨ cong ((swap *̃) ∘ᶠ (repl y† *̃) ∘ᶠ (suc (repl y′) *̃) ∘ᶠ tgt (E′/E (⊖₁ 𝐸))) (sym ≡R) ⟩
                   (swap *̃) ((repl y† *̃) ((suc (repl y′) *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                ≡⟨ cong (λ z → (swap *̃) ((repl z *̃) ((suc (repl y′) *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))) (sym cheat₁) ⟩
                   (swap *̃) ((repl (weaken ̃ y) *̃) ((suc (repl y′) *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                ≅⟨ ≅-sym (id-suc-id-swap-id-suc-id̃ y y′ (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))) ⟩
                   (repl (weaken ̃ y′) *̃) ((suc (repl y) *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                ≡⟨ cong (λ z → ((repl z *̃) ((suc (repl y) *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))))) cheat₂ ⟩
                   (repl y‡ *̃) ((suc (repl y) *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐸) ((repl y‡ *̃) ∘ᶠ (suc (repl y) *̃)) (≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐸) _)) ⟩
                   (repl y‡ *̃) ((suc (repl y) *̃) (braiding (ᵇ∇ᵇ {a = x •} {u •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                ≡⟨ cong ((repl y‡ *̃) ∘ᶠ (suc (repl y) *̃)) IH₁ ⟩
                   (repl y‡ *̃) ((suc (repl y) *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)))
                ≡⟨ cong ((repl y‡ *̃) ∘ᶠ (suc (repl y) *̃) ∘ᶠ tgt (E/E′ (⊖₁ 𝐸))) ≡R′ ⟩
                   (repl y‡ *̃) ((suc (repl y) *̃) (tgt (E/E′ (⊖₁ 𝐸)) R′))
                ≡⟨ cong (repl y‡ *̃) (renᵇ-tgt-comm (E/E′ (⊖₁ 𝐸)) (repl y) R′) ⟩
                   (repl y‡ *̃) (tgt ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸))) ((repl y *̃) R′))
                ≡⟨ cong (repl y‡ *̃) ≡P″ ⟩
                   (repl y‡ *̃) P″
                ∎
             γ : (swap *̃) Q′ ≅ Q″
             γ = let open ≅-Reasoning in
                begin
                   (swap *̃) Q′
                ≡⟨ cong (swap *̃) (trans (sym ≡Q′) (cong (tgt (E′/E (⊖₁ 𝐹))) (sym ≡S))) ⟩
                   (swap *̃) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q))
                ≅⟨ ≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐹) _) ⟩
                   braiding (ᵇ∇ᵇ {a = • x} {• u}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q))
                ≡⟨ IH₂ ⟩
                   tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)
                ≡⟨ trans (cong (tgt (E/E′ (⊖₁ 𝐹))) ≡S′) ≡Q″ ⟩
                   Q″
                ∎
             α : (ᴿ.swap *) ((idᶠ *) ((ᴿ.suc idᶠ *) (tgt₁ (⊖₁ 𝐸)))) ≡ (idᶠ *) ((ᴿ.suc idᶠ *) (tgt₂ (⊖₁ 𝐸)))
             α = let open EqReasoning (setoid _) in
                begin
                   (ᴿ.swap *) ((idᶠ *) ((ᴿ.suc idᶠ *) (tgt₁ (⊖₁ 𝐸))))
                ≡⟨ cong (ᴿ.swap *) (*-preserves-id _) ⟩
                   (ᴿ.swap *) ((ᴿ.suc idᶠ *) (tgt₁ (⊖₁ 𝐸)))
                ≡⟨ cong (ᴿ.swap *) (+-id-elim 1 _) ⟩
                   (ᴿ.swap *) (tgt₁ (⊖₁ 𝐸))
                ≡⟨ γ₁ 𝐸 ⟩
                   tgt₂ (⊖₁ 𝐸)
                ≡⟨ sym (+-id-elim 1 _) ⟩
                   (ᴿ.suc idᶠ *) (tgt₂ (⊖₁ 𝐸))
                ≡⟨ sym (*-preserves-id _) ⟩
                   (idᶠ *) ((ᴿ.suc idᶠ *) (tgt₂ (⊖₁ 𝐸)))
                ∎
             open ≅-Reasoning in ≅-to-≡ (
         begin
            braid̂ (γ₁ (𝐸 │ᵥ′ 𝐹)) [ ν [ ν [ (repl y† *̃) P′ │ Q′ ] ] ]
         ≅⟨ coerce-braid ((repl y† *̃) P′) Q′ ⟩
            [ ν [ ν ((swap *̃) [ (repl y† *̃) P′ │ Q′ ]) ] ]
         ≅⟨ [ν-]-cong (cong ν_ (cong₂ _│_ α (γ₁ 𝐹)))
                      ([ν-]-cong (cong₂ _│_ α (γ₁ 𝐹)) ([-│-]-cong α β (γ₁ 𝐹) γ)) ⟩
            [ ν [ ν [ (repl y‡ *̃) P″ │ Q″ ] ] ]
         ∎) where
             α₁ = trans (sym (*-preserves-id _)) (cong (idᶠ *) (sym (+-id-elim 1 (tgt₁ (⊖₁ 𝐸)))))
             α₂ = trans (sym (*-preserves-id _)) (cong (idᶠ *) (sym (+-id-elim 1 (tgt₂ (⊖₁ 𝐸)))))

             jibble : γ₁ (𝐸 │ᵥ′ 𝐹) ≅ νν-swapᵣ (tgt₁ (⊖₁ 𝐸) │ tgt₁ (⊖₁ 𝐹))
             jibble rewrite sym α₁ | sym α₂ | sym (γ₁ 𝐸) | sym (γ₁ 𝐹) = ≅-refl

             hubble : νν-swapᵣ (tgt₁ (⊖₁ 𝐸) │ tgt₁ (⊖₁ 𝐹)) ≅ νν-swapᵣ ((idᶠ *) ((ᴿ.suc idᶠ *) (tgt₁ (⊖₁ 𝐸))) │ tgt₁ (⊖₁ 𝐹))
             hubble = ≅-cong (λ P → νν-swapᵣ (P │ tgt₁ (⊖₁ 𝐹))) (≡-to-≅ α₁)

             quibble : γ₁ (𝐸 │ᵥ′ 𝐹) ≅ νν-swapᵣ ((idᶠ *) ((ᴿ.suc idᶠ *) (tgt₁ (⊖₁ 𝐸))) │ tgt₁ (⊖₁ 𝐹))
             quibble = ≅-trans jibble hubble

             nibble : (P′ : ↓ (idᶠ *) ((ᴿ.suc idᶠ *) (tgt₁ (⊖₁ 𝐸)))) (Q′ : ↓ tgt₁ (⊖₁ 𝐹)) →
                      braid̂ (νν-swapᵣ ((idᶠ *) ((ᴿ.suc idᶠ *) (tgt₁ (⊖₁ 𝐸))) │ tgt₁ (⊖₁ 𝐹))) [ ν [ ν [ P′ │ Q′ ] ] ] ≡
                      [ ν [ ν ((swap *̃) [ P′ │ Q′ ]) ] ]
             nibble _ _ = refl

             open import Braiding.Proc using (_⋉̂_)

             glah : {P₁ P₂ Q₁ Q₂ : Proc (Γ + 2)} (P′ : ↓ P₁) (Q′ : ↓ Q₁) (γ : ν (ν (P₁ │ Q₁)) ⋉̂ ν (ν (P₂ │ Q₂)))
                    (γ′ : ν (ν (P₁ │ Q₁)) ⋉̂ ν (ν ((ᴿ.swap *) P₁ │ (ᴿ.swap *) Q₁))) →
                    γ ≅ γ′ → braid̂ γ [ ν [ ν [ P′ │ Q′ ] ] ] ≅ braid̂ γ′ [ ν [ ν [ P′ │ Q′ ] ] ]
             glah P′ Q′ γ γ′ _ = {!!}

             dribble : (P′ : ↓ (idᶠ *) ((ᴿ.suc idᶠ *) (tgt₁ (⊖₁ 𝐸)))) (Q′ : ↓ tgt₁ (⊖₁ 𝐹)) →
                       braid̂ (γ₁ (𝐸 │ᵥ′ 𝐹)) [ ν [ ν [ P′ │ Q′ ] ] ] ≅
                       braid̂ (νν-swapᵣ ((idᶠ *) ((ᴿ.suc idᶠ *) (tgt₁ (⊖₁ 𝐸))) │ tgt₁ (⊖₁ 𝐹))) [ ν [ ν [ P′ │ Q′ ] ] ]
             dribble P′ Q′ = glah P′ Q′ (γ₁ (𝐸 │ᵥ′ 𝐹)) (νν-swapᵣ ((idᶠ *) ((ᴿ.suc idᶠ *) (tgt₁ (⊖₁ 𝐸))) │ tgt₁ (⊖₁ 𝐹))) quibble

             coerce-braid : (P′ : ↓ (idᶠ *) ((ᴿ.suc idᶠ *) (tgt₁ (⊖₁ 𝐸)))) (Q′ : ↓ tgt₁ (⊖₁ 𝐹)) →
                            braid̂ (γ₁ (𝐸 │ᵥ′ 𝐹)) [ ν [ ν [ P′ │ Q′ ] ] ] ≅ [ ν [ ν ((swap *̃) [ P′ │ Q′ ]) ] ]
             coerce-braid P′ Q′ = ≅-trans (dribble P′ Q′) (≡-to-≅ (nibble P′ Q′))

      subcase :
         braid̂ (γ₁ (𝐸 │ᵥ′ 𝐹))
         (tgt (νᶜ ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸)) │ᵥ E′/E (⊖₁ 𝐹))) [ ν [ (repl y′ *̃) R │ S ] ])
         ≡
         tgt (νᶜ ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) │ᵥ E/E′ (⊖₁ 𝐹))) [ ν [ (repl y *̃) R′ │ S′ ] ]
      subcase
         with step ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸))) ((repl y′ *̃) R) | step (E′/E (⊖₁ 𝐹)) S |
              step ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸))) ((repl y *̃) R′) | step (E/E′ (⊖₁ 𝐹)) S′ |
              inspect (step ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸)))) ((repl y′ *̃) R) | inspect (step (E′/E (⊖₁ 𝐹))) S |
              inspect (step ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)))) ((repl y *̃) R′) | inspect (step (E/E′ (⊖₁ 𝐹))) S′
      ... | ◻ , P′ | ◻ , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | ◻ , Q′ | ◻ , P″ | [ • ._ ﹙ y‡ ﹚ ᵇ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ y‡ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | ◻ , Q′ | [ ._ • ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | ◻ , Q′ | [ ._ • ᵇ ] , P″ | [ • ._ ﹙ y‡ ﹚ ᵇ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ y‡ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | [ • ._ ﹙ y† ﹚ ᵇ ] , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | [ • ._ ﹙ y† ﹚ ᵇ ] , Q′ | ◻ , P″ | [ • ._ ﹙ y‡ ﹚ ᵇ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† y‡ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | [ • ._ ﹙ y† ﹚ ᵇ ] , Q′ | [ ._ • ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | [ • ._ ﹙ y† ﹚ ᵇ ] , Q′ | [ ._ • ᵇ ] , P″ | [ • ._ ﹙ y‡ ﹚ ᵇ ] , Q″ |
         [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† y‡ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ ._ • ᵇ ] , P′ | ◻ , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ ._ • ᵇ ] , P′ | ◻ , Q′ | ◻ , P″ | [ • ._ ﹙ y‡ ﹚ ᵇ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ y‡ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ ._ • ᵇ ] , P′ | ◻ , Q′ | [ ._ • ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ ._ • ᵇ ] , P′ | ◻ , Q′ | [ ._ • ᵇ ] , P″ | [ • ._ ﹙ y‡ ﹚ ᵇ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ y‡ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ ._ • ᵇ ] , P′ | [ • ._ ﹙ y† ﹚ ᵇ ] , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ ._ • ᵇ ] , P′ | [ • ._ ﹙ y† ﹚ ᵇ ] , Q′ | ◻ , P″ | [ • ._ ﹙ y‡ ﹚ ᵇ ] , Q″ |
         [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† y‡ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ ._ • ᵇ ] , P′ | [ • ._ ﹙ y† ﹚ ᵇ ] , Q′ | [ ._ • ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ ._ • ᵇ ] , P′ | [ • ._ ﹙ y† ﹚ ᵇ ] , Q′ | [ ._ • ᵇ ] , P″ | [ • ._ ﹙ y‡ ﹚ ᵇ ] , Q″ |
         [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† y‡ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)

   case : braid̂ (γ₁ (𝐸 │ᵥ′ 𝐹))
          (tgt (νᶜ ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸)) │ᵥ E′/E (⊖₁ 𝐹))) (tgt (E │ᵥ F) [ P │ Q ]))
          ≡
          tgt (νᶜ ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) │ᵥ E/E′ (⊖₁ 𝐹))) (tgt (E′ │ᵥ F′) [ P │ Q ])
   case
      with step E′ P | step E P | step F′ Q | step F Q |
           inspect (step E′) P | inspect (step E) P | inspect (step F′) Q | inspect (step F) Q
   ... | ◻ , R′ | ◻ , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | ◻ , R′ | ◻ , R | ◻ , S′ | [ • ._ ﹙ y ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | ◻ , R′ | ◻ , R | [ • ._ ﹙ y′ ﹚ ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | ◻ , R′ | ◻ , R | [ • ._ ﹙ y′ ﹚ ᵇ ] , S′ | [ • ._ ﹙ y ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | ◻ , R′ | [ ._ • ᵇ ] , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | ◻ , R′ | [ ._ • ᵇ ] , R | ◻ , S′ | [ • ._ ﹙ y ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | ◻ , R′ | [ ._ • ᵇ ] , R | [ • ._ ﹙ y′ ﹚ ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | ◻ , R′ | [ ._ • ᵇ ] , R | [ • ._ ﹙ y′ ﹚ ᵇ ] , S′ | [ • ._ ﹙ y ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | ◻ , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | ◻ , R | ◻ , S′ | [ • ._ ﹙ y ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | ◻ , R | [ • ._ ﹙ y′ ﹚ ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | ◻ , R | [ • ._ ﹙ y′ ﹚ ᵇ ] , S′ | [ • ._ ﹙ y ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | [ ._ • ᵇ ] , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | [ ._ • ᵇ ] , R | ◻ , S′ | [ • ._ ﹙ y ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | [ ._ • ᵇ ] , R | [ • ._ ﹙ y′ ﹚ ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | [ ._ • ᵇ ] , R | [ • ._ ﹙ y′ ﹚ ᵇ ] , S′ | [ • ._ ﹙ y ﹚ ᵇ ] , S |
      [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
