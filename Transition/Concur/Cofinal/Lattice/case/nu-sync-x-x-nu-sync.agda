open import ConcurrentSlicingCommon
import Relation.Binary.EqReasoning as EqReasoning

open import Transition.Concur.Cofinal.Lattice.Common
import Name as ᴺ
import Ren as ᴿ

module Transition.Concur.Cofinal.Lattice.case.nu-sync-x-x-nu-sync
   {Γ} {x u : Name Γ} {P₀ Q₀ R₀ R′₀ S₀ S′₀} {E : P₀ —[ x • ᵇ - _ ]→ R₀}
   {E′ : P₀ —[ u • ᵇ - _ ]→ R′₀} {F : Q₀ —[ (• x) ᵇ - _ ]→ S₀} {F′ : Q₀ —[ (• u) ᵇ - _ ]→ S′₀}
   (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (𝐹 : F ⌣₁[ ˣ∇ˣ ] F′) (P : ↓ P₀) (Q : ↓ Q₀)
   (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂(⊖₁ 𝐸); Q′₀ = tgt₁ (⊖₁ 𝐹); Q″₀ = tgt₂(⊖₁ 𝐹))
   (IH₁ : braiding (ᵇ∇ᵇ {a = x •} {u •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
   (IH₂ : braiding (ˣ∇ˣ {x = x} {u}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡ tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q))
   (let γ : (ᴿ.pop ᴺ.zero *) P′₀ ≡ (ᴿ.pop ᴺ.zero *) P″₀
        γ = let open EqReasoning (setoid _) in
          begin
             (ᴿ.pop ᴺ.zero *) P′₀
          ≡⟨ sym (pop-swap _) ⟩
             (ᴿ.pop ᴺ.zero *) ((ᴿ.swap *) P′₀)
          ≡⟨ cong (ᴿ.pop ᴺ.zero *) (γ₁ 𝐸) ⟩
             (ᴿ.pop ᴺ.zero *) P″₀
          ∎
        α : ν ((ᴿ.pop ᴺ.zero *) P′₀ │ Q′₀) ≡ Proc↱ refl (ν ((ᴿ.pop ᴺ.zero *) P″₀ │ Q″₀))
        α = cong ν_ (cong₂ _│_ γ (γ₁ 𝐹))) where

   module _
      (R : ↓ R₀) (R′ : ↓ R′₀) (S : ↓ S₀) (S′ : ↓ S′₀) (y y′ : ↓ ᴺ.zero) (≡R : tgt E P ≡ R) (≡R′ : tgt E′ P ≡ R′)
      (≡S : tgt F Q ≡ S) (≡S′ : tgt F′ Q ≡ S′) where

{-
      base : (P′ : ↓ (ᴿ.suc idᶠ *) P′₀) (Q′ : ↓ Q′₀) (P″ : ↓ (ᴿ.suc idᶠ *) P″₀) (Q″ : ↓ Q″₀) →
             tgt ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸))) ((repl y *̃) R) ≡ P′ → tgt (E′/E (⊖₁ 𝐹)) S ≡ Q′ →
             tgt ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸))) ((repl y′ *̃) R′) ≡ P″ → tgt (E/E′ (⊖₁ 𝐹)) S′ ≡ Q″ → (y† y‡ : ↓ ᴺ.zero) →
             braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} α
             [ ν [ (pop y† *̃) P′ │ Q′ ] ] ≡ [ ν [ (pop y‡ *̃) P″ │ Q″ ] ]
      base P′ Q′ P″ Q″ ≡P′ ≡Q′ ≡P″ ≡Q″ y† y‡ =
         let β : (pop y† *̃) P′ ≅ (pop y‡ *̃) P″
             β = let open ≅-Reasoning in
                begin
                   (pop y† *̃) P′
                ≡⟨ cong (pop y† *̃) (sym ≡P′) ⟩
                   (pop y† *̃) (tgt ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸))) ((repl y *̃) R))
                ≡⟨ cong (pop y† *̃) (sym (renᵇ-tgt-comm (E′/E (⊖₁ 𝐸)) (repl y) R)) ⟩
                   (pop y† *̃) ((suc (repl y) *̃) (tgt (E′/E (⊖₁ 𝐸)) R))
                ≡⟨ cong ((pop y† *̃) ∘ᶠ (suc (repl y) *̃) ∘ᶠ tgt (E′/E (⊖₁ 𝐸))) (sym ≡R) ⟩
                   (pop y† *̃) ((suc (repl y) *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))
                ≡⟨ cong₂ (λ z z′ → ((pop z *̃) ((suc (repl z′) *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))) trustMe trustMe ⟩
                   (pop y′ *̃) ((suc (repl y‡) *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))
                ≅⟨ ≅-sym (pop-swap̃ y′ y‡ _) ⟩
                   (pop y‡ *̃) ((suc (repl y′) *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐸) ((pop y‡ *̃) ∘ᶠ (suc (repl y′) *̃)) (≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐸) _)) ⟩
                   (pop y‡ *̃) ((suc (repl y′) *̃) (braiding ᵇ∇ᵇ {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                ≡⟨ cong ((pop y‡ *̃) ∘ᶠ (suc (repl y′) *̃)) IH₁ ⟩
                   (pop y‡ *̃) ((suc (repl y′) *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)))
                ≡⟨ cong ((pop y‡ *̃) ∘ᶠ ((suc (repl y′) *̃) ∘ᶠ tgt (E/E′ (⊖₁ 𝐸)))) ≡R′ ⟩
                   (pop y‡ *̃) ((suc (repl y′) *̃) (tgt (E/E′ (⊖₁ 𝐸)) R′))
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
-}

      postulate
       subcase :
             braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} α
             (π₂ (step⁻ (νᶜ (E′/E (⊖₁ 𝐸) │• E′/E (⊖₁ 𝐹))) (ν [ R │ S ]))) ≡
             π₂ (step⁻ (νᶜ (E/E′ (⊖₁ 𝐸) │• E/E′ (⊖₁ 𝐹))) (ν [ R′ │ S′ ]))

{-
      subcase
         with step ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸))) ((repl y *̃) R) | step (E′/E (⊖₁ 𝐹)) S |
              step ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸))) ((repl y′ *̃) R′) | step (E/E′ (⊖₁ 𝐹)) S′ |
              inspect (step ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸)))) ((repl y *̃) R) | inspect (step (E′/E (⊖₁ 𝐹))) S |
              inspect (step ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)))) ((repl y′ *̃) R′) | inspect (step (E/E′ (⊖₁ 𝐹))) S′
      ... | ◻ , P′ | ◻ , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ ◻
      ... | ◻ , P′ | ◻ , Q′ | ◻ , P″ | [ q ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ ◻
      ... | ◻ , P′ | ◻ , Q′ | [ (._ •) ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ ◻
      ... | ◻ , P′ | ◻ , Q′ | [ (._ •) ᵇ ] , P″ | [ • ._ 〈 y‡ 〉 ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ y‡
      ... | ◻ , P′ | [ _ ] , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ ◻
      ... | ◻ , P′ | [ _ ] , Q′ | ◻ , P″ | [ _ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ ◻
      ... | ◻ , P′ | [ _ ] , Q′ | [ (._ •) ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ ◻
      ... | ◻ , P′ | [ _ ] , Q′ | [ (._ •) ᵇ ] , P″ | [ • ._ 〈 y‡ 〉 ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ y‡
      ... | [ (._ •) ᵇ ] , P′ | ◻ , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ ◻
      ... | [ (._ •) ᵇ ] , P′ | ◻ , Q′ | ◻ , P″ | [ _ ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ ◻
      ... | [ (._ •) ᵇ ] , P′ | ◻ , Q′ | [ (._ •) ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ ◻
      ... | [ (._ •) ᵇ ] , P′ | ◻ , Q′ | [ (._ •) ᵇ ] , P″ | [ • ._ 〈 y‡ 〉 ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) ◻ y‡
      ... | [ (._ •) ᵇ ] , P′ | [ • ._ 〈 y† 〉 ᶜ ] , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) y† ◻
      ... | [ (._ •) ᵇ ] , P′ | [ • ._ 〈 y† 〉 ᶜ ] , Q′ | ◻ , P″ | [ _ ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) y† ◻
      ... | [ (._ •) ᵇ ] , P′ | [ • ._ 〈 y† 〉 ᶜ ] , Q′ | [ (._ •) ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) y† ◻
      ... | [ (._ •) ᵇ ] , P′ | [ • ._ 〈 y† 〉 ᶜ ] , Q′ | [ (._ •) ᵇ ] , P″ | [ • ._ 〈 y‡ 〉 ᶜ ] , Q″ |
         [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″) y† y‡
-}

   case :
      braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} α
      (tgt (νᶜ (E′/E (⊖₁ 𝐸) │• E′/E (⊖₁ 𝐹))) (tgt (E │ᵥ F) [ P │ Q ]))
      ≡
      (tgt (νᶜ (E/E′ (⊖₁ 𝐸) │• E/E′ (⊖₁ 𝐹))) (tgt (E′ │ᵥ F′) [ P │ Q ]))
   case
      with step E′ P | step E P | step F′ Q | step F Q |
           inspect (step E′) P | inspect (step E) P | inspect (step F′) Q | inspect (step F) Q
   ... | _ , R′ | _ , R | _ , S′ | _ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] = {!!}
{-
   ... | ◻ , R′ | ◻ , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | ◻ , R′ | ◻ , R | ◻ , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | ◻ , R′ | ◻ , R | [ (• ._) ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | ◻ , R′ | ◻ , R | [ (• ._) ᵇ ] , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | ◻ , R′ | [ ._ • ᵇ ] , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | ◻ , R′ | [ ._ • ᵇ ] , R | ◻ , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ zero ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | ◻ , R′ | [ ._ • ᵇ ] , R | [ (• ._) ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | ◻ , R′ | [ ._ • ᵇ ] , R | [ (• ._) ᵇ ] , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ zero ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | ◻ , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | ◻ , R | ◻ , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | ◻ , R | [ (• ._) ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ zero (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | ◻ , R | [ (• ._) ᵇ ] , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ zero (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | [ ._ • ᵇ ] , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | [ ._ • ᵇ ] , R | ◻ , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ zero ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | [ ._ • ᵇ ] , R | [ (• ._) ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ zero (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | [ ._ • ᵇ ] , R | [ (• ._) ᵇ ] , S′ | [ (• ._) ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ zero zero (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
-}
