open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common

import Relation.Binary.EqReasoning as EqReasoning
import Name as ᴺ
import Name.Lattice as ᴺ̃
import Ren as ᴿ

module Transition.Concur.Cofinal.Lattice.case.sync-nu-sync
   {Γ} {x u y : Name Γ} {P₀ Q₀ R₀ R′₀ S₀ S′₀} {E : P₀ —[ x • ᵇ - _ ]→ R₀} {E′ : P₀ —[ u • ᵇ - _ ]→ R′₀}
   {F : Q₀ —[ • x 〈 y 〉 ᶜ - _ ]→ S₀} {F′ : Q₀ —[ (• u) ᵇ - _ ]→ S′₀} (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (𝐹 : F ⌣₁[ ᶜ∇ᵇ ] F′)
   (P : ↓ P₀) (Q : ↓ Q₀)
   (IH₁ : braiding (ᵇ∇ᵇ {a = x •} {u •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
   (IH₂ : braiding (ᶜ∇ᵇ {a = • x 〈 y 〉} {• u}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡ tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q))
   (let
      P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂(⊖₁ 𝐸)
      α = let open EqReasoning (setoid _) in
         begin
            ((ᴿ.suc (ᴿ.pop y) *) P′₀)
         ≡⟨ cong (ᴿ.suc (ᴿ.pop y) *) (sym (swap-involutive _ )) ⟩
            (ᴿ.suc (ᴿ.pop y) *) ((ᴿ.swap *) ((ᴿ.swap *) P′₀))
         ≡⟨ cong (ᴿ.suc (ᴿ.pop y) *) (cong (ᴿ.swap *) (γ₁ 𝐸)) ⟩
            (ᴿ.suc (ᴿ.pop y) *) ((ᴿ.swap *) P″₀)
         ≡⟨ suc-pop∘swap y _ ⟩
            (ᴿ.pop (ᴺ.suc y) *) P″₀
         ∎)
   where

   module _
      (pop-y*E′/E : (ᴿ.pop y *) R₀ —[ u • ᵇ - _ ]→ (ᴿ.suc (ᴿ.pop y) *) (tgt₁ (⊖₁ 𝐸))) (R : ↓ R₀) (R′ : ↓ R′₀)
      (S : ↓ S₀) (S′ : ↓ S′₀) (y′ : ↓ y) (≡R : tgt E P ≡ R) (≡R′ : tgt E′ P ≡ R′) (≡S : tgt F Q ≡ S)
      (≡S′ : tgt F′ Q ≡ S′) (≡pop-y*E′/E : (ᴿ.pop y *ᵇ) (E′/E (⊖₁ 𝐸)) ≡ pop-y*E′/E)
      where

      module _
         (P′ : ↓ (ᴿ.suc (ᴿ.pop y) *) P′₀) (Q′ : ↓ tgt₁ (⊖₁ 𝐹)) (P″ : ↓ P″₀) (Q″ : ↓ tgt₂ (⊖₁ 𝐹)) (y† : ↓ ᴺ.suc y)
         (≡P′ : tgt pop-y*E′/E ((pop y′ *̃) R) ≡ P′) (≡Q′ : tgt (E′/E (⊖₁ 𝐹)) S ≡ Q′)
         (≡P″ : tgt (E/E′ (⊖₁ 𝐸)) R′ ≡ P″) (≡Q″ : tgt (E/E′ (⊖₁ 𝐹)) S′ ≡ Q″)
         where

         cheat : ᴺ̃.suc y′ ≡ y†
         cheat = trustMe

         β : P′ ≅ (pop y† *̃) P″
         β = let open ≅-Reasoning in
            begin
               P′
            ≡⟨ sym ≡P′ ⟩
               tgt pop-y*E′/E ((pop y′ *̃) R)
            ≡⟨ cong (tgt pop-y*E′/E ∘ᶠ (pop y′ *̃)) (sym ≡R) ⟩
               tgt pop-y*E′/E ((pop y′ *̃) (tgt E P))
            ≡⟨ cong (λ E† → tgt E† ((pop y′ *̃) (tgt E P))) (sym ≡pop-y*E′/E) ⟩
               tgt ((ᴿ.pop y *ᵇ) (E′/E (⊖₁ 𝐸))) ((pop y′ *̃) (tgt E P))
            ≡⟨ sym (renᵇ-tgt-comm (E′/E (⊖₁ 𝐸)) (pop y′) (tgt E P)) ⟩
               (suc (pop y′) *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
            ≅⟨ ≅-cong✴ ↓_ (sym (swap-involutive P′₀))
                       (suc (pop y′) *̃) (≅-sym (swap-involutivẽ (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))) ⟩
               (suc (pop y′) *̃) ((swap *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
            ≅⟨ suc-pop∘swap̃ y′ ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))) ⟩
               (pop (ᴺ̃.suc y′) *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))
            ≡⟨ cong (λ y‡ → (pop y‡ *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))) cheat ⟩
               (pop y† *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))
            ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐸) (pop y† *̃) (≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐸) _)) ⟩
               (pop y† *̃) (braiding (ᵇ∇ᵇ {a = x •} {u •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))
            ≡⟨ cong (pop y† *̃) IH₁ ⟩
               (pop y† *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
            ≡⟨ cong ((pop y† *̃) ∘ᶠ tgt (E/E′ (⊖₁ 𝐸))) ≡R′ ⟩
               (pop y† *̃) (tgt (E/E′ (⊖₁ 𝐸)) R′)
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
            ≅⟨ ≅-sym (reduce-ᶜ∇ᵇ (γ₁ 𝐹) _) ⟩
               braiding (ᶜ∇ᵇ {a = • x 〈 y 〉} {• u}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q))
            ≡⟨ IH₂ ⟩
               tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)
            ≡⟨ cong (tgt (E/E′ (⊖₁ 𝐹))) ≡S′ ⟩
               tgt (E/E′ (⊖₁ 𝐹)) S′
            ≡⟨ ≡Q″ ⟩
               Q″
            ∎

         base :
            braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (cong ν_ (cong₂ _│_ α (γ₁ 𝐹)))
            [ ν [ P′ │ Q′ ] ]
            ≡
            [ ν [ (pop y† *̃) P″ │ Q″ ] ]
         base =
            let open ≅-Reasoning in ≅-to-≡ (
            begin
               braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (cong ν_ (cong₂ _│_ α (γ₁ 𝐹))) [ ν [ P′ │ Q′ ] ]
            ≅⟨ reduce-ᶜ∇ᶜ (cong ν_ (cong₂ _│_ α (γ₁ 𝐹))) _ ⟩
               [ ν [ P′ │ Q′ ] ]
            ≅⟨ [ν-]-cong (cong₂ _│_ α (γ₁ 𝐹)) ([-│-]-cong α β (γ₁ 𝐹) δ) ⟩
               [ ν [ (pop y† *̃) P″ │ Q″ ] ]
            ∎)

      subcase :
         braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (cong ν_ (cong₂ _│_ α (γ₁ 𝐹)))
         (tgt (pop-y*E′/E │ᵥ E′/E (⊖₁ 𝐹)) [ (pop y′ *̃) R │ S ])
         ≡
         tgt (νᶜ (E/E′ (⊖₁ 𝐸) │• E/E′ (⊖₁ 𝐹))) [ ν [ R′ │ S′ ] ]
      subcase
         with step pop-y*E′/E ((pop y′ *̃) R) | step (E′/E (⊖₁ 𝐹)) S | step (E/E′ (⊖₁ 𝐸)) R′ | step (E/E′ (⊖₁ 𝐹)) S′ |
              inspect (step pop-y*E′/E) ((pop y′ *̃) R) | inspect (step (E′/E (⊖₁ 𝐹))) S |
              inspect (step (E/E′ (⊖₁ 𝐸))) R′ | inspect (step (E/E′ (⊖₁ 𝐹))) S′
      ... | ◻ , P′ | ◻ , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | ◻ , Q′ | ◻ , P″ | [ • ._ 〈 y† 〉 ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | ◻ , Q′ | [ ._ • ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | ◻ , Q′ | [ ._ • ᵇ ] , P″ | [ • ._ 〈 y† 〉 ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | [ (• .u) ᵇ ] , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | [ (• .u) ᵇ ] , Q′ | ◻ , P″ | [ • ._ 〈 y† 〉 ᶜ ] , Q″ |
         [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | [ (• .u) ᵇ ] , Q′ | [ ._ • ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | [ (• .u) ᵇ ] , Q′ | [ ._ • ᵇ ] , P″ | [ • ._ 〈 y† 〉 ᶜ ] , Q″ |
         [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ .u • ᵇ ] , P′ | ◻ , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ .u • ᵇ ] , P′ | ◻ , Q′ | ◻ , P″ | [ • ._ 〈 y† 〉 ᶜ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ .u • ᵇ ] , P′ | ◻ , Q′ | [ ._ • ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ .u • ᵇ ] , P′ | ◻ , Q′ | [ ._ • ᵇ ] , P″ | [ • ._ 〈 y† 〉 ᶜ ] , Q″ |
         [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ .u • ᵇ ] , P′ | [ (• .u) ᵇ ] , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ .u • ᵇ ] , P′ | [ (• .u) ᵇ ] , Q′ | ◻ , P″ | [ • ._ 〈 y† 〉 ᶜ ] , Q″ |
         [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ .u • ᵇ ] , P′ | [ (• .u) ᵇ ] , Q′ | [ ._ • ᵇ ] , P″ | ◻ , Q″ |
         [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ ◻ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ .u • ᵇ ] , P′ | [ (• .u) ᵇ ] , Q′ | [ ._ • ᵇ ] , P″ | [ • ._ 〈 y† 〉 ᶜ ] , Q″ |
         [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ y† (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)

   case :
      braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (γ₁ (𝐸 │•ᵥ 𝐹))
      (tgt (E′/E (⊖₁ (𝐸 │•ᵥ 𝐹))) (tgt (E │• F) [ P │ Q ]))
      ≡
      (tgt (E/E′ (⊖₁ (𝐸 │•ᵥ 𝐹))) (tgt (E′ │ᵥ F′) [ P │ Q ]))
   case
      with (ᴿ.pop y *ᵇ) (E′/E (⊖₁ 𝐸)) | inspect (ᴿ.pop y *ᵇ) (E′/E (⊖₁ 𝐸))
   ... | pop-y*E′/E | [ ≡pop-y*E′/E ]
      with step E P | step F Q | step E′ P | step F′ Q |
           inspect (step E) P | inspect (step F) Q | inspect (step E′) P | inspect (step F′) Q
   ... | ◻ , R | ◻ , S | ◻ , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E R R′ S S′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E
   ... | ◻ , R | ◻ , S | ◻ , R′ | [ (• .u) ᵇ ] , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E R R′ S S′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E
   ... | ◻ , R | ◻ , S | [ .u • ᵇ ] , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E R R′ S S′ ◻(,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E
   ... | ◻ , R | ◻ , S | [ .u • ᵇ ] , R′ | [ (• .u) ᵇ ] , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E R R′ S S′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E
   ... | ◻ , R | [ • .x 〈 y′ 〉 ᶜ ] , S | ◻ , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E R R′ S S′ y′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E
   ... | ◻ , R | [ • .x 〈 y′ 〉 ᶜ ] , S | ◻ , R′ | [ (• .u) ᵇ ] , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E R R′ S S′ y′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E
   ... | ◻ , R | [ • .x 〈 y′ 〉 ᶜ ] , S | [ .u • ᵇ ] , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E R R′ S S′ y′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E
   ... | ◻ , R | [ • .x 〈 y′ 〉 ᶜ ] , S | [ .u • ᵇ ] , R′ | [ (• .u) ᵇ ] , S′ |
       [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E R R′ S S′ y′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E
   ... | [ .x • ᵇ ] , R | ◻ , S | ◻ , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E R R′ S S′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E
   ... | [ .x • ᵇ ] , R | ◻ , S | ◻ , R′ | [ (• .u) ᵇ ] , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E R R′ S S′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E
   ... | [ .x • ᵇ ] , R | ◻ , S | [ .u • ᵇ ] , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E R R′ S S′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E
   ... | [ .x • ᵇ ] , R | ◻ , S | [ .u • ᵇ ] , R′ | [ (• .u) ᵇ ] , S′ |
       [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E R R′ S S′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E
   ... | [ .x • ᵇ ] , R | [ • .x 〈 y′ 〉 ᶜ ] , S | ◻ , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E R R′ S S′ y′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E
   ... | [ .x • ᵇ ] , R | [ • .x 〈 y′ 〉 ᶜ ] , S | ◻ , R′ | [ (• .u) ᵇ ] , S′ |
      [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E R R′ S S′ y′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E
   ... | [ .x • ᵇ ] , R | [ • .x 〈 y′ 〉 ᶜ ] , S | [ .u • ᵇ ] , R′ | ◻ , S′ |
      [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E R R′ S S′ y′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E
   ... | [ .x • ᵇ ] , R | [ • .x 〈 y′ 〉 ᶜ ] , S | [ .u • ᵇ ] , R′ | [ (• .u) ᵇ ] , S′ |
      [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E R R′ S S′ y′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E
