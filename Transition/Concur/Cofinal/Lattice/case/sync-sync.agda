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
      open EqReasoning (setoid _)
      α =
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
      where

      subcase :
         braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (cong₂ _│_ α (γ₁ 𝐹))
         (π₂ (step⁻ (pop-y*E′/E │• E′/E (⊖₁ 𝐹)) ((pop y′ *̃) R │ S)))
         ≡
         π₂ (step⁻ (pop-z*E/E′ │• E/E′ (⊖₁ 𝐹)) ((pop z′ *̃) R′ │ S′))
      subcase
         with step pop-y*E′/E ((pop y′ *̃) R) | step (E′/E (⊖₁ 𝐹)) S |
              step pop-z*E/E′ ((pop z′ *̃) R′) | step (E/E′ (⊖₁ 𝐹)) S′ |
              inspect (step pop-y*E′/E) ((pop y′ *̃) R) | inspect (step (E′/E (⊖₁ 𝐹))) S |
              inspect (step pop-z*E/E′) ((pop z′ *̃) R′) | inspect (step (E/E′ (⊖₁ 𝐹))) S′
      ... | ◻ , P′ | ◻ , P″ | ◻ , Q′ | ◻ , Q″ | [ ≡P′ ] | [ ≡P″ ] | [ ≡Q′ ] | [ ≡Q″ ] = {!!}
      ... | ◻ , P′ | ◻ , P″ | ◻ , Q′ | [ x₁ ] , Q″ | [ ≡P′ ] | [ ≡P″ ] | [ ≡Q′ ] | [ ≡Q″ ] = {!!}
      ... | ◻ , P′ | ◻ , P″ | [ x₁ ] , Q′ | ◻ , Q″ | [ ≡P′ ] | [ ≡P″ ] | [ ≡Q′ ] | [ ≡Q″ ] = {!!}
      ... | ◻ , P′ | ◻ , P″ | [ x₁ ] , Q′ | [ x₂ ] , Q″ | [ ≡P′ ] | [ ≡P″ ] | [ ≡Q′ ] | [ ≡Q″ ] = {!!}
      ... | ◻ , P′ | [ x₁ ] , P″ | ◻ , Q′ | ◻ , Q″ | [ ≡P′ ] | [ ≡P″ ] | [ ≡Q′ ] | [ ≡Q″ ] = {!!}
      ... | ◻ , P′ | [ x₁ ] , P″ | ◻ , Q′ | [ x₂ ] , Q″ | [ ≡P′ ] | [ ≡P″ ] | [ ≡Q′ ] | [ ≡Q″ ] = {!!}
      ... | ◻ , P′ | [ x₁ ] , P″ | [ x₂ ] , Q′ | ◻ , Q″ | [ ≡P′ ] | [ ≡P″ ] | [ ≡Q′ ] | [ ≡Q″ ] = {!!}
      ... | ◻ , P′ | [ x₁ ] , P″ | [ x₂ ] , Q′ | [ x₃ ] , Q″ | [ ≡P′ ] | [ ≡P″ ] | [ ≡Q′ ] | [ ≡Q″ ] = {!!}
      ... | [ x₁ ] , P′ | ◻ , P″ | ◻ , Q′ | ◻ , Q″ | [ ≡P′ ] | [ ≡P″ ] | [ ≡Q′ ] | [ ≡Q″ ] = {!!}
      ... | [ x₁ ] , P′ | ◻ , P″ | ◻ , Q′ | [ x₂ ] , Q″ | [ ≡P′ ] | [ ≡P″ ] | [ ≡Q′ ] | [ ≡Q″ ] = {!!}
      ... | [ x₁ ] , P′ | ◻ , P″ | [ x₂ ] , Q′ | ◻ , Q″ | [ ≡P′ ] | [ ≡P″ ] | [ ≡Q′ ] | [ ≡Q″ ] = {!!}
      ... | [ x₁ ] , P′ | ◻ , P″ | [ x₂ ] , Q′ | [ x₃ ] , Q″ | [ ≡P′ ] | [ ≡P″ ] | [ ≡Q′ ] | [ ≡Q″ ] = {!!}
      ... | [ x₁ ] , P′ | [ x₂ ] , P″ | ◻ , Q′ | ◻ , Q″ | [ ≡P′ ] | [ ≡P″ ] | [ ≡Q′ ] | [ ≡Q″ ] = {!!}
      ... | [ x₁ ] , P′ | [ x₂ ] , P″ | ◻ , Q′ | [ x₃ ] , Q″ | [ ≡P′ ] | [ ≡P″ ] | [ ≡Q′ ] | [ ≡Q″ ] = {!!}
      ... | [ x₁ ] , P′ | [ x₂ ] , P″ | [ x₃ ] , Q′ | ◻ , Q″ | [ ≡P′ ] | [ ≡P″ ] | [ ≡Q′ ] | [ ≡Q″ ] = {!!}
      ... | [ x₁ ] , P′ | [ x₂ ] , P″ | [ x₃ ] , Q′ | [ x₄ ] , Q″ | [ ≡P′ ] | [ ≡P″ ] | [ ≡Q′ ] | [ ≡Q″ ] = {!!}

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
   ... | ◻ , R | ◻ , S | ◻ , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ ◻ z′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
   ... | ◻ , R | ◻ , S | [ .u • ᵇ ] , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
   ... | ◻ , R | ◻ , S | [ .u • ᵇ ] , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ ◻ z′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
   ... | ◻ , R | [ • .x 〈 y′ 〉 ᶜ ] , S | ◻ , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ y′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
   ... | ◻ , R | [ • .x 〈 y′ 〉 ᶜ ] , S | ◻ , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ y′ z′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
   ... | ◻ , R | [ • .x 〈 y′ 〉 ᶜ ] , S | [ .u • ᵇ ] , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ y′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
   ... | ◻ , R | [ • .x 〈 y′ 〉 ᶜ ] , S | [ .u • ᵇ ] , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ |
       [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ y′ z′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
   ... | [ .x • ᵇ ] , R | ◻ , S | ◻ , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
   ... | [ .x • ᵇ ] , R | ◻ , S | ◻ , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ ◻ z′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
   ... | [ .x • ᵇ ] , R | ◻ , S | [ .u • ᵇ ] , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
   ... | [ .x • ᵇ ] , R | ◻ , S | [ .u • ᵇ ] , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ |
       [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ ◻ z′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
   ... | [ .x • ᵇ ] , R | [ • .x 〈 y′ 〉 ᶜ ] , S | ◻ , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ y′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
   ... | [ .x • ᵇ ] , R | [ • .x 〈 y′ 〉 ᶜ ] , S | ◻ , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ |
      [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ y′ z′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
   ... | [ .x • ᵇ ] , R | [ • .x 〈 y′ 〉 ᶜ ] , S | [ .u • ᵇ ] , R′ | ◻ , S′ |
      [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ y′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
   ... | [ .x • ᵇ ] , R | [ • .x 〈 y′ 〉 ᶜ ] , S | [ .u • ᵇ ] , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ |
      [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] =
      subcase pop-y*E′/E pop-z*E/E′ R R′ S S′ y′ z′ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′) ≡pop-y*E′/E ≡pop-z*E/E′
