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
--      (pop-y*E′/E : ↓ _) (≡pop-y*E′/E : (ᴿ.pop y *ᵇ) (E′/E (⊖₁ 𝐸)) ≡ pop-y*E′/E) (y′ : ↓ y)
      (R : ↓ R₀)
      where

{-
      postulate
       subcase :
         braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (cong₂ _│_ α (γ₁ 𝐹))
         (π₂ (step⁻ (pop-y*E′/E │• E′/E (⊖₁ 𝐹)) ((pop y′ *̃) R │ R′)))
         ≡
         π₂ (step⁻ (pop-z*E/E′ │• E/E′ (⊖₁ 𝐹)) ((pop z′ *̃) S │ S′))
-}

   case :
      braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (cong₂ _│_ α (γ₁ 𝐹))
      (tgt (E′/E (⊖₁ (𝐸 │• 𝐹))) (tgt (E │• F) [ P │ Q ]))
      ≡
      tgt (E/E′ (⊖₁ (𝐸 │• 𝐹))) (tgt (E′ │• F′) [ P │ Q ])
   case
      with (ᴿ.pop y *ᵇ) (E′/E (⊖₁ 𝐸)) | (ᴿ.pop z *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E′/E | pop-z*E/E′ rewrite pop∘push u y | pop∘push x z
      with step E P | step F Q | step E′ P | step F′ Q |
           inspect (step E) P | inspect (step F) Q | inspect (step E′) P | inspect (step F′) Q
   ... | ◻ , R | ◻ , S | ◻ , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] = {!!}
   ... | ◻ , R | ◻ , S | ◻ , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] = {!!}
   ... | ◻ , R | ◻ , S | [ .u • ᵇ ] , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] = {!!}
   ... | ◻ , R | ◻ , S | [ .u • ᵇ ] , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] = {!!}
   ... | ◻ , R | [ • .x 〈 y′ 〉 ᶜ ] , S | ◻ , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] = {!!}
   ... | ◻ , R | [ • .x 〈 y′ 〉 ᶜ ] , S | ◻ , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] = {!!}
   ... | ◻ , R | [ • .x 〈 y′ 〉 ᶜ ] , S | [ .u • ᵇ ] , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] = {!!}
   ... | ◻ , R | [ • .x 〈 y′ 〉 ᶜ ] , S | [ .u • ᵇ ] , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ |
       [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] = {!!}
   ... | [ .x • ᵇ ] , R | ◻ , S | ◻ , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] = {!!}
   ... | [ .x • ᵇ ] , R | ◻ , S | ◻ , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] = {!!}
   ... | [ .x • ᵇ ] , R | ◻ , S | [ .u • ᵇ ] , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] = {!!}
   ... | [ .x • ᵇ ] , R | ◻ , S | [ .u • ᵇ ] , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ |
       [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] = {!!}
   ... | [ .x • ᵇ ] , R | [ • .x 〈 y′ 〉 ᶜ ] , S | ◻ , R′ | ◻ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] = {!!}
   ... | [ .x • ᵇ ] , R | [ • .x 〈 y′ 〉 ᶜ ] , S | ◻ , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ |
      [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] = {!!}
   ... | [ .x • ᵇ ] , R | [ • .x 〈 y′ 〉 ᶜ ] , S | [ .u • ᵇ ] , R′ | ◻ , S′ |
      [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] = {!!}
   ... | [ .x • ᵇ ] , R | [ • .x 〈 y′ 〉 ᶜ ] , S | [ .u • ᵇ ] , R′ | [ • .u 〈 z′ 〉 ᶜ ] , S′ |
      [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] = {!!}
