open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common

import Relation.Binary.EqReasoning as EqReasoning
import Name as ᴺ
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
      (pop-y*E′/E : (ᴿ.pop y *) R₀ —[ u • ᵇ - _ ]→ (ᴿ.suc (ᴿ.pop y) *) (tgt₁ (⊖₁ 𝐸)))
      (≡pop-y*E′/E : (ᴿ.pop y *ᵇ) (E′/E (⊖₁ 𝐸)) ≡ pop-y*E′/E)
      where

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
      {!!} --
   ... | _ , R | _ , S | _ , R′ | _ , S′ | [ ≡R ] | [ ≡S ] | [ ≡R′ ] | [ ≡S′ ] = {!!}
{-
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
-}
