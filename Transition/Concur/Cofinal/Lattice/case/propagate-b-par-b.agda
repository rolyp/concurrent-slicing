open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common

module Transition.Concur.Cofinal.Lattice.case.propagate-b-par-b
   {Γ} {P₀ Q₀ R₀ S₀} {a a′ : Actionᵇ Γ} (E : P₀ —[ a ᵇ - _ ]→ R₀) (F : Q₀ —[ a′ ᵇ - _ ]→ S₀)
   (P : ↓ P₀) (Q : ↓ Q₀)
   where

   import Ren as ᴿ
   import Transition as ᵀ

   case :
      braiding (ᵇ∇ᵇ {a = a} {a′}) {0}
      (sym (cong₂ _│_ (swap∘push R₀) (swap∘suc-push S₀)))
      (tgt (R₀ │ᵇ (ᴿ.push *ᵇ) F) (tgt (E ᵇ│ Q₀) [ P │ Q ]))
      ≡
      tgt ((ᴿ.push *ᵇ) E ᵇ│ S₀) (tgt (P₀ │ᵇ F) [ P │ Q ])
   case =
      let S† : tgt ((ᴿ.push *ᵇ) E) ((push *̃) P) ≅ (swap *̃) ((push *̃) (tgt E P))
          S† = ≅-trans (≡-to-≅ (sym (renᵇ-tgt-comm E push P))) (swap∘push̃ _)
          S‡ : (push *̃) (tgt F Q) ≅ (swap *̃) (tgt ((ᴿ.push *ᵇ) F) ((push *̃) Q))
          S‡ = ≅-trans (swap∘suc-push̃ _) (≡-to-≅ (cong (swap *̃) (renᵇ-tgt-comm F push Q)))
          open ≅-Reasoning in ≅-to-≡ (
      begin
         braiding (ᵇ∇ᵇ {a = a} {a′}) {0} (sym (cong₂ _│_ (swap∘push R₀) (swap∘suc-push S₀)))
                                        [ (push *̃) (tgt E P) │ tgt ((ᴿ.push *ᵇ) F) ((push *̃) Q) ]
      ≅⟨ reduce-ᵇ∇ᵇ (sym (cong₂ _│_ (swap∘push R₀) (swap∘suc-push S₀))) _ ⟩
         [ (swap *̃) ((push *̃) (tgt E P)) │ (swap *̃) (tgt ((ᴿ.push *ᵇ) F) ((push *̃) Q)) ]
      ≅⟨ ≅-sym ([-│-]-cong (swap∘push R₀) S† (swap∘suc-push S₀) S‡) ⟩
         [ tgt ((ᴿ.push *ᵇ) E) ((push *̃) P) │ (push *̃) (tgt F Q) ]
      ∎)
