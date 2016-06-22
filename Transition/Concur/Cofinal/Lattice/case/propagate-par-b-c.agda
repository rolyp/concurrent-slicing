open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common

module Transition.Concur.Cofinal.Lattice.case.propagate-par-b-c
   {Γ} {P₀ Q₀ S₀ S₀′} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} {F : Q₀ —[ a ᵇ - _ ]→ S₀} {F′ : Q₀ —[ a′ ᶜ - _ ]→ S₀′}
   (𝐹 : F ⌣₁[ ᵇ∇ᶜ ] F′) (P : ↓ P₀) (Q : ↓ Q₀)
   (IH : braiding (ᵇ∇ᶜ {a = a} {a′}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡ tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)) where

   import Ren as ᴿ

   case :
      braiding (ᵇ∇ᶜ {a = a} {a′}) {0} (cong₂ _│_ refl (γ₁ 𝐹))
      (tgt ((ᴿ.push *) P₀ │ᶜ E′/E (⊖₁ 𝐹)) (tgt (P₀ │ᵇ F) [ P │ Q ]))
      ≡
      tgt (P₀ │ᵇ E/E′ (⊖₁ 𝐹)) (tgt (P₀ │ᶜ F′) [ P │ Q ])
   case =
      let S† = tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)
          S‡ = tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)
          open ≅-Reasoning in ≅-to-≡ (
      begin
         braiding ᵇ∇ᶜ (cong₂ _│_ refl (γ₁ 𝐹)) [ (push *̃) P │ S‡ ]
      ≅⟨ reduce-ᵇ∇ᶜ (cong₂ _│_ refl (γ₁ 𝐹)) _ ⟩
         [ (push *̃) P │ S‡ ]
      ≅⟨ [│-]-cong _ (trans (γ₁ 𝐹) (≅-to-≡ (Proc↲ refl (tgt₂ (⊖₁ 𝐹)))))
                     (≅-trans (≅-sym (reduce-ᵇ∇ᶜ (γ₁ 𝐹) _)) (≡-to-≅ IH)) ⟩
         [ (push *̃) P │ S† ]
      ∎)
