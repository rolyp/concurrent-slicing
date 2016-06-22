open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common

module Transition.Concur.Cofinal.Lattice.case.propagate-par-c-c
   {Γ} {P₀ Q₀ S₀ S₀′} {a a′ : Actionᶜ Γ} {F : Q₀ —[ a ᶜ - _ ]→ S₀} {F′ : Q₀ —[ a′ ᶜ - _ ]→ S₀′}
   (𝐹 : F ⌣₁[ ᶜ∇ᶜ ] F′) (P : ↓ P₀) (Q : ↓ Q₀)
   (IH : braiding (ᶜ∇ᶜ {a = a} {a′}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡ tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)) where

   case :
      braiding (ᶜ∇ᶜ {a = a} {a′}) {0} (cong₂ _│_ refl (γ₁ 𝐹))
      (tgt (P₀ │ᶜ E′/E (⊖₁ 𝐹)) (tgt (P₀ │ᶜ F) [ P │ Q ]))
      ≡
      tgt (P₀ │ᶜ E/E′ (⊖₁ 𝐹)) (tgt (P₀ │ᶜ F′) [ P │ Q ])
   case =
      let S† = tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)
          S‡ = tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)
          open ≅-Reasoning in ≅-to-≡ (
      begin
         braiding ᶜ∇ᶜ (cong₂ _│_ refl (γ₁ 𝐹)) [ P │ S‡ ]
      ≅⟨ reduce-ᶜ∇ᶜ (cong₂ _│_ refl (γ₁ 𝐹)) _ ⟩
         [ P │ S‡ ]
      ≅⟨ [│-]-cong _ (trans (γ₁ 𝐹) (≅-to-≡ (Proc↲ refl (tgt₂ (⊖₁ 𝐹)))))
                     (≅-trans (≅-sym (reduce-ᶜ∇ᶜ (γ₁ 𝐹) _)) (≡-to-≅ IH)) ⟩
         [ P │ S† ]
      ∎)
