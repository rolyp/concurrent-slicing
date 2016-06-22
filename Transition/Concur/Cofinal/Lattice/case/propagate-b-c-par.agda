open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common

module Transition.Concur.Cofinal.Lattice.case.propagate-b-c-par
   {Γ} {P₀ Q₀ R₀ R₀′} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} {E : P₀ —[ a ᵇ - _ ]→ R₀} {E′ : P₀ —[ a′ ᶜ - _ ]→ R₀′}
   (𝐸 : E ⌣₁[ ᵇ∇ᶜ ] E′) (P : ↓ P₀) (Q : ↓ Q₀)
   (IH : braiding (ᵇ∇ᶜ {a = a} {a′}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
   where

   import Ren as ᴿ

   case :
      braiding (ᵇ∇ᶜ {a = a} {a′}) {0} (cong₂ _│_ (γ₁ 𝐸) refl)
      (tgt (E′/E (⊖₁ 𝐸) ᶜ│ (ᴿ.push *) Q₀) (tgt (E ᵇ│ Q₀) [ P │ Q ]))
      ≡
      tgt (E/E′ (⊖₁ 𝐸) ᵇ│ Q₀) (tgt (E′ ᶜ│ Q₀) [ P │ Q ])
   case =
      let S† = tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)
          S‡ = tgt (E′/E (⊖₁ 𝐸)) (tgt E P)
          open ≅-Reasoning in ≅-to-≡ (
      begin
         braiding ᵇ∇ᶜ (cong₂ _│_ (γ₁ 𝐸) refl) [ S‡ │ (push *̃) Q ]
      ≅⟨ reduce-ᵇ∇ᶜ (cong₂ _│_ (γ₁ 𝐸) refl) _ ⟩
         [ S‡ │ (push *̃) Q ]
      ≅⟨ [-│]-cong _ (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl (tgt₂ (⊖₁ 𝐸)))))
                     (≅-trans (≅-sym (reduce-ᵇ∇ᶜ (γ₁ 𝐸) _)) (≡-to-≅ IH)) ⟩
         [ S† │ (push *̃) Q ]
      ∎)
