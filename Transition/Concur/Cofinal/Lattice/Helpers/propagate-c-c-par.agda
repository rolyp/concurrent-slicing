open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common

module Transition.Concur.Cofinal.Lattice.Helpers.propagate-c-c-par
   {Γ} {P₀ Q₀ R₀ R₀′} {a a′ : Actionᶜ Γ} {E : P₀ —[ a ᶜ - _ ]→ R₀} {E′ : P₀ —[ a′ ᶜ - _ ]→ R₀′}
   (𝐸 : E ⌣₁[ ᶜ∇ᶜ ] E′) (P : ↓ P₀) (Q : ↓ Q₀)
   (IH : braiding (ᶜ∇ᶜ {a = a} {a′}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
   where

   case :
      braiding (ᶜ∇ᶜ {a = a} {a′}) {0} (cong₂ _│_ (γ₁ 𝐸) refl)
      (tgt (E′/E (⊖₁ 𝐸) ᶜ│ Q₀) (tgt (E ᶜ│ Q₀) [ P │ Q ]))
      ≡
      tgt (E/E′ (⊖₁ 𝐸) ᶜ│ Q₀) (tgt (E′ ᶜ│ Q₀) [ P │ Q ])
   case =
      let S† = tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)
          S‡ = tgt (E′/E (⊖₁ 𝐸)) (tgt E P)
          open ≅-Reasoning in ≅-to-≡ (
      begin
         braiding ᶜ∇ᶜ (cong₂ _│_ (γ₁ 𝐸) refl) [ S‡ │  Q ]
      ≅⟨ reduce-ᶜ∇ᶜ (cong₂ _│_ (γ₁ 𝐸) refl) _ ⟩
         [ S‡ │ Q ]
      ≅⟨ [-│]-cong _ (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl (tgt₂ (⊖₁ 𝐸)))))
                     (≅-trans (≅-sym (reduce-ᶜ∇ᶜ (γ₁ 𝐸) _)) (≡-to-≅ IH)) ⟩
         [ S† │ Q ]
      ∎)
