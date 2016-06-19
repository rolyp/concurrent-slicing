open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common

module Transition.Concur.Cofinal.Lattice.Helpers.propagate-par-b-b
   {Γ} {P₀ Q₀ S₀ S₀′} {x u : Name Γ} {F : Q₀ —[ (• x) ᵇ - _ ]→ S₀} {F′ : Q₀ —[ (• u) ᵇ - _ ]→ S₀′}
   (𝐹 : F ⌣₁[ ˣ∇ˣ ] F′) (P : ↓ P₀) (Q : ↓ Q₀)
   (IH : braiding (ˣ∇ˣ {x = x} {u}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡ tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q))
   where

   import Ren as ᴿ
   import Transition as ᵀ

   case :
      braiding (ˣ∇ˣ {x = x} {u}) {0} (cong₂ _│_ refl (γ₁ 𝐹))
      (tgt ((ᴿ.push *) P₀ │ᶜ E′/E (⊖₁ 𝐹)) (tgt (P₀ │ᵇ F) [ P │ Q ]))
      ≡
      tgt ((ᴿ.push *) P₀ │ᶜ E/E′ (⊖₁ 𝐹)) (tgt (P₀ │ᵇ F′) [ P │ Q ])
   case =
      let S† = tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)
          S‡ = tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)
          open ≅-Reasoning in ≅-to-≡ (
      begin
         braiding (ˣ∇ˣ {x = x} {u}) {0} (cong₂ _│_ refl (γ₁ 𝐹)) [ (push *̃) P │ S‡ ]
      ≅⟨ reduce-ˣ∇ˣ {x = x} {u} (cong₂ _│_ refl (γ₁ 𝐹)) _ ⟩
         [ (push *̃) P │ S‡ ]
      ≅⟨ [│-]-cong _ (trans (γ₁ 𝐹) (≅-to-≡ (Proc↲ refl (tgt₂ (⊖₁ 𝐹)))))
                     (≅-trans (≅-sym (reduce-ˣ∇ˣ {x = x} {u} (γ₁ 𝐹) _)) (≡-to-≅ IH)) ⟩
         [ (push *̃) P │ S† ]
      ∎)
