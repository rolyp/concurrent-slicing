open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common

module Transition.Concur.Cofinal.Lattice.Helpers.propagate-b-b-par
   {Γ} {P₀ Q₀ R₀ R₀′}
   where

   import Ren as ᴿ
   import Transition as ᵀ

   module ˣ∇ˣ
      {x u : Name Γ} {E : P₀ —[ (• x) ᵇ - _ ]→ R₀} {E′ : P₀ —[ (• u) ᵇ - _ ]→ R₀′}
      (𝐸 : E ⌣₁[ ˣ∇ˣ ] E′) (P : ↓ P₀) (Q : ↓ Q₀)
      (IH : braiding (ˣ∇ˣ {x = x} {u}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)) where

      case :
          braiding (ˣ∇ˣ {x = x} {u}) {0} (cong₂ _│_ (γ₁ 𝐸) refl)
          (tgt (E′/E (⊖₁ 𝐸) ᶜ│ (ᴿ.push *) Q₀) (tgt (E ᵇ│ Q₀) [ P │ Q ]))
          ≡
          tgt (E/E′ (⊖₁ 𝐸) ᶜ│ (ᴿ.push *) Q₀) (tgt (E′ ᵇ│ Q₀) [ P │ Q ])
      case =
         let S† = tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)
             S‡ = tgt (E′/E (⊖₁ 𝐸)) (tgt E P)
             open ≅-Reasoning in ≅-to-≡ (
         begin
            braiding (ˣ∇ˣ {x = x} {u}) {0} (cong₂ _│_ (γ₁ 𝐸) refl) [ S‡ │ (push *̃) Q ]
         ≅⟨ reduce-ˣ∇ˣ {x = x} {u} (cong₂ _│_ (γ₁ 𝐸) refl) _ ⟩
            [ S‡ │ (push *̃) Q ]
         ≅⟨ [-│]-cong _ (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl (tgt₂ (⊖₁ 𝐸)))))
                        (≅-trans (≅-sym (reduce-ˣ∇ˣ {x = x} {u} (γ₁ 𝐸) _)) (≡-to-≅ IH)) ⟩
            [ S† │ (push *̃) Q ]
         ∎)

   module ᵇ∇ᵇ
      {a a′ : Actionᵇ Γ} {E : P₀ —[ a ᵇ - _ ]→ R₀} {E′ : P₀ —[ a′ ᵇ - _ ]→ R₀′}
      (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (P : ↓ P₀) (Q : ↓ Q₀)
      (IH : braiding (ᵇ∇ᵇ {a = a} {a′}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)) where

      case :
         braiding (ᵇ∇ᵇ {a = a} {a′}) {0} (cong₂ _│_ (γ₁ 𝐸) (swap∘push∘push Q₀))
         (tgt (E′/E (⊖₁ 𝐸) ᵇ│ (ᴿ.push *) Q₀) (tgt (E ᵇ│ Q₀) [ P │ Q ]))
         ≡
         (tgt (E/E′ (⊖₁ 𝐸) ᵇ│ (ᴿ.push *) Q₀) (tgt (E′ ᵇ│ Q₀) [ P │ Q ]))
      case =
         let S† = tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)
             S‡ = tgt (E′/E (⊖₁ 𝐸)) (tgt E P)
             open ≅-Reasoning in ≅-to-≡ (
         begin
            braiding ᵇ∇ᵇ {0} (cong₂ _│_ (γ₁ 𝐸) (swap∘push∘push Q₀)) [ S‡ │ (push *̃) ((push *̃) Q) ]
         ≅⟨ reduce-ᵇ∇ᵇ (cong₂ _│_ (γ₁ 𝐸) (swap∘push∘push Q₀)) _ ⟩
            [ (swap *̃) S‡ │ (swap *̃) ((push *̃) ((push *̃) Q)) ]
         ≅⟨ [-│-]-cong (γ₁ 𝐸) (≅-trans (≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐸) S‡)) (≡-to-≅ IH))
                       (swap∘push∘push Q₀) (swap∘push∘push̃ Q) ⟩
            [ S† │ (push *̃) ((push *̃) Q) ]
         ∎)
