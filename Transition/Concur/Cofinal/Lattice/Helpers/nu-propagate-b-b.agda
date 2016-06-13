module Transition.Concur.Cofinal.Lattice.Helpers.nu-propagate-b-b where

   open import ConcurrentSlicingCommon
   import Relation.Binary.EqReasoning as EqReasoning
   import Ren as ᴿ
   open import Transition.Concur.Cofinal.Lattice.Common

   private
      base : ∀ {Γ P₀ R₀ R′₀} {a a′ : Actionᵇ Γ} {E : P₀ —[ (ᴿ.push *) a ᵇ - _ ]→ R₀}
             {E′ : P₀ —[ (ᴿ.push *) a′ ᵇ - _ ]→ R′₀} (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (P : ↓ P₀) (R : ↓ R₀) (R′ : ↓ R′₀)
             (S : ↓ (ᴿ.suc ᴿ.swap *) (tgt₁ (⊖₁ 𝐸))) (S′ : ↓ (ᴿ.suc ᴿ.swap *) (tgt₂ (⊖₁ 𝐸))) →
             tgt E P ≡ R → tgt E′ P ≡ R′ → tgt ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) ≡ S →
             tgt ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) ≡ S′ →
             braiding (ᵇ∇ᵇ{a = (ᴿ.push *) a} {(ᴿ.push *) a′}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡
             tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P) →
             let α = let open EqReasoning (setoid _) in
                    begin
                       (ᴿ.suc ᴿ.swap *) ((ᴿ.swap *) ((ᴿ.suc ᴿ.swap *) (tgt₁ (⊖₁ 𝐸))))
                    ≡⟨ sym (swap∘suc-swap∘swap _) ⟩
                       (ᴿ.swap *) ((ᴿ.suc ᴿ.swap *) ((ᴿ.swap *) (tgt₁ (⊖₁ 𝐸))))
                    ≡⟨ cong (ᴿ.swap *) (cong (ᴿ.suc ᴿ.swap *) (γ₁ 𝐸)) ⟩
                       (ᴿ.swap *) ((ᴿ.suc ᴿ.swap *) (tgt₂(⊖₁ 𝐸)))
                    ∎ in
             braiding (ᵇ∇ᵇ {a = a} {a′}) {0} (cong ν_ α)
             [ ν (swap *̃) S ] ≡ [ ν (swap *̃) S′ ]
      base {a = a} {a′} {E} {E′} 𝐸 P R R′ S S′ ≡R ≡R′ ≡S ≡S′ IH =
         let α = let open EqReasoning (setoid _) in
                begin
                   (ᴿ.suc ᴿ.swap *) ((ᴿ.swap *) ((ᴿ.suc ᴿ.swap *) (tgt₁ (⊖₁ 𝐸))))
                ≡⟨ sym (swap∘suc-swap∘swap _) ⟩
                   (ᴿ.swap *) ((ᴿ.suc ᴿ.swap *) ((ᴿ.swap *) (tgt₁ (⊖₁ 𝐸))))
                ≡⟨ cong (ᴿ.swap *) (cong (ᴿ.suc ᴿ.swap *) (γ₁ 𝐸)) ⟩
                   (ᴿ.swap *) ((ᴿ.suc ᴿ.swap *) (tgt₂(⊖₁ 𝐸)))
                ∎
             β : (suc swap *̃) ((swap *̃) S) ≅ (swap *̃) S′
             β = let open ≅-Reasoning in
                begin
                   (suc swap *̃) ((swap *̃) S)
                ≡⟨ cong ((suc swap *̃) ∘ᶠ (swap *̃)) (sym ≡S) ⟩
                   (suc swap *̃) ((swap *̃) (tgt ((ᴿ.swap *ᵇ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R)))
                ≡⟨ cong ((suc swap *̃) ∘ᶠ (swap *̃)) (sym (renᵇ-tgt-comm (E′/E (⊖₁ 𝐸)) swap R)) ⟩
                   (suc swap *̃) ((swap *̃) ((suc swap *̃) (tgt (E′/E (⊖₁ 𝐸)) R)))
                ≡⟨ cong ((suc swap *̃) ∘ᶠ (swap *̃) ∘ᶠ (suc swap *̃) ∘ᶠ tgt (E′/E (⊖₁ 𝐸))) (sym ≡R) ⟩
                   (suc swap *̃) ((swap *̃) ((suc swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                ≅⟨ ≅-sym (swap∘suc-swap∘swap̃ (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))) ⟩
                   (swap *̃) ((suc swap *̃) ((swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐸) ((swap *̃) ∘ᶠ (suc swap *̃)) (≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐸) _)) ⟩
                   (swap *̃) ((suc swap *̃)
                              (braiding (ᵇ∇ᵇ{a = (ᴿ.push *) a} {(ᴿ.push *) a′}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))))
                ≡⟨ cong ((swap *̃) ∘ᶠ (suc swap *̃)) IH ⟩
                   (swap *̃) ((suc swap *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)))
                ≡⟨ cong ((swap *̃) ∘ᶠ (suc swap *̃) ∘ᶠ tgt (E/E′ (⊖₁ 𝐸))) ≡R′ ⟩
                   (swap *̃) ((suc swap *̃) (tgt (E/E′ (⊖₁ 𝐸)) R′))
                ≡⟨ cong (swap *̃) (renᵇ-tgt-comm (E/E′ (⊖₁ 𝐸)) swap R′) ⟩
                   (swap *̃) (tgt ((ᴿ.swap *ᵇ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′))
                ≡⟨ cong (swap *̃) ≡S′ ⟩
                   (swap *̃) S′
                ∎
             open ≅-Reasoning in ≅-to-≡ (
         begin
            braiding (ᵇ∇ᵇ {a = a} {a′}) {0} (cong ν_ α) [ ν (swap *̃) S ]
         ≅⟨ reduce-ᵇ∇ᵇ (cong ν_ α) _ ⟩
            [ ν (suc swap *̃) ((swap *̃) S) ]
         ≅⟨ [ν-]-cong α β ⟩
            [ ν (swap *̃) S′ ]
         ∎)

   module x•-x•
      {Γ P₀ R₀ R′₀} {x x′ : Name Γ} {E : P₀ —[ ᴿ.push x • ᵇ - _ ]→ R₀}
      {E′ : P₀ —[ ᴿ.push x′ • ᵇ - _ ]→ R′₀} (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (P : ↓ P₀)
      (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂ (⊖₁ 𝐸))
      (IH : braiding (ᵇ∇ᵇ {a = ᴿ.push x •} {ᴿ.push x′ •}) {0} (γ₁ 𝐸)
            (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      postulate
       case :
         braiding (ᵇ∇ᵇ {a = x •} {x′ •}) {0} (γ₁ (νᵇᵇ 𝐸))
         (tgt (E′/E (⊖₁ (νᵇᵇ 𝐸))) (tgt (νᵇ E) [ ν P ])) ≡ tgt (E/E′ (⊖₁ (νᵇᵇ 𝐸))) (tgt (νᵇ E′) [ ν P ])

{-
      case
         with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
      ... | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | ◻ , R′ | [ ._ • ᵇ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ τ ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ τ ᶜ ] , R′ | [ ._ • ᵇ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
-}
