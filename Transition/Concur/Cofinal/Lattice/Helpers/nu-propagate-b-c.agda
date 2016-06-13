module Transition.Concur.Cofinal.Lattice.Helpers.nu-propagate-b-c where

   open import ConcurrentSlicingCommon
   import Ren as ᴿ
   open import Transition.Concur.Cofinal.Lattice.Common

   private
      base : ∀ {Γ P₀ R₀ R′₀} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} {E : P₀ —[ (ᴿ.push *) a ᵇ - _ ]→ R₀}
             {E′ : P₀ —[ (ᴿ.push *) a′ ᶜ - _ ]→ R′₀} (𝐸 : E ⌣₁[ ᵇ∇ᶜ ] E′) (P : ↓ P₀) (R : ↓ R₀) (R′ : ↓ R′₀)
             (S : ↓ (ᴿ.swap *) (tgt₁ (⊖₁ 𝐸))) (S′ : ↓ tgt₂ (⊖₁ 𝐸)) →
             tgt E P ≡ R → tgt E′ P ≡ R′ → tgt ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) ≡ S → tgt (E/E′ (⊖₁ 𝐸)) R′ ≡ S′ →
             braiding (ᵇ∇ᶜ {a = (ᴿ.push *) a} {(ᴿ.push *) a′}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡
             tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P) →
             braiding (ᵇ∇ᶜ {a = a} {a′}) {0} (cong ν_ (cong (ᴿ.swap *) (γ₁ 𝐸)))
             [ ν S ] ≡ [ ν (swap *̃) S′ ]
      base {a = a} {a′} {E} {E′} 𝐸 P R R′ S S′ ≡R ≡R′ ≡S ≡S′ IH =
         let α : S ≅ (swap *̃) S′
             α = let open ≅-Reasoning in
                begin
                   S
                ≡⟨ sym ≡S ⟩
                   tgt ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R)
                ≡⟨ cong (tgt ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ∘ᶠ (swap *̃)) (sym ≡R) ⟩
                   tgt ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) (tgt E P))
                ≡⟨ sym (renᶜ-tgt-comm (E′/E (⊖₁ 𝐸)) swap (tgt E P)) ⟩
                   (swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
                ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐸) (swap *̃) (≅-sym (reduce-ᵇ∇ᶜ (γ₁ 𝐸) _)) ⟩
                   (swap *̃) (braiding ᵇ∇ᶜ {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))
                ≡⟨ cong (swap *̃) IH ⟩
                   (swap *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
                ≡⟨ cong ((swap *̃) ∘ᶠ tgt (E/E′ (⊖₁ 𝐸))) ≡R′ ⟩
                   (swap *̃) (tgt (E/E′ (⊖₁ 𝐸)) R′)
                ≡⟨ cong (swap *̃) ≡S′ ⟩
                   (swap *̃) S′
                ∎
             open ≅-Reasoning in ≅-to-≡ (
         begin
            braiding ᵇ∇ᶜ (cong ν_ (cong (ᴿ.swap *) (γ₁ 𝐸))) [ ν S ]
         ≅⟨ reduce-ᵇ∇ᶜ (cong ν_ (cong (ᴿ.swap *) (γ₁ 𝐸))) _  ⟩
            [ ν S ]
         ≅⟨ [ν-]-cong (cong (ᴿ.swap *) (γ₁ 𝐸)) α ⟩
            [ ν (swap *̃) S′ ]
         ∎)

   module x•-•x〈y〉
      {Γ P₀ R₀ R′₀} {x x′ y : Name Γ} {E : P₀ —[ (• ᴿ.push x) ᵇ - _ ]→ R₀}
      {E′ : P₀ —[ • ᴿ.push x′ 〈 ᴿ.push y 〉 ᶜ - _ ]→ R′₀} (𝐸 : E ⌣₁[ ᵇ∇ᶜ ] E′) (P : ↓ P₀)
      (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂ (⊖₁ 𝐸))
      (IH : braiding (ᵇ∇ᶜ {a = • ᴿ.push x} {• ᴿ.push x′ 〈 ᴿ.push y 〉}) {0} (γ₁ 𝐸)
            (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      private
         module sub
            (R : ↓ R₀) (R′ : ↓ R′₀) (≡R : tgt E P ≡ R) (≡R′ : tgt E′ P ≡ R′) where

            case′ :
               braiding (ᵇ∇ᶜ {a = • x} {• x′ 〈 y 〉}) {0} (cong ν_ (cong (ᴿ.swap *) (γ₁ 𝐸)))
               (π₂ (step⁻ (νᶜ (ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) (ν (swap *̃) R))) ≡ π₂ (step⁻ (νᵇ E/E′ (⊖₁ 𝐸)) (ν R′))
            case′
               with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step (E/E′ (⊖₁ 𝐸)) R′ |
                    inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) | inspect (step (E/E′ (⊖₁ 𝐸))) R′
            case′ | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
               base 𝐸 P R R′ S S′ ≡R ≡R′ (,-inj₂ ≡S) (,-inj₂ ≡S′) IH
            case′ | ◻ , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
               base 𝐸 P R R′ S S′ ≡R ≡R′ (,-inj₂ ≡S) (,-inj₂ ≡S′) IH
            case′ | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
               base 𝐸 P R R′ S S′ ≡R ≡R′ (,-inj₂ ≡S) (,-inj₂ ≡S′) IH
            case′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
               base 𝐸 P R R′ S S′ ≡R ≡R′ (,-inj₂ ≡S) (,-inj₂ ≡S′) IH
            case′ | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
               base 𝐸 P R R′ S S′ ≡R ≡R′ (,-inj₂ ≡S) (,-inj₂ ≡S′) IH
            case′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S | [ (• ._) ᵇ ] , S′ | [ ≡S ] | [ ≡S′ ] =
               base 𝐸 P R R′ S S′ ≡R ≡R′ (,-inj₂ ≡S) (,-inj₂ ≡S′) IH

      open sub

      case :
         braiding (ᵇ∇ᶜ {a = • x} {• x′ 〈 y 〉}) {0} (γ₁ (νᵇᶜ 𝐸))
         (tgt (E′/E (⊖₁ (νᵇᶜ 𝐸))) (tgt (νᵇ E) [ ν P ])) ≡ tgt (E/E′ (⊖₁ (νᵇᶜ 𝐸))) (tgt (νᶜ E′) [ ν P ])
      case
         with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
      ... | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | ◻ , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
