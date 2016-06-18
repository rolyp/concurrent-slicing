module Transition.Concur.Cofinal.Lattice.Helpers.nu-sync-propagate-b where

   open import ConcurrentSlicingCommon
   import Name as ᴺ
   import Ren as ᴿ
   open import Transition.Concur.Cofinal.Lattice.Common

   private
      base : ∀ {Γ x P₀ R₀ R′₀} {a : Actionᵇ Γ} {E : P₀ —[ • ᴺ.suc x 〈 ᴺ.zero 〉 ᶜ - _ ]→ R₀}
             {E′ : P₀ —[ (ᴿ.push *) a ᵇ - _ ]→ R′₀} (𝐸 : E ⌣₁[ ᶜ∇ᵇ ] E′) (P : ↓ P₀) (R : ↓ R₀) (R′ : ↓ R′₀)
             (S′ : ↓ (ᴿ.swap *) (tgt₂ (⊖₁ 𝐸))) → tgt E P ≡ R → tgt E′ P ≡ R′ →
             tgt ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) ≡ S′ →
             braiding (ᶜ∇ᵇ {a = • ᴺ.suc x 〈 ᴺ.zero 〉} {(ᴿ.push *) a}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡
             tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P) →
             braiding (ᵇ∇ᵇ {a = • x} {a}) {0} (cong (ᴿ.swap *) (γ₁ 𝐸)) (tgt (E′/E (⊖₁ 𝐸)) R) ≡ S′
      base {x = x} {a = a} {E} {E′} 𝐸 P R R′ S′ ≡R ≡R′ ≡S′ IH =
         let open ≅-Reasoning in ≅-to-≡ (
         begin
            braiding ᵇ∇ᵇ {0} (cong (ᴿ.swap *) (γ₁ 𝐸)) (tgt (E′/E (⊖₁ 𝐸)) R)
         ≅⟨ reduce-ᵇ∇ᵇ (cong (ᴿ.swap *) (γ₁ 𝐸)) _ ⟩
            (swap *̃) (tgt (E′/E (⊖₁ 𝐸)) R)
         ≡⟨ cong ((swap *̃) ∘ᶠ tgt (E′/E (⊖₁ 𝐸))) (sym ≡R) ⟩
            (swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
         ≅⟨ ≅-cong✴ ↓_ (γ₁ 𝐸) (swap *̃) (≅-sym (reduce-ᶜ∇ᵇ (γ₁ 𝐸) _)) ⟩
            (swap *̃) (braiding (ᶜ∇ᵇ {a = • ᴺ.suc x 〈 ᴺ.zero 〉} {(ᴿ.push *) a}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)))
         ≡⟨ cong (swap *̃) IH ⟩
            (swap *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
         ≡⟨ renᶜ-tgt-comm (E/E′ (⊖₁ 𝐸)) swap (tgt E′ P) ⟩
            tgt ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) (tgt E′ P))
         ≡⟨ cong (tgt ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ∘ᶠ (swap *̃)) ≡R′ ⟩
            tgt ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′)
         ≡⟨ ≡S′ ⟩
            S′
         ∎)

   module x•
      {Γ} {x x′ : Name Γ} {P₀ R₀ R′₀} {E : P₀ —[ • ᴺ.suc x 〈 ᴺ.zero 〉 ᶜ - _ ]→ R₀}
      {E′ : P₀ —[ ᴺ.suc x′ • ᵇ - _ ]→ R′₀} (𝐸 : E ⌣₁[ ᶜ∇ᵇ ] E′) (P : ↓ P₀)
      (IH : braiding (ᶜ∇ᵇ {a = • ᴺ.suc x 〈 ᴺ.zero 〉} {ᴺ.suc x′ •}) {0} (γ₁ 𝐸)
            (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      private
         module _
            (R : ↓ R₀) (R′ : ↓ R′₀) (≡R : tgt E P ≡ R) (≡R′ : tgt E′ P ≡ R′) where

            case′ :
               braiding (ᵇ∇ᵇ {a = • x} {x′ •}) {0} (cong (ᴿ.swap *) (γ₁ 𝐸))
               (tgt (E′/E (⊖₁ 𝐸)) R) ≡ tgt (ν• (ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) [ ν (swap *̃) R′ ]
            case′
               with step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
                    inspect (step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
            ... | ◻ , S′ | [ ≡S′ ] = base 𝐸 P R R′ S′ ≡R ≡R′ (,-inj₂ ≡S′) IH
            ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = base 𝐸 P R R′ S′ ≡R ≡R′ (,-inj₂ ≡S′) IH
            ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S′ ] = base 𝐸 P R R′ S′ ≡R ≡R′ (,-inj₂ ≡S′) IH

      case :
         braiding (ᵇ∇ᵇ {a = • x} {x′ •}) {0} (cong (ᴿ.swap *) (γ₁ 𝐸))
         (tgt (E′/E (⊖₁ 𝐸)) (tgt (ν• E) [ ν P ])) ≡ tgt (ν• (ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) (tgt (νᵇ E′) [ ν P ])
      case
         with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
      ... | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | ◻ , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | ◻ , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ ._ • ᵇ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ ._ • ᵇ ] , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ ._ • ᵇ ] , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)

   module •x
      {Γ} {x x′ : Name Γ} {P₀ R₀ R′₀} {E : P₀ —[ • ᴺ.suc x 〈 ᴺ.zero 〉 ᶜ - _ ]→ R₀}
      {E′ : P₀ —[ (• ᴺ.suc x′) ᵇ - _ ]→ R′₀} (𝐸 : E ⌣₁[ ᶜ∇ᵇ ] E′) (P : ↓ P₀)
      (IH : braiding (ᶜ∇ᵇ {a = • ᴺ.suc x 〈 ᴺ.zero 〉} {• ᴺ.suc x′}) {0} (γ₁ 𝐸)
            (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      private
         module _
            (R : ↓ R₀) (R′ : ↓ R′₀) (≡R : tgt E P ≡ R) (≡R′ : tgt E′ P ≡ R′) where

            case′ :
               braiding (ᵇ∇ᵇ {a = • x} {• x′}) {0} (cong (ᴿ.swap *) (γ₁ 𝐸))
               (tgt (E′/E (⊖₁ 𝐸)) R) ≡ tgt (ν• (ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) [ ν (swap *̃) R′ ]
            case′
               with step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
                    inspect (step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
            ... | ◻ , S′ | [ ≡S′ ] = base 𝐸 P R R′ S′ ≡R ≡R′ (,-inj₂ ≡S′) IH
            ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = base 𝐸 P R R′ S′ ≡R ≡R′ (,-inj₂ ≡S′) IH
            ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , S′ | [ ≡S′ ] = base 𝐸 P R R′ S′ ≡R ≡R′ (,-inj₂ ≡S′) IH

      case :
         braiding (ᵇ∇ᵇ {a = • x} {• x′}) {0} (cong (ᴿ.swap *) (γ₁ 𝐸))
         (tgt (E′/E (⊖₁ 𝐸)) (tgt (ν• E) [ ν P ])) ≡ tgt (ν• (ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) (tgt (νᵇ E′) [ ν P ])
      case
         with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
      ... | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | ◻ , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | ◻ , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ (• ._) ᵇ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ (• ._) ᵇ ] , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ (• ._) ᵇ ] , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
