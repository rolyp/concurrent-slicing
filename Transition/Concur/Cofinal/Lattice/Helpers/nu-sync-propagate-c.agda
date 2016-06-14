module Transition.Concur.Cofinal.Lattice.Helpers.nu-sync-propagate-c where

   open import ConcurrentSlicingCommon
   import Name as ᴺ
   import Ren as ᴿ
   open import Transition.Concur.Cofinal.Lattice.Common

   private
      base : ∀ {Γ x P₀ R₀ R′₀} {a : Actionᶜ Γ} {E : P₀ —[ • ᴺ.suc x 〈 ᴺ.zero 〉 ᶜ - _ ]→ R₀}
             {E′ : P₀ —[ (ᴿ.push *) a ᶜ - _ ]→ R′₀} (𝐸 : E ⌣₁[ ᶜ∇ᶜ ] E′) (P : ↓ P₀) (R : ↓ R₀) (R′ : ↓ R′₀)
             (S′ : ↓ tgt₂ (⊖₁ 𝐸)) → tgt E P ≡ R → tgt E′ P ≡ R′ → tgt (E/E′ (⊖₁ 𝐸)) R′ ≡ S′ →
             braiding (ᶜ∇ᶜ {a = • ᴺ.suc x 〈 ᴺ.zero 〉} {(ᴿ.push *) a}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡
             tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P) →
             braiding (ᵇ∇ᶜ {a = • x} {a}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) R) ≡ S′
      base {x = x} {a = a} {E} {E′} 𝐸 P R R′ S′ ≡R ≡R′ ≡S′ IH =
         let open ≅-Reasoning in ≅-to-≡ (
         begin
            braiding ᵇ∇ᶜ {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) R)
         ≅⟨ reduce-ᵇ∇ᶜ (γ₁ 𝐸) _ ⟩
            tgt (E′/E (⊖₁ 𝐸)) R
         ≡⟨ cong (tgt (E′/E (⊖₁ 𝐸))) (sym ≡R) ⟩
            tgt (E′/E (⊖₁ 𝐸)) (tgt E P)
         ≅⟨ ≅-sym (reduce-ᶜ∇ᶜ {a = • ᴺ.suc x 〈 ᴺ.zero 〉} {(ᴿ.push *) a} (γ₁ 𝐸) _) ⟩
            braiding ᶜ∇ᶜ {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
         ≡⟨ IH ⟩
            tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)
         ≡⟨ cong (tgt (E/E′ (⊖₁ 𝐸))) ≡R′ ⟩
            tgt (E/E′ (⊖₁ 𝐸)) R′
         ≡⟨ ≡S′ ⟩
            S′
         ∎)

   module •x〈y〉
      {Γ} {x x′ y : Name Γ} {P₀ R₀ R′₀} {E : P₀ —[ • ᴺ.suc x 〈 ᴺ.zero 〉 ᶜ - _ ]→ R₀}
      {E′ : P₀ —[ • ᴺ.suc x′ 〈 ᴺ.suc y 〉 ᶜ - _ ]→ R′₀} (𝐸 : E ⌣₁[ ᶜ∇ᶜ ] E′) (P : ↓ P₀)
      (IH : braiding (ᶜ∇ᶜ {a = • ᴺ.suc x 〈 ᴺ.zero 〉} {• ᴺ.suc x′ 〈 ᴺ.suc y 〉}) {0} (γ₁ 𝐸)
            (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      private
         module sub
            (R : ↓ R₀) (R′ : ↓ R′₀) (≡R : tgt E P ≡ R) (≡R′ : tgt E′ P ≡ R′) where

            case′ : braiding (ᵇ∇ᶜ {a = • x} {• x′ 〈 y 〉}) {0} (γ₁ 𝐸)
                   (tgt (E′/E (⊖₁ 𝐸)) R) ≡ tgt (ν• E/E′ (⊖₁ 𝐸)) [ ν R′ ]
            case′
               with step (E/E′ (⊖₁ 𝐸)) R′ | inspect (step (E/E′ (⊖₁ 𝐸))) R′
            ... | ◻ , S′ | [ ≡S′ ] = base 𝐸 P R R′ S′ ≡R ≡R′ (,-inj₂ ≡S′) IH
            ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S′ ] = base 𝐸 P R R′ S′ ≡R ≡R′ (,-inj₂ ≡S′) IH
            ... | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , S′ | [ ≡S′ ] = base 𝐸 P R R′ S′ ≡R ≡R′ (,-inj₂ ≡S′) IH

      open sub

      case :
         braiding (ᵇ∇ᶜ {a = • x} {• x′ 〈 y 〉}) {0} (γ₁ 𝐸)
         (tgt (E′/E (⊖₁ 𝐸)) (tgt (ν• E) [ ν P ])) ≡ tgt (ν• E/E′ (⊖₁ 𝐸)) (tgt (νᶜ E′) [ ν P ])
      case
         with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
      ... | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | ◻ , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | ◻ , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
