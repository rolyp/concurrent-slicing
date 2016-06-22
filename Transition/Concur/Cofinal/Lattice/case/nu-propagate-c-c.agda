module Transition.Concur.Cofinal.Lattice.case.nu-propagate-c-c where

   open import ConcurrentSlicingCommon
   import Ren as ᴿ
   open import Transition.Concur.Cofinal.Lattice.Common

   private
      base : ∀ {Γ P₀ R₀ R′₀} {a a′ : Actionᶜ Γ} {E : P₀ —[ (ᴿ.push *) a ᶜ - _ ]→ R₀} {E′ : P₀ —[ (ᴿ.push *) a′ ᶜ - _ ]→ R′₀}
             (𝐸 : E ⌣₁[ ᶜ∇ᶜ ] E′) (P : ↓ P₀) (R : ↓ R₀) (R′ : ↓ R′₀) (S : ↓ tgt₁ (⊖₁ 𝐸)) (S′ : ↓ tgt₂ (⊖₁ 𝐸)) →
             tgt E P ≡ R → tgt E′ P ≡ R′ → tgt (E′/E (⊖₁ 𝐸)) R ≡ S → tgt (E/E′ (⊖₁ 𝐸)) R′ ≡ S′ →
             braiding (ᶜ∇ᶜ {a = (ᴿ.push *) a} {(ᴿ.push *) a′}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡
             tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P) →
             braiding (ᶜ∇ᶜ {a = a} {a′}) {0} (cong ν_ (γ₁ 𝐸))
             [ ν S ] ≡ [ ν S′ ]
      base {a = a} {a′} {E} {E′} 𝐸 P R R′ S S′ ≡R ≡R′ ≡S ≡S′ IH =
         let α : S ≅ S′
             α = let open ≅-Reasoning in
                begin
                   S
                ≡⟨ sym ≡S ⟩
                   tgt (E′/E (⊖₁ 𝐸)) R
                ≡⟨ cong (tgt (E′/E (⊖₁ 𝐸))) (sym ≡R) ⟩
                   tgt (E′/E (⊖₁ 𝐸)) (tgt E P)
                ≅⟨ ≅-sym (reduce-ᶜ∇ᶜ (γ₁ 𝐸) _) ⟩
                   braiding (ᶜ∇ᶜ {a = (ᴿ.push *) a} {(ᴿ.push *) a′}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
                ≡⟨ IH ⟩
                   tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)
                ≡⟨ cong (tgt (E/E′ (⊖₁ 𝐸))) ≡R′ ⟩
                   tgt (E/E′ (⊖₁ 𝐸)) R′
                ≡⟨ ≡S′ ⟩
                   S′
                ∎
             open ≅-Reasoning in ≅-to-≡ (
         begin
            braiding ᶜ∇ᶜ (cong ν_ (γ₁ 𝐸)) [ ν S ]
         ≅⟨ reduce-ᶜ∇ᶜ (cong ν_ (γ₁ 𝐸)) _  ⟩
            [ ν S ]
         ≅⟨ [ν-]-cong (γ₁ 𝐸) α ⟩
            [ ν S′ ]
         ∎)

   module •x〈y〉-•x〈y〉
      {Γ P₀ R₀ R′₀} {x y x′ y′ : Name Γ} {E : P₀ —[ • ᴿ.push x 〈 ᴿ.push y 〉 ᶜ - _ ]→ R₀}
      {E′ : P₀ —[ • ᴿ.push x′ 〈 ᴿ.push y′ 〉 ᶜ - _ ]→ R′₀} (𝐸 : E ⌣₁[ ᶜ∇ᶜ ] E′) (P : ↓ P₀)
      (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂ (⊖₁ 𝐸))
      (IH : braiding (ᶜ∇ᶜ {a = • ᴿ.push x 〈 ᴿ.push y 〉} {• ᴿ.push x′ 〈 ᴿ.push y′ 〉}) {0} (γ₁ 𝐸)
            (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      private
         module _
            (R : ↓ R₀) (R′ : ↓ R′₀) (≡R : tgt E P ≡ R) (≡R′ : tgt E′ P ≡ R′) where

            case′ :
               braiding (ᶜ∇ᶜ {a = • x 〈 y 〉} {• x′ 〈 y′ 〉}) {0} (cong ν_ (γ₁ 𝐸))
               (tgt (νᶜ E′/E (⊖₁ 𝐸)) [ ν R ]) ≡ tgt (νᶜ E/E′ (⊖₁ 𝐸)) [ ν R′ ]
            case′
               with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ |
                    inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
            ... | ◻ , P′ | ◻ , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH
            ... | ◻ , P′ | [ • ._ 〈 ◻ 〉 ᶜ ] , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH
            ... | ◻ , P′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH
            ... | [ • ._ 〈 ◻ 〉 ᶜ ] , P′ | ◻ , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH
            ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , P′ | ◻ , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH
            ... | [ • ._ 〈 ◻ 〉 ᶜ ] , P′ | [ • ._ 〈 ◻ 〉 ᶜ ] , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH
            ... | [ • ._ 〈 ◻ 〉 ᶜ ] , P′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH
            ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , P′ | [ • ._ 〈 ◻ 〉 ᶜ ] , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH
            ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , P′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH

      case :
         braiding (ᶜ∇ᶜ {a = • x 〈 y 〉} {• x′ 〈 y′ 〉}) {0} (cong ν_ (γ₁ 𝐸))
         (tgt (νᶜ E′/E (⊖₁ 𝐸)) (tgt (νᶜ E) [ ν P ])) ≡ tgt (νᶜ E/E′ (⊖₁ 𝐸)) (tgt (νᶜ E′) [ ν P ])
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

   module •x〈y〉-τ
      {Γ P₀ R₀ R′₀} {x y : Name Γ} {E : P₀ —[ • ᴿ.push x 〈 ᴿ.push y 〉 ᶜ - _ ]→ R₀}
      {E′ : P₀ —[ τ ᶜ - _ ]→ R′₀} (𝐸 : E ⌣₁[ ᶜ∇ᶜ ] E′) (P : ↓ P₀)
      (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂ (⊖₁ 𝐸))
      (IH : braiding (ᶜ∇ᶜ {a = • ᴿ.push x 〈 ᴿ.push y 〉} {τ}) {0} (γ₁ 𝐸)
            (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      private
         module _
            (R : ↓ R₀) (R′ : ↓ R′₀) (≡R : tgt E P ≡ R) (≡R′ : tgt E′ P ≡ R′) where

            case′ :
               braiding (ᶜ∇ᶜ {a = • x 〈 y 〉} {τ}) {0} (cong ν_ (γ₁ 𝐸))
               (tgt (νᶜ E′/E (⊖₁ 𝐸)) [ ν R ]) ≡ tgt (νᶜ E/E′ (⊖₁ 𝐸)) [ ν R′ ]
            case′
               with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ |
                    inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
            ... | ◻ , P′ | ◻ , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH
            ... | ◻ , P′ | [ • ._ 〈 ◻ 〉 ᶜ ] , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH
            ... | ◻ , P′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH
            ... | [ τ ᶜ ] , P′ | ◻ , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH
            ... | [ τ ᶜ ] , P′ | [ • ._ 〈 ◻ 〉 ᶜ ] , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH
            ... | [ τ ᶜ ] , P′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH

      case :
         braiding (ᶜ∇ᶜ {a = • x 〈 y 〉} {τ}) {0} (cong ν_ (γ₁ 𝐸))
         (tgt (νᶜ E′/E (⊖₁ 𝐸)) (tgt (νᶜ E) [ ν P ])) ≡ tgt (νᶜ E/E′ (⊖₁ 𝐸)) (tgt (νᶜ E′) [ ν P ])
      case
         with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
      ... | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | ◻ , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | ◻ , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ τ ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ τ ᶜ ] , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ τ ᶜ ] , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)

   module τ-•x〈y〉
      {Γ P₀ R₀ R′₀} {x′ y′ : Name Γ} {E : P₀ —[ τ ᶜ - _ ]→ R₀}
      {E′ : P₀ —[ • ᴿ.push x′ 〈 ᴿ.push y′ 〉 ᶜ - _ ]→ R′₀} (𝐸 : E ⌣₁[ ᶜ∇ᶜ ] E′) (P : ↓ P₀)
      (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂ (⊖₁ 𝐸))
      (IH : braiding (ᶜ∇ᶜ {a = τ} {• ᴿ.push x′ 〈 ᴿ.push y′ 〉}) {0} (γ₁ 𝐸)
            (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      private
         module _
            (R : ↓ R₀) (R′ : ↓ R′₀) (≡R : tgt E P ≡ R) (≡R′ : tgt E′ P ≡ R′) where

            case′ :
               braiding (ᶜ∇ᶜ {a = τ} {• x′ 〈 y′ 〉}) {0} (cong ν_ (γ₁ 𝐸))
               (tgt (νᶜ E′/E (⊖₁ 𝐸)) [ ν R ]) ≡ tgt (νᶜ E/E′ (⊖₁ 𝐸)) [ ν R′ ]
            case′
               with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ |
                    inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
            ... | ◻ , P′ | ◻ , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH
            ... | ◻ , P′ | [ τ ᶜ ] , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH
            ... | [ • ._ 〈 ◻ 〉 ᶜ ] , P′ | ◻ , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH
            ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , P′ | ◻ , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH
            ... | [ • ._ 〈 ◻ 〉 ᶜ ] , P′ | [ τ ᶜ ] , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH
            ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , P′ | [ τ ᶜ ] , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH

      case :
         braiding (ᶜ∇ᶜ {a = τ} {• x′ 〈 y′ 〉}) {0} (cong ν_ (γ₁ 𝐸))
         (tgt (νᶜ E′/E (⊖₁ 𝐸)) (tgt (νᶜ E) [ ν P ])) ≡ tgt (νᶜ E/E′ (⊖₁ 𝐸)) (tgt (νᶜ E′) [ ν P ])
      case
         with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
      ... | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | ◻ , R′ | [ τ ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | [ τ ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | [ τ ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)

   module τ-τ
      {Γ P₀ R₀ R′₀} {E : P₀ —[ τ ᶜ - _ ]→ R₀} {E′ : P₀ —[ τ ᶜ - _ ]→ R′₀} (𝐸 : E ⌣₁[ ᶜ∇ᶜ ] E′) (P : ↓ P₀)
      (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂ (⊖₁ 𝐸))
      (IH : braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (γ₁ 𝐸)
            (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
      where

      private
         module _
            (R : ↓ R₀) (R′ : ↓ R′₀) (≡R : tgt E P ≡ R) (≡R′ : tgt E′ P ≡ R′) where

            case′ :
               braiding {Γ} (ᶜ∇ᶜ {a = τ} {τ}) {0} (cong ν_ (γ₁ 𝐸))
               (tgt (νᶜ E′/E (⊖₁ 𝐸)) [ ν R ]) ≡ tgt (νᶜ E/E′ (⊖₁ 𝐸)) [ ν R′ ]
            case′
               with step (E′/E (⊖₁ 𝐸)) R | step (E/E′ (⊖₁ 𝐸)) R′ |
                    inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E/E′ (⊖₁ 𝐸))) R′
            ... | ◻ , P′ | ◻ , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH
            ... | ◻ , P′ | [ τ ᶜ ] , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH
            ... | [ τ ᶜ ] , P′ | ◻ , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH
            ... | [ τ ᶜ ] , P′ | [ τ ᶜ ] , P″ | [ ≡P′ ] | [ ≡P″ ] =
               base 𝐸 P R R′ P′ P″ ≡R ≡R′ (,-inj₂ ≡P′) (,-inj₂ ≡P″) IH

      case :
         braiding (ᶜ∇ᶜ {a = τ} {τ}) {0} (cong ν_ (γ₁ 𝐸))
         (tgt (νᶜ E′/E (⊖₁ 𝐸)) (tgt (νᶜ E) [ ν P ])) ≡ tgt (νᶜ E/E′ (⊖₁ 𝐸)) (tgt (νᶜ E′) [ ν P ])
      case
         with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
      ... | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | ◻ , R′ | [ τ ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ τ ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
      ... | [ τ ᶜ ] , R′ | [ τ ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
