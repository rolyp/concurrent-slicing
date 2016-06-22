open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common
import Name as ᴺ
import Ren as ᴿ

module Transition.Concur.Cofinal.Lattice.case.nu-propagate-x-x
   {Γ P₀ R₀ R′₀} {x u : Name Γ} {E : P₀ —[ (• ᴺ.suc x) ᵇ - _ ]→ R₀} {E′ : P₀ —[ (• ᴺ.suc u) ᵇ - _ ]→ R′₀}
   (𝐸 : E ⌣₁[ ˣ∇ˣ ] E′) (P : ↓ P₀)
   (let P′₀ = tgt₁ (⊖₁ 𝐸); P″₀ = tgt₂ (⊖₁ 𝐸))
   (IH : braiding (ˣ∇ˣ {x = ᴺ.suc x} {ᴺ.suc u}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
   where

   private
      base : (R : ↓ R₀) (R′ : ↓ R′₀) (S : ↓ (ᴿ.swap *) P′₀) (S′ : ↓ (ᴿ.swap *) P″₀) →
             tgt E P ≡ R → tgt E′ P ≡ R′ →
             tgt ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) ≡ S → tgt ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) ≡ S′ →
             braiding (ˣ∇ˣ {x = x} {u}) {0} (cong ν_ (cong (ᴿ.swap *) (γ₁ 𝐸)))
             [ ν S ] ≡ [ ν S′ ]

      base R R′ S S′ ≡R ≡R′ ≡S ≡S′ =
         let α : S ≅ S′
             α = let open ≅-Reasoning in
                begin
                   S
                ≡⟨ sym ≡S ⟩
                   tgt ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R)
                ≡⟨ cong (tgt ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ∘ᶠ (swap *̃)) (sym ≡R) ⟩
                   tgt ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) (tgt E P))
                ≡⟨ sym (renᶜ-tgt-comm (E′/E (⊖₁ 𝐸)) swap (tgt E P)) ⟩
                   (swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
                ≅⟨ ≅-cong✴ ↓_ (≅-to-≡ (≅-trans (≡-to-≅ (γ₁ 𝐸)) (Proc↲ refl P″₀)))
                           (swap *̃) (≅-trans (≅-sym (reduce-ˣ∇ˣ {x = ᴺ.suc x} {ᴺ.suc u} (γ₁ 𝐸) _)) (≡-to-≅ IH)) ⟩
                   (swap *̃) (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
                ≡⟨ renᶜ-tgt-comm (E/E′ (⊖₁ 𝐸)) swap (tgt E′ P) ⟩
                   tgt ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) (tgt E′ P))
                ≡⟨ cong (tgt ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ∘ᶠ (swap *̃)) ≡R′ ⟩
                   tgt ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′)
                ≡⟨ ≡S′ ⟩
                   S′
                ∎
             open ≅-Reasoning in ≅-to-≡ (
         begin
            braiding (ˣ∇ˣ {x = x} {u}) (cong ν_ (cong (ᴿ.swap *) (γ₁ 𝐸))) [ ν S ]
         ≅⟨ reduce-ˣ∇ˣ {x = x} {u} (cong ν_ (cong (ᴿ.swap *) (γ₁ 𝐸))) _ ⟩
            [ ν S ]
         ≅⟨ [ν-]-cong (cong (ᴿ.swap *) (γ₁ 𝐸)) α ⟩
            [ ν S′ ]
         ∎)

   private
      module _
         (R : ↓ R₀) (R′ : ↓ R′₀) (≡R : tgt E P ≡ R) (≡R′ : tgt E′ P ≡ R′) where

         case′ :
            braiding (ˣ∇ˣ {x = x} {u}) {0} (cong ν_ (cong (ᴿ.swap *) (γ₁ 𝐸)))
            (tgt (νᶜ (ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) [ ν (swap *̃) R ]) ≡
            tgt (νᶜ (ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) [ ν (swap *̃) R′ ]
         case′
            with step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) ((swap *̃) R) | step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) ((swap *̃) R′) |
                 inspect (step ((ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸)))) ((swap *̃) R) |
                 inspect (step ((ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸)))) ((swap *̃) R′)
         ... | ◻ , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
            base R R′ S S′ ≡R ≡R′ (,-inj₂ ≡S) (,-inj₂ ≡S′)
         ... | ◻ , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
            base R R′ S S′ ≡R ≡R′ (,-inj₂ ≡S) (,-inj₂ ≡S′)
         ... | ◻ , S | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
            base R R′ S S′ ≡R ≡R′ (,-inj₂ ≡S) (,-inj₂ ≡S′)
         ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
            base R R′ S S′ ≡R ≡R′ (,-inj₂ ≡S) (,-inj₂ ≡S′)
         ... | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S | ◻ , S′ | [ ≡S ] | [ ≡S′ ] =
            base R R′ S S′ ≡R ≡R′ (,-inj₂ ≡S) (,-inj₂ ≡S′)
         ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
            base R R′ S S′ ≡R ≡R′ (,-inj₂ ≡S) (,-inj₂ ≡S′)
         ... | [ • ._ 〈 ◻ 〉 ᶜ ] , S | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
            base R R′ S S′ ≡R ≡R′ (,-inj₂ ≡S) (,-inj₂ ≡S′)
         ... | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S | [ • ._ 〈 ◻ 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
            base R R′ S S′ ≡R ≡R′ (,-inj₂ ≡S) (,-inj₂ ≡S′)
         ... | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S | [ • ._ 〈 [ .(ᴺ.suc ᴺ.zero) ] 〉 ᶜ ] , S′ | [ ≡S ] | [ ≡S′ ] =
            base  R R′ S S′ ≡R ≡R′ (,-inj₂ ≡S) (,-inj₂ ≡S′)

   case :
      braiding (ˣ∇ˣ {x = x} {u}) {0} (cong ν_ (cong (ᴿ.swap *) (γ₁ 𝐸)))
      (tgt (νᶜ (ᴿ.swap *ᶜ) (E′/E (⊖₁ 𝐸))) (tgt (νᵇ E) [ ν P ])) ≡
      tgt (νᶜ (ᴿ.swap *ᶜ) (E/E′ (⊖₁ 𝐸))) (tgt (νᵇ E′) [ ν P ])
   case
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   ... | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
   ... | ◻ , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
   ... | [ (• ._) ᵇ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
   ... | [ (• ._) ᵇ ] , R′ | [ (• ._) ᵇ ] , R | [ ≡R′ ] | [ ≡R ] = case′ R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
