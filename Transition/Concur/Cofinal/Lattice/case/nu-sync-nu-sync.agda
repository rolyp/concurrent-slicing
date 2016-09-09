open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common
import Name as ᴺ
import Ren as ᴿ

module Transition.Concur.Cofinal.Lattice.case.nu-sync-nu-sync
   {Γ} {x u : Name Γ} {P₀ Q₀ R₀ R′₀ S₀ S′₀} {E : P₀ —[ x • ᵇ - _ ]→ R₀}
   {E′ : P₀ —[ u • ᵇ - _ ]→ R′₀} {F : Q₀ —[ (• x) ᵇ - _ ]→ S₀} {F′ : Q₀ —[ (• u) ᵇ - _ ]→ S′₀}
   (𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′) (𝐹 : F ⌣₁[ ᵇ∇ᵇ ] F′) (P : ↓ P₀) (Q : ↓ Q₀)
   (IH₁ : braiding (ᵇ∇ᵇ {a = x •} {u •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P))
   (IH₂ : braiding (ᵇ∇ᵇ {a = • x} {• u}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q)) ≡ tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)) where

   module _
      (R : ↓ R₀) (R′ : ↓ R′₀) (S : ↓ S₀) (S′ : ↓ S′₀) (y y′ : ↓ ᴺ.zero) (≡R : tgt E P ≡ R) (≡R′ : tgt E′ P ≡ R′)
      (≡S : tgt F Q ≡ S) (≡S′ : tgt F′ Q ≡ S′) where

{-
      coerce-braid : (P′ : ↓ tgt₁ (⊖₁ 𝐸)) (Q′ : ↓ tgt₁ (⊖₁ 𝐹)) →
                     braid̂ (γ₁ (𝐸 │ᵥ′ 𝐹)) [ ν [ ν [ P′ │ Q′ ] ] ] ≅
                     braid̂ (νν-swapᵣ (tgt₁ (⊖₁ 𝐸) │ tgt₁ (⊖₁ 𝐹))) [ ν [ ν [ P′ │ Q′ ] ] ]
      coerce-braid _ _ rewrite (sym (γ₁ 𝐸)) | (sym (γ₁ 𝐹)) = ≅-refl

      base : (P′ : ↓ (tgt₁ (⊖₁ 𝐸))) (Q′ : ↓ tgt₁ (⊖₁ 𝐹)) (P″ : ↓ (tgt₂ (⊖₁ 𝐸)))
             (Q″ : ↓ tgt₂ (⊖₁ 𝐹)) → tgt (E′/E (⊖₁ 𝐸)) R ≡ P′ →
             tgt (E′/E (⊖₁ 𝐹)) S ≡ Q′ → tgt (E/E′ (⊖₁ 𝐸)) R′ ≡ P″ → tgt (E/E′ (⊖₁ 𝐹)) S′ ≡ Q″ →
             braid̂ (γ₁ (𝐸 │ᵥ′ 𝐹)) [ ν [ ν [ P′ │ Q′ ] ] ] ≡ [ ν [ ν [ P″ │ Q″ ] ] ]

      base P′ Q′ P″ Q″ ≡P′ ≡Q′ ≡P″ ≡Q″ =
         let β : (swap *̃) P′ ≅ P″
             β = let open ≅-Reasoning in
                begin
                   (swap *̃) P′
                ≡⟨ cong (swap *̃) (trans (sym ≡P′) (cong (tgt (E′/E (⊖₁ 𝐸))) (sym ≡R))) ⟩
                   (swap *̃) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
                ≅⟨ ≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐸) _) ⟩
                   braiding (ᵇ∇ᵇ {a = x •} {u •}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
                ≡⟨ IH₁ ⟩
                   tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)
                ≡⟨ trans (cong (tgt (E/E′ (⊖₁ 𝐸))) ≡R′) ≡P″ ⟩
                   P″
                ∎
             γ : (swap *̃) Q′ ≅ Q″
             γ = let open ≅-Reasoning in
                begin
                   (swap *̃) Q′
                ≡⟨ cong (swap *̃) (trans (sym ≡Q′) (cong (tgt (E′/E (⊖₁ 𝐹))) (sym ≡S))) ⟩
                   (swap *̃) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q))
                ≅⟨ ≅-sym (reduce-ᵇ∇ᵇ (γ₁ 𝐹) _) ⟩
                   braiding (ᵇ∇ᵇ {a = • x} {• u}) {0} (γ₁ 𝐹) (tgt (E′/E (⊖₁ 𝐹)) (tgt F Q))
                ≡⟨ IH₂ ⟩
                   tgt (E/E′ (⊖₁ 𝐹)) (tgt F′ Q)
                ≡⟨ trans (cong (tgt (E/E′ (⊖₁ 𝐹))) ≡S′) ≡Q″ ⟩
                   Q″
                ∎
             open ≅-Reasoning in ≅-to-≡ (
         begin
            braid̂ (γ₁ (𝐸 │ᵥ′ 𝐹)) [ ν [ ν [ P′ │ Q′ ] ] ]
         ≅⟨ coerce-braid P′ Q′ ⟩
            braid̂ (νν-swapᵣ (tgt₁ (⊖₁ 𝐸) │ tgt₁ (⊖₁ 𝐹))) [ ν [ ν [ P′ │ Q′ ] ] ]
         ≡⟨ refl ⟩
            [ ν [ ν [ (swap *̃) P′ │ (swap *̃) Q′ ] ] ]
         ≅⟨ [ν-]-cong (cong ν_ (cong₂ _│_ (γ₁ 𝐸) (γ₁ 𝐹)))
                      ([ν-]-cong (cong₂ _│_ (γ₁ 𝐸) (γ₁ 𝐹)) ([-│-]-cong (γ₁ 𝐸) β (γ₁ 𝐹) γ)) ⟩
            [ ν [ ν [ P″ │ Q″ ] ] ]
         ∎)
-}

      postulate
       subcase :
         braid̂ (γ₁ (𝐸 │ᵥ′ 𝐹))
         (tgt (νᶜ ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸)) │ᵥ E′/E (⊖₁ 𝐹))) [ ν [ (repl y′ *̃) R │ S ] ])
         ≡
         tgt (νᶜ ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) │ᵥ E/E′ (⊖₁ 𝐹))) [ ν [ (repl y *̃) R′ │ S′ ] ]
{-
      subcase
         with step (E′/E (⊖₁ 𝐸)) R | step (E′/E (⊖₁ 𝐹)) S |
              step (E/E′ (⊖₁ 𝐸)) R′ | step (E/E′ (⊖₁ 𝐹)) S′ |
              inspect (step (E′/E (⊖₁ 𝐸))) R | inspect (step (E′/E (⊖₁ 𝐹))) S |
              inspect (step (E/E′ (⊖₁ 𝐸))) R′ | inspect (step (E/E′ (⊖₁ 𝐹))) S′
      ... | ◻ , P′ | ◻ , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | ◻ , Q′ | ◻ , P″ | [ (• ._) ᵇ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | ◻ , Q′ | [ (._ •) ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | ◻ , Q′ | [ (._ •) ᵇ ] , P″ | [ (• ._) ᵇ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | [ (• ._) ᵇ ] , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | [ (• ._) ᵇ ] , Q′ | ◻ , P″ | [ (• ._) ᵇ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | [ (• ._) ᵇ ] , Q′ | [ (._ •) ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | ◻ , P′ | [ (• ._) ᵇ ] , Q′ | [ (._ •) ᵇ ] , P″ | [ (• ._) ᵇ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ (._ •) ᵇ ] , P′ | ◻ , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ (._ •) ᵇ ] , P′ | ◻ , Q′ | ◻ , P″ | [ (• ._) ᵇ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ (._ •) ᵇ ] , P′ | ◻ , Q′ | [ (._ •) ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ (._ •) ᵇ ] , P′ | ◻ , Q′ | [ (._ •) ᵇ ] , P″ | [ (• ._) ᵇ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ (._ •) ᵇ ] , P′ | [ (• ._) ᵇ ] , Q′ | ◻ , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ (._ •) ᵇ ] , P′ | [ (• ._) ᵇ ] , Q′ | ◻ , P″ | [ (• ._) ᵇ ] , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ (._ •) ᵇ ] , P′ | [ (• ._) ᵇ ] , Q′ | [ (._ •) ᵇ ] , P″ | ◻ , Q″ | [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
      ... | [ (._ •) ᵇ ] , P′ | [ (• ._) ᵇ ] , Q′ | [ (._ •) ᵇ ] , P″ | [ (• ._) ᵇ ] , Q″ |
         [ ≡P′ ] | [ ≡Q′ ] | [ ≡P″ ] | [ ≡Q″ ] =
         base P′ Q′ P″ Q″ (,-inj₂ ≡P′) (,-inj₂ ≡Q′) (,-inj₂ ≡P″) (,-inj₂ ≡Q″)
-}

   case : braid̂ (γ₁ (𝐸 │ᵥ′ 𝐹))
          (tgt (νᶜ ((idᶠ *ᵇ) (E′/E (⊖₁ 𝐸)) │ᵥ E′/E (⊖₁ 𝐹))) (tgt (E │ᵥ F) [ P │ Q ]))
          ≡
          tgt (νᶜ ((idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) │ᵥ E/E′ (⊖₁ 𝐹))) (tgt (E′ │ᵥ F′) [ P │ Q ])
   case
      with step E′ P | step E P | step F′ Q | step F Q |
           inspect (step E′) P | inspect (step E) P | inspect (step F′) Q | inspect (step F) Q
   ... | ◻ , R′ | ◻ , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | ◻ , R′ | ◻ , R | ◻ , S′ | [ • ._ ﹙ y ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | ◻ , R′ | ◻ , R | [ • ._ ﹙ y′ ﹚ ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | ◻ , R′ | ◻ , R | [ • ._ ﹙ y′ ﹚ ᵇ ] , S′ | [ • ._ ﹙ y ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | ◻ , R′ | [ ._ • ᵇ ] , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | ◻ , R′ | [ ._ • ᵇ ] , R | ◻ , S′ | [ • ._ ﹙ y ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | ◻ , R′ | [ ._ • ᵇ ] , R | [ • ._ ﹙ y′ ﹚ ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | ◻ , R′ | [ ._ • ᵇ ] , R | [ • ._ ﹙ y′ ﹚ ᵇ ] , S′ | [ • ._ ﹙ y ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | ◻ , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | ◻ , R | ◻ , S′ | [ • ._ ﹙ y ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | ◻ , R | [ • ._ ﹙ y′ ﹚ ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | ◻ , R | [ • ._ ﹙ y′ ﹚ ᵇ ] , S′ | [ • ._ ﹙ y ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | [ ._ • ᵇ ] , R | ◻ , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | [ ._ • ᵇ ] , R | ◻ , S′ | [ • ._ ﹙ y ﹚ ᵇ ] , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ ◻ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | [ ._ • ᵇ ] , R | [ • ._ ﹙ y′ ﹚ ᵇ ] , S′ | ◻ , S | [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
   ... | [ ._ • ᵇ ] , R′ | [ ._ • ᵇ ] , R | [ • ._ ﹙ y′ ﹚ ᵇ ] , S′ | [ • ._ ﹙ y ﹚ ᵇ ] , S |
      [ ≡R′ ] | [ ≡R ] | [ ≡S′ ] | [ ≡S ] =
      subcase R R′ S S′ y′ y (,-inj₂ ≡R) (,-inj₂ ≡R′) (,-inj₂ ≡S) (,-inj₂ ≡S′)
