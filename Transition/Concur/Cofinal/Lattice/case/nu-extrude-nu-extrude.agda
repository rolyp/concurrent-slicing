open import ConcurrentSlicingCommon
open import Transition.Concur.Cofinal.Lattice.Common
import Name as ᴺ
import Ren as ᴿ

module Transition.Concur.Cofinal.Lattice.case.nu-extrude-nu-extrude
   {Γ} {x u : Name Γ} {P₀ R₀ R′₀} {E : P₀ —[ • ᴺ.suc x 〈 ᴺ.zero 〉 ᶜ - _ ]→ R₀}
   {E′ : P₀ —[ • ᴺ.suc u 〈 ᴺ.zero 〉 ᶜ - _ ]→ R′₀} (𝐸 : E ⌣₁[ ᶜ∇ᶜ ] E′) (P : ↓ P₀)
   (IH : braiding (ᶜ∇ᶜ {a = • (ᴺ.suc x) 〈 ᴺ.zero 〉} {• ᴺ.suc u 〈 ᴺ.zero 〉}) {0} (γ₁ 𝐸)
         (tgt (E′/E (⊖₁ 𝐸)) (tgt E P)) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)) where

   private
      base : (R : ↓ R₀) (R′ : ↓ R′₀) →
             tgt E P ≡ R → tgt E′ P ≡ R′ →
             braiding (ˣ∇ˣ {x = x} {u}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) R) ≡ tgt (E/E′ (⊖₁ 𝐸)) R′
      base R R′ ≡R ≡R′ =
         let open ≅-Reasoning in ≅-to-≡ (
         begin
            braiding (ˣ∇ˣ {x = x} {u}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) R)
         ≅⟨ reduce-ˣ∇ˣ {x = x} {u} (γ₁ 𝐸) _ ⟩
            tgt (E′/E (⊖₁ 𝐸)) R
         ≡⟨ cong (tgt (E′/E (⊖₁ 𝐸))) (sym ≡R) ⟩
            tgt (E′/E (⊖₁ 𝐸)) (tgt E P)
         ≅⟨ ≅-sym (reduce-ᶜ∇ᶜ (γ₁ 𝐸) _) ⟩
            braiding (ᶜ∇ᶜ {a = • (ᴺ.suc x) 〈 ᴺ.zero 〉} {• ᴺ.suc u 〈 ᴺ.zero 〉}) {0} (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P))
         ≡⟨ IH ⟩
            tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P)
         ≡⟨ cong (tgt (E/E′ (⊖₁ 𝐸))) ≡R′ ⟩
            tgt (E/E′ (⊖₁ 𝐸)) R′
         ∎)

   case :
      braiding (ˣ∇ˣ {x = x} {u}) {0} (γ₁ 𝐸)
      (tgt (E′/E (⊖₁ 𝐸)) (tgt (ν• E) [ ν P ])) ≡ tgt (E/E′ (⊖₁ 𝐸)) (tgt (ν• E′) [ ν P ])
   case
      with step E′ P | step E P | inspect (step E′) P | inspect (step E) P
   ... | ◻ , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = base R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
   ... | ◻ , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = base R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
   ... | ◻ , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = base R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = base R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | ◻ , R | [ ≡R′ ] | [ ≡R ] = base R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = base R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | [ • ._ 〈 ◻ 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = base R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = base R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R′ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , R | [ ≡R′ ] | [ ≡R ] = base R R′ (,-inj₂ ≡R) (,-inj₂ ≡R′)
