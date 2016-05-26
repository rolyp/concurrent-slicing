module Transition.Lattice where

   open import ConcurrentSlicingCommon

   open import Action as ᴬ using (Action; module Action; Actionᵇ; module Actionᵇ; Actionᶜ; module Actionᶜ);
      open Action; open Actionᵇ; open Actionᶜ
   import Action.Lattice as ᴬ̃;
      open ᴬ̃.↓_; open ᴬ̃.↓⁻_; open ᴬ̃.↓ᵇ⁻_; open ᴬ̃.↓ᶜ⁻_; open ᴬ̃._≤_; open ᴬ̃._≤⁻_; open ᴬ̃._≤ᵇ⁻_; open ᴬ̃._≤ᶜ⁻_
   open import Action.Ren
   open import Lattice using (Lattices; Prefixes);
      open Lattice.Prefixes ⦃...⦄
         using (ᴹ; ⁻ᴹ; _⊔ᴹ_; _⊔ʳ_; ≤-trans; ≤⁻-trans)
         renaming (↓_ to ↓′_; ↓⁻_ to ↓⁻′_; _≤_ to _≤′_; _≤⁻_ to _≤⁻′_; _⊔_ to _⊔′_; _⊔⁻_ to _⊔⁻′_)
   import Lattice.Product
   open import Name as ᴺ using (Name; _+_)
   open import Name.Lattice as ᴺ̃ using (zero; suc; sucᴹ); open ᴺ̃.↓_; open ᴺ̃._≤_
   open import Proc using (Proc; module Proc); open Proc.Proc
   import Proc.Lattice as ᴾ̃; open ᴾ̃.↓_; open ᴾ̃.↓⁻_; open ᴾ̃._≤_; open ᴾ̃._≤⁻_
   open import Proc.Ren.Lattice renaming (_* to _*̃)
   open import Ren as ᴿ using (module Renameable); open Renameable ⦃...⦄
   open import Ren.Lattice as ᴿ̃ using (pop; popᴹ; push; swap)
   open import Transition as ᵀ using (_—[_-_]→_; module _—[_-_]→_); open _—[_-_]→_

   open module Action×Proc {Γ} = Lattice.Product (Action Γ) (Proc ∘ᶠ ᴬ.target) using (×-prefixes)

   -- Seem to need this to coerce product lattice to more specific type.
   instance
      ᴬᴾ-prefixes : ∀ {Γ} → Lattice.Prefixes (Σ[ a ∈ Action Γ ] Proc (ᴬ.target a))
      ᴬᴾ-prefixes = ×-prefixes

   {-
   outᴹ : ∀ {Γ P} {a : Action Γ} {R} {E₀ : P —[ a - _ ]→ R} {E E′ : ↓ E₀} → E ≤ E′ → out E ≤′ out E′
   outᴹ {E = [ _ │• F′ ]} {[ _ │• F″ ]} [ E │• F ] with outᴹ E | out F′ | out F″ | outᴹ F
   ... | _ , P | ◻ , _ | ◻ , _ | ◻ , Q = [ τ ᶜ ] , [ (popᴹ ◻ *ᴹ) P │ Q ]
   ... | _ , P | ◻ , _ | [ • _ 〈 _ 〉 ᶜ ] , _ | ◻ , Q = [ τ ᶜ ] , [ (popᴹ ◻ *ᴹ) P │ Q ]
   ... | _ , P | [ • _ 〈 _ 〉 ᶜ ] , _ | [ • _ 〈 _ 〉 ᶜ ] , _ | [ • _ 〈 y 〉 ᶜ ] , Q = [ τ ᶜ ] , [ (popᴹ y *ᴹ) P │ Q ]
   outᴹ [ E │ᵥ F ] with outᴹ E | outᴹ F
   ... | _ , P | _ , Q = [ τ ᶜ ] , [ ν [ P │ Q ] ]
   outᴹ {E = [ ν• E′ ]} {[ ν• E″ ]} [ ν•_ {x = x} E ] with out E′ | out E″ | outᴹ E
   ... | ◻ , _ | ◻ , _ | _ , P = ◻ , P
   ... | ◻ , _ | [ • ◻ 〈 _ 〉 ᶜ ] , _ | _ , P = ◻ , P
   ... | ◻ , _ | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | _ , P = ◻ , P
   ... | ◻ , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | _ , P = ◻ , P
   ... | [ • ◻ 〈 _ 〉 ᶜ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , P = ◻ , P
   ... | [ • ◻ 〈 _ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , P = ◻ , P
   ... | [ • ◻ 〈 _ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , P = ◻ , P
   ... | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , P = ◻ , P
   ... | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , P = ◻ , P
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , P =
      [ (• [ x ]) ᵇ ] , P
   outᴹ {a = x • ᵇ} {E = [ νᵇ E′ ]} {[ νᵇ E″ ]} [ νᵇ E ] with out E′ | out E″ | outᴹ E
   ... | ◻ , _ | ◻ , _ | _ , P = ◻ , [ ν (ᴹ swap *ᴹ) P ]
   ... | ◻ , _ | [ (◻ •) ᵇ ] , _ | _ , P = ◻ , [ ν (ᴹ swap *ᴹ) P ]
   ... | ◻ , _ | [ ([ ._ ] •) ᵇ ] , _ | _ , P = ◻ , [ ν (ᴹ swap *ᴹ) P ]
   ... | [ (◻ •) ᵇ ] , _ | [ (◻ •) ᵇ ] , _ | [ (◻ •) ᵇ ] , P = ◻ , [ ν (ᴹ swap *ᴹ) P ]
   ... | [ (◻ •) ᵇ ] , _ | [ ([ ._ ] •) ᵇ ] , _ | [ (◻ •) ᵇ ] , P = ◻ , [ ν (ᴹ swap *ᴹ) P ]
   ... | [ [ ._ ] • ᵇ ] , _ | [ [ ._ ] • ᵇ ] , _ | [ [ ._ ] • ᵇ ] , P = [ [ x ] • ᵇ ] , [ ν (ᴹ swap *ᴹ) P ]
   outᴹ {a = (• x) ᵇ} {E = [ νᵇ E′ ]} {[ νᵇ E″ ]} [ νᵇ E ] with out E′ | out E″ | outᴹ E
   ... | ◻ , _ | ◻ , _ | _ , P = ◻ , [ ν (ᴹ swap *ᴹ) P ]
   ... | ◻ , _ | [ (• ◻) ᵇ ] , _ | _ , P = ◻ , [ ν (ᴹ swap *ᴹ) P ]
   ... | ◻ , _ | [ (• [ ._ ]) ᵇ ] , _ | _ , P = ◻ , [ ν (ᴹ swap *ᴹ) P ]
   ... | [ (• ◻) ᵇ ] , _ | [ (• ◻) ᵇ ] , _ | [ (• ◻) ᵇ ] , P = ◻ , [ ν (ᴹ swap *ᴹ) P ]
   ... | [ (• ◻) ᵇ ] , _ | [ (• [ ._ ]) ᵇ ] , _ | [ (• ◻) ᵇ ] , P = ◻ , [ ν (ᴹ swap *ᴹ) P ]
   ... | [ (• [ ._ ]) ᵇ ] , _ | [ (• [ ._ ]) ᵇ ] , _ | [ (• [ ._ ]) ᵇ ] , P = [ (• [ x ]) ᵇ ] , [ ν (ᴹ swap *ᴹ) P ]
   outᴹ {a = • x 〈 y 〉 ᶜ} {E = [ νᶜ E′ ]} {[ νᶜ E″ ]} [ νᶜ E ] with out E′ | out E″ | outᴹ E
   ... | ◻ , _ | ◻ , _ | _ , P = ◻ , [ ν P ]
   ... | ◻ , _ | [ • ◻ 〈 _ 〉 ᶜ ] , _ | _ , P = ◻ , [ ν P ]
   ... | ◻ , _ | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | _ , P = ◻ , [ ν P ]
   ... | ◻ , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | _ , P = ◻ , [ ν P ]
   ... | [ • ◻ 〈 _ 〉 ᶜ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , P = ◻ , [ ν P ]
   ... | [ • ◻ 〈 _ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , P = ◻ , [ ν P ]
   ... | [ • ◻ 〈 _ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , P = ◻ , [ ν P ]
   ... | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , P = ◻ , [ ν P ]
   ... | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , P = ◻ , [ ν P ]
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , P =
      [ • [ x ] 〈 [ y ] 〉 ᶜ ] , [ ν P ]
   outᴹ {a = τ ᶜ} {E = [ νᶜ E′ ]} {[ νᶜ E″ ]} [ νᶜ E ] with out E′ | out E″ | outᴹ E
   ... | ◻ , _ | ◻ , _ | _ , P = ◻ , [ ν P ]
   ... | ◻ , _ | [ τ ᶜ ] , _ | _ , P = ◻ , [ ν P ]
   ... | [ τ ᶜ ] , _ | [ τ ᶜ ] , _ | [ τ ᶜ ] , P = [ τ ᶜ ] , [ ν P ]
   outᴹ [ ! E ] = outᴹ E
-}
   step : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓′ P → ↓′ ᵀ.out E
   step⁻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓⁻′ P → ↓′ ᵀ.out E

   step E [ P ] = step⁻ E P
   step E ◻ = ◻ , ◻

   step⁻ (_ •∙ _) (x •∙ P) = [ (x •) ᵇ ] , P
   step⁻ (• _ 〈 _ 〉∙ _) (• x 〈 y 〉∙ P) = [ • x 〈 y 〉 ᶜ ] , P
   step⁻ (E ➕₁ _) (P ➕ Q) = step E P
   step⁻ {a = _ ᵇ} (E ᵇ│ _) (P │ Q) = let a , R = step E P in a , [ R │ (push *̃) Q ]
   step⁻ {a = _ ᶜ} (E ᶜ│ _) (P │ Q) = let a , R = step E P in a , [ R │ Q ]
   step⁻ {a = _ ᵇ} (_ │ᵇ F) (P │ Q) = let a , S = step F Q in a , [ (push *̃) P │ S ]
   step⁻ {a = _ ᶜ} (_ │ᶜ F) (P │ Q) = let a , S = step F Q in a , [ P │ S ]
   step⁻ (E │• F) (P │ Q) with step E P
   ... | [ [ x ] • ᵇ ] , R with step F Q
   ... | [ • [ .x ] 〈 y 〉 ᶜ ] , S = [ τ ᶜ ] , [ (pop y *̃) R │ S ]
   ... | _ , S = ◻ , [ (pop ◻ *̃) R │ S ]
   step⁻ (E │• F) (P │ Q) | _ , R = let _ , S = step F Q in ◻ , [ (pop ◻ *̃) R │ S ]
   step⁻ (E │ᵥ F) (P │ Q) with step E P
   ... | [ [ x ] • ᵇ ] , R with step F Q
   ... | [ (• [ .x ]) ᵇ ] , S = [ τ ᶜ ] , [ ν [ R │ S ] ]
   ... | _ , S = ◻ , [ ν [ R │ S ] ]
   step⁻ (E │ᵥ F) (P │ Q) | _ , R = let _ , S = step F Q in ◻ , [ ν [ R │ S ] ]
-- step⁻ (E │ᵥ F) (P │ Q) with step E P | step F Q
-- ... | [ [ x ] • ᵇ ] , R | [ (• [ .x ]) ᵇ ] , S = [ τ ᶜ ] , [ ν [ R │ S ] ]
-- ... | _ , R | _ , S = ◻ , [ ν [ R │ S ] ]
   step⁻ (ν•_ {x = x} E) (ν P) with step E P
   ... | [ • [ .(ᴺ.suc x) ] 〈 [ .ᴺ.zero ] 〉 ᶜ ] , R = [ (• [ x ]) ᵇ ] , R
   ... | _ , R = ◻ , R
   step⁻ {a = x • ᵇ} (νᵇ E) (ν P) with step E P
   ... | [ [ .(ᴺ.suc x) ] • ᵇ ] , R = [ [ x ] • ᵇ ] , [ ν (swap *̃) R ]
   ... | _ , R = ◻ , [ ν (swap *̃) R ]
   step⁻ {a = (• x) ᵇ} (νᵇ E) (ν P) with step E P
   ... | [ (• [ .(ᴺ.suc x) ]) ᵇ ] , R = [ (• [ x ]) ᵇ ] ,  [ ν (swap *̃) R ]
   ... | _ , R = ◻ , [ ν (swap *̃) R ]
   step⁻ {a = • x 〈 y 〉 ᶜ} (νᶜ E) (ν P) with step E P
   ... | [ • [ .(ᴺ.suc x) ] 〈 [ .(ᴺ.suc y) ] 〉 ᶜ ] , R = [ • [ x ] 〈 [ y ] 〉 ᶜ ] , [ ν R ]
   ... | _ , R = ◻ , [ ν R ]
   -- Explicitly match the action, so we can translate it from Γ + 1 to Γ.
   step⁻ {a = τ ᶜ} (νᶜ E) (ν P) with step E P
   ... | [ τ ᶜ ] , R = [ τ ᶜ ] , [ ν R ]
   ... | ◻ , R = ◻ , [ ν R ]
   step⁻ (! E) (! P) = step E [ P │ [ ! P ] ]

   stepᴹ : ∀ {Γ P₀} {a : Action Γ} {P′} (E : P₀ —[ a - _ ]→ P′) {P P′ : ↓′ P₀} → P ≤′ P′ → step E P ≤′ step E P′
   step⁻ᴹ : ∀ {Γ P₀} {a : Action Γ} {P′} (E : P₀ —[ a - _ ]→ P′) {P P′ : ↓⁻′ P₀} → P ≤⁻′ P′ → step⁻ E P ≤′ step⁻ E P′

   stepᴹ E [ P ] = step⁻ᴹ E P
   stepᴹ E ◻ = ◻ , ◻

   step⁻ᴹ (_ •∙ _) (x •∙ P) = [ (x •) ᵇ ] , P
   step⁻ᴹ (• _ 〈 _ 〉∙ _) (• x 〈 y 〉∙ P) = [ • x 〈 y 〉 ᶜ ] , P
   step⁻ᴹ (E ➕₁ _) (P ➕ Q) = stepᴹ E P
   step⁻ᴹ {a = _ ᵇ} (E ᵇ│ _) (P │ Q) = let a , R = stepᴹ E P in a , [ R │ (ᴹ push *ᴹ) Q ]
   step⁻ᴹ {a = _ ᶜ} (E ᶜ│ _) (P │ Q) = let a , R = stepᴹ E P in a , [ R │ Q ]
   step⁻ᴹ {a = _ ᵇ} (_ │ᵇ F) (P │ Q) = let a , S = stepᴹ F Q in a , [ (ᴹ push *ᴹ) P │ S ]
   step⁻ᴹ {a = _ ᶜ} (_ │ᶜ F) (P │ Q) = let a , S = stepᴹ F Q in a , [ P │ S ]
{-
   step⁻ᴹ (E │• F) {P₀ │ Q₀} {P₀′ │ Q₀′} (P │ Q) with step E P₀ | step E P₀′ | stepᴹ E P
   ... | ◻ , proj₂ | ◻ , proj₄ | _ = {!!}
   ... | ◻ , proj₂ | [ (◻ •) ᵇ ] , proj₄ | _ = {!!}
   ... | ◻ , proj₂ | [ ([ x ] •) ᵇ ] , proj₄ | _ with step F Q₀ | step F Q₀′ | stepᴹ F Q
   ... | q | ◻ , _ | r = {!!}
   ... | q | [ • ◻ 〈 x₂ 〉 ᶜ ] , _ | r = {!!}
   ... | q | [ • [ .x ] 〈 x₂ 〉 ᶜ ] , _ | r = {!!}
   step⁻ᴹ (E │• F) {P₀ │ Q₀} {P₀′ │ Q₀′} (P₁ │ Q₁) | [ x₁ ] , proj₂ | ◻ , proj₄ | () , proj₆
   step⁻ᴹ (E │• F) {P₀ │ Q₀} {P₀′ │ Q₀′} (P₁ │ Q₁) | [ ◻ • ᵇ ] , proj₂ | [ ◻ • ᵇ ] , proj₄ | [ (x₁ •) ᵇ ] , proj₆ = {!!}
   step⁻ᴹ (E │• F) {P₀ │ Q₀} {P₀′ │ Q₀′} (P₁ │ Q) | [ ◻ • ᵇ ] , proj₂ | [ [ x ] • ᵇ ] , proj₄ | [ (x₁ •) ᵇ ] , proj₆
      with step F Q₀ | step F Q₀′ | stepᴹ F Q
   ... | q | ◻ , _ | s = {!!}
   ... | q | [ • ◻ 〈 x₂ 〉 ᶜ ] , _ | s = {!!}
   ... | q | [ • [ .x ] 〈 x₂ 〉 ᶜ ] , _ | s = {!!}
   step⁻ᴹ (E │• F) {P₀ │ Q₀} {P₀′ │ Q₀′} (P₁ │ Q₁) | [ [ x ] • ᵇ ] , _ | [ ◻ • ᵇ ] , _ | [ () • ᵇ ] , _
   step⁻ᴹ (E │• F) {P₀ │ Q₀} {P₀′ │ Q₀′} (P₁ │ Q) | [ [ x ] • ᵇ ] , proj₂ | [ [ .x ] • ᵇ ] , proj₄ | [ x₁ • ᵇ ] , proj₆
      with step F Q₀ | step F Q₀′ | stepᴹ F Q
   ... | ◻ , _ | ◻ , _ | s = {!!}
   ... | [ • ◻ 〈 x₂ 〉 ᶜ ] , _ | ◻ , _ | s = {!!}
   ... | [ • [ .x ] 〈 x₂ 〉 ᶜ ] , _ | ◻ , _ | () , _
   ... | ◻ , _ | [ • ◻ 〈 x₂ 〉 ᶜ ] , _ | s = {!!}
   ... | ◻ , _ | [ • [ .x ] 〈 x₂ 〉 ᶜ ] , _ | s = {!!}
   ... | [ • ◻ 〈 x₂ 〉 ᶜ ] , _ | [ • ◻ 〈 x₃ 〉 ᶜ ] , _ | s = {!!}
   ... | [ • ◻ 〈 x₂ 〉 ᶜ ] , _ | [ • [ .x ] 〈 x₃ 〉 ᶜ ] , _ | s = {!!}
   ... | [ • [ .x ] 〈 x₂ 〉 ᶜ ] , _ | [ • ◻ 〈 x₃ 〉 ᶜ ] , _ | s = {!!}
   ... | [ • [ .x ] 〈 x₂ 〉 ᶜ ] , _ | [ • [ .x ] 〈 x₃ 〉 ᶜ ] , _ | s = {!!}
-}
   step⁻ᴹ (E │ᵥ F) {P │ Q} {P′ │ Q′} (P† │ Q†)
      with step E P | step E P′ | stepᴹ E P†
   ... | ◻ , _ | ◻ , _ | _ , R† = let _ , S† = stepᴹ F Q† in ◻ , [ ν [ R† │ S† ] ]
   ... | ◻ , _ | [ (◻ •) ᵇ ] , _ | _ , R† = let _ , S† = stepᴹ F Q† in ◻ , [ ν [ R† │ S† ] ]
   ... | ◻ , _ | [ ([ x ] •) ᵇ ] , _ | _ , R†
      with step F Q′ | stepᴹ F Q†
   ... | ◻ , _ | _ , S† = ◻ , [ ν [ R† │ S† ] ]
   ... | [ (• ◻) ᵇ ] , _ | _ , S† = ◻ , [ ν [ R† │ S† ] ]
   ... | [ (• [ .x ]) ᵇ ] , _ | _ , S† = ◻ , [ ν [ R† │ S† ] ]
   step⁻ᴹ (E │ᵥ F) {P │ Q} {P′ │ Q′} (P† │ Q†) | [ _ ] , _ | ◻ , _ | () , _
   step⁻ᴹ (E │ᵥ F) {P │ Q} {P′ │ Q′} (P† │ Q†) | [ (◻ •) ᵇ ] , _ | [ (◻ •) ᵇ ] , _ | _ , R† =
      let _ , S† = stepᴹ F Q† in ◻ , [ ν [ R† │ S† ] ]
   step⁻ᴹ (E │ᵥ F) {P │ Q} {P′ │ Q′} (P† │ Q†) | [ (◻ •) ᵇ ] , _ | [ [ x ] • ᵇ ] , _ | _ , R†
      with step F Q′ | stepᴹ F Q†
   ... | ◻ , _ | _ , S† = ◻ , [ ν [ R† │ S† ] ]
   ... | [ (• ◻) ᵇ ] , _ | _ , S† = ◻ , [ ν [ R† │ S† ] ]
   ... | [ (• [ .x ]) ᵇ ] , _ | _ , S† = ◻ , [ ν [ R† │ S† ] ]
   step⁻ᴹ (E │ᵥ F) {P │ Q} {P′ │ Q′} (P† │ Q†) | [ ([ x ] •) ᵇ ] , _ | [ (◻ •) ᵇ ] , _ | [ (() •) ᵇ ] , proj₈
   step⁻ᴹ (E │ᵥ F) {P │ Q} {P′ │ Q′} (P† │ Q†) | [ ([ x ] •) ᵇ ] , proj₂ | [ ([ .x ] •) ᵇ ] , proj₄ | w
      with step F Q | step F Q′ | stepᴹ F Q†
   ... | ◻ , _ | ◻ , _ | proj₅ , S = {!!}
   ... | ◻ , _ | [ (• ◻) ᵇ ] , _ | proj₅ , S = {!!}
   ... | ◻ , _ | [ (• [ .x ]) ᵇ ] , _ | proj₅ , S = {!!}
   ... | [ (• ◻) ᵇ ] , _ | ◻ , _ | proj₅ , S = {!!}
   ... | [ (• [ .x ]) ᵇ ] , _ | ◻ , _ | () , _
   ... | [ (• ◻) ᵇ ] , _ | [ (• ◻) ᵇ ] , _ | proj₅ , proj₆ = {!!}
   ... | [ (• ◻) ᵇ ] , _ | [ (• [ .x ]) ᵇ ] , _ | proj₅ , proj₆ = {!!}
   ... | [ (• [ .x ]) ᵇ ] , _ | [ (• ◻) ᵇ ] , _ | [ (• ()) ᵇ ] , _
   ... | [ (• [ .x ]) ᵇ ] , _ | [ (• [ .x ]) ᵇ ] , _ | proj₅ , proj₆ = {!!}

   step⁻ᴹ E P = {!!}
{-
   step⁻ᴹ (E │ᵥ F) {R = R │ S} {R′ │ S′} (P │ Q) with action (step E R) | action (step E R′) | actionᴹ (stepᴹ E P)
   ... | ◻ | _ | _ = ◻
   ... | [ ◻ • ᵇ ] | [ _ • ᵇ ] | [ ◻ • ᵇ ] = ◻
   ... | [ ([ x ] •) ᵇ ] | [ ([ .x ] •) ᵇ ] | [ ([ .x ] •) ᵇ ]
      with action (step F S) | action (step F S′) | actionᴹ (stepᴹ F Q)
   ... | ◻ | _ | _ = ◻
   ... | [ (• ◻) ᵇ ] | [ (• _) ᵇ ] | [ (• ◻) ᵇ ] = ◻
   ... | [ (• [ .x ]) ᵇ ] | [ (• [ .x ]) ᵇ ] | [ (• [ .x ]) ᵇ ] = [ stepᴹ E P │ᵥ stepᴹ F Q ]
   step⁻ᴹ (ν• E) {R = ν R} {ν R′} (ν P) with action (step E R) | action (step E R′) | actionᴹ (stepᴹ E P)
   ... | ◻ | _ | _ = ◻
   ... | [ • ◻ 〈 _ 〉 ᶜ ] | [ • _ 〈 _ 〉 ᶜ ] | [ • ◻ 〈 _ 〉 ᶜ ] = ◻
   ... | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] | [ • [ ._ ] 〈 _ 〉 ᶜ ] | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] = ◻
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] = [ ν• (stepᴹ E P) ]
   step⁻ᴹ {a = (• x) ᵇ} (νᵇ E) {R = ν R} {ν R′} (ν P) with action (step E R) | action (step E R′) | actionᴹ (stepᴹ E P)
   ... | ◻ | _ | _ = ◻
   ... | [ (• ◻) ᵇ ] | [ (• _) ᵇ ] | [ (• ◻) ᵇ ] = ◻
   ... | [ (• [ ._ ]) ᵇ ] | [ (• [ ._ ]) ᵇ ] | [ (• [ ._ ]) ᵇ ] = [ νᵇ (stepᴹ E P) ]
   step⁻ᴹ {a = x • ᵇ} (νᵇ E ) {R = ν R} {ν R′} (ν P) with action (step E R) | action (step E R′) | actionᴹ (stepᴹ E P)
   ... | ◻ | _ | _ = ◻
   ... | [ ◻ • ᵇ ] | [ _ • ᵇ ] | [ ◻ • ᵇ ] = ◻
   ... | [ [ ._ ] • ᵇ ] | [ [ ._ ] • ᵇ ] | [ [ ._ ] • ᵇ ] = [ νᵇ (stepᴹ E P) ]
   step⁻ᴹ {a = • x 〈 y 〉 ᶜ} (νᶜ E) {R = ν R} {ν R′} (ν P)
      with action (step E R) | action (step E R′) | actionᴹ (stepᴹ E P)
   ... | ◻ | _ | _ = ◻
   ... | [ • ◻ 〈 _ 〉 ᶜ ] | [ • _ 〈 _ 〉 ᶜ ] | [ • ◻ 〈 _ 〉 ᶜ ] = ◻
   ... | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] | [ • [ ._ ] 〈 _ 〉 ᶜ ] | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] = ◻
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] = [ νᶜ (stepᴹ E P) ]
   ... | [ • [ ._ ] 〈 _ 〉 ᶜ ] | [ • ◻ 〈 _ 〉 ᶜ ] | [ • () 〈 _ 〉 ᶜ ]
   step⁻ᴹ {a = τ ᶜ} (νᶜ E) {R = ν R} {ν R′} (ν P) with action (step E R) | action (step E R′) | actionᴹ (stepᴹ E P)
   ... | ◻ | _ | _ = ◻
   ... | [ τ ᶜ ] | [ τ ᶜ ] | [ τ ᶜ ] = [ νᶜ (stepᴹ E P) ]
   step⁻ᴹ (! E) (! P) = [ ! stepᴹ E [ P │ [ ! P ] ] ]
-}
   action : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓′ P → ↓′ a
   action E = π₁ ∘ᶠ step E

   actionᴹ : ∀ {Γ P₀} {a : Action Γ} {R} (E : P₀ —[ a - _ ]→ R) {P P′ : ↓′ P₀} → P ≤′ P′ → action E P ≤′ action E P′
   actionᴹ E = π₁ ∘ᶠ stepᴹ E

   -- Called 'fwd' in the paper.
   target : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓′ P → ↓′ R
   target E = π₂ ∘ᶠ step E

   targetᴹ : ∀ {Γ P₀} {a : Action Γ} {R} (E : P₀ —[ a - _ ]→ R) {P P′ : ↓′ P₀} → P ≤′ P′ → target E P ≤′ target E P′
   targetᴹ E = π₂ ∘ᶠ stepᴹ E
{-
   -- unstep reflects ◻. The unstep-◻ variant slices with a ◻ process and a non-◻ action. The recursion case
   -- is simpler than in the paper, because we don't specify here the slice of the source process.
   unstep : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) → ↓′ a → ↓′ P′ → ↓ E
   unstep-◻ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) → ↓⁻′ a → ↓⁻ E
   unstep⁻ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) → ↓′ a → ↓⁻′ P′ → ↓⁻ E

   unstep E a [ R ] = [ unstep⁻ E a R ]
   unstep E [ a ] ◻ = [ unstep-◻ E a ]
   unstep _ ◻ ◻ = ◻

   unstep-◻ (_ •∙ P) (x • ᵇ) = x •∙ ◻
   unstep-◻ (• _ 〈 _ 〉∙ _) (• x 〈 y 〉 ᶜ) = • x 〈 y 〉∙ ◻
   unstep-◻ (E ➕₁ Q) a = [ unstep-◻ E a ] ➕₁ ◻
   unstep-◻ (E ᵇ│ Q) a = [ unstep-◻ E a ] ᵇ│ ◻
   unstep-◻ (E ᶜ│ Q) a = [ unstep-◻ E a ] ᶜ│ ◻
   unstep-◻ (P │ᵇ E) a = ◻ │ᵇ [ unstep-◻ E a ]
   unstep-◻ (P │ᶜ E) a = ◻ │ᶜ [ unstep-◻ E a ]
   unstep-◻ (E │• F) (τ ᶜ) = [ unstep-◻ E ([ _ ] • ᵇ) ] │• [ unstep-◻ F (• [ _ ] 〈 ◻ 〉 ᶜ) ]
   unstep-◻ (E │ᵥ F) (τ ᶜ) = [ unstep-◻ E ([ _ ] • ᵇ) ] │ᵥ [ unstep-◻ F ((• [ _ ]) ᵇ) ]
   unstep-◻ (ν• E) ((• _) ᵇ) = ν• [ unstep-◻ E (• suc [ _ ] 〈 zero 〉 ᶜ) ]
   unstep-◻ {a = x • ᵇ} (νᵇ E) _ = νᵇ [ unstep-◻ E ([ (ᴿ.push *) x ] • ᵇ) ]
   unstep-◻ {a = (• x) ᵇ} (νᵇ E) _ = νᵇ [ unstep-◻ E ((• [ (ᴿ.push *) x ]) ᵇ) ]
   unstep-◻ {a = • x 〈 y 〉 ᶜ} (νᶜ E) _ = νᶜ [ unstep-◻ E (• [ (ᴿ.push *) x ] 〈 [ (ᴿ.push *) y ] 〉 ᶜ) ]
   unstep-◻ {a = τ ᶜ} (νᶜ E) _ = νᶜ [ unstep-◻ E (τ ᶜ) ]
   unstep-◻ (! E) a = ! [ unstep-◻ E a ]

   unstep⁻ (_ •∙ _) ◻ R = ◻ •∙ [ R ]
   unstep⁻ (_ •∙ _) [ x • ᵇ ] R = x •∙ [ R ]
   unstep⁻ (• _ 〈 _ 〉∙ ._) ◻ R = • ◻ 〈 ◻ 〉∙ [ R ]
   unstep⁻ (• _ 〈 _ 〉∙ ._) [ • x 〈 y 〉 ᶜ ] R = • x 〈 y 〉∙ [ R ]
   unstep⁻ (E ➕₁ _) a R = [ unstep⁻ E a R ] ➕₁ ◻
   unstep⁻ {a = _ ᵇ} (E ᵇ│ Q) a (R │ S) = unstep E a R ᵇ│ π₂ ((ᴿ.push †) Q S)
   unstep⁻ {a = _ ᶜ} (E ᶜ│ Q) a (R │ S) = unstep E a R ᶜ│ S
   unstep⁻ {a = _ ᵇ} (P │ᵇ E) a (R │ S) = π₂ ((ᴿ.push †) P R) │ᵇ unstep E a S
   unstep⁻ {a = _ ᶜ} (P │ᶜ E) a (R │ S) = R │ᶜ unstep E a S
   unstep⁻ (_│•_ {R = P′} {x = x} {y} E F) _ (R │ S) with (ᴿ.pop y †) P′ R
   ... | pop-y , R′ = unstep E [ [ _ ] • ᵇ ] R′ │• unstep F [ • [ _ ] 〈 pop-y ᴺ.zero 〉 ᶜ ] S
   unstep⁻ (E │ᵥ F) _ (ν ◻) = [ unstep-◻ E ([ _ ] • ᵇ) ] │ᵥ [ unstep-◻ F ((• [ _ ]) ᵇ) ]
   unstep⁻ (E │ᵥ F) _ (ν [ R │ S ]) = unstep E [ [ _ ] • ᵇ ] R │ᵥ unstep F [ (• [ _ ]) ᵇ ] S
   unstep⁻ (ν• E) _ R = ν• [ unstep⁻ E [ • suc [ _ ] 〈 zero 〉 ᶜ ] R ]
   unstep⁻ {a = x • ᵇ} (νᵇ_ {R = P′} E) _ (ν R) = νᵇ unstep E [ [ (ᴿ.push *) x ] • ᵇ ] (π₂ ((ᴿ.swap †) P′ R))
   unstep⁻ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) _ (ν R) = νᵇ unstep E [ (• [ (ᴿ.push *) x ]) ᵇ ] (π₂ ((ᴿ.swap †) P′ R))
   unstep⁻ {a = • x 〈 y 〉 ᶜ} (νᶜ_ {R = P′} E) _ (ν R) = νᶜ unstep E [ (• [ (ᴿ.push *) x ] 〈 [ (ᴿ.push *) y ] 〉) ᶜ ] R
   unstep⁻ {a = τ ᶜ} (νᶜ_ {R = P′} E) _ (ν R) = νᶜ unstep E [ τ ᶜ ] R
   unstep⁻ (! E) a R = ! [ unstep⁻ E a R ]

   unstep-◻ᴹ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) {a′ a″ : ↓⁻′ a} →
               a′ ≤⁻′ a″ → unstep-◻ E a′ ≤⁻ unstep-◻ E a″
   unstep-◻ᴹ (_ •∙ _) (x • ᵇ) = x •∙ ◻
   unstep-◻ᴹ (• _ 〈 _ 〉∙ _) (• x 〈 y 〉 ᶜ) = • x 〈 y 〉∙ ◻
   unstep-◻ᴹ (E ➕₁ _) a = [ unstep-◻ᴹ E a ] ➕₁ ◻
   unstep-◻ᴹ (E ᵇ│ _) a = [ unstep-◻ᴹ E a ] ᵇ│ ◻
   unstep-◻ᴹ (E ᶜ│ _) a = [ unstep-◻ᴹ E a ] ᶜ│ ◻
   unstep-◻ᴹ (_ │ᵇ E) a = ◻ │ᵇ [ unstep-◻ᴹ E a ]
   unstep-◻ᴹ (_ │ᶜ E) a = ◻ │ᶜ [ unstep-◻ᴹ E a ]
   unstep-◻ᴹ (E │• F) (τ ᶜ) = [ unstep-◻ᴹ E ([ _ ] • ᵇ) ] │• [ unstep-◻ᴹ F (• [ _ ] 〈 ◻ 〉 ᶜ) ]
   unstep-◻ᴹ (ν• E) ((• _) ᵇ) = ν• [ unstep-◻ᴹ E (• sucᴹ [ _ ] 〈 ᴹ zero 〉 ᶜ) ]
   unstep-◻ᴹ (E │ᵥ F) (τ ᶜ) = [ unstep-◻ᴹ E ([ _ ] • ᵇ) ] │ᵥ [ unstep-◻ᴹ F ((• [ _ ]) ᵇ) ]
   unstep-◻ᴹ {a = x • ᵇ} (νᵇ E) (_ • ᵇ) = νᵇ [ unstep-◻ᴹ E ([ (ᴿ.push *) x ] • ᵇ) ]
   unstep-◻ᴹ {a = (• x) ᵇ} (νᵇ E) ((• _) ᵇ) = νᵇ [ unstep-◻ᴹ E ((• [ (ᴿ.push *) x ]) ᵇ) ]
   unstep-◻ᴹ {a = • x 〈 y 〉 ᶜ} (νᶜ E) (• _ 〈 _ 〉 ᶜ) = νᶜ [ unstep-◻ᴹ E (• [ (ᴿ.push *) x ] 〈 [ (ᴿ.push *) y ] 〉 ᶜ) ]
   unstep-◻ᴹ {a = τ ᶜ} (νᶜ E) (τ ᶜ) = νᶜ [ unstep-◻ᴹ E (τ ᶜ) ]
   unstep-◻ᴹ (! E) a = ! [ unstep-◻ᴹ E a ]

   -- Auxiliary lemmas needed for monotonicity.
   unstep-◻-min : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) (a′ : ↓⁻′ a) (R : ↓′ P′) →
                  [ unstep-◻ E a′ ] ≤ unstep E [ a′ ] R
   unstep-◻-min⁻ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) (a′ : ↓⁻′ a) (R : ↓⁻′ P′) →
                   unstep-◻ E a′ ≤⁻ unstep⁻ E [ a′ ] R

   unstep-◻-min E a ◻ = [ ⁻ᴹ (unstep-◻ E a) ]
   unstep-◻-min E a [ R ] = [ unstep-◻-min⁻ E a R ]

   unstep-◻-min⁻ (_ •∙ _) (x • ᵇ) _ = ᴹ x •∙ ◻
   unstep-◻-min⁻ (• _ 〈 _ 〉∙ _) (• x 〈 y 〉 ᶜ) _ = • ᴹ x 〈 ᴹ y 〉∙ ◻
   unstep-◻-min⁻ (E ➕₁ _) a P = [ unstep-◻-min⁻ E a P ] ➕₁ ◻
   unstep-◻-min⁻ (E ᵇ│ _) a (P │ Q) = unstep-◻-min E a P ᵇ│ ◻
   unstep-◻-min⁻ (E ᶜ│ _) a (P │ Q) = unstep-◻-min E a P ᶜ│ ◻
   unstep-◻-min⁻ (_ │ᵇ E) a (P │ Q) = ◻ │ᵇ unstep-◻-min E a Q
   unstep-◻-min⁻ (_ │ᶜ E) a (P │ Q) = ◻ │ᶜ unstep-◻-min E a Q
   unstep-◻-min⁻ (_│•_ {R = P′} {y = y} E F) (τ ᶜ) (P │ Q) with (ᴿ.pop y †) P′ P
   ... | pop-y , R =
      unstep-◻-min E ([ _ ] • ᵇ) R │•
      ≤-trans [ unstep-◻ᴹ F (• [ _ ] 〈 ◻ 〉 ᶜ) ] (unstep-◻-min F (• [ _ ] 〈 pop-y ᴺ.zero 〉 ᶜ) Q)
   unstep-◻-min⁻ (ν• E) ((• _) ᵇ) P = ν• [ unstep-◻-min⁻ E (• suc [ _ ] 〈 zero 〉 ᶜ) P ]
   unstep-◻-min⁻ (E │ᵥ F) (τ ᶜ) (ν ◻) = [ ⁻ᴹ (unstep-◻ E ([ _ ] • ᵇ)) ] │ᵥ [ ⁻ᴹ (unstep-◻ F ((• [ _ ]) ᵇ)) ]
   unstep-◻-min⁻ (E │ᵥ F) (τ ᶜ) (ν [ P │ Q ]) = unstep-◻-min E ([ _ ] • ᵇ) P │ᵥ unstep-◻-min F ((• [ _ ]) ᵇ) Q
   unstep-◻-min⁻ {a = x • ᵇ} (νᵇ_ {R = P′} E) _ (ν P) = νᵇ unstep-◻-min E ([ (ᴿ.push *) x ] • ᵇ) (π₂ ((ᴿ.swap †) P′ P))
   unstep-◻-min⁻ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) _ (ν P) = νᵇ unstep-◻-min E ((• [ (ᴿ.push *) x ]) ᵇ) (π₂ ((ᴿ.swap †) P′ P))
   unstep-◻-min⁻ {a = • x 〈 y 〉 ᶜ} (νᶜ_ {R = P′} E) _ (ν P) = νᶜ unstep-◻-min E (• [ (ᴿ.push *) x ] 〈 [ (ᴿ.push *) y ] 〉 ᶜ) P
   unstep-◻-min⁻ {a = τ ᶜ} (νᶜ_ {R = P′} E) _ (ν P) = νᶜ unstep-◻-min E (τ ᶜ) P
   unstep-◻-min⁻ (! E) a R = ! [ unstep-◻-min⁻ E a R ]

   unstepᴹ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) {a′ a″ : ↓′ a} {R R′ : ↓′ P′} →
                a′ ≤′ a″ → R ≤′ R′ → unstep E a′ R ≤ unstep E a″ R′
   unstep⁻ᴹ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) {a′ a″ : ↓′ a} {R R′ : ↓⁻′ P′} →
              a′ ≤′ a″ → R ≤⁻′ R′ → unstep⁻ E a′ R ≤⁻ unstep⁻ E a″ R′

   unstepᴹ E a [ R ] = [ unstep⁻ᴹ E a R ]
   unstepᴹ E {[ _ ]} {[ _ ]} {◻} {◻} [ a ] ◻ = [ unstep-◻ᴹ E a ]
   unstepᴹ E {[ _ ]} {[ _ ]} {◻} {[ R ]} [ a ] ◻ = [ ≤⁻-trans (unstep-◻ᴹ E a) (unstep-◻-min⁻ E _ R) ]
   unstepᴹ E {◻} ◻ ◻ = ◻

   unstep⁻ᴹ (_ •∙ _) {◻} {◻} ◻ R = ◻ •∙ [ R ]
   unstep⁻ᴹ (_ •∙ _) {◻} {[ _ • ᵇ ]} ◻ R = ◻ •∙ [ R ]
   unstep⁻ᴹ (_ •∙ _) {[ _ • ᵇ ]} {[ _ • ᵇ ]} [ u • ᵇ ] R = u •∙ [ R ]
   unstep⁻ᴹ (• _ 〈 _ 〉∙ _) {◻} {◻} ◻ R = • ◻ 〈 ◻ 〉∙ [ R ]
   unstep⁻ᴹ (• _ 〈 _ 〉∙ _) {◻} {[ • _ 〈 _ 〉 ᶜ ]} ◻ R = • ◻ 〈 ◻ 〉∙ [ R ]
   unstep⁻ᴹ (• _ 〈 _ 〉∙ _) {[ • _ 〈 _ 〉 ᶜ ]} {[ • _ 〈 _ 〉 ᶜ ]} [ • x 〈 y 〉 ᶜ ] R = • x 〈 y 〉∙ [ R ]
   unstep⁻ᴹ (E ➕₁ Q) a R = [ unstep⁻ᴹ E a R ] ➕₁ ◻
   unstep⁻ᴹ (E ᵇ│ Q) a′ (R │ S) = unstepᴹ E a′ R ᵇ│ π₂ ((ᴿ.push †ᴹ) Q S)
   unstep⁻ᴹ (E ᶜ│ Q) a′ (R │ S) = unstepᴹ E a′ R ᶜ│ S
   unstep⁻ᴹ (P │ᵇ E) a′ (R │ S) = π₂ ((ᴿ.push †ᴹ) P R) │ᵇ unstepᴹ E a′ S
   unstep⁻ᴹ (P │ᶜ E) a′ (R │ S) = R │ᶜ unstepᴹ E a′ S
   unstep⁻ᴹ (_│•_ {R = P″} {y = y} E F) {R = P │ _} {P′ │ _} a (R │ S) with (ᴿ.pop y †ᴹ) P″ R
   ... | pop-y , R′ = unstepᴹ E [ [ _ ] • ᵇ ] R′ │• unstepᴹ F [ • [ _ ] 〈 pop-y ᴺ.zero 〉 ᶜ ] S
   unstep⁻ᴹ (ν• E) _ R = ν• [ unstep⁻ᴹ E [ • sucᴹ [ _ ] 〈 ᴹ zero 〉 ᶜ ] R ]
   unstep⁻ᴹ (E │ᵥ F) {R = ν ◻} {ν ◻} _ (ν ◻) = [ ⁻ᴹ (unstep-◻ E ([ _ ] • ᵇ)) ] │ᵥ [ ⁻ᴹ (unstep-◻ F ((• _) ᵇ)) ]
   unstep⁻ᴹ (E │ᵥ F) {R = ν ◻} {ν [ P │ Q ]} _ (ν ◻) = unstep-◻-min E ([ _ ] • ᵇ) P │ᵥ unstep-◻-min F ((• _) ᵇ) Q
   unstep⁻ᴹ (E │ᵥ F) {R = ν [ _ │ _ ]} {ν [ _ │ _ ]} _ (ν [ R │ S ]) =
      unstepᴹ E [ [ _ ] • ᵇ ] R │ᵥ unstepᴹ F [ (• [ _ ]) ᵇ ] S
   unstep⁻ᴹ {a = x • ᵇ} (νᵇ_ {R = P′} E) _ (ν R) = νᵇ unstepᴹ E [ [ (ᴿ.push *) x ] • ᵇ ] (π₂ ((ᴿ.swap †ᴹ) P′ R))
   unstep⁻ᴹ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) _ (ν R) = νᵇ unstepᴹ E [ (• [ (ᴿ.push *) x ]) ᵇ ] (π₂ ((ᴿ.swap †ᴹ) P′ R))
   unstep⁻ᴹ {a = • x 〈 y 〉 ᶜ} (νᶜ_ {R = P′} E) _ (ν R) = νᶜ unstepᴹ E [ • [ (ᴿ.push *) x ] 〈 [ (ᴿ.push *) y ] 〉 ᶜ ] R
   unstep⁻ᴹ {a = τ ᶜ} (νᶜ_ {R = P′} E) _ (ν R) = νᶜ unstepᴹ E [ τ ᶜ ] R
   unstep⁻ᴹ (! E) a R = ! [ unstep⁻ᴹ E a R ]

   fwd : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓′ P → ↓′ (a , R)
   fwd E = out ∘ᶠ step E

   fwd⁻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓⁻′ P → ↓′ (a , R)
   fwd⁻ E = out ∘ᶠ step⁻ E

   fwdᴹ : ∀ {Γ P₀} {a : Action Γ} {R} (E : P₀ —[ a - _ ]→ R) {P P′ : ↓′ P₀} → P ≤′ P′ → fwd E P ≤′ fwd E P′
   fwdᴹ E = outᴹ ∘ᶠ stepᴹ E

   fwd⁻ᴹ : ∀ {Γ P₀} {a : Action Γ} {R} (E : P₀ —[ a - _ ]→ R) {P P′ : ↓⁻′ P₀} → P ≤⁻′ P′ → fwd⁻ E P ≤′ fwd⁻ E P′
   fwd⁻ᴹ E = outᴹ ∘ᶠ step⁻ᴹ E

   bwd : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓′ (a , R) → ↓′ P
   bwd E (a , R) = source (unstep E a R)

   bwdᴹ : ∀ {Γ P} {a₀ : Action Γ} {R₀} (E : P —[ a₀ - _ ]→ R₀) {a a′ : ↓′ a₀} {R R′ : ↓′ R₀} →
          (a , R) ≤′ (a′ , R′) → bwd E (a , R) ≤′ bwd E (a′ , R′)
   bwdᴹ E (a , R) = sourceᴹ (unstepᴹ E a R)

   bwd-◻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓⁻′ a → ↓⁻′ P
   bwd-◻ E a = source⁻ (unstep-◻ E a)

   bwd⁻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓′ a → ↓⁻′ R → ↓⁻′ P
   bwd⁻ E a R = source⁻ (unstep⁻ E a R)

   bwd⁻ᴹ : ∀ {Γ P} {a₀ : Action Γ} {R₀} (E : P —[ a₀ - _ ]→ R₀) {a a′ : ↓′ a₀} {R R′ : ↓⁻′ R₀} →
           a ≤′ a′ → R ≤⁻′ R′ → bwd⁻ E a R ≤⁻′ bwd⁻ E a′ R′
   bwd⁻ᴹ E a R = source⁻ᴹ (unstep⁻ᴹ E a R)
-}
