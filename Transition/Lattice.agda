module Transition.Lattice where

   open import ConcurrentSlicingCommon

   open import Action as ᴬ using (Action; module Action; Actionᵇ; module Actionᵇ; Actionᶜ; module Actionᶜ);
      open Action; open Actionᵇ; open Actionᶜ
   open import Action.Lattice as ᴬ̃ using (ᴬ◻);
      open ᴬ̃.↓_; open ᴬ̃.↓ᵇ_; open ᴬ̃.↓ᶜ_; open ᴬ̃._≤_; open ᴬ̃._≤ᵇ_; open ᴬ̃._≤ᶜ_
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

   open module Action×Proc {Γ} = Lattice.Product (Action Γ) (Proc ∘ᶠ ᴬ.tgt) using (×-prefixes)

   -- Seem to need this to coerce product lattice to more specific type.
   instance
      ᴬᴾ-prefixes : ∀ {Γ} → Lattice.Prefixes (Σ[ a ∈ Action Γ ] Proc (ᴬ.tgt a))
      ᴬᴾ-prefixes = ×-prefixes

   step : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓′ P → ↓′ ᵀ.out E
   step⁻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓⁻′ P → ↓′ ᵀ.out E

   step E [ P ] = step⁻ E P
   step E ◻ = ᴬ◻ , ◻

   step⁻ (x •∙ _) (.x •∙ P) = (x •) ᵇ , P
   step⁻ (• x 〈 _ 〉∙ _) (• .x 〈 y 〉∙ P) = • x 〈 y 〉 ᶜ , P
   step⁻ (E ➕₁ _) (P ➕ Q) = step E P
   step⁻ {a = _ ᵇ} (E ᵇ│ _) (P │ Q) = let a , R = step E P in a , [ R │ (push *̃) Q ]
   step⁻ {a = _ ᶜ} (E ᶜ│ _) (P │ Q) = let a , R = step E P in a , [ R │ Q ]
   step⁻ {a = _ ᵇ} (_ │ᵇ F) (P │ Q) = let a , S = step F Q in a , [ (push *̃) P │ S ]
   step⁻ {a = _ ᶜ} (_ │ᶜ F) (P │ Q) = let a , S = step F Q in a , [ P │ S ]
   step⁻ (E │• F) (P │ Q) with step E P | step F Q
   ... | (x •) ᵇ , R | • .x 〈 y 〉 ᶜ , S = τ ᶜ , [ (pop y *̃) R │ S ]
   step⁻ (E │ᵥ F) (P │ Q) with step E P | step F Q
   ... | x • ᵇ , R | (• .x) ᵇ , S = τ ᶜ , [ ν [ R │ S ] ]
   step⁻ (ν•_ {x = x} E) (ν P) with step E P
   ... | • .(ᴺ.suc x) 〈 _ 〉 ᶜ , R = (• x) ᵇ , R
   step⁻ {a = x • ᵇ} (νᵇ E) (ν P) with step E P
   ... | .(ᴺ.suc x) • ᵇ , R = x • ᵇ , [ ν (swap *̃) R ]
   step⁻ {a = (• x) ᵇ} (νᵇ E) (ν P) with step E P
   ... | (• .(ᴺ.suc x)) ᵇ , R = (• x) ᵇ ,  [ ν (swap *̃) R ]
   step⁻ {a = • x 〈 y 〉 ᶜ} (νᶜ E) (ν P) with step E P
   ... | • .(ᴺ.suc x) 〈 [ .(ᴺ.suc y) ] 〉 ᶜ , R = • x 〈 [ y ] 〉 ᶜ , [ ν R ]
   ... | • .(ᴺ.suc x) 〈 ◻ 〉 ᶜ , R = • x 〈 ◻ 〉 ᶜ , [ ν R ]
   -- Explicitly match the action to translate it by (+ 1).
   step⁻ {a = τ ᶜ} (νᶜ E) (ν P) with step E P
   ... | τ ᶜ , R = τ ᶜ , [ ν R ]
   step⁻ (! E) (! P) = step E [ P │ [ ! P ] ]

   stepᴹ : ∀ {Γ P₀} {a : Action Γ} {P′} (E : P₀ —[ a - _ ]→ P′) {P P′ : ↓′ P₀} → P ≤′ P′ → step E P ≤′ step E P′
   step⁻ᴹ : ∀ {Γ P₀} {a : Action Γ} {P′} (E : P₀ —[ a - _ ]→ P′) {P P′ : ↓⁻′ P₀} → P ≤⁻′ P′ → step⁻ E P ≤′ step⁻ E P′

   stepᴹ E [ P ] = step⁻ᴹ E P
   stepᴹ E ◻ = {!!} , ◻

   step⁻ᴹ (x •∙ _) (.x •∙ P) = (x •) ᵇ , P
   step⁻ᴹ (• x 〈 _ 〉∙ _) (• .x 〈 y 〉∙ P) = • x 〈 y 〉 ᶜ , P
   step⁻ᴹ (E ➕₁ _) (P ➕ Q) = stepᴹ E P
   step⁻ᴹ {a = _ ᵇ} (E ᵇ│ _) (P │ Q) = let a , R = stepᴹ E P in a , [ R │ (ᴹ push *ᴹ) Q ]
   step⁻ᴹ {a = _ ᶜ} (E ᶜ│ _) (P │ Q) = let a , R = stepᴹ E P in a , [ R │ Q ]
   step⁻ᴹ {a = _ ᵇ} (_ │ᵇ F) (P │ Q) = let a , S = stepᴹ F Q in a , [ (ᴹ push *ᴹ) P │ S ]
   step⁻ᴹ {a = _ ᶜ} (_ │ᶜ F) (P │ Q) = let a , S = stepᴹ F Q in a , [ P │ S ]

   step⁻ᴹ (E │• F) {P │ Q} {P′ │ Q′} (P† │ Q†)
      with step E P | step E P′ | stepᴹ E P†
   ... | x • ᵇ , _ | .x • ᵇ , _ | .x • ᵇ , R†
      with step F Q | step F Q′ | stepᴹ F Q†
   ... | • .x 〈 _ 〉 ᶜ , _ | • .x 〈 _ 〉 ᶜ , _ | • .x 〈 y 〉 ᶜ , S† = τ ᶜ , [ (popᴹ y *ᴹ) R† │ S† ]

   step⁻ᴹ (E │ᵥ F) {P │ Q} {P′ │ Q′} (P† │ Q†)
      with step E P | step E P′ | stepᴹ E P†
   ... | ( x •) ᵇ , _ | (.x •) ᵇ , _ | _ , R†
      with step F Q | step F Q′ | stepᴹ F Q†
   ... | (• .x) ᵇ , _ | (• .x) ᵇ , _ | _ , S† = τ ᶜ , [ ν [ R† │ S† ] ]

   step⁻ᴹ (ν•_ {x = x} E) {ν P} {ν P′} (ν P†)
      with step E P | step E P′ | stepᴹ E P†
   ... | • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ , _ | • ._ 〈 ◻ 〉 ᶜ , _ | • ._ 〈 () 〉 ᶜ , R†
   ... | • ._ 〈 _ 〉 ᶜ , _ | • ._ 〈 _ 〉 ᶜ , _ | _ , R† = (• x) ᵇ , R†

   step⁻ᴹ {a = x • ᵇ} (νᵇ E) {ν P} {ν P′} (ν P†)
      with step E P | step E P′ | stepᴹ E P†
   ... | ._ • ᵇ , _ | ._ • ᵇ , _ | _ , R† = x • ᵇ , [ ν (ᴹ swap *ᴹ) R† ]

   step⁻ᴹ {a = (• x) ᵇ} (νᵇ E) {ν P} {ν P′} (ν P†)
      with step E P | step E P′ | stepᴹ E P†
   ... | (• ._) ᵇ , _ | (• ._) ᵇ , _ | _ , R† = (• x) ᵇ , [ ν (ᴹ swap *ᴹ) R† ]

   step⁻ᴹ {a = • x 〈 y 〉 ᶜ} (νᶜ E) {ν P} {ν P′} (ν P†)
      with step E P | step E P′ | stepᴹ E P†
   ... | • ._ 〈 [ ._ ] 〉 ᶜ , _ | • ._ 〈 ◻ 〉 ᶜ , _ | • ._ 〈 () 〉 ᶜ , R†
   ... | • ._ 〈 ◻ 〉 ᶜ , _ | • ._ 〈 ◻ 〉 ᶜ , _ | _ , R† = • x 〈 ◻ 〉 ᶜ , [ ν R† ]
   ... | • ._ 〈 ◻ 〉 ᶜ , _ | • ._ 〈 [ ._ ] 〉 ᶜ , _ | _ , R† = • x 〈 ◻ 〉 ᶜ , [ ν R† ]
   ... | • ._ 〈 [ ._ ] 〉 ᶜ , _ | • ._ 〈 [ ._ ] 〉 ᶜ , _ | _ , R† = • x 〈 [ y ] 〉 ᶜ , [ ν R† ]

   step⁻ᴹ {a = τ ᶜ} (νᶜ E) {ν P} {ν P′} (ν P†)
      with step E P | step E P′ | stepᴹ E P†
   ... | τ ᶜ , _ | τ ᶜ , _ | τ ᶜ , R† = τ ᶜ , [ ν R† ]

   step⁻ᴹ (! E) (! P) = stepᴹ E [ P │ [ ! P ] ]

   action : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓′ P → ↓′ a
   action E = π₁ ∘ᶠ step E

   actionᴹ : ∀ {Γ P₀} {a : Action Γ} {R} (E : P₀ —[ a - _ ]→ R) {P P′ : ↓′ P₀} → P ≤′ P′ → action E P ≤′ action E P′
   actionᴹ E = π₁ ∘ᶠ stepᴹ E

   -- Called 'fwd' in the paper.
   tgt : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) → ↓′ P → ↓′ R
   tgt E = π₂ ∘ᶠ step E

   tgtᴹ : ∀ {Γ P₀} {a : Action Γ} {R} (E : P₀ —[ a - _ ]→ R) {P P′ : ↓′ P₀} → P ≤′ P′ → tgt E P ≤′ tgt E P′
   tgtᴹ E = π₂ ∘ᶠ stepᴹ E

   -- unstep reflects ◻. The unstep-◻ variant slices with a ◻ process.
   unstep : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) → ↓′ a → ↓′ P′ → ↓′ P
   unstep-◻ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) → ↓′ a → ↓⁻′ P
   unstep⁻ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) → ↓′ a → ↓⁻′ P′ → ↓⁻′ P

   unstep E a [ P ] = [ unstep⁻ E a P ]
   unstep E a ◻ = [ unstep-◻ E a ]

   unstep-◻ (x •∙ P) (.x • ᵇ) = x •∙ ◻
   unstep-◻ (• x 〈 _ 〉∙ _) (• .x 〈 y 〉 ᶜ) = • x 〈 y 〉∙ ◻
   unstep-◻ (E ➕₁ Q) a = [ unstep-◻ E a ] ➕ ◻
   unstep-◻ (E ᵇ│ Q) a = [ unstep-◻ E a ] │ ◻
   unstep-◻ (E ᶜ│ Q) a = [ unstep-◻ E a ] │ ◻
   unstep-◻ (P │ᵇ E) a = ◻ │ [ unstep-◻ E a ]
   unstep-◻ (P │ᶜ E) a = ◻ │ [ unstep-◻ E a ]
   unstep-◻ (E │• F) (τ ᶜ) = [ unstep-◻ E (_ • ᵇ) ] │ [ unstep-◻ F (• _ 〈 ◻ 〉 ᶜ) ]
   unstep-◻ (E │ᵥ F) (τ ᶜ) = [ unstep-◻ E (_ • ᵇ) ] │ [ unstep-◻ F ((• _) ᵇ) ]
   unstep-◻ (ν• E) ((• _) ᵇ) = ν [ unstep-◻ E (• ᴺ.suc _ 〈 zero 〉 ᶜ) ]
   unstep-◻ {a = x • ᵇ} (νᵇ E) _ = ν [ unstep-◻ E ((ᴿ.push *) x • ᵇ) ]
   unstep-◻ {a = (• x) ᵇ} (νᵇ E) _ = ν [ unstep-◻ E ((• (ᴿ.push *) x) ᵇ) ]
   unstep-◻ {a = • x 〈 y 〉 ᶜ} (νᶜ E) _ = ν [ unstep-◻ E (• (ᴿ.push *) x 〈 [ (ᴿ.push *) y ] 〉 ᶜ) ]
   unstep-◻ {a = τ ᶜ} (νᶜ E) _ = ν [ unstep-◻ E (τ ᶜ) ]
   unstep-◻ (! E) a with unstep-◻ E a
   ... | P │ ◻ = ! P
   ... | P │ [ P′ ] = ! P ⊔⁻′ P′

   unstep⁻ (x •∙ _) (.x • ᵇ) R = x •∙ [ R ]
   unstep⁻ (• x 〈 _ 〉∙ ._) (• .x 〈 y 〉 ᶜ) R = • x 〈 y 〉∙ [ R ]
   unstep⁻ (E ➕₁ _) a R = [ unstep⁻ E a R ] ➕ ◻
   unstep⁻ {a = _ ᵇ} (E ᵇ│ Q) a (R │ S) = unstep E a R │ π₂ ((ᴿ.push †) Q S)
   unstep⁻ {a = _ ᶜ} (E ᶜ│ Q) a (R │ S) = unstep E a R │ S
   unstep⁻ {a = _ ᵇ} (P │ᵇ E) a (R │ S) = π₂ ((ᴿ.push †) P R) │ unstep E a S
   unstep⁻ {a = _ ᶜ} (P │ᶜ E) a (R │ S) = R │ unstep E a S
   unstep⁻ (_│•_ {R = P′} {x = x} {y} E F) _ (R │ S) with (ᴿ.pop y †) P′ R
   ... | pop-y , R′ = unstep E (x • ᵇ) R′ │ unstep F (• x 〈 pop-y ᴺ.zero 〉 ᶜ) S
   unstep⁻ (E │ᵥ F) _ (ν ◻) = [ unstep-◻ E (_ • ᵇ) ] │ [ unstep-◻ F ((• _) ᵇ) ]
   unstep⁻ (E │ᵥ F) _ (ν [ R │ S ]) = unstep E (_ • ᵇ) R │ unstep F ((• _) ᵇ) S
   unstep⁻ (ν• E) _ R = ν [ unstep⁻ E (• ᴺ.suc _ 〈 zero 〉 ᶜ) R ]
   unstep⁻ {a = x • ᵇ} (νᵇ_ {R = P′} E) _ (ν R) = ν unstep E ((ᴿ.push *) x • ᵇ) (π₂ ((ᴿ.swap †) P′ R))
   unstep⁻ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) _ (ν R) = ν unstep E ((• (ᴿ.push *) x) ᵇ) (π₂ ((ᴿ.swap †) P′ R))
   unstep⁻ {a = • x 〈 y 〉 ᶜ} (νᶜ_ {R = P′} E) _ (ν R) = ν unstep E ((• (ᴿ.push *) x 〈 [ (ᴿ.push *) y ] 〉) ᶜ) R
   unstep⁻ {a = τ ᶜ} (νᶜ_ {R = P′} E) _ (ν R) = ν unstep E (τ ᶜ) R
   unstep⁻ (! E) a R with unstep⁻ E a R
   ... | P │ ◻ = ! P
   ... | P │ [ P′ ] = ! P ⊔⁻′ P′

   unstep-◻ᴹ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) {a′ a″ : ↓⁻′ a} →
               a′ ≤⁻′ a″ → unstep-◻ E a′ ≤⁻′ unstep-◻ E a″
   unstep-◻ᴹ (x •∙ _) (.x • ᵇ) = x •∙ ◻
   unstep-◻ᴹ (• x 〈 _ 〉∙ _) (• .x 〈 y 〉 ᶜ) = • x 〈 y 〉∙ ◻
   unstep-◻ᴹ (E ➕₁ _) a = [ unstep-◻ᴹ E a ] ➕ ◻
   unstep-◻ᴹ (E ᵇ│ _) a = [ unstep-◻ᴹ E a ] │ ◻
   unstep-◻ᴹ (E ᶜ│ _) a = [ unstep-◻ᴹ E a ] │ ◻
   unstep-◻ᴹ (_ │ᵇ E) a = ◻ │ [ unstep-◻ᴹ E a ]
   unstep-◻ᴹ (_ │ᶜ E) a = ◻ │ [ unstep-◻ᴹ E a ]
   unstep-◻ᴹ (E │• F) (τ ᶜ) = [ unstep-◻ᴹ E (_ • ᵇ) ] │ [ unstep-◻ᴹ F (• _ 〈 ◻ 〉 ᶜ) ]
   unstep-◻ᴹ (ν• E) ((• _) ᵇ) = ν [ unstep-◻ᴹ E (• ᴺ.suc _ 〈 ᴹ zero 〉 ᶜ) ]
   unstep-◻ᴹ (E │ᵥ F) (τ ᶜ) = [ unstep-◻ᴹ E (_ • ᵇ) ] │ [ unstep-◻ᴹ F ((• _) ᵇ) ]
   unstep-◻ᴹ {a = x • ᵇ} (νᵇ E) (._ • ᵇ) = ν [ unstep-◻ᴹ E ((ᴿ.push *) x • ᵇ) ]
   unstep-◻ᴹ {a = (• x) ᵇ} (νᵇ E) ((• ._) ᵇ) = ν [ unstep-◻ᴹ E ((• (ᴿ.push *) x) ᵇ) ]
   unstep-◻ᴹ {a = • x 〈 y 〉 ᶜ} (νᶜ E) (• ._ 〈 _ 〉 ᶜ) = ν [ unstep-◻ᴹ E (• (ᴿ.push *) x 〈 [ (ᴿ.push *) y ] 〉 ᶜ) ]
   unstep-◻ᴹ {a = τ ᶜ} (νᶜ E) (τ ᶜ) = ν [ unstep-◻ᴹ E (τ ᶜ) ]
   unstep-◻ᴹ (! E) {a′ = a′} {a″} a with unstep-◻ E a′ | unstep-◻ E a″ | unstep-◻ᴹ E a
   ... | _ │ ◻ | _ │ ◻ | P │ ◻ = ! P
   ... | _ │ ◻ | P │ [ ! P′ ] | P† │ _ = ! ≤-trans P† (P ⊔ʳ P′)
   ... | _ │ [ ! _ ] | _ │ ◻ | _ │ ()
   ... | _ │ [ ! _ ] | _ │ [ ! _ ] | P │ [ ! P′ ] = ! (P ⊔ᴹ P′)

   -- Auxiliary lemmas needed for monotonicity.
   unstep-◻-min : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) (a′ : ↓⁻′ a) (R : ↓′ P′) →
                  [ unstep-◻ E a′ ] ≤′ unstep E a′ R
   unstep-◻-min⁻ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) (a′ : ↓⁻′ a) (R : ↓⁻′ P′) →
                   unstep-◻ E a′ ≤⁻′ unstep⁻ E a′ R

   unstep-◻-min E a ◻ = [ ⁻ᴹ (unstep-◻ E a) ]
   unstep-◻-min E a [ R ] = [ unstep-◻-min⁻ E a R ]

   unstep-◻-min⁻ (x •∙ _) (.x • ᵇ) _ = x •∙ ◻
   unstep-◻-min⁻ (• x 〈 _ 〉∙ _) (• .x 〈 y 〉 ᶜ) _ = • x 〈 ᴹ y 〉∙ ◻
   unstep-◻-min⁻ (E ➕₁ _) a P = [ unstep-◻-min⁻ E a P ] ➕ ◻
   unstep-◻-min⁻ (E ᵇ│ _) a (P │ Q) = unstep-◻-min E a P │ ◻
   unstep-◻-min⁻ (E ᶜ│ _) a (P │ Q) = unstep-◻-min E a P │ ◻
   unstep-◻-min⁻ (_ │ᵇ E) a (P │ Q) = ◻ │ unstep-◻-min E a Q
   unstep-◻-min⁻ (_ │ᶜ E) a (P │ Q) = ◻ │ unstep-◻-min E a Q
   unstep-◻-min⁻ (_│•_ {R = P′} {y = y} E F) (τ ᶜ) (P │ Q) with (ᴿ.pop y †) P′ P
   ... | pop-y , R =
      unstep-◻-min E (_ • ᵇ) R │
      ≤-trans [ unstep-◻ᴹ F (• _ 〈 ◻ 〉 ᶜ) ] (unstep-◻-min F (• _ 〈 pop-y ᴺ.zero 〉 ᶜ) Q)
   unstep-◻-min⁻ (ν• E) ((• _) ᵇ) P = ν [ unstep-◻-min⁻ E (• ᴺ.suc _ 〈 zero 〉 ᶜ) P ]
   unstep-◻-min⁻ (E │ᵥ F) (τ ᶜ) (ν ◻) = [ ⁻ᴹ (unstep-◻ E (_ • ᵇ)) ] │ [ ⁻ᴹ (unstep-◻ F ((• _) ᵇ)) ]
   unstep-◻-min⁻ (E │ᵥ F) (τ ᶜ) (ν [ P │ Q ]) = unstep-◻-min E (_ • ᵇ) P │ unstep-◻-min F ((• _) ᵇ) Q
   unstep-◻-min⁻ {a = x • ᵇ} (νᵇ_ {R = P′} E) _ (ν P) = ν unstep-◻-min E ((ᴿ.push *) x • ᵇ) (π₂ ((ᴿ.swap †) P′ P))
   unstep-◻-min⁻ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) _ (ν P) = ν unstep-◻-min E ((• (ᴿ.push *) x) ᵇ) (π₂ ((ᴿ.swap †) P′ P))
   unstep-◻-min⁻ {a = • x 〈 y 〉 ᶜ} (νᶜ_ {R = P′} E) _ (ν P) = ν unstep-◻-min E (• (ᴿ.push *) x 〈 [ (ᴿ.push *) y ] 〉 ᶜ) P
   unstep-◻-min⁻ {a = τ ᶜ} (νᶜ_ {R = P′} E) _ (ν P) = ν unstep-◻-min E (τ ᶜ) P
   unstep-◻-min⁻ (! E) a R with unstep-◻ E a | unstep⁻ E a R | unstep-◻-min⁻ E a R
   ... | _ │ ◻ | _ │ ◻ | P │ ◻ = ! P
   ... | _ │ ◻ | P │ [ ! P′ ] | P† │ _ = ! ≤-trans P† (P ⊔ʳ P′)
   ... | _ │ [ ! _ ] | _ │ ◻ | _ │ ()
   ... | _ │ [ ! _ ] | _ │ [ ! _ ] | P │ [ ! P′ ] = ! (P ⊔ᴹ P′)

   unstepᴹ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) {a′ a″ : ↓′ a} {R R′ : ↓′ P′} →
                a′ ≤′ a″ → R ≤′ R′ → unstep E a′ R ≤′ unstep E a″ R′
   unstep⁻ᴹ : ∀ {Γ P} {a : Action Γ} {P′} (E : P —[ a - _ ]→ P′) {a′ a″ : ↓′ a} {R R′ : ↓⁻′ P′} →
              a′ ≤′ a″ → R ≤⁻′ R′ → unstep⁻ E a′ R ≤⁻′ unstep⁻ E a″ R′

   unstepᴹ E a [ R ] = [ unstep⁻ᴹ E a R ]
   unstepᴹ E {R = ◻} {◻} a ◻ = [ unstep-◻ᴹ E a ]
   unstepᴹ E {R = ◻} {[ R ]} a ◻ = [ ≤⁻-trans (unstep-◻ᴹ E a) (unstep-◻-min⁻ E _ R) ]

   unstep⁻ᴹ (x •∙ _) (.x • ᵇ) R = x •∙ [ R ]
   unstep⁻ᴹ (• x 〈 _ 〉∙ _) (• .x 〈 y 〉 ᶜ) R = • x 〈 y 〉∙ [ R ]
   unstep⁻ᴹ (E ➕₁ Q) a R = [ unstep⁻ᴹ E a R ] ➕ ◻
   unstep⁻ᴹ (E ᵇ│ Q) a′ (R │ S) = unstepᴹ E a′ R │ π₂ ((ᴿ.push †ᴹ) Q S)
   unstep⁻ᴹ (E ᶜ│ Q) a′ (R │ S) = unstepᴹ E a′ R │ S
   unstep⁻ᴹ (P │ᵇ E) a′ (R │ S) = π₂ ((ᴿ.push †ᴹ) P R) │ unstepᴹ E a′ S
   unstep⁻ᴹ (P │ᶜ E) a′ (R │ S) = R │ unstepᴹ E a′ S
   unstep⁻ᴹ (_│•_ {R = P″} {y = y} E F) {R = P │ _} {P′ │ _} a (R │ S) with (ᴿ.pop y †ᴹ) P″ R
   ... | pop-y , R′ = unstepᴹ E (_ • ᵇ) R′ │ unstepᴹ F (• _ 〈 pop-y ᴺ.zero 〉 ᶜ) S
   unstep⁻ᴹ (ν• E) _ R = ν [ unstep⁻ᴹ E (• ᴺ.suc _ 〈 ᴹ zero 〉 ᶜ) R ]
   unstep⁻ᴹ (E │ᵥ F) {R = ν ◻} {ν ◻} _ (ν ◻) = [ ⁻ᴹ (unstep-◻ E (_ • ᵇ)) ] │ [ ⁻ᴹ (unstep-◻ F ((• _) ᵇ)) ]
   unstep⁻ᴹ (E │ᵥ F) {R = ν ◻} {ν [ P │ Q ]} _ (ν ◻) = unstep-◻-min E (_ • ᵇ) P │ unstep-◻-min F ((• _) ᵇ) Q
   unstep⁻ᴹ (E │ᵥ F) {R = ν [ _ │ _ ]} {ν [ _ │ _ ]} _ (ν [ R │ S ]) =
      unstepᴹ E (_ • ᵇ) R │ unstepᴹ F ((• _) ᵇ) S
   unstep⁻ᴹ {a = x • ᵇ} (νᵇ_ {R = P′} E) _ (ν R) = ν unstepᴹ E ((ᴿ.push *) x • ᵇ) (π₂ ((ᴿ.swap †ᴹ) P′ R))
   unstep⁻ᴹ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) _ (ν R) = ν unstepᴹ E ((• (ᴿ.push *) x) ᵇ) (π₂ ((ᴿ.swap †ᴹ) P′ R))
   unstep⁻ᴹ {a = • x 〈 y 〉 ᶜ} (νᶜ_ {R = P′} E) _ (ν R) = ν unstepᴹ E (• (ᴿ.push *) x 〈 [ (ᴿ.push *) y ] 〉 ᶜ) R
   unstep⁻ᴹ {a = τ ᶜ} (νᶜ_ {R = P′} E) _ (ν R) = ν unstepᴹ E (τ ᶜ) R
   unstep⁻ᴹ (! E) {a′} {a″} {R′} {R″} a R with unstep⁻ E a′ R′ | unstep⁻ E a″ R″ | unstep⁻ᴹ E a R
   ... | _ │ ◻ | _ │ ◻ | P │ ◻ = ! P
   ... | _ │ ◻ | P │ [ ! P′ ] | P† │ _ = ! ≤-trans P† (P ⊔ʳ P′)
   ... | _ │ [ ! _ ] | _ │ ◻ | _ │ ()
   ... | _ │ [ ! _ ] | _ │ [ ! _ ] | P │ [ ! P′ ] = ! (P ⊔ᴹ P′)
