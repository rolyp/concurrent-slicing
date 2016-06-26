module Transition.Lattice.GaloisConnection where

   open import ConcurrentSlicingCommon hiding (poset)
   open import Ext.Algebra
   open import Ext.Algebra.Structures

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Lattice as ᴬ̃ using (↓ᵇ_; ↓ᶜ_);
      open ᴬ̃.↓_; open ᴬ̃.↓⁻_; open ᴬ̃.↓ᵇ_; open ᴬ̃.↓ᶜ_; open ᴬ̃._≤_; open ᴬ̃._≤⁻_; open ᴬ̃._≤ᵇ_; open ᴬ̃._≤ᶜ_
   import Lattice; open Lattice.Prefixes ⦃...⦄
   import Lattice.Product
   open import Proc using (Proc)
   import Proc.Lattice as ᴾ̃; open ᴾ̃.↓⁻_; open ᴾ̃.↓_; open ᴾ̃._≤_; open ᴾ̃._≤⁻_
   open import Proc.Ren.Lattice using (unren; unrenᴹ; _*ᴹ) renaming (_* to _*̃)
   open import Proc.Ren.Lattice.GaloisConnection using (id≤ren∘unren; unren∘ren≤id)
   import Name as ᴺ
   open import Name.Lattice as ᴺ̃ using (zero; suc; sucᴹ); open ᴺ̃.↓_; open ᴺ̃._≤_
   open import Ren as ᴿ using (push; pop; swap; ᴺren); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice as ᴿ̃ using (pop-top; popᴹ; top)
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_
   open import Transition.Lattice as ᵀ̃ using (step; stepᴹ; step⁻; step⁻ᴹ; unstep; unstepᴹ; unstep-◻; unstep⁻; unstep⁻ᴹ)

   id≤step∘unstep : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) (aR : ↓ (a , R)) → aR ≤ (step E ∘ᶠ unstep E) aR
   id≤step⁻∘unstep-◻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) (a′ : ↓⁻ a) → [ a′ ] ≤ π₁ (step⁻ E (unstep-◻ E a′))
   id≤step⁻∘unstep⁻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) (a′ : ↓ a) (R′ : ↓⁻ R) →
                     (a′ , [ R′ ]) ≤ step⁻ E (unstep⁻ E a′ R′)

   id≤step∘unstep E (a , [ R ]) = id≤step⁻∘unstep⁻ E a R
   id≤step∘unstep E ([ a ] , ◻) = id≤step⁻∘unstep-◻ E a , ◻
   id≤step∘unstep _ (◻ , ◻) = ◻ , ◻

   id≤step⁻∘unstep-◻ (x •∙ _) (.x • ᵇ) = [ x • ᵇ ]
   id≤step⁻∘unstep-◻ (• x 〈 _ 〉∙ _) (• .x 〈 y 〉 ᶜ) = [ • x 〈 ᴹ y 〉 ᶜ ]
   id≤step⁻∘unstep-◻ (E ➕₁ Q) a = id≤step⁻∘unstep-◻ E a
   id≤step⁻∘unstep-◻ (E ᵇ│ Q) (a ᵇ) = id≤step⁻∘unstep-◻ E (a ᵇ)
   id≤step⁻∘unstep-◻ (E ᶜ│ Q) (a ᶜ) = id≤step⁻∘unstep-◻ E (a ᶜ)
   id≤step⁻∘unstep-◻ (P │ᵇ E) (a ᵇ) = id≤step⁻∘unstep-◻ E (a ᵇ)
   id≤step⁻∘unstep-◻ (P │ᶜ E) (a ᶜ) = id≤step⁻∘unstep-◻ E (a ᶜ)
   id≤step⁻∘unstep-◻ (_│•_ {x = x} E F) (τ ᶜ)
      with step⁻ E (unstep-◻ E ( x • ᵇ)) | step⁻ F (unstep-◻ F (• x 〈 ◻ 〉 ᶜ)) |
           id≤step⁻∘unstep-◻ E (x • ᵇ) | id≤step⁻∘unstep-◻ F (• x 〈 ◻ 〉 ᶜ)
   ... | [ ._ • ᵇ ] , _ | [ • ._ 〈 _ 〉 ᶜ ] , _ | [ ._ • ᵇ ] | [ • ._ 〈 _ 〉 ᶜ ] = [ τ ᶜ ]
   id≤step⁻∘unstep-◻ (_│ᵥ_ {x = x} E F) (τ ᶜ)
      with step⁻ E (unstep-◻ E (x • ᵇ)) | step⁻ F (unstep-◻ F ((• x) ᵇ)) |
           id≤step⁻∘unstep-◻ E (x • ᵇ) | id≤step⁻∘unstep-◻ F ((• x) ᵇ)
   ... | [ (._ •) ᵇ ] , _ | [ (• ._) ᵇ ] , _ | [ ._ • ᵇ ] | [ (• ._) ᵇ ] = [ τ ᶜ ]
   id≤step⁻∘unstep-◻ (ν•_ {x = x} E) ((• ._) ᵇ)
      with step⁻ E (unstep-◻ E (• ᴺ.suc x 〈 zero 〉 ᶜ)) | id≤step⁻∘unstep-◻ E (• ᴺ.suc x 〈 zero 〉 ᶜ)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , _ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] = [ (• x) ᵇ ]
   id≤step⁻∘unstep-◻ {a = x • ᵇ} (νᵇ E) (._ • ᵇ)
      with step⁻ E (unstep-◻ E (ᴺ.suc x • ᵇ)) | id≤step⁻∘unstep-◻ E (ᴺ.suc x • ᵇ)
   ... | [ ._ • ᵇ ] , _ | [ ._ • ᵇ ] = [ x • ᵇ ]
   id≤step⁻∘unstep-◻ {a = (• x) ᵇ} (νᵇ E) ((• ._) ᵇ)
      with step⁻ E (unstep-◻ E ((• ᴺ.suc x) ᵇ)) | id≤step⁻∘unstep-◻ E ((• ᴺ.suc x) ᵇ)
   ... | [ (• ._) ᵇ ] , _ | [ (• ._) ᵇ ] = [ (• x) ᵇ ]
   id≤step⁻∘unstep-◻ {a = • x 〈 y 〉 ᶜ} (νᶜ E) (• ._ 〈 ◻ 〉 ᶜ)
      with step⁻ E (unstep-◻ E (• ᴺ.suc x 〈 ◻ 〉 ᶜ)) | id≤step⁻∘unstep-◻ E (• ᴺ.suc x 〈 ◻ 〉 ᶜ)
   ... | ◻ , _ | ()
   ... | [ • .(ᴺ.suc x) 〈 ◻ 〉 ᶜ ] , _ | _ = [ • x 〈 ◻ 〉 ᶜ ]
   ... | [ • .(ᴺ.suc x) 〈 [ .(ᴺ.suc y) ] 〉 ᶜ ] , _ | _ = [ • x 〈 ◻ 〉 ᶜ ]
   id≤step⁻∘unstep-◻ {a = • x 〈 y 〉 ᶜ} (νᶜ E) (• ._ 〈 [ ._ ] 〉 ᶜ)
      with step⁻ E (unstep-◻ E (• ᴺ.suc x 〈 [ ᴺ.suc y ] 〉 ᶜ)) | id≤step⁻∘unstep-◻ E (• ᴺ.suc x 〈 [ ᴺ.suc y ] 〉 ᶜ)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , _ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] = [ • x 〈 [ y ] 〉 ᶜ ]
   id≤step⁻∘unstep-◻ {a = τ ᶜ} (νᶜ E) (τ ᶜ)
      with step⁻ E (unstep-◻ E (τ ᶜ)) | id≤step⁻∘unstep-◻ E (τ ᶜ)
   ... | [ τ ᶜ ] , _ | [ _ ] = [ τ ᶜ ]
   id≤step⁻∘unstep-◻ (! E) a with unstep-◻ E a | id≤step⁻∘unstep-◻ E a
   ... | R │ ◻ | a′ = ≤-trans a′ (π₁ (step⁻ᴹ E (ᴹ R │ ◻)))
   ... | R │ [ ! R′ ] | a′ = ≤-trans a′ (π₁ (step⁻ᴹ E (R ⊔ʳ R′ │ [ ! (R ⊔ˡ R′) ])))

   id≤step⁻∘unstep⁻ (_ •∙ ._) ◻ R = ◻ , ᴹ [ R ]
   id≤step⁻∘unstep⁻ (x •∙ _) [ .x • ᵇ ] R = [ x • ᵇ ] , ᴹ [ R ]
   id≤step⁻∘unstep⁻ (• _ 〈 _ 〉∙ ._) ◻ R = ◻ , ᴹ [ R ]
   id≤step⁻∘unstep⁻ (• x 〈 _ 〉∙ ._) [ • .x 〈 y 〉 ᶜ ] R = [ • x 〈 ᴹ y 〉 ᶜ ] , ᴹ [ R ]
   id≤step⁻∘unstep⁻ (E ➕₁ Q) a R = id≤step⁻∘unstep⁻ E a R
   id≤step⁻∘unstep⁻ {a = _ ᵇ} (E ᵇ│ Q) a (R │ S) =
      let a′ , P′ = id≤step∘unstep E (a , R); ρ , Q′ = unren push  Q S in
      a′ , [ P′ │ ≤-trans (id≤ren∘unren push Q S) ((top push *ᴹ) (ᴹ Q′)) ]
   id≤step⁻∘unstep⁻ {a = _ ᶜ} (E ᶜ│ Q) a (R │ S) =
      let a′ , P′ = id≤step∘unstep E (a , R) in a′ , [ P′ │ ᴹ S ]
   id≤step⁻∘unstep⁻ {a = _ ᵇ} (P │ᵇ E) a (R │ S) =
      let a′ , Q′ = id≤step∘unstep E (a , S); ρ , P′ = unren push P R in
      a′ , [ ≤-trans (id≤ren∘unren push P R) ((top push *ᴹ) (ᴹ P′)) │ Q′ ]
   id≤step⁻∘unstep⁻ {a = _ ᶜ} (P │ᶜ E) a (R │ S) =
      let a′ , Q′ = id≤step∘unstep E (a , S) in a′ , [ ᴹ R │ Q′ ]
   id≤step⁻∘unstep⁻ (_│•_ {x = x} {y} E F) ◻ (R │ S)
      with π₁ (unren (pop y) (ᵀ.tgt E) R) | id≤ren∘unren (pop y) (ᵀ.tgt E) R |
           π₁ (unren (pop y) (ᵀ.tgt E) R) ᴺ.zero | inspect (π₁ (unren (pop y) (ᵀ.tgt E) R)) ᴺ.zero
   ... | pop-◻ | pop-◻≤ | ◻ | [ ≡y† ]
      with step E (unstep E (◻ , π₂ (unren (pop y) (ᵀ.tgt E) R))) | step F (unstep F (◻ , S)) |
           id≤step∘unstep E (◻ , π₂ (unren (pop y) (ᵀ.tgt E) R)) | id≤step∘unstep F (◻ , S)
   ... | ◻ , R† | ◻ , S′ | _ , P | _ , Q =
      ◻ , [ ≤-trans pop-◻≤ (((≤-trans (subst (λ y† → pop-◻ ≤ ᴿ̃.pop y†) ≡y† pop-top) (popᴹ ◻)) *ᴹ) P) │ Q ]
   ... | ◻ , R† | [ • .x 〈 y′ 〉 ᶜ ] , S′ | _ , P | _ , Q =
      ◻ , [ ≤-trans pop-◻≤ (((≤-trans (subst (λ y† → pop-◻ ≤ ᴿ̃.pop y†) ≡y† pop-top) (popᴹ ◻)) *ᴹ) P) │ Q ]
   ... | [ (.x •) ᵇ ] , R† | ◻ , S′ | _ , P | _ , Q =
      ◻ , [ ≤-trans pop-◻≤ (((≤-trans (subst (λ y† → pop-◻ ≤ ᴿ̃.pop y†) ≡y† pop-top) (popᴹ ◻)) *ᴹ) P) │ Q ]
   ... | [ (.x •) ᵇ ] , R† | [ • .x 〈 y′ 〉 ᶜ ] , S′ | _ , P | _ , Q =
      ◻ , [ ≤-trans pop-◻≤ (((≤-trans (subst (λ y† → pop-◻ ≤ ᴿ̃.pop y†) ≡y† pop-top) (popᴹ ◻)) *ᴹ) P) │ Q ]
   id≤step⁻∘unstep⁻ (_│•_ {x = x} {y} E F) ◻ (R │ S) | pop-y† | pop-y†≤ | [ .y ] | [ ≡y† ]
      with step E (unstep E (◻ , π₂ (unren (pop y) (ᵀ.tgt E) R))) | step F (unstep F ([ • x 〈 [ y ] 〉 ᶜ ] , S)) |
           id≤step∘unstep E (◻ , π₂ (unren (pop y) (ᵀ.tgt E) R)) | id≤step∘unstep F ([ • x 〈 [ y ] 〉 ᶜ ] , S)
   ... | _ , R† | ◻ , S′ | _ , P | () , Q
   ... | ◻ , R† | [ • .x 〈 [ .y ] 〉 ᶜ ] , S′ | ◻ , P | [ • .x 〈 [ .y ] 〉 ᶜ ] , Q =
      ◻ , [ ≤-trans pop-y†≤ (((≤-trans pop-top (≤-reflexive (cong-app (cong ᴿ̃.pop ≡y†)))) *ᴹ) P) │ Q ]
   ... | [ (.x •) ᵇ ] , R† | [ • .x 〈 [ .y ] 〉 ᶜ ] , S′ | _ , P | [ • .x 〈 [ .y ] 〉 ᶜ ] , Q =
      ◻ , [ ≤-trans pop-y†≤ (((≤-trans pop-top (≤-reflexive (cong-app (cong ᴿ̃.pop ≡y†)))) *ᴹ) P) │ Q ]
   id≤step⁻∘unstep⁻ (_│•_ {x = x} {y} E F) [ τ ᶜ ] (R │ S)
      with unren (pop y) (ᵀ.tgt E) R | id≤ren∘unren (pop y) (ᵀ.tgt E) R
   ... | pop-y , R′ | R″
      with step E (unstep E ([ x • ᵇ ] , R′)) | step F (unstep F ([ • x 〈 pop-y ᴺ.zero 〉 ᶜ ] , S)) |
           id≤step∘unstep E ([ x • ᵇ ] , R′) | id≤step∘unstep F ([ • x 〈 pop-y ᴺ.zero 〉 ᶜ ] , S)
   ... | [ .x • ᵇ ] , _ | [ • .x 〈 y′ 〉 ᶜ ] , _ | [ .x • ᵇ ] , P | [ • .x 〈 y″ 〉 ᶜ ] , Q =
      [ τ ᶜ ] , [ ≤-trans R″ ((≤-trans pop-top (popᴹ y″) *ᴹ) (≤-trans (ᴹ R′) P)) │ Q ]
   id≤step⁻∘unstep⁻ (_│ᵥ_ {x = x} E F) ◻ (ν ◻)
      with step E (unstep E (◻ , ◻)) | step F (unstep F (◻ , ◻)) |
           id≤step∘unstep E (◻ , ◻) | id≤step∘unstep F (◻ , ◻)
   ... | ◻ , _ | _ , _ | _ , P | _ , Q = ◻ , [ ν ◻ ]
   ... | [ .x • ᵇ ] , _ | ◻ , _ | _ , P | _ , Q = ◻ , [ ν ◻ ]
   ... | [ .x • ᵇ ] , _ | [ (• .x) ᵇ ] , _ | _ , P | _ , Q = ◻ , [ ν ◻ ]
   id≤step⁻∘unstep⁻ (_│ᵥ_ {x = x} E F) [ τ ᶜ ] (ν ◻)
      with step⁻ E (unstep-◻ E (x • ᵇ)) | step⁻ F (unstep-◻ F ((• x) ᵇ)) |
           id≤step⁻∘unstep-◻ E (x • ᵇ) | id≤step⁻∘unstep-◻ F ((• x) ᵇ)
   ... | [ .x • ᵇ ] , _ | [ (• .x) ᵇ ] , _ | [ ._ • ᵇ ] | [ (• .x) ᵇ ] = [ τ ᶜ ] , [ ν ◻ ]
   id≤step⁻∘unstep⁻ (E │ᵥ F) ◻ (ν [ R │ S ])
      with step E (unstep E (◻ , R)) | step F (unstep F (◻ , S)) |
           id≤step∘unstep E (◻ , R) | id≤step∘unstep F (◻ , S)
   ... | ◻ , R† | _ , S′ | _ , P | _ , Q = ◻ , [ ν [ P │ Q ] ]
   ... | [ x • ᵇ ] , R† | ◻ , S′ | _ , P | _ , Q = ◻ , [ ν [ P │ Q ] ]
   ... | [ x • ᵇ ] , R† | [ (• .x) ᵇ ] , S′ | _ , P | _ , Q = ◻ , [ ν [ P │ Q ] ]
   id≤step⁻∘unstep⁻ (_│ᵥ_ {x = x} E F) [ τ ᶜ ] (ν [ R │ S ])
      with step E (unstep E ([ x • ᵇ ] , R)) | step F (unstep F ([ (• x) ᵇ ] , S)) |
           id≤step∘unstep E ([ x • ᵇ ] , R) | id≤step∘unstep F ([ (• x) ᵇ ] , S)
   ... | [ .x • ᵇ ] , _ | [ (• .x) ᵇ ] , _ | [ ._ • ᵇ ] , P | [ (• ._) ᵇ ] , Q =
      [ τ ᶜ ] , [ ν [ P │ Q ] ]
   id≤step⁻∘unstep⁻ (ν•_ {x = x} E) ◻ R
      with step⁻ E (unstep⁻ E ◻ R) | id≤step⁻∘unstep⁻ E ◻ R
   ... | ◻ , _ | _ , P = ◻ , P
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , _ | _ , P = ◻ , P
   ... | [ • ._ 〈 [ .ᴺ.zero ] 〉 ᶜ ] , _ | _ , P = ◻ , P
   id≤step⁻∘unstep⁻ (ν• E) [ (• x) ᵇ ] R
      with step⁻ E (unstep⁻ E [ • ᴺ.suc x 〈 zero 〉 ᶜ ] R) | id≤step⁻∘unstep⁻ E [ • ᴺ.suc x 〈 zero 〉 ᶜ ] R
   ... | [ • ._ 〈 ._ 〉 ᶜ ] , _ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , P = [ (• x) ᵇ ] , P
   id≤step⁻∘unstep⁻ {a = x • ᵇ} (νᵇ_ {R = P′} E) ◻ (ν R)
      with unren swap P′ R | id≤ren∘unren swap P′ R; ... | ρ , R′ | R″
      with step E (unstep E (◻ , R′)) | id≤step∘unstep E (◻ , R′)
   ... | ◻ , _ | _ , P = ◻ , [ ν ≤-trans R″ ((top swap *ᴹ) P) ]
   ... | [ ._ • ᵇ ] , _ | _ , P = ◻ , [ ν ≤-trans R″ ((top swap *ᴹ) P) ]
   id≤step⁻∘unstep⁻ {a = x • ᵇ} (νᵇ_ {R = P′} E) [ .x • ᵇ ] (ν R)
      with unren swap P′ R | id≤ren∘unren swap P′ R; ... | ρ , R′ | R″
      with step E (unstep E ([ ᴺ.suc x • ᵇ ] , R′)) | id≤step∘unstep E ([ ᴺ.suc x • ᵇ ] , R′)
   ... | [ ._ • ᵇ ] , _ | [ ._ • ᵇ ] , P = [ x • ᵇ ] , [ ν ≤-trans R″ ((top swap *ᴹ) P) ]
   id≤step⁻∘unstep⁻ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) ◻ (ν R)
      with unren swap P′ R | id≤ren∘unren swap P′ R; ... | ρ , R′ | R″
      with step E (unstep E (◻ , R′)) | id≤step∘unstep E (◻ , R′)
   ... | ◻ , _ | _ , P = ◻ , [ ν ≤-trans R″ ((top swap *ᴹ) P) ]
   ... | [ (• ._) ᵇ ] , _ | _ , P = ◻ , [ ν ≤-trans R″ ((top swap *ᴹ) P) ]
   id≤step⁻∘unstep⁻ (νᵇ_ {R = P′} E) [ (• x) ᵇ ] (ν R)
      with unren swap P′ R | id≤ren∘unren swap P′ R; ... | ρ , R′ | R″
      with step E (unstep E ([ (• ᴺ.suc x) ᵇ ] , R′)) | id≤step∘unstep E ([ (• ᴺ.suc x) ᵇ ] , R′)
   ... | [ (• ._) ᵇ ] , _ | [ (• ._) ᵇ ] , P = [ (• x) ᵇ ] , [ ν ≤-trans R″ ((top swap *ᴹ) P) ]
   id≤step⁻∘unstep⁻ {a = • x 〈 y 〉 ᶜ} (νᶜ_ {R = P′} E) ◻ (ν R)
      with step E (unstep E (◻ , R)) | id≤step∘unstep E (◻ , R)
   ... | ◻ , _ | _ , P = ◻ , [ ν P ]
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , _ | _ , P = ◻ , [ ν P ]
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , _ | _ , P = ◻ , [ ν P ]
   id≤step⁻∘unstep⁻ {a = • x 〈 y 〉 ᶜ} (νᶜ_ {R = P′} E) [ • .x 〈 ◻ 〉 ᶜ ] (ν R)
      with step E (unstep E ([ • ᴺ.suc x 〈 ◻ 〉 ᶜ ] , R)) | id≤step∘unstep E ([ • ᴺ.suc x 〈 ◻ 〉 ᶜ ] , R)
   ... | ◻ , _ | () , _
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , _ | _ , P = [ • x 〈 ◻ 〉 ᶜ ] , [ ν P ]
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , _ | _ , P = [ • x 〈 ◻ 〉 ᶜ ] , [ ν P ]
   id≤step⁻∘unstep⁻ {a = • x 〈 y 〉 ᶜ} (νᶜ_ {R = P′} E) [ • .x 〈 [ .y ] 〉 ᶜ ] (ν R)
      with step E (unstep E ([ • ᴺ.suc x 〈 [ ᴺ.suc y ] 〉 ᶜ ] , R)) |
           id≤step∘unstep E ([ • ᴺ.suc x 〈 [ ᴺ.suc y ] 〉 ᶜ ] , R)
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , _ | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , P = [ • x 〈 [ y ] 〉 ᶜ ] , [ ν P ]
   id≤step⁻∘unstep⁻ {a = τ ᶜ} (νᶜ_ {R = P′} E) ◻ (ν R)
      with step E (unstep E (◻ , R)) | id≤step∘unstep E (◻ , R)
   ... | ◻ , _ | _ , P = ◻ , [ ν P ]
   ... | [ τ ᶜ ] , _ | _ , P = ◻ , [ ν P ]
   id≤step⁻∘unstep⁻ {a = τ ᶜ} (νᶜ_ {R = P′} E) [ τ ᶜ ] (ν R)
      with step E (unstep E ([ τ ᶜ ] , R)) | id≤step∘unstep E ([ τ ᶜ ] , R)
   ... | [ τ ᶜ ] , _ | [ _ ] , P = [ τ ᶜ ] , [ ν P ]
   id≤step⁻∘unstep⁻ (! E) a R with unstep⁻ E a R | id≤step⁻∘unstep⁻ E a R
   ... | R′ │ ◻ | a′ , P = ≤-trans (a′ , P) (stepᴹ E [ ᴹ R′ │ ◻ ])
   ... | R′ │ [ ! R″ ] | a′ , P = ≤-trans (a′ , P) (stepᴹ E [ R′ ⊔ʳ R″ │ [ ! (R′ ⊔ˡ R″) ] ])

   unstep∘step≤id : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) (P′ : ↓ P) → (unstep E ∘ᶠ step E) P′ ≤ P′
   unstep∘step⁻≤id : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) (P′ : ↓⁻ P) → (unstep E ∘ᶠ step⁻ E) P′ ≤ [ P′ ]

   unstep∘step≤id E [ P ] = unstep∘step⁻≤id E P
   unstep∘step≤id {a = _ ᵇ} _ ◻ = ◻
   unstep∘step≤id {a = _ ᶜ} _ ◻ = ◻

   unstep∘step⁻≤id (x •∙ _) (.x •∙ ◻) = [ x •∙ ◻ ]
   unstep∘step⁻≤id (x •∙ _) (.x •∙ [ R ]) = [ x •∙ ᴹ [ R ] ]
   unstep∘step⁻≤id (• x 〈 _ 〉∙ _) (• .x 〈 y 〉∙ ◻) = [ • x 〈 ᴹ y 〉∙ ◻ ]
   unstep∘step⁻≤id (• x 〈 _ 〉∙ ._) (• .x 〈 y 〉∙ [ R ]) = [ • x 〈 ᴹ y 〉∙ ᴹ [ R ] ]
   unstep∘step⁻≤id (E ➕₁ _) (R ➕ _) with step E R | unstep∘step≤id E R
   ... | _ , [ _ ] | P = [ P ➕ ◻ ]
   ... | [ _ ] , ◻ | P = [ P ➕ ◻ ]
   ... | ◻ , ◻ | _ = ◻
   unstep∘step⁻≤id {a = _ ᵇ} (E ᵇ│ Q) (R │ S) with step E R | unstep∘step≤id E R | π₂ (unren∘ren≤id ᴿ̃.push S)
   ... | _ , [ _ ] | P | Q′ = [ P │ Q′ ]
   ... | [ _ ] , _ | P | Q′ = [ P │ Q′ ]
   ... | ◻ , ◻ | _ | Q′ = [ ◻ │ Q′ ]
   unstep∘step⁻≤id {a = _ ᶜ} (E ᶜ│ Q) (R │ S) with step E R | unstep∘step≤id E R
   ... | _ , [ _ ] | P = [ P │ ᴹ S ]
   ... | [ _ ] , _ | P = [ P │ ᴹ S ]
   ... | ◻ , ◻ | _ = [ ◻ │ ᴹ S ]
   unstep∘step⁻≤id {a = _ ᵇ} (P │ᵇ E) (R │ S) with π₂ (unren∘ren≤id ᴿ̃.push R) | step E S | unstep∘step≤id E S
   ... | P′ | _ , [ _ ] | Q = [ P′ │ Q ]
   ... | P′ |  [ _ ] , _ | Q = [ P′ │ Q ]
   ... | P′ | ◻ , ◻ | _ = [ P′ │ ◻ ]
   unstep∘step⁻≤id {a = _ ᶜ} (P │ᶜ E) (R │ S) with step E S | unstep∘step≤id E S
   ... | _ , [ _ ] | Q = [ ᴹ R │ Q ]
   ... | [ _ ] , _ | Q = [ ᴹ R │ Q ]
   ... | ◻ , ◻ | _ = [ ᴹ R │ ◻ ]
   unstep∘step⁻≤id (_│•_ {y = y} E F) (R │ S)
      with step E R | step F S | unstep∘step≤id E R | unstep∘step≤id F S
   ... | ◻ , R′ | ◻ , S′ | P | Q = {!!}
   ... | ◻ , R′ | [ • x 〈 y′ 〉 ᶜ ] , S′ | P | Q =
      {!!} -- [ ≤-trans (unstepᴹ E (◻ , π₂ (unren∘ren≤id (ᴿ̃.pop ◻) R′))) P │ (≤-trans (unstepᴹ F (◻ , ᴹ S′)) Q) ]
   ... | [ x • ᵇ ] , R′ | ◻ , S′ | P | Q =
      {!!} -- [ ≤-trans (unstepᴹ E (◻ , π₂ (unren∘ren≤id (ᴿ̃.pop ◻) R′))) P │ Q ]
   ... | [ x • ᵇ ] , R′ | [ • .x 〈 y′ 〉 ᶜ ] , S′ | P | Q =
      let pop-y′ , P″ = unren∘ren≤id (ᴿ̃.pop y′) R′ in
      [ ≤-trans (unstepᴹ E ([ x • ᵇ ] , P″)) P │ ≤-trans (unstepᴹ F ([ • _ 〈 pop-y′ ᴺ.zero 〉 ᶜ ] , ᴹ S′)) Q ]
   unstep∘step⁻≤id (E │ᵥ F) (R │ S)
      with step E R | step F S | unstep∘step≤id E R | unstep∘step≤id F S
   ... | ◻ , R′ | ◻ , _ | P | Q = [ P │ Q ]
   ... | ◻ , R′ | [ (• x) ᵇ ] , S′ | P | Q = [ P │ ≤-trans (unstepᴹ F (◻ , ᴹ S′)) Q ]
   ... | [ ._ • ᵇ ] , R′ | ◻ , _ | P | Q = [ ≤-trans (unstepᴹ E (◻ , ᴹ R′)) P │ Q ]
   ... | [ x • ᵇ ] , R′ | [ (• .x) ᵇ ] , _ | P | Q = [ P │ Q ]
   unstep∘step⁻≤id (ν• E) (ν R) with step E R | unstep∘step≤id E R
   ... | ◻ , ◻ | _ = ◻
   ... | ◻ , [ R′ ] | P = [ ν P ]
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , ◻ | _ = ◻
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , [ R′ ] | P = [ ν (≤-trans [ unstep⁻ᴹ E ◻ (⁻ᴹ R′) ] P) ]
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , ◻ | P = [ ν P ]
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , [ _ ] | P = [ ν P ]
   unstep∘step⁻≤id {a = x • ᵇ} (νᵇ E) (ν R) with step E R | unstep∘step≤id E R
   ... | ◻ , R′ | P = [ ν ≤-trans (unstepᴹ E (◻ , (π₂ (unren∘ren≤id ᴿ̃.swap R′)))) P ]
   ... | [ ._ • ᵇ ] , R′ | P =
      [ ν ≤-trans (unstepᴹ E ([ ᴺ.suc x • ᵇ ] , π₂ (unren∘ren≤id ᴿ̃.swap R′))) P ]
   unstep∘step⁻≤id {a = (• x) ᵇ} (νᵇ E) (ν R) with step E R | unstep∘step≤id E R
   ... | ◻ , R′ | P = [ ν ≤-trans (unstepᴹ E (◻ , (π₂ (unren∘ren≤id ᴿ̃.swap R′)))) P ]
   ... | [ (• .(ᴺ.suc x)) ᵇ ] , R′ | P =
      [ ν ≤-trans (unstepᴹ E ([ (• ᴺ.suc x) ᵇ ] , π₂ (unren∘ren≤id ᴿ̃.swap R′))) P ]
   unstep∘step⁻≤id {a = • _ 〈 _ 〉 ᶜ} (νᶜ E) (ν R) with step E R | unstep∘step≤id E R
   ... | ◻ , ◻ | _ = [ ν ◻ ]
   ... | ◻ , [ _ ] | P = [ ν P ]
   ... | [ • ._ 〈 ◻ 〉 ᶜ ] , _ | P = [ ν P ]
   ... | [ • ._ 〈 [ ._ ] 〉 ᶜ ] , _ | P = [ ν P ]
   unstep∘step⁻≤id {a = τ ᶜ} (νᶜ E) (ν R) with step E R | unstep∘step≤id E R
   ... | ◻ , _ | P = [ ν P ]
   ... | [ τ ᶜ ] , R′ | P = [ ν P ]
   unstep∘step⁻≤id (! E) (! R) with step E [ R │ [ ! R ] ] | unstep∘step≤id E [ R │ [ ! R ] ]
   ... | ◻ , ◻ | _ = ◻
   ... | [ a ] , ◻ | _ with unstep-◻ E a
   unstep∘step⁻≤id (! _) (! _) | [ _ ] , ◻ | [ R │ _ ] | _ │ ◻ = [ ! R ]
   unstep∘step⁻≤id (! _) (! _) | [ _ ] , ◻ | [ R │ [ ! R′ ] ] | _ │ [ ! _ ] = [ ! (R ⊔-lub R′) ]
   unstep∘step⁻≤id (! E) (! _) | a , [ R ] | _ with unstep⁻ E a R
   unstep∘step⁻≤id (! _) (! _) | a , [ _ ] | [ R │ _ ] | _ │ ◻ = [ ! R ]
   unstep∘step⁻≤id (! _) (! _) | a , [ _ ] | [ R │ [ ! R′ ] ] | _ │ [ ! _ ] = [ ! (R ⊔-lub R′) ]

   gc : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) →
        IsGaloisConnection (poset {a = P}) (poset {a = a , R}) (step E) (unstep E)
   gc E = record {
         f-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ stepᴹ E ∘ᶠ ≤ᴸ⇒≤;
         g-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ unstepᴹ E ∘ᶠ ≤ᴸ⇒≤;
         id≤f∘g = ≤⇒≤ᴸ ∘ᶠ id≤step∘unstep E;
         g∘f≤id = ≤⇒≤ᴸ ∘ᶠ unstep∘step≤id E
      }
