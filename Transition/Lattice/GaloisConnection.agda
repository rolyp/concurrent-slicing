module Transition.Lattice.GaloisConnection where

   open import ConcurrentSlicingCommon hiding (poset)
   open import Ext.Algebra
   open import Ext.Algebra.Structures

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Lattice as ᴬ̃ using (top; ↓ᵇ⁻_; ↓ᶜ⁻_);
      open ᴬ̃.↓_; open ᴬ̃.↓⁻_; open ᴬ̃.↓ᵇ⁻_; open ᴬ̃.↓ᶜ⁻_; open ᴬ̃._≤_; open ᴬ̃._≤⁻_; open ᴬ̃._≤ᵇ⁻_; open ᴬ̃._≤ᶜ⁻_
   import Lattice; open Lattice.Prefixes ⦃...⦄
   import Lattice.Product
   open import Proc using (Proc)
   import Proc.Lattice as ᴾ̃; open ᴾ̃.↓⁻_; open ᴾ̃.↓_; open ᴾ̃._≤_; open ᴾ̃._≤⁻_
   open import Proc.Ren.Lattice using (_†; _†ᴹ; _*ᴹ) renaming (_* to _*̃)
   open import Proc.Ren.Lattice.GaloisConnection using (id≤ren∘unren; unren∘ren≤id)
   import Name as ᴺ
   open import Name.Lattice as ᴺ̃ using (zero; suc; sucᴹ); open ᴺ̃.↓_; open ᴺ̃._≤_
   open import Ren as ᴿ using (push; pop; swap; ᴺren); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice as ᴿ̃ using (pop-top)
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_
   open import Transition.Lattice as ᵀ̃ using (fwd; fwdᴹ; fwd⁻; fwd⁻ᴹ; bwd; bwdᴹ; bwd-◻; bwd⁻);
      open ᵀ̃.↓_; open ᵀ̃.↓⁻_; open ᵀ̃._≤_; open ᵀ̃._≤⁻_

   id≤fwd∘bwd : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) (aR : ↓ (a , R)) → aR ≤ (fwd E ∘ᶠ bwd E) aR
   id≤fwd⁻∘bwd-◻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) (a′ : ↓⁻ a) → [ a′ ] ≤ π₁ (fwd⁻ E (bwd-◻ E a′))
   id≤fwd⁻∘bwd⁻ : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) (a′ : ↓ a) (R′ : ↓⁻ R) → (a′ , [ R′ ]) ≤ fwd⁻ E (bwd⁻ E a′ R′)

   id≤fwd∘bwd E (a , [ R ]) = id≤fwd⁻∘bwd⁻ E a R
   id≤fwd∘bwd E ([ a ] , ◻) = id≤fwd⁻∘bwd-◻ E a , ◻
   id≤fwd∘bwd _ (◻ , ◻) = ◻ , ◻

   id≤fwd⁻∘bwd-◻ (_ •∙ _) (x • ᵇ) = [ ᴹ x • ᵇ ]
   id≤fwd⁻∘bwd-◻ (• _ 〈 _ 〉∙ _) (• x 〈 y 〉 ᶜ) = [ • ᴹ x 〈 ᴹ y 〉 ᶜ ]
   id≤fwd⁻∘bwd-◻ (E ➕₁ Q) a = id≤fwd⁻∘bwd-◻ E a
   id≤fwd⁻∘bwd-◻ (E ᵇ│ Q) (a ᵇ) = id≤fwd⁻∘bwd-◻ E (a ᵇ)
   id≤fwd⁻∘bwd-◻ (E ᶜ│ Q) (a ᶜ) = id≤fwd⁻∘bwd-◻ E (a ᶜ)
   id≤fwd⁻∘bwd-◻ (P │ᵇ E) (a ᵇ) = id≤fwd⁻∘bwd-◻ E (a ᵇ)
   id≤fwd⁻∘bwd-◻ (P │ᶜ E) (a ᶜ) = id≤fwd⁻∘bwd-◻ E (a ᶜ)
   id≤fwd⁻∘bwd-◻ (_│•_ {x = x} E F) (τ ᶜ)
      with fwd⁻ E (bwd-◻ E ([ x ] • ᵇ)) | fwd⁻ F (bwd-◻ F (• [ x ] 〈 ◻ 〉 ᶜ)) |
           id≤fwd⁻∘bwd-◻ E ([ x ] • ᵇ) | id≤fwd⁻∘bwd-◻ F (• [ x ] 〈 ◻ 〉 ᶜ) |
           inspect (fwd⁻ E ∘ᶠ bwd-◻ E) ([ x ] • ᵇ) | inspect (fwd⁻ F ∘ᶠ bwd-◻ F) (• [ x ] 〈 ◻ 〉 ᶜ)
   ... | [ ([ ._ ] •) ᵇ ] , _ | [ • [ ._ ] 〈 _ 〉 ᶜ ] , _ | [ [ ._ ] • ᵇ ] | [ • [ ._ ] 〈 _ 〉 ᶜ ]
       | [ eq ] | [ eq′ ] rewrite eq | eq′ = [ τ ᶜ ]
   id≤fwd⁻∘bwd-◻ (_│ᵥ_ {x = x} E F) (τ ᶜ)
      with fwd⁻ E (bwd-◻ E ([ x ] • ᵇ)) | fwd⁻ F (bwd-◻ F ((• [ x ]) ᵇ)) |
           id≤fwd⁻∘bwd-◻ E ([ x ] • ᵇ) | id≤fwd⁻∘bwd-◻ F ((• [ x ]) ᵇ)
   ... | [ ([ ._ ] •) ᵇ ] , _ | [ (• [ ._ ]) ᵇ ] , _ | [ [ ._ ] • ᵇ ] | [ (• [ ._ ]) ᵇ ] = [ τ ᶜ ]
   id≤fwd⁻∘bwd-◻ (ν•_ {x = x} E) ((• _) ᵇ)
      with fwd⁻ E (bwd-◻ E (• suc [ x ] 〈 zero 〉 ᶜ)) | id≤fwd⁻∘bwd-◻ E (• suc [ x ] 〈 zero 〉 ᶜ) |
           inspect (fwd⁻ E ∘ᶠ bwd-◻ E) (• suc [ x ] 〈 zero 〉 ᶜ)
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] | [ eq ] rewrite eq = top ((• x) ᵇ)
   id≤fwd⁻∘bwd-◻ {a = x • ᵇ} (νᵇ E) (_ • ᵇ)
      with fwd⁻ E (bwd-◻ E ([ (push *) x ] • ᵇ)) | id≤fwd⁻∘bwd-◻ E ([ (push *) x ] • ᵇ) |
           inspect (fwd⁻ E ∘ᶠ bwd-◻ E) ([ (push *) x ] • ᵇ)
   ... | [ [ ._ ] • ᵇ ] , _ | [ [ ._ ] • ᵇ ] | [ eq ] rewrite eq = top (x • ᵇ)
   id≤fwd⁻∘bwd-◻ {a = (• x) ᵇ} (νᵇ E) ((• _) ᵇ)
      with fwd⁻ E (bwd-◻ E ((• [ (push *) x ]) ᵇ)) | id≤fwd⁻∘bwd-◻ E ((• [ (push *) x ]) ᵇ) |
           inspect (fwd⁻ E ∘ᶠ bwd-◻ E) ((• [ (push *) x ]) ᵇ)
   ... | [ (• [ ._ ]) ᵇ ] , _ | [ (• [ ._ ]) ᵇ ] | [ eq ] rewrite eq = top ((• x) ᵇ)
   id≤fwd⁻∘bwd-◻ {a = • x 〈 y 〉 ᶜ} (νᶜ E) (• _ 〈 _ 〉 ᶜ)
      with fwd⁻ E (bwd-◻ E (• [ (push *) x ] 〈 [ (push *) y ] 〉 ᶜ)) | id≤fwd⁻∘bwd-◻ E (• [ (push *) x ] 〈 [ (push *) y ] 〉 ᶜ) |
           inspect (fwd⁻ E ∘ᶠ bwd-◻ E) (• [ (push *) x ] 〈 [ (push *) y ] 〉 ᶜ)
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] | [ eq ] rewrite eq = top (• x 〈 y 〉 ᶜ)
   id≤fwd⁻∘bwd-◻ {a = τ ᶜ} (νᶜ E) (τ ᶜ)
      with fwd⁻ E (bwd-◻ E (τ ᶜ)) | id≤fwd⁻∘bwd-◻ E (τ ᶜ) | inspect (fwd⁻ E ∘ᶠ bwd-◻ E) (τ ᶜ)
   ... | [ τ ᶜ ] , _ | [ _ ] | [ eq ] rewrite eq = [ τ ᶜ ]
   id≤fwd⁻∘bwd-◻ (! E) a with bwd-◻ E a | id≤fwd⁻∘bwd-◻ E a
   ... | R │ ◻ | a′ = ≤-trans a′ (π₁ (fwd⁻ᴹ E (ᴹ R │ ◻)))
   ... | R │ [ ! R′ ] | a′ = ≤-trans a′ (π₁ (fwd⁻ᴹ E (R ⊔ʳ R′ │ [ ! (R ⊔ˡ R′) ])))

   id≤fwd⁻∘bwd⁻ (_ •∙ ._) ◻ R = ◻ , ᴹ [ R ]
   id≤fwd⁻∘bwd⁻ (_ •∙ _) [ x • ᵇ ] R = [ ᴹ x • ᵇ ] , ᴹ [ R ]
   id≤fwd⁻∘bwd⁻ (• _ 〈 _ 〉∙ ._) ◻ R = ◻ , ᴹ [ R ]
   id≤fwd⁻∘bwd⁻ (• _ 〈 _ 〉∙ ._) [ • x 〈 y 〉 ᶜ ] R = ᴹ [ • x 〈 y 〉 ᶜ ] , ᴹ [ R ]
   id≤fwd⁻∘bwd⁻ (E ➕₁ Q) a R = id≤fwd⁻∘bwd⁻ E a R
   id≤fwd⁻∘bwd⁻ {a = _ ᵇ} (E ᵇ│ Q) a (R │ S) =
      let a′ , P′ = id≤fwd∘bwd E (a , R); ρ , Q′ = (ᴿ.push †) Q S in
      a′ , [ P′ │ ≤-trans (id≤ren∘unren push Q S) ((ᴿ̃.top push *ᴹ) (ᴹ Q′)) ]
   id≤fwd⁻∘bwd⁻ {a = _ ᶜ} (E ᶜ│ Q) a (R │ S) =
      let a′ , P′ = id≤fwd∘bwd E (a , R) in a′ , [ P′ │ ᴹ S ]
   id≤fwd⁻∘bwd⁻ {a = _ ᵇ} (P │ᵇ E) a (R │ S) =
      let a′ , Q′ = id≤fwd∘bwd E (a , S); ρ , P′ = (push †) P R in
      a′ , [ ≤-trans (id≤ren∘unren push P R) ((ᴿ̃.top push *ᴹ) (ᴹ P′)) │ Q′ ]
   id≤fwd⁻∘bwd⁻ {a = _ ᶜ} (P │ᶜ E) a (R │ S) =
      let a′ , Q′ = id≤fwd∘bwd E (a , S) in a′ , [ ᴹ R │ Q′ ]
   id≤fwd⁻∘bwd⁻ (_│•_ {R = P′} {x = x} {y} E F) a (R │ S)
      with (pop y †) P′ R | id≤ren∘unren (pop y) P′ R
   ... | pop-y , R′ | R″
      with fwd E (bwd E ([ [ x ] • ᵇ ] , R′)) | fwd F (bwd F ([ • [ x ] 〈 pop-y ᴺ.zero 〉 ᶜ ] , S)) |
           id≤fwd∘bwd E ([ [ x ] • ᵇ ] , R′) | id≤fwd∘bwd F ([ • [ x ] 〈 pop-y ᴺ.zero 〉 ᶜ ] , S) |
           inspect (fwd E ∘ᶠ bwd E) ([ [ x ] • ᵇ ] , R′) | inspect (fwd F ∘ᶠ bwd F) ([ • [ x ] 〈 pop-y ᴺ.zero 〉 ᶜ ] , S)
   ... | [ [ .x ] • ᵇ ] , _ | [ • [ .x ] 〈 y′ 〉 ᶜ ] , _ | [ [ .x ] • ᵇ ] , P | [ • [ .x ] 〈 v′ 〉 ᶜ ] , Q
       | [ eq ] | [ eq′ ] rewrite eq | eq′
      with ≤-trans R″ ((≤-trans pop-top (ᴿ̃.popᴹ v′) *ᴹ) (≤-trans (ᴹ R′) P))
   ... | P″ = top (τ ᶜ) , [ P″ │ Q ]
   id≤fwd⁻∘bwd⁻ (_│ᵥ_ {x = x} E F) a (ν ◻)
      with fwd⁻ E (bwd-◻ E ([ x ] • ᵇ)) | fwd⁻ F (bwd-◻ F ((• [ x ]) ᵇ)) |
           id≤fwd⁻∘bwd-◻ E ([ x ] • ᵇ) | id≤fwd⁻∘bwd-◻ F ((• [ x ]) ᵇ)
   ... | [ [ .x ] • ᵇ ] , _ | [ (• [ .x ]) ᵇ ] , _ | [ [ ._ ] • ᵇ ] | [ (• [ .x ]) ᵇ ] = top (τ ᶜ) , [ ν ◻ ]
   id≤fwd⁻∘bwd⁻ (_│ᵥ_ {x = x} E F) a (ν [ R │ S ])
      with fwd E (bwd E ([ [ x ] • ᵇ ] , R)) | fwd F (bwd F ([ (• [ x ]) ᵇ ] , S)) |
           id≤fwd∘bwd E ([ [ x ] • ᵇ ] , R) | id≤fwd∘bwd F ([ (• [ x ]) ᵇ ] , S) |
           inspect (fwd E ∘ᶠ bwd E) ([ [ x ] • ᵇ ] , R) | inspect (fwd F ∘ᶠ bwd F) ([ (• [ x ]) ᵇ ] , S)
   ... | [ [ .x ] • ᵇ ] , _ | [ (• [ .x ]) ᵇ ] , _ | [ [ ._ ] • ᵇ ] , P | [ (• [ ._ ]) ᵇ ] , Q
       | [ eq ] | [ eq′ ] rewrite eq | eq′ = top (τ ᶜ) , [ ν [ P │ Q ] ]
   id≤fwd⁻∘bwd⁻ (ν•_ {x = x} E) a R
      with fwd⁻ E (bwd⁻ E [ • suc [ x ] 〈 zero 〉 ᶜ ] R) | id≤fwd⁻∘bwd⁻ E [ • suc [ x ] 〈 zero 〉 ᶜ ] R |
           inspect (fwd⁻ E ∘ᶠ bwd⁻ E [ • suc [ x ] 〈 zero 〉 ᶜ ]) R
   ... | [ • [ ._ ] 〈 ._ 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , P | [ eq ] rewrite eq = top ((• x) ᵇ) , P
   id≤fwd⁻∘bwd⁻ {a = x • ᵇ} (νᵇ_ {R = P′} E) _ (ν R)
      with ((swap †) P′ R) | id≤ren∘unren swap P′ R; ... | ρ , R′ | R″
      with fwd E (bwd E ([ [ (push *) x ] • ᵇ ] , R′)) | id≤fwd∘bwd E ([ [ (push *) x ] • ᵇ ] , R′) |
           inspect (fwd E ∘ᶠ bwd E) ([ [ (push *) x ] • ᵇ ] , R′)
   ... | [ [ ._ ] • ᵇ ] , _ | [ [ ._ ] • ᵇ ] , P | [ eq ] rewrite eq = top _ , [ ν ≤-trans R″ ((ᴿ̃.top swap *ᴹ) P) ]
   id≤fwd⁻∘bwd⁻ {a = (• x) ᵇ} (νᵇ_ {R = P′} E) _ (ν R)
      with ((swap †) P′ R) | id≤ren∘unren swap P′ R; ... | ρ , R′ | R″
      with fwd E (bwd E ([ (• [ (push *) x ]) ᵇ ] , R′)) | id≤fwd∘bwd E ([ (• [ (push *) x ]) ᵇ ] , R′) |
           inspect (fwd E ∘ᶠ bwd E) ([ (• [ (push *) x ]) ᵇ ] , R′)
   ... | [ (• [ ._ ]) ᵇ ] , _ | [ (• [ ._ ]) ᵇ ] , P | [ eq ] rewrite eq = top ((• x) ᵇ) , [ ν ≤-trans R″ ((ᴿ̃.top swap *ᴹ) P) ]
   id≤fwd⁻∘bwd⁻ {a = • x 〈 y 〉 ᶜ} (νᶜ_ {R = P′} E) _ (ν R)
      with fwd E (bwd E ([ • [ (push *) x ] 〈 [ (push *) y ] 〉 ᶜ ] , R)) |
           id≤fwd∘bwd E ([ • [ (push *) x ] 〈 [ (push *) y ] 〉 ᶜ ] , R) |
           inspect (fwd E ∘ᶠ bwd E) ([ • [ (push *) x ] 〈 [ (push *) y ] 〉 ᶜ ] , R)
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , P | [ eq ] rewrite eq = top (• x 〈 y 〉 ᶜ) , [ ν P ]
   id≤fwd⁻∘bwd⁻ {a = τ ᶜ} (νᶜ_ {R = P′} E) _ (ν R)
      with fwd E (bwd E ([ τ ᶜ ] , R)) | id≤fwd∘bwd E ([ τ ᶜ ] , R) | inspect (fwd E ∘ᶠ bwd E) ([ τ ᶜ ] , R)
   ... | [ τ ᶜ ] , _ | [ _ ] , P | [ eq ] rewrite eq = top (τ ᶜ) , [ ν P ]
   id≤fwd⁻∘bwd⁻ (! E) a R with bwd⁻ E a R | id≤fwd⁻∘bwd⁻ E a R
   ... | R′ │ ◻ | a′ , P = ≤-trans (a′ , P) (fwdᴹ E [ ᴹ R′ │ ◻ ])
   ... | R′ │ [ ! R″ ] | a′ , P = ≤-trans (a′ , P) (fwdᴹ E [ R′ ⊔ʳ R″ │ [ ! (R′ ⊔ˡ R″) ] ])

   bwd∘fwd≤id : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) (P′ : ↓ P) → (bwd E ∘ᶠ fwd E) P′ ≤ P′
   bwd∘fwd⁻≤id : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) (P′ : ↓⁻ P) → (bwd E ∘ᶠ fwd⁻ E) P′ ≤ [ P′ ]

   bwd∘fwd≤id E [ P ] = bwd∘fwd⁻≤id E P
   bwd∘fwd≤id {a = _ ᵇ} _ ◻ = ◻
   bwd∘fwd≤id {a = _ ᶜ} _ ◻ = ◻

   bwd∘fwd⁻≤id (_ •∙ _) (x •∙ ◻) = [ ᴹ x •∙ ◻ ]
   bwd∘fwd⁻≤id (_ •∙ _) (x •∙ [ R ]) = [ ᴹ x •∙ ᴹ [ R ] ]
   bwd∘fwd⁻≤id (• _ 〈 _ 〉∙ _) (• x 〈 y 〉∙ ◻) = [ • ᴹ x 〈 ᴹ y 〉∙ ◻ ]
   bwd∘fwd⁻≤id (• _ 〈 _ 〉∙ ._) (• x 〈 y 〉∙ [ R ]) = [ • ᴹ x 〈 ᴹ y 〉∙ ᴹ [ R ] ]
   bwd∘fwd⁻≤id (E ➕₁ _) (R ➕ _) with fwd E R | bwd∘fwd≤id E R
   ... | _ , [ _ ] | P = [ P ➕ ◻ ]
   ... | [ _ ] , ◻ | P = [ P ➕ ◻ ]
   ... | ◻ , ◻ | _ = ◻
   bwd∘fwd⁻≤id {a = _ ᵇ} (E ᵇ│ Q) (R │ S) with fwd E R | bwd∘fwd≤id E R | π₂ (unren∘ren≤id ᴿ̃.push S)
   ... | _ , [ _ ] | P | Q′ = [ P │ Q′ ]
   ... | [ _ ] , _ | P | Q′ = [ P │ Q′ ]
   ... | ◻ , ◻ | _ | Q′ = [ ◻ │ Q′ ]
   bwd∘fwd⁻≤id {a = _ ᶜ} (E ᶜ│ Q) (R │ S) with fwd E R | bwd∘fwd≤id E R
   ... | _ , [ _ ] | P = [ P │ ᴹ S ]
   ... | [ _ ] , _ | P = [ P │ ᴹ S ]
   ... | ◻ , ◻ | _ = [ ◻ │ ᴹ S ]
   bwd∘fwd⁻≤id {a = _ ᵇ} (P │ᵇ E) (R │ S) with π₂ (unren∘ren≤id ᴿ̃.push R) | fwd E S | bwd∘fwd≤id E S
   ... | P′ | _ , [ _ ] | Q = [ P′ │ Q ]
   ... | P′ |  [ _ ] , _ | Q = [ P′ │ Q ]
   ... | P′ | ◻ , ◻ | _ = [ P′ │ ◻ ]
   bwd∘fwd⁻≤id {a = _ ᶜ} (P │ᶜ E) (R │ S) with fwd E S | bwd∘fwd≤id E S
   ... | _ , [ _ ] | Q = [ ᴹ R │ Q ]
   ... | [ _ ] , _ | Q = [ ᴹ R │ Q ]
   ... | ◻ , ◻ | _ = [ ᴹ R │ ◻ ]
   bwd∘fwd⁻≤id (_│•_ {R = P′} {y = y} E F) (R │ S)
      with fwd E R | fwd F S | bwd∘fwd≤id E R | bwd∘fwd≤id F S | inspect (fwd E) R | inspect (fwd F) S
   ... | ◻ , _ | _ , _ | _ | _ | _ | _ = ◻
   ... | [ ◻ • ᵇ ] , _ | _ | _ | _ | _ | _ = ◻
   ... | [ [ ._ ] • ᵇ ] , _ | ◻ , _ | _ | _ | _ | _ = ◻
   ... | [ [ ._ ] • ᵇ ] , _ | [ • ◻ 〈 _ 〉 ᶜ ] , _ | _ | _ | _ | _ = ◻
   ... | [ [ ._ ] • ᵇ ] , R′ | [ • [ ._ ] 〈 v 〉 ᶜ ] , S′ | P | Q | [ eq ] | [ eq′ ] rewrite eq | eq′
      with unren∘ren≤id (ᴿ̃.pop v) R′
   ... | pop-v , P″ =
      [ (≤-trans (bwdᴹ E ([ [ _ ] • ᵇ ] , P″)) P) │ ≤-trans (bwdᴹ F ([ • [ _ ] 〈 pop-v ᴺ.zero 〉 ᶜ ] , ᴹ S′)) Q ]
   bwd∘fwd⁻≤id (E │ᵥ F) (R │ S)
      with fwd E R | fwd F S | bwd∘fwd≤id E R | bwd∘fwd≤id F S | inspect (fwd E) R | inspect (fwd F) S
   ... | ◻ , _ | _ | _ | _ | _ | _ = ◻
   ... | [ ◻ • ᵇ ] , _ | _ , _ | _ | _ | _ | _ = ◻
   ... | [ [ ._ ] • ᵇ ] , _ | ◻ , _ | _ | _ | _ | _ = ◻
   ... | [ [ ._ ] • ᵇ ] , _ | [ (• ◻) ᵇ ] , _ | _ | _ | _ | _ = ◻
   ... | [ [ ._ ] • ᵇ ] , _ | [ (• [ ._ ]) ᵇ ] , _ | P | Q | [ eq ] | [ eq′ ] rewrite eq | eq′ = [ P │ Q ]
   bwd∘fwd⁻≤id (ν• E) (ν R) with fwd E R | bwd∘fwd≤id E R | inspect (fwd E) R
   ... | ◻ , _ | _ | _ = ◻
   ... | [ • ◻ 〈 _ 〉 ᶜ ] , _ | _ | _ = ◻
   ... | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | _ | _ = ◻
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , ◻ | P | [ eq ] rewrite eq = [ ν P ]
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , [ _ ] | P | [ eq ] rewrite eq = [ ν P ]
   bwd∘fwd⁻≤id {a = x • ᵇ} (νᵇ E) (ν R) with fwd E R | bwd∘fwd≤id E R | inspect (fwd E) R
   ... | ◻ , _ | _ | _ = ◻
   ... | [ ◻ • ᵇ ] , _ | _ | _ = ◻
   ... | [ [ ._ ] • ᵇ ] , R′ | P | [ eq ] rewrite eq =
      [ ν ≤-trans (bwdᴹ E ([ [ (push *) x ] • ᵇ ] , π₂ (unren∘ren≤id ᴿ̃.swap R′))) P ]
   bwd∘fwd⁻≤id {a = (• x) ᵇ} (νᵇ E) (ν R) with fwd E R | bwd∘fwd≤id E R | inspect (fwd E) R
   ... | ◻ , _ | _ | _ = ◻
   ... | [ (• ◻) ᵇ ] , _ | _ | _ = ◻
   ... | [ (• [ ._ ]) ᵇ ] , R′ | P | [ eq ] rewrite eq =
      [ ν ≤-trans (bwdᴹ E ([ (• [ (push *) x ]) ᵇ ] , π₂ (unren∘ren≤id ᴿ̃.swap R′))) P ]
   bwd∘fwd⁻≤id {a = • _ 〈 _ 〉 ᶜ} (νᶜ E) (ν R) with fwd E R | bwd∘fwd≤id E R | inspect (fwd E) R
   ... | ◻ , _ | _ | _ = ◻
   ... | [ • ◻ 〈 _ 〉 ᶜ ] , _ | _ | _ = ◻
   ... | [ • [ ._ ] 〈 ◻ 〉 ᶜ ] , _ | _ | _ = ◻
   ... | [ • [ ._ ] 〈 [ ._ ] 〉 ᶜ ] , _ | P | [ eq ] rewrite eq = [ ν P ]
   bwd∘fwd⁻≤id {a = τ ᶜ} (νᶜ E) (ν R) with fwd E R | bwd∘fwd≤id E R | inspect (fwd E) R
   ... | ◻ , _ | _ | _ = ◻
   ... | [ τ ᶜ ] , R′ | P | [ eq ] rewrite eq = [ ν P ]
   bwd∘fwd⁻≤id (! E) (! R) with fwd E [ R │ [ ! R ] ] | bwd∘fwd≤id E [ R │ [ ! R ] ]
   ... | ◻ , ◻ | _ = ◻
   ... | [ a ] , ◻ | _ with bwd-◻ E a
   bwd∘fwd⁻≤id (! _) (! _) | [ _ ] , ◻ | [ R │ _ ] | _ │ ◻ = [ ! R ]
   bwd∘fwd⁻≤id (! _) (! _) | [ _ ] , ◻ | [ R │ [ ! R′ ] ] | _ │ [ ! _ ] = [ ! (R ⊔-lub R′) ]
   bwd∘fwd⁻≤id (! E) (! _) | a , [ R ] | _ with bwd⁻ E a R
   bwd∘fwd⁻≤id (! _) (! _) | a , [ _ ] | [ R │ _ ] | _ │ ◻ = [ ! R ]
   bwd∘fwd⁻≤id (! _) (! _) | a , [ _ ] | [ R │ [ ! R′ ] ] | _ │ [ ! _ ] = [ ! (R ⊔-lub R′) ]

   gc : ∀ {Γ P} {a : Action Γ} {R} (E : P —[ a - _ ]→ R) →
        IsGaloisConnection (poset {a = P}) (poset {a = a , R}) (fwd E) (bwd E)
   gc E = record {
         f-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ fwdᴹ E ∘ᶠ ≤ᴸ⇒≤;
         g-mono = λ _ _ → ≤⇒≤ᴸ ∘ᶠ bwdᴹ E ∘ᶠ ≤ᴸ⇒≤;
         id≤f∘g = ≤⇒≤ᴸ ∘ᶠ id≤fwd∘bwd E;
         g∘f≤id = ≤⇒≤ᴸ ∘ᶠ bwd∘fwd≤id E
      }
