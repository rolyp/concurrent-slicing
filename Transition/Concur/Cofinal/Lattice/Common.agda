module Transition.Concur.Cofinal.Lattice.Common where

   open import ConcurrentSlicingCommon

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ) public;
      open ᴬ.Action public; open ᴬ.Actionᵇ public; open ᴬ.Actionᶜ public
   open import Action.Concur  using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖; ᴬ⌣-sym; ᴬ⌣-sym-involutive; ᴬγ) public;
      open _ᴬ⌣_ public
   open import Action.Concur.Lattice using (residual) public
   open import Action.Lattice as ᴬ̃ using () public;
      open ᴬ̃.↓_ public; open ᴬ̃.↓⁻_ public; open ᴬ̃.↓ᵇ_ public; open ᴬ̃.↓ᶜ_ public
   open import Action.Ren.Lattice using () renaming (_* to _ᴬ*̃) public
   open import Braiding.Proc using (module _⋉̂_) public;
      open _⋉̂_ public
   open import Braiding.Proc.Lattice using (braid̂) public
   open import Lattice using (Lattices) public;
      open Lattice.Prefixes ⦃...⦄ public
   open import Name as ᴺ using (Name; Cxt; _+_) public
   open import Name.Lattice as ᴺ̃ using (zero) public;
      open ᴺ̃.↓_ public
   open import Proc as ᴾ using (Proc; Proc↱; Proc↲) public;
      open ᴾ.Proc public
   open import Proc.Lattice as ᴾ̃ using () public;
      open ᴾ̃.↓_ public; open ᴾ̃.↓⁻_ public
   open import Proc.Ren.Lattice using () renaming (_* to _*̃) public
   open import Ren as ᴿ using () public;
      open ᴿ.Renameable ⦃...⦄ public
   open import Ren.Lattice as ᴿ̃ using (swap; pop; push; id; repl; weaken; _ᴿ+_; suc) public
   open import Ren.Lattice.Properties public
   open import Ren.Properties public
   open import Transition as ᵀ using (_—[_-_]→_) public;
      open ᵀ._—[_-_]→_ public
   open import Transition.Concur using (Concur₁; module Concur₁; module Delta′; ⊖₁) public;
      open Concur₁ public
   open import Transition.Concur.Cofinal using (⋈̂[_,_,_]; γ₁) public
   open import Transition.Lattice using (tgt; action; step⁻; step) public
   open import Transition.Ren using (_*ᵇ; _*ᶜ) public
   open import Transition.Ren.Lattice using (renᵇ-tgt-comm; renᵇ-action-comm; renᶜ-tgt-comm; renᶜ-action-comm) public

   open Delta′ public

   braiding : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {Δ : Cxt} {P P′} (γ : ⋈̂[ Γ , 𝑎 , Δ ] P P′) → ↓ P → ↓ P′
   braiding ˣ∇ˣ eq rewrite eq = idᶠ
   braiding ᵇ∇ᵇ {Δ} refl = (swap ᴿ+ Δ) *̃
   braiding ᵇ∇ᶜ refl = idᶠ
   braiding ᶜ∇ᵇ refl = idᶠ
   braiding ᶜ∇ᶜ refl = idᶠ
   braiding ᵛ∇ᵛ = braid̂
