module Transition.Concur.Cofinal.Lattice where

   open import ConcurrentSlicingCommon
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖-✓); open _ᴬ⌣_
   open import Braiding.Proc using (module _⋉̂_); open _⋉̂_
   open import Braiding.Proc.Lattice using (braid̂)
   open import Name using (Cxt; zero)
   open import Proc as ᴾ using (Proc; Proc↱); open ᴾ.Proc
   open import Proc.Lattice as ᴾ̃ using (↓_; ↓⁻_); open ᴾ̃.↓_; open ᴾ̃.↓⁻_
   import Proc.Ren
   open import Proc.Ren.Lattice renaming (_* to _*̃)
   open import Ren as ᴿ using (suc; _ᴿ+_); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice using (swap)
   open import Ren.Properties
   open import Transition using (_—[_-_]→_; target)
   open import Transition.Concur using (Concur₁; module Concur₁; module Delta′; ⊖₁); open Concur₁; open Delta′
   open import Transition.Concur.Cofinal using (⋈[_,_,_,_]; ⋈̂[_,_,_]; ⊖₁-✓)
   open import Transition.Ren using (_*ᵇ)

   braiding′ : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {Δ : Cxt} {P P′} → ⋈̂[ Γ , 𝑎 , Δ ] P P′ → ↓ P → ↓ P′
   braiding′ ˣ∇ˣ refl = idᶠ
   braiding′ ᵇ∇ᵇ _ P† = {!!}
   braiding′ ᵇ∇ᶜ refl = idᶠ
   braiding′ ᶜ∇ᵇ refl = idᶠ
   braiding′ ᶜ∇ᶜ refl = idᶠ
   braiding′ ᵛ∇ᵛ = braid̂
