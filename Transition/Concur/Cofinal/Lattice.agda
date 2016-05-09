module Transition.Concur.Cofinal.Lattice where

   open import ConcurrentSlicingCommon

   open import Action as ᴬ using (Action)
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_); open _ᴬ⌣_
   open import Braiding.Proc.Lattice using (braid̂)
   open import Name using (Cxt)
   open import Proc.Lattice as ᴾ̃ using (↓_); open ᴾ̃.↓_
   import Proc.Ren
   open import Proc.Ren.Lattice renaming (_* to _*̃)
   open import Ren as ᴿ using (_ᴿ+_); open ᴿ.Renameable ⦃...⦄
   open import Ren.Lattice using (swap)
   open import Ren.Properties
   open import Transition.Concur.Cofinal using (⋈̂[_,_,_])

   braiding′ : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {Δ : Cxt} {P P′} → ⋈̂[ Γ , 𝑎 , Δ ] P P′ → ↓ P → ↓ P′
   braiding′ ˣ∇ˣ refl = idᶠ
   braiding′ ᵇ∇ᵇ _ P† = {!!}
   braiding′ ᵇ∇ᶜ refl = idᶠ
   braiding′ ᶜ∇ᵇ refl = idᶠ
   braiding′ ᶜ∇ᶜ refl = idᶠ
   braiding′ ᵛ∇ᵛ = braid̂
