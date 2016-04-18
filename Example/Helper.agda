module Example.Helper where

   open import ConcurrentSlicingCommon

   open import Action using (τ; _ᶜ)
   import Lattice; open Lattice.Prefixes ⦃...⦄
   open import Name using (Name; Cxt; _+_; zero; suc; shift)
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   import Proc.Lattice as ᴾ̃; open ᴾ̃.↓_; open ᴾ̃.↓⁻_
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_

   _^_ : ∀ {m} → Name m → (n : Cxt) → Name (m + n)
   _^_ = flip shift

   close : ∀ {Γ} → Proc Γ → Proc 0
   close {zero} P = P
   close {suc _} P = close (ν P)

   closeᶜ : ∀ {Γ} {P′ Q′ : Proc Γ} → P′ —[ τ ᶜ - _ ]→ Q′ → close P′ —[ τ ᶜ - _ ]→ close Q′
   closeᶜ {zero} E = E
   closeᶜ {suc _} E = closeᶜ (νᶜ E)

   closẽ : ∀ {Γ} {P : Proc Γ} → ↓ P → ↓ close P
   closẽ {zero} P = P
   closẽ {suc _} P = closẽ [ ν P ]
