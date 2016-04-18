module Name.Lattice.Show where

   open import ConcurrentSlicingCommon
   open import Data.Fin using (toℕ)
   import Data.Nat.Show

   open import Ext.Show

   open import Lattice using (); open Lattice.Prefixes ⦃...⦄
   open import Name using (Name)
   import Name.Lattice as ᴺ̃; open ᴺ̃.↓_

   show : ∀ {Γ} {x : Name Γ} → ↓ x → String
   show ◻ = "◻"
   show [ x ] = Data.Nat.Show.show (toℕ x)

   instance
      show′ : ∀ {Γ} {x : Name Γ} → Show (↓ x)
      show′ = record { show = show }
