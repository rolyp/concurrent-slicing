module Proc.Lattice.Show where

   open import ConcurrentSlicingCommon
   open import Ext.Show using (Show); open Ext.Show.Show ⦃...⦄ renaming (show to show′)

   import Lattice; open Lattice.Prefixes ⦃...⦄
   import Name.Lattice.Show
   open import Proc using (Proc)
   import Proc.Lattice as ᴾ̃; open ᴾ̃.↓_; open ᴾ̃.↓⁻_

   show : ∀ {Γ} {P : Proc Γ} → ↓ P → String
   show ◻ = "◻"
   show [ Ο ] = "Ο"
   show [ x •∙ P ] = show′ x ++ "." ++ show P
   show [ • x 〈 y 〉∙ P ] = "•" ++ show′ x ++ "〈" ++ show′ y ++ "〉." ++ show P
   show [ P ➕ Q ] = show P ++ " ➕ " ++ show Q
   show [ P │ Q ] = show P ++ " │ " ++ show Q
   show [ ν P ] = "ν " ++ show P
   show [ ! P ] = "! " ++ show P

   instance
      show† : ∀ {Γ} {P : Proc Γ} → Show (↓ P)
      show† = record { show = show }
