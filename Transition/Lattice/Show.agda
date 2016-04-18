module Transition.Lattice.Show where

   open import SharedModules
   open import Common.Show using (Show); open Common.Show.Show ⦃...⦄ renaming (show to show′)

   open import Action using (Action)
   open import Lattice using (); open Lattice.Prefixes ⦃...⦄
   import Name.Lattice.Show
   import Proc.Lattice.Show
   open import Transition using (_—[_-_]→_)
   import Transition.Lattice as ᵀ̃; open ᵀ̃.↓_; open ᵀ̃.↓⁻_

   -- Not useful to distinguish between the different propagation forms for │.
   show : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → ↓ E → String
   show ◻ = "◻"
   show [ x •∙ P ] = show′ x ++ "." ++ show′ P
   show [ • x 〈 y 〉∙ P ] = "•" ++ show′ x ++ "〈" ++ show′ y ++ "〉." ++ show′ P
   show [ E ➕₁ Q ] = show E ++ " ➕ " ++ show′ Q
   show [ E ᵇ│ Q ] = show E ++ " │ " ++ show′ Q
   show [ E ᶜ│ Q ] = show E ++ " │ " ++ show′ Q
   show [ P │ᵇ F ] = show′ P ++ " │ " ++ show F
   show [ P │ᶜ F ] = show′ P ++ " │ " ++ show F
   show [ E │• F ] = show E ++ " │• " ++ show F
   show [ E •│ F ] = show E ++ " •│ " ++ show F
   show [ E │ᵥ F ] = show E ++ " │ᵥ " ++ show F
   show [ ν• E ] = "ν• " ++ show E
   show [ νᵇ E ] = "νᵇ " ++ show E
   show [ νᶜ E ] = "νᶜ " ++ show E
   show [ ! E ] = "! " ++ show E

   instance
      show† : ∀ {Γ P} {a : Action Γ} {R} {E : P —[ a - _ ]→ R} → Show (↓ E)
      show† = record { show = show }
