-- Milner's buggy scheduler example, with n = 2.
module Example where

   open import ConcurrentSlicingCommon
   import Ext.Show; open Ext.Show.Show ⦃...⦄ using (show)

   import Lattice; open Lattice.Prefixes ⦃...⦄
   open import Example.Helper
   open import Name using (fromℕ; pred; shift)
   import Name.Lattice as ᴺ̃; open ᴺ̃.↓_
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   open import Proc.Lattice as ᴾ̃ using (to-↓); open ᴾ̃.↓_; open ᴾ̃.↓⁻_
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_
   open import Transition.Seq as ᵀ* using (_—[_]→⋆_); open ᵀ*._—[_]→⋆_
   import Transition.Seq.Lattice
   open import Transition.Seq.Lattice.GaloisConnection using (bwd⋆)

   ■ = fromℕ 8
   b₂ = pred ■
   a₂ = pred b₂
   b₁ = pred a₂
   a₁ = pred b₁
   call₁ = pred a₁
   c₁ = pred call₁
   call₂ = pred c₁
   c₂ = pred call₂

   P : Proc 9
   P =
      ! (call₁ •∙ a₁ ^ 1 •∙ c₁ ^ 2 •∙ b₁ ^ 3 •∙ • c₂ ^ 4 〈 ■ ^ 4 〉∙ • call₁ ^ 4 〈 ■ ^ 4 〉∙ Ο) │
      a₁ •∙ c₁ ^ 1 •∙ b₁ ^ 2 •∙ • c₂ ^ 3 〈 ■ ^ 3 〉∙ • call₁ ^ 3 〈 ■ ^ 3 〉∙ Ο │
      ! (call₂ •∙ a₂ ^ 1 •∙ c₂ ^ 2 •∙ b₂ ^ 3 •∙ • c₂ ^ 4 〈 ■ ^ 4 〉∙ • call₂ ^ 4 〈 ■ ^ 4 〉∙ Ο) │
      • c₁ 〈 ■ 〉∙ • call₂ 〈 ■ 〉∙ Ο │
      -- P₁ and P₂ simply start and stop.
      • a₁ 〈 ■ 〉∙ • b₁ 〈 ■ 〉∙ Ο │
      • a₂ 〈 ■ 〉∙ • b₂ 〈 ■ 〉∙ Ο

   -- Maybe Agda can infer this with a few hints, but it's useful to see the final state anyway.
   R : Proc 9
   R =
      ! (call₁ •∙ a₁ ^ 1 •∙ c₁ ^ 2 •∙ b₁ ^ 3 •∙ • c₂ ^ 4 〈 ■ ^ 4 〉∙ • call₁ ^ 4 〈 ■ ^ 4 〉∙ Ο) │
      • call₁ 〈 ■ 〉∙ Ο │
      (b₂ •∙ • c₂ ^ 1 〈 ■ ^ 1 〉∙ • call₂ ^ 1 〈 ■ ^ 1 〉∙ Ο │
       ! (call₂ •∙ a₂ ^ 1 •∙ c₂ ^ 2 •∙ b₂ ^ 3 •∙ • c₂ ^ 4 〈 ■ ^ 4 〉∙ • call₂ ^ 4 〈 ■ ^ 4 〉∙ Ο)) │
      Ο │
      Ο │
      • b₂ 〈 ■ 〉∙ Ο

{-
   -- Requires •│ synchronisation form.
   Es : close P —[ _ ]→⋆ close R
   Es =
      [] ∷ʳ
      closeᶜ (_ │ᵇ (a₁ •∙ _) ᵇ│ _ ᵇ│ _ │• (• a₁ 〈 _ 〉∙ _) ᶜ│ _) ∷ʳ
      closeᶜ (_ │ᵇ (c₁ •∙ _) ᵇ│ _ │• (• c₁ 〈 _ 〉∙ _) ᶜ│ _ ᶜ│ _) ∷ʳ
      closeᶜ (_ │ᵇ ! (call₂ •∙ _ ᵇ│ _) │• (• call₂ 〈 _ 〉∙ _) ᶜ│ _ ᶜ│ _) ∷ʳ
      closeᶜ (_ │ᵇ ((a₂ •∙ _) ᵇ│ _) ᵇ│ _ ᵇ│ _ │• (• a₂ 〈 _ 〉∙ _)) ∷ʳ
      closeᶜ (_ │ᵇ b₁ •∙ _ ᵇ│ _ ᵇ│ _ │• (• b₁ 〈 _ 〉∙ _) ᶜ│ _) ∷ʳ
      closeᶜ (_ │ᶜ • c₂ 〈 _ 〉∙ _ •│ (c₂ •∙ _ ᵇ│ _) ᶜ│ _ ᶜ│ _ ᶜ│ _)

   R₁ R₁′ : ↓ R
   R₁ = [ ◻ │ [ • [ b₂ ] 〈 ◻ 〉∙ ◻ ] ]
   R₁′ = [ ◻ │ [ • ◻ 〈 ◻ 〉∙ ◻ ] ]

   slice₀ slice₁ slice₁′ : ↓ Es
   slice₀ = unstep* Es (closẽ (to-↓ R))
   slice₁ = unstep* Es (closẽ R₁)
   slice₁′ = unstep* Es (closẽ R₁′)
-}
