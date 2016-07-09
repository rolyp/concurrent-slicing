-- Proof of pentagon theorem. Module for each main case, otherwise type-checking is too slow.
module Transition.Concur.Cofinal.Lattice where

   open import ConcurrentSlicingCommon

   open import Transition.Concur.Cofinal.Lattice.Common
   open import Transition.Concur.Cofinal.Lattice.Common using (braiding) public
   import Transition.Concur.Cofinal.Lattice.case.propagate-b-par-b as ᵇ│ᵇ
   import Transition.Concur.Cofinal.Lattice.case.sync-propagate-b as │•ᵇ
   import Transition.Concur.Cofinal.Lattice.case.sync-propagate-c as │•ᶜ
   import Transition.Concur.Cofinal.Lattice.case.propagate-b-sync as ᵇ│•
   import Transition.Concur.Cofinal.Lattice.case.propagate-c-sync as ᶜ│•
   import Transition.Concur.Cofinal.Lattice.case.nu-sync-propagate-b as │ᵥᵇ
   import Transition.Concur.Cofinal.Lattice.case.nu-sync-propagate-c as │ᵥᶜ
   import Transition.Concur.Cofinal.Lattice.case.propagate-b-nu-sync as ᵇ│ᵥ
{-
   import Transition.Concur.Cofinal.Lattice.case.propagate-c-nu-sync as ᶜ│ᵥ
-}
   import Transition.Concur.Cofinal.Lattice.case.propagate-par-b-b as │ᵇᵇ
   import Transition.Concur.Cofinal.Lattice.case.propagate-par-b-c as │ᵇᶜ
   import Transition.Concur.Cofinal.Lattice.case.propagate-par-c-c as │ᶜᶜ
   import Transition.Concur.Cofinal.Lattice.case.propagate-b-b-par as ᵇᵇ│
   import Transition.Concur.Cofinal.Lattice.case.propagate-b-c-par as ᵇᶜ│
   import Transition.Concur.Cofinal.Lattice.case.propagate-c-c-par as ᶜᶜ│
   import Transition.Concur.Cofinal.Lattice.case.sync-sync as │•
{-
   import Transition.Concur.Cofinal.Lattice.case.sync-nu-sync as │•ᵥ
   import Transition.Concur.Cofinal.Lattice.case.nu-sync-x-x-nu-sync as │ᵥ
   import Transition.Concur.Cofinal.Lattice.case.nu-sync-nu-sync as │ᵥ′
   import Transition.Concur.Cofinal.Lattice.case.nu-extrude-nu-extrude as ν•
   import Transition.Concur.Cofinal.Lattice.case.nu-extrude-propagate-b as ν•ᵇ
   import Transition.Concur.Cofinal.Lattice.case.nu-extrude-propagate-c as ν•ᶜ
   import Transition.Concur.Cofinal.Lattice.case.nu-propagate-b-b as νᵇᵇ
   import Transition.Concur.Cofinal.Lattice.case.nu-propagate-x-x as νˣˣ
   import Transition.Concur.Cofinal.Lattice.case.nu-propagate-b-c as νᵇᶜ
   import Transition.Concur.Cofinal.Lattice.case.nu-propagate-c-c as νᶜᶜ
   import Transition.Concur.Cofinal.Lattice.case.nu-propagate-nu-nu as νᵛᵛ
-}

   import Ren as ᴿ
   import Transition as ᵀ

   private
      coerceCxt : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) →
                  let Γ′ = Γ + inc a′ + inc (π₂ (ᴬ⊖ 𝑎)) in ∀ {P : Proc Γ′} → ↓ P → ↓ Proc↱ (sym (ᴬγ 𝑎)) P
      coerceCxt 𝑎 rewrite sym (ᴬγ 𝑎) = idᶠ

   -- γ₁ lifted to the lattice setting.
   gamma₁ : ∀ {Γ} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
            (𝐸 : E ⌣₁[ 𝑎 ] E′) → ∀ P′ →
            braiding 𝑎 (γ₁ 𝐸) (tgt (E′/E (⊖₁ 𝐸)) (tgt E P′)) ≡ coerceCxt 𝑎 (tgt (E/E′ (⊖₁ 𝐸)) (tgt E′ P′))

   gamma₁ {𝑎 = ˣ∇ˣ {x = x} {u}} 𝐸 ◻ =
      ≅-to-≡ (≅-trans (reduce-ˣ∇ˣ {x = x} {u} (γ₁ 𝐸) _) (◻-cong (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl _)))))
   gamma₁ {𝑎 = ᵇ∇ᵇ} 𝐸 ◻ =
      ≅-to-≡ (≅-trans (reduce-ᵇ∇ᵇ (γ₁ 𝐸) _) (◻-cong (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl _)))))
   gamma₁ {𝑎 = ᵇ∇ᶜ} 𝐸 ◻ =
      ≅-to-≡ (≅-trans (reduce-ᵇ∇ᶜ (γ₁ 𝐸) _) (◻-cong (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl _)))))
   gamma₁ {𝑎 = ᶜ∇ᵇ} 𝐸 ◻ =
      ≅-to-≡ (≅-trans (reduce-ᶜ∇ᵇ (γ₁ 𝐸) _) (◻-cong (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl _)))))
   gamma₁ {𝑎 = ᶜ∇ᶜ} 𝐸 ◻ =
      ≅-to-≡ (≅-trans (reduce-ᶜ∇ᶜ (γ₁ 𝐸) _) (◻-cong (trans (γ₁ 𝐸) (≅-to-≡ (Proc↲ refl _)))))
   gamma₁ {𝑎 = ᵛ∇ᵛ} 𝐸 ◻ = refl
   gamma₁ {a = a ᵇ} {a′ ᵇ} {E = .E ᵇ│ Q₀} {E′ = P₀ │ᵇ .F} (E ᵇ│ᵇ F) [ P │ Q ] =
      let open ᵇ│ᵇ in case E F P Q
   gamma₁ (E ᵇ│ᶜ F) [ P │ Q ] =
      cong (λ Q′ → [ _ │ Q′ ]) (sym (renᶜ-tgt-comm F push Q))
   gamma₁ (E ᶜ│ᵇ F) [ P │ Q ] =
      cong (λ P′ → [ P′ │ _ ]) (renᶜ-tgt-comm E push P)
   gamma₁ (E ᶜ│ᶜ F) [ P │ Q ] = refl
   gamma₁ {E = E ᵇ│ _} {E′ = E′ │• .F} (_│•ᵇ_ {x = x} {y} {a = a} 𝐸 F) [ P │ Q ] =
      let open │•ᵇ in case 𝐸 F P Q (gamma₁ 𝐸 P)
   gamma₁ {E = E ᶜ│ Q₀} {E′ = E′ │• .F} (𝐸 │•ᶜ F) [ P │ Q ] =
      let open │•ᶜ in case 𝐸 F P Q (gamma₁ 𝐸 P)
   gamma₁ {E = P₀ │ᵇ F} {E′ = .E │• F′} (_ᵇ│•_ {y = y} E 𝐹) [ P │ Q ] =
      let open ᵇ│• in case E 𝐹 P Q (gamma₁ 𝐹 Q)
   gamma₁ {E = P₀ │ᶜ F} {E′ = .E │• F′} (_ᶜ│•_ {y = y} E 𝐹) [ P │ Q ] =
      let open ᶜ│• in case E 𝐹 P Q (gamma₁ 𝐹 Q)
   gamma₁ {E = E ᵇ│ Q₀} {E′ │ᵥ .F} (_│ᵥᵇ_ {x = x} {a = x′ •} 𝐸 F) [ P │ Q ] =
      let open │ᵥᵇ.x• in case 𝐸 F P Q (gamma₁ 𝐸 P)
   gamma₁ {E = E ᵇ│ Q₀} {E′ │ᵥ .F} (_│ᵥᵇ_ {x = x} {a = • x′} 𝐸 F) [ P │ Q ] =
      let open │ᵥᵇ.•x in case 𝐸 F P Q (gamma₁ 𝐸 P)
   gamma₁ {E = E ᶜ│ Q₀} {E′ │ᵥ .F} (_│ᵥᶜ_ {a = τ} 𝐸 F) [ P │ Q ] =
      let open │ᵥᶜ.τ in case 𝐸 F P Q (gamma₁ 𝐸 P)
   gamma₁ {E = E ᶜ│ Q₀} {E′ │ᵥ .F} (_│ᵥᶜ_ {a = • x′ 〈 y′ 〉} 𝐸 F) [ P │ Q ] =
      let open │ᵥᶜ.•x〈y〉 in case 𝐸 F P Q (gamma₁ 𝐸 P)
   gamma₁ {E = P₀ │ᵇ F} {.E │ᵥ F′} (_ᵇ│ᵥ_ {a = • x′} {ˣ∇ˣ} E 𝐹) [ P │ Q ] =
      let open ᵇ│ᵥ.ˣ∇ˣ in case E 𝐹 P Q (gamma₁ 𝐹 Q)
   gamma₁ {E = P₀ │ᵇ F} {.E │ᵥ F′} (_ᵇ│ᵥ_ {a = • x′} {ᵇ∇ᵇ} E 𝐹) [ P │ Q ] =
      let open ᵇ│ᵥ.ᵇ∇ᵇ-•x in case E 𝐹 P Q (gamma₁ 𝐹 Q)
   gamma₁ {E = P₀ │ᵇ F} {.E │ᵥ F′} (_ᵇ│ᵥ_ {a = x′ •} {ᵇ∇ᵇ} E 𝐹) [ P │ Q ] =
      let open ᵇ│ᵥ.ᵇ∇ᵇ-x• in case E 𝐹 P Q (gamma₁ 𝐹 Q)
   gamma₁ (_ᶜ│ᵥ_ {a = • x′ 〈 y′ 〉} E 𝐹) [ P │ Q ] =
      {!!} -- let open ᶜ│ᵥ.•x〈y〉 in case E 𝐹 P Q (gamma₁ 𝐹 Q)
   gamma₁ (_ᶜ│ᵥ_ {a = τ} E 𝐹) [ P │ Q ] =
      {!!} -- let open ᶜ│ᵥ.τ in case E 𝐹 P Q (gamma₁ 𝐹 Q)
   gamma₁ (𝐸 ➕₁ Q) [ P ➕ _ ] =
      gamma₁ 𝐸 P
   gamma₁ {𝑎 = ˣ∇ˣ {x = x} {u}} {E = _ │ᵇ F} {._ │ᵇ F′} (._ │ᵇᵇ 𝐹) [ P │ Q ] =
      let open │ᵇᵇ.ˣ∇ˣ in case 𝐹 P Q (gamma₁ 𝐹 Q)
   gamma₁ {𝑎 = ᵇ∇ᵇ} {E = P₀ │ᵇ F} {._ │ᵇ F′} (._ │ᵇᵇ 𝐹) [ P │ Q ] =
      let open │ᵇᵇ.ᵇ∇ᵇ in case 𝐹 P Q (gamma₁ 𝐹 Q)
   gamma₁ {E = _ │ᵇ F} {._ │ᶜ F′} (._ │ᵇᶜ 𝐹) [ P │ Q ] =
      let open │ᵇᶜ in case 𝐹 P Q (gamma₁ 𝐹 Q)
   gamma₁ {E = _ │ᶜ F} {._ │ᶜ F′} (._ │ᶜᶜ 𝐹) [ P │ Q ] =
      let open │ᶜᶜ in case 𝐹 P Q (gamma₁ 𝐹 Q)
   gamma₁ {E = P₀ │ᶜ F} {._ │ᶜ F′} (._ │ᵛᵛ 𝐹) [ P │ Q ] =
      cong (λ Q → [ P │ Q ]) (gamma₁ 𝐹 Q)
   gamma₁ {𝑎 = ˣ∇ˣ {x = x} {u}} {E = E ᵇ│ Q₀} {E′ ᵇ│ ._} (𝐸 ᵇᵇ│ ._) [ P │ Q ] =
      let open ᵇᵇ│.ˣ∇ˣ in case 𝐸 P Q (gamma₁ 𝐸 P)
   gamma₁ {𝑎 = ᵇ∇ᵇ} {E = E ᵇ│ Q₀} {E′ ᵇ│ ._} (𝐸 ᵇᵇ│ ._) [ P │ Q ] =
      let open ᵇᵇ│.ᵇ∇ᵇ in case 𝐸 P Q (gamma₁ 𝐸 P)
   gamma₁ {E = E ᵇ│ _} {E′ ᶜ│ ._} (𝐸 ᵇᶜ│ ._) [ P │ Q ] =
      let open ᵇᶜ│ in case 𝐸 P Q (gamma₁ 𝐸 P)
   gamma₁ {E = E ᶜ│ _} {E′ ᶜ│ ._} (𝐸 ᶜᶜ│ ._) [ P │ Q ] =
      let open ᶜᶜ│ in case 𝐸 P Q (gamma₁ 𝐸 P)
   gamma₁ {E = E ᶜ│ Q₀} {E′ ᶜ│ ._} (𝐸 ᵛᵛ│ ._) [ P │ Q ] =
      cong (λ P → [ P │ Q ]) (gamma₁ 𝐸 P)
   gamma₁ (𝐸 │• 𝐹) [ P │ Q ] =
      {!!} -- let open │• in case 𝐸 𝐹 P Q (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q)
   gamma₁ (𝐸 │•ᵥ 𝐹) [ P │ Q ] =
      {!!} -- let open │•ᵥ in case 𝐸 𝐹 P Q (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q)
   gamma₁ {E = E │ᵥ F} {E′ │ᵥ F′} (𝐸 │ᵥ 𝐹) [ P │ Q ] =
      {!!} -- let open │ᵥ in case 𝐸 𝐹 P Q (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q)
   gamma₁ {E = E │ᵥ F} {E′ │ᵥ F′} (𝐸 │ᵥ′ 𝐹) [ P │ Q ] =
      {!!} -- let open │ᵥ′ in case 𝐸 𝐹 P Q (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q)
   gamma₁ {E = ν• E} {ν• E′} (ν• 𝐸) [ ν P ] =
      {!!} -- let open ν• in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a′ = • x 〈 y 〉 ᶜ} {E = ν• E} {νᶜ E′} (ν•ᶜ 𝐸) [ ν P ] =
      {!!} -- let open ν•ᶜ.•x〈y〉 in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a′ = τ ᶜ} {E = ν• E} {νᶜ E′} (ν•ᶜ 𝐸) [ ν P ] =
      {!!} -- let open ν•ᶜ.τ in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a′ = x • ᵇ} {E = ν• E} {νᵇ E′} (ν•ᵇ 𝐸) [ ν P ] =
      {!!} -- let open ν•ᵇ.x• in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a′ = (• x) ᵇ} {E = ν• E} {νᵇ E′} (ν•ᵇ 𝐸) [ ν P ] =
      {!!} -- let open ν•ᵇ.•x in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {x′ • ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] =
      {!!} -- let open νᵇᵇ.x•-x• in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {(• x′) ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] =
      {!!} -- let open νᵇᵇ.x•-•x in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {(x′ •) ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] =
      {!!} -- let open νᵇᵇ.•x-x• in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {(• x′) ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] =
      {!!} -- let open νᵇᵇ.•x-•x in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {E = νᵇ E} {νᵇ E′} (νˣˣ 𝐸) [ ν P ] =
      {!!} -- let open νˣˣ in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {• x′ 〈 y 〉 ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] =
      {!!} -- let open νᵇᶜ.x•-•x〈y〉 in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {τ ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] =
      {!!} -- let open νᵇᶜ.x•-τ in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {• x′ 〈 y 〉 ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] =
      {!!} -- let open νᵇᶜ.•x-•x〈y〉 in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {τ ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] =
      {!!} -- let open νᵇᶜ.•x-τ in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = • x 〈 y 〉 ᶜ} {• x′ 〈 y′ 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] =
      {!!} -- let open νᶜᶜ.•x〈y〉-•x〈y〉 in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = • x 〈 y 〉 ᶜ} {τ ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] =
      {!!} -- let open νᶜᶜ.•x〈y〉-τ in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = τ ᶜ} {• x 〈 y 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] =
      {!!} -- let open νᶜᶜ.τ-•x〈y〉 in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = τ ᶜ} {τ ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] =
      {!!} -- let open νᶜᶜ.τ-τ in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {E = νᶜ E} {νᶜ E′} (νᵛᵛ 𝐸) [ ν P ] =
      {!!} -- let open νᵛᵛ in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ (! 𝐸) [ ! P ] = gamma₁ 𝐸 [ P │ [ ! P ] ]
