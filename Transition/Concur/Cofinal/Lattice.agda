module Transition.Concur.Cofinal.Lattice where

   open import ConcurrentSlicingCommon

   open import Transition.Concur.Cofinal.Lattice.Common
   import Transition.Concur.Cofinal.Lattice.Helpers.propagate-b-par-b as ᵇ│ᵇ
   import Transition.Concur.Cofinal.Lattice.Helpers.propagate-par-b-b as │ᵇᵇ
   import Transition.Concur.Cofinal.Lattice.Helpers.propagate-par-b-c as │ᵇᶜ
   import Transition.Concur.Cofinal.Lattice.Helpers.propagate-par-c-c as │ᶜᶜ
   import Transition.Concur.Cofinal.Lattice.Helpers.propagate-b-b-par as ᵇᵇ│
   import Transition.Concur.Cofinal.Lattice.Helpers.propagate-b-c-par as ᵇᶜ│
   import Transition.Concur.Cofinal.Lattice.Helpers.propagate-c-c-par as ᶜᶜ│
   import Transition.Concur.Cofinal.Lattice.Helpers.propagate-b-nu-sync as ᵇ│ᵥ
   import Transition.Concur.Cofinal.Lattice.Helpers.nu-sync-propagate-b as │ᵥᵇ
   import Transition.Concur.Cofinal.Lattice.Helpers.nu-sync-propagate-c as │ᵥᶜ
   import Transition.Concur.Cofinal.Lattice.Helpers.nu-sync-x-x-nu-sync as │ᵥ
   import Transition.Concur.Cofinal.Lattice.Helpers.nu-sync-nu-sync as │ᵥ′
   import Transition.Concur.Cofinal.Lattice.Helpers.nu-extrude-nu-extrude as ν•
   import Transition.Concur.Cofinal.Lattice.Helpers.nu-extrude-propagate-c as ν•ᶜ
   import Transition.Concur.Cofinal.Lattice.Helpers.nu-extrude-propagate-b as ν•ᵇ
   import Transition.Concur.Cofinal.Lattice.Helpers.nu-propagate-b-b as νᵇᵇ
   import Transition.Concur.Cofinal.Lattice.Helpers.nu-propagate-x-x as νˣˣ
   import Transition.Concur.Cofinal.Lattice.Helpers.nu-propagate-c-c as νᶜᶜ
   import Transition.Concur.Cofinal.Lattice.Helpers.nu-propagate-b-c as νᵇᶜ
   import Transition.Concur.Cofinal.Lattice.Helpers.nu-propagate-nu-nu as νᵛᵛ

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
   gamma₁ {𝑎 = ᵛ∇ᵛ} 𝐸 ◻ =
      refl
   gamma₁ {a = a ᵇ} {a′ ᵇ} {E = .E ᵇ│ Q₀} {E′ = P₀ │ᵇ .F} (E ᵇ│ᵇ F) [ P │ Q ] =
      let open ᵇ│ᵇ in case E F P Q
   gamma₁ (E ᵇ│ᶜ F) [ P │ Q ] =
      cong (λ Q′ → [ _ │ Q′ ]) (sym (renᶜ-tgt-comm F push Q))
   gamma₁ (E ᶜ│ᵇ F) [ P │ Q ] =
      cong (λ P′ → [ P′ │ _ ]) (renᶜ-tgt-comm E push P)
   gamma₁ (E ᶜ│ᶜ F) [ P │ Q ] =
      refl
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
   gamma₁ {E = E ᵇ│ _} {E′ = E′ │• .F} (_│•ᵇ_ {x = x} {y} {a = a} 𝐸 F) [ P │ Q ] = {!!}
{-
      with step E′ P | inspect (step E′) P
   ... | ◻ , R′ | [ ≡R′ ]
      with step (E′/E (⊖₁ 𝐸)) (tgt E P) | inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P)
   ... | ◻ , P′ | [ ≡P′ ] =
      let S† = tgt ((ᴿ.push *ᶜ) F) ((push *̃) Q); S‡ = tgt F Q in
      gamma₁-│•ᵇ 𝐸 F P Q S† S‡ R′ P′ ◻ ◻ (,-inj₂ ≡R′) (,-inj₂ ≡P′) refl refl refl (gamma₁ 𝐸 P)
   ... | [ (._ •) ᵇ ] , P′ | [ ≡P′ ] =
      ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R′))) (trans (sym (ᴬgamma₁ 𝐸 P)) (,-inj₁ ≡P′))))
   gamma₁ {E = E ᵇ│ _} {E′ │• .F} (𝐸 │•ᵇ F) [ P │ Q ] |
      [ x • ᵇ ] , R′ | [ ≡R′ ]
      with step (E′/E (⊖₁ 𝐸)) (tgt E P) | inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P) |
           step F Q | inspect (step F) Q
   ... | ◻ , P′ | [ ≡P′ ] | ◻ , S‡ | [ ≡S‡ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P′)) (trans (ᴬgamma₁ 𝐸 P) (cong (push ᴬ*̃) (,-inj₁ ≡R′)))))
   ... | [ (._ •) ᵇ ] , P′ | [ ≡P′ ] | ◻ , S‡ | [ ≡S‡ ]
      with step ((ᴿ.push *ᶜ) F) ((push *̃) Q) | inspect (step ((ᴿ.push *ᶜ) F)) ((push *̃) Q)
   ... | ◻ , S† | [ ≡S† ] =
      gamma₁-│•ᵇ 𝐸 F P Q S† S‡ R′ P′ ◻ ◻ (,-inj₂ ≡R′) (,-inj₂ ≡P′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) refl (gamma₁ 𝐸 P)
   ... | [ • ._ 〈 y′ 〉 ᶜ ] , S† | [ ≡S† ] =
      ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡S‡))) (trans (renᶜ-action-comm F push Q) (,-inj₁ ≡S†))))
   gamma₁ {E = E ᵇ│ _} {E′ │• .F} (𝐸 │•ᵇ F) [ P │ Q ] |
      [ x • ᵇ ] , R′ | [ ≡R′ ] | ◻ , P′ | [ ≡P′ ] | [ • .x 〈 y‡ 〉 ᶜ ] , S‡ | [ ≡S‡ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P′)) (trans (ᴬgamma₁ 𝐸 P) (cong (push ᴬ*̃) (,-inj₁ ≡R′)))))
   gamma₁ {E = E ᵇ│ _} {E′ │• .F} (_│•ᵇ_ {y = y} {a = a} 𝐸 F) [ P │ Q ] |
      [ x • ᵇ ] , R′ | [ ≡R′ ] | [ ._ • ᵇ ] , P′ | [ ≡P′ ] | [ • .x 〈 y‡ 〉 ᶜ ] , S‡ | [ ≡S‡ ]
      with step ((ᴿ.push *ᶜ) F) ((push *̃) Q) | inspect (step ((ᴿ.push *ᶜ) F)) ((push *̃) Q)
   ... | ◻ , S† | [ ≡S† ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡S†)) (trans (sym (renᶜ-action-comm F push Q)) (cong (push ᴬ*̃) (,-inj₁ ≡S‡)))))
   ... | [ • .(ᴺ.suc x) 〈 y† 〉 ᶜ ] , S† | [ ≡S† ] =
      let α : [ • ᴺ.suc x 〈 (push ᴿ̃.*) y‡ 〉 ᶜ ] ≡ [ • ᴺ.suc x 〈 y† 〉 ᶜ ]
          α = trans (sym (cong (push ᴬ*̃) (,-inj₁ ≡S‡))) (trans (renᶜ-action-comm F push Q) (,-inj₁ ≡S†)) in
      gamma₁-│•ᵇ 𝐸 F P Q S† S‡ R′ P′ y† y‡ (,-inj₂ ≡R′) (,-inj₂ ≡P′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (sym ([•x〈-〉ᶜ]-inj α)) (gamma₁ 𝐸 P)
-}
   gamma₁ {E = E ᶜ│ Q₀} {E′ = E′ │• .F} (_│•ᶜ_ {x = x} {y} {a = a} 𝐸 F) [ P │ Q ] = {!!}
{-
      with step E′ P | step (E′/E (⊖₁ 𝐸)) (tgt E P) | step F Q |
           inspect (step E′) P | inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P) | inspect (step F) Q
   ... | ◻ , R′ | ◻ , S† | _ , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      gamma₁-│•ᶜ 𝐸 F P Q S† S‡ R′ ◻ (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | ◻ , R′ | [ (.x •) ᵇ ] , S† | _ , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡R′)) (trans (sym (ᴬgamma₁ 𝐸 P)) (,-inj₁ ≡S†))))
   ... | [ (.x •) ᵇ ] , R′ | ◻ , S† | _ , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      ⊥-elim (◻≢[-] (sym (trans (sym (,-inj₁ ≡R′)) (trans (sym (ᴬgamma₁ 𝐸 P)) (,-inj₁ ≡S†)))))
   ... | [ (.x •) ᵇ ] , R′ | [ (.x •) ᵇ ] , S† | ◻ , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      gamma₁-│•ᶜ 𝐸 F P Q S† S‡ R′ ◻ (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
   ... | [ (.x •) ᵇ ] , R′ | [ (.x •) ᵇ ] , S† | [ • .x 〈 y‡ 〉 ᶜ ] , S‡ | [ ≡R′ ] | [ ≡S† ] | [ ≡S‡ ] =
      gamma₁-│•ᶜ 𝐸 F P Q S† S‡ R′ y‡ (,-inj₂ ≡R′) (,-inj₂ ≡S†) (,-inj₂ ≡S‡) (gamma₁ 𝐸 P)
-}
   gamma₁ {E = P₀ │ᵇ F} {E′ = .E │• F′} (_ᵇ│•_ {y = y} E 𝐹) [ P │ Q ] = {!!}
{-
      with step F′ Q | step (E′/E (⊖₁ 𝐹)) (tgt F Q) | step E P | step ((ᴿ.push *ᵇ) E) ((push *̃) P) |
           inspect (step F′) Q | inspect (step (E′/E (⊖₁ 𝐹))) (tgt F Q) | inspect (step E) P |
           inspect (step ((ᴿ.push *ᵇ) E)) ((push *̃) P)
   ... | ◻ , S′ | ◻ , Q′ | ◻ , R | ◻ , R† | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] | [ ≡R† ] =
      gamma₁-ᵇ│• E 𝐹 P Q R R† S′ Q′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R†) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl (gamma₁ 𝐹 Q)
   ... | _ | _ | [ _ ᵇ ] , R | ◻ , R† | _ | _ | [ ≡R ] | [ ≡R† ] =
      ⊥-elim (◻≢[-] (sym (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R))) (trans (renᵇ-action-comm E push P) (,-inj₁ ≡R†)))))
   ... | _ | _ | ◻ , R | [ _ ᵇ ] , R† | _ | _ | [ ≡R ] | [ ≡R† ] =
      ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R))) (trans (renᵇ-action-comm E push P) (,-inj₁ ≡R†))))
   ... | ◻ , S′ | ◻ , Q′ | [ (x •) ᵇ ] , R | [ (.(ᴺ.suc x) •) ᵇ ] , R† | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] | [ ≡R† ] =
      gamma₁-ᵇ│• E 𝐹 P Q R R† S′ Q′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R†) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl (gamma₁ 𝐹 Q)
   ... | ◻ , S′ | [ • ._ 〈 _ 〉 ᶜ ] , Q′ | _ | _ | [ ≡S′ ] | [ ≡Q′ ] | _ | _ =
      ⊥-elim (◻≢[-] (trans (sym (cong (push ᴬ*̃) (,-inj₁ ≡S′))) (trans (sym (ᴬgamma₁ 𝐹 Q)) (,-inj₁ ≡Q′))))
   ... | [ • _ 〈 _ 〉 ᶜ ] , S′ | ◻ , _ | _ | _ | [ ≡S′ ] | [ ≡Q′ ] | _ | _ =
      ⊥-elim (◻≢[-] (sym (trans (sym (cong (push ᴬ*̃) (,-inj₁ ≡S′))) (trans (sym (ᴬgamma₁ 𝐹 Q)) (,-inj₁ ≡Q′)))))
   ... | [ • x 〈 _ 〉 ᶜ ] , S′ | [ • .(ᴺ.suc x) 〈 _ 〉 ᶜ ] , Q′ | ◻ , R | ◻ , R† | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] | [ ≡R† ] =
      gamma₁-ᵇ│• E 𝐹 P Q R R† S′ Q′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡R†) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl (gamma₁ 𝐹 Q)
   ... | [ • x 〈 y‡ 〉 ᶜ ] , S′ | [ • .(ᴺ.suc x) 〈 y† 〉 ᶜ ] , Q′ | [ (.x •) ᵇ ] , R | [ .(ᴺ.suc x) • ᵇ ] , R†
       | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] | [ ≡R† ] =
      let α : [ • ᴺ.suc x 〈 (push ᴿ̃.*) y‡ 〉 ᶜ ] ≡ [ • ᴺ.suc x 〈 y† 〉 ᶜ ]
          α = trans (sym (cong (push ᴬ*̃) (,-inj₁ ≡S′))) (trans (sym (ᴬgamma₁ 𝐹 Q)) (,-inj₁ ≡Q′)) in
      gamma₁-ᵇ│• E 𝐹 P Q R R† S′ Q′ y† y‡ (,-inj₂ ≡R) (,-inj₂ ≡R†) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) (sym ([•x〈-〉ᶜ]-inj α)) (gamma₁ 𝐹 Q)
-}
   gamma₁ {E = P₀ │ᶜ F} {E′ = .E │• F′} (_ᶜ│•_ {y = y} E 𝐹) [ P │ Q ] = {!!}
{-
      with step F′ Q | step (E′/E (⊖₁ 𝐹)) (tgt F Q) | step E P |
           inspect (step F′) Q | inspect (step (E′/E (⊖₁ 𝐹))) (tgt F Q) | inspect (step E) P
   ... | ◻ , S′ | ◻ , Q′ | ◻ , R | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] =
      gamma₁-ᶜ│• E 𝐹 P Q R S′ Q′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl (gamma₁ 𝐹 Q)
   ... | ◻ , S′ | ◻ , Q′ | [ (x •) ᵇ ] , R | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] =
      gamma₁-ᶜ│• E 𝐹 P Q R S′ Q′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl (gamma₁ 𝐹 Q)
   ... | ◻ , S′ | [ _ ] , Q′ | _ | [ ≡S′ ] | [ ≡Q′ ] | _ =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡S′)) (trans (sym (ᴬgamma₁ 𝐹 Q)) (,-inj₁ ≡Q′))))
   ... | [ _ ] , S′ | ◻ , Q′ | _ | [ ≡S′ ] | [ ≡Q′ ] | _ =
      ⊥-elim (◻≢[-] (sym (trans (sym (,-inj₁ ≡S′)) (trans (sym (ᴬgamma₁ 𝐹 Q)) (,-inj₁ ≡Q′)))))
   ... | [ _ ᶜ ] , S′ | [ _ ᶜ ] , Q′ | ◻ , R | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] =
      gamma₁-ᶜ│• E 𝐹 P Q R S′ Q′ ◻ ◻ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) refl (gamma₁ 𝐹 Q)
   ... | [ • x 〈 y† 〉 ᶜ ] , S′ | [ • .x 〈 y‡ 〉 ᶜ ] , Q′ | [ (.x •) ᵇ ] , R | [ ≡S′ ] | [ ≡Q′ ] | [ ≡R ] =
      let α : [ • x 〈 y‡ 〉 ᶜ ] ≡ [ • x 〈 y† 〉 ᶜ ]
          α = trans (sym (,-inj₁ ≡Q′)) (trans (ᴬgamma₁ 𝐹 Q) (,-inj₁ ≡S′)) in
      gamma₁-ᶜ│• E 𝐹 P Q R S′ Q′ y† y‡ (,-inj₂ ≡R) (,-inj₂ ≡S′) (,-inj₂ ≡Q′) (sym ([•x〈-〉ᶜ]-inj α)) (gamma₁ 𝐹 Q)
-}
   gamma₁ {E = E ᵇ│ Q₀} {E′ │ᵥ .F} (_│ᵥᵇ_ {x = x} {a = x′ •} 𝐸 F) [ P │ Q ] = {!!}
{-
      with (idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) | step E′ P | step F Q | step (E′/E (⊖₁ 𝐸)) (tgt E P) |
           step ((ᴿ.push *ᵇ) F) ((push *̃) Q) | inspect (idᶠ *ᵇ) (E/E′ (⊖₁ 𝐸)) | inspect (step E′) P |
           inspect (step F) Q | inspect (step (E′/E (⊖₁ 𝐸))) (tgt E P) | inspect (step ((ᴿ.push *ᵇ) F)) ((push *̃) Q)
   ... | id*E/E′ | [ ._ • ᵇ ] , R′ | _ , S | ◻ , P′ | _ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡P′)) (trans (π₁ (ᴬgamma₁ 𝐸 P)) (cong (push ᴬ*̃) (,-inj₁ ≡R′)))))
   ... | id*E/E′ | ◻ , R′ | _ , S | [ ._ • ᵇ ] , P′ | _ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡R′))) (trans (sym (π₁ (ᴬgamma₁ 𝐸 P))) (,-inj₁ ≡P′))))
   ... | id*E/E′ | _ , R′ | [ (• ._) ᵇ ] , S | _ , P′ | ◻ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      ⊥-elim (◻≢[-] (trans (sym (,-inj₁ ≡S′)) (trans (sym (renᵇ-action-comm F push Q)) (cong (push ᴬ*̃) (,-inj₁ ≡S)))))
   ... | id*E/E′ | _ , R′ | ◻ , S | _ , P′ | [ (• ._) ᵇ ] , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      ⊥-elim (◻≢[-] (trans (cong (push ᴬ*̃) (sym (,-inj₁ ≡S))) (trans (renᵇ-action-comm F push Q) (,-inj₁ ≡S′))))
   ... | id*E/E′ | ◻ , R′ | ◻ , S | ◻ , P′ | ◻ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      let open │ᵥᵇ-x• 𝐸 F P Q P′ S′ id*E/E′ S R′ ◻
                     ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in
      case
   ... | id*E/E′ | ◻ , R′ | [ (• ._) ᵇ ] , S | ◻ , P′ | [ (• ._) ᵇ ] , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      let open │ᵥᵇ-x• 𝐸 F P Q P′ S′ id*E/E′ S R′ ◻
                     ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in
      case
   ... | id*E/E′ | [ ._ • ᵇ ] , R′ | ◻ , S | [ ._ • ᵇ ] , P′ | ◻ , S′ | [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      let open │ᵥᵇ-x• 𝐸 F P Q P′ S′ id*E/E′ S R′ ◻
                     ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in
      case
   ... | id*E/E′ | [ ._ • ᵇ ] , R′ | [ (• ._) ᵇ ] , S | [ ._ • ᵇ ] , P′ | [ (• ._) ᵇ ] , S′ |
      [ ≡id*E/E′ ] | [ ≡R′ ] | [ ≡S ] | [ ≡P′ ] | [ ≡S′ ] =
      let open │ᵥᵇ-x• 𝐸 F P Q P′ S′ id*E/E′ S R′ [ ᴺ.zero ]
                     ≡id*E/E′ (,-inj₂ ≡P′) (,-inj₂ ≡S) (,-inj₂ ≡S′) (,-inj₂ ≡R′) (gamma₁ 𝐸 P) in
      case
-}
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
   gamma₁ (E ᶜ│ᵥ 𝐸) P = trustMe
   gamma₁ (𝐸 │• 𝐹) P = trustMe
   gamma₁ (𝐸 │•ᵥ 𝐹) P = trustMe
   gamma₁ {E = E │ᵥ F} {E′ │ᵥ F′} (𝐸 │ᵥ 𝐹) [ P │ Q ] =
      let open │ᵥ in case 𝐸 𝐹 P Q (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q)
   gamma₁ {E = E │ᵥ F} {E′ │ᵥ F′} (𝐸 │ᵥ′ 𝐹) [ P │ Q ] =
      let open │ᵥ′ in case 𝐸 𝐹 P Q (gamma₁ 𝐸 P) (gamma₁ 𝐹 Q)
   gamma₁ {E = ν• E} {ν• E′} (ν• 𝐸) [ ν P ] =
      let open ν• in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a′ = • x 〈 y 〉 ᶜ} {E = ν• E} {νᶜ E′} (ν•ᶜ 𝐸) [ ν P ] =
      let open ν•ᶜ.•x〈y〉 in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a′ = τ ᶜ} {E = ν• E} {νᶜ E′} (ν•ᶜ 𝐸) [ ν P ] =
      let open ν•ᶜ.τ in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a′ = x • ᵇ} {E = ν• E} {νᵇ E′} (ν•ᵇ 𝐸) [ ν P ] =
      let open ν•ᵇ.x• in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a′ = (• x) ᵇ} {E = ν• E} {νᵇ E′} (ν•ᵇ 𝐸) [ ν P ] =
      let open ν•ᵇ.•x in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {x′ • ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] =
      let open νᵇᵇ.x•-x• in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {(• x′) ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] =
      let open νᵇᵇ.x•-•x in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {(x′ •) ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] =
      let open νᵇᵇ.•x-x• in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {(• x′) ᵇ} {E = νᵇ E} {νᵇ E′} (νᵇᵇ 𝐸) [ ν P ] =
      let open νᵇᵇ.•x-•x in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {E = νᵇ E} {νᵇ E′} (νˣˣ 𝐸) [ ν P ] =
      let open νˣˣ in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {• x′ 〈 y 〉 ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] =
      let open νᵇᶜ.x•-•x〈y〉 in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = x • ᵇ} {τ ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] =
      let open νᵇᶜ.x•-τ in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {• x′ 〈 y 〉 ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] =
      let open νᵇᶜ.•x-•x〈y〉 in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = (• x) ᵇ} {τ ᶜ} {E = νᵇ E} {νᶜ E′} (νᵇᶜ 𝐸) [ ν P ] =
      let open νᵇᶜ.•x-τ in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = • x 〈 y 〉 ᶜ} {• x′ 〈 y′ 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] =
      let open νᶜᶜ.•x〈y〉-•x〈y〉 in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = • x 〈 y 〉 ᶜ} {τ ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] =
      let open νᶜᶜ.•x〈y〉-τ in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = τ ᶜ} {• x 〈 y 〉 ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] =
      let open νᶜᶜ.τ-•x〈y〉 in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {a = τ ᶜ} {τ ᶜ} {E = νᶜ E} {νᶜ E′} (νᶜᶜ 𝐸) [ ν P ] =
      let open νᶜᶜ.τ-τ in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ {E = νᶜ E} {νᶜ E′} (νᵛᵛ 𝐸) [ ν P ] =
      let open νᵛᵛ in case 𝐸 P (gamma₁ 𝐸 P)
   gamma₁ (! 𝐸) [ ! P ] = gamma₁ 𝐸 [ P │ [ ! P ] ]
