# concurrent-slicing

Agda development accompanying the paper _Causally consistent dynamic
slicing_, accepted to CONCUR 2016. To typecheck the entire development,
compile `ConcurrentSlicing.agda`. The module structure is summarised in
Appendix A of the paper.

## Required compiler and libraries:

* Agda, version 2.4.2.3 (doesn't compile under 2.5.1)
* Agda standard library version 0.9
* `agda-stdlib-ext`, version [0.0.2] (https://github.com/rolyp/agda-stdlib-ext/releases/tag/0.0.2)
* `proof-relevant-pi`, version [0.2] (https://github.com/rolyp/proof-relevant-pi/releases/tag/0.2)

### Minor todos:

* Sync Agda names with paper:
  * `∘ᶠ` → `∘ᶠ`, `idᶠ` → `id`
  * `tgt` → `fwd` ?
  * `get`/`put` → `app`/`unapp`
* Bump revision numbers for `agda-stdlib-ext`, `proof-relevant-pi` and `concurrent-slicing`

### Postulates which will remain postulates:

* `Proc.Ren.Lattice.*-preserves-≃ₑ` and `*-preserves-∘`
* `Ren.Lattice.Properties` postulate counterpart to `Ren.Properties`
* `Transition.Ren.Lattice` postulates
* `Transition.Concur.Cofinal.Lattice.Common.ᴬgamma₁`
