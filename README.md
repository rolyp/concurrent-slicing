# concurrent-slicing, release 0.1

Agda development accompanying the paper
[Causally consistent dynamic slicing](http://dynamicaspects.org/papers/concur16.pdf),
presented at CONCUR 2016. To typecheck the entire development, compile
`ConcurrentSlicing.agda`. The module structure is summarised in Appendix
A of the paper.

## Required compiler and libraries:

* Agda, version 2.4.2.3; there seems to be a problem with typeclass resolution under 2.5.1.
* Agda standard library version 0.9.
* `agda-stdlib-ext`, version [0.0.3](https://github.com/rolyp/agda-stdlib-ext/releases/tag/0.0.3).
* `proof-relevant-pi`, version [0.3](https://github.com/rolyp/proof-relevant-pi/releases/tag/0.3).

### Future to-do items:

* Improvements to names (more conventional or more aligned with paper):
  * `∘ᶠ` → `∘`, `idᶠ` → `id`
  * `tgt` → `fwd` ?
  * `get`/`put` → `app`/`unapp`

### Postulates which will remain postulates:

I made a strategic decision to leave certain aspects of the development
unformalised. The main parts are listed here:

* `Proc.Ren.Lattice.*-preserves-≃ₑ` and `*-preserves-∘`
* `Ren.Lattice.Properties` counterpart to `Ren.Properties`
* `Transition.Ren.Lattice` postulates
* `Transition.Concur.Cofinal.Lattice.Common.ᴬgamma₁`
