# concurrent-slicing

Agda development accompanying the paper _Causally consistent dynamic
slicing_, submitted to CONCUR 2016. To typecheck the entire development,
compile `ConcurrentSlicing.agda`. The module structure is summarised in
Appendix A of the paper.

## Required compiler and libraries:

* Agda, version 2.4.2.3
* Agda standard library version 0.9
* `agda-stdlib-ext`, version [0.0.2] (https://github.com/rolyp/agda-stdlib-ext/releases/tag/0.0.2)
* `proof-relevant-pi`, version [0.2] (https://github.com/rolyp/proof-relevant-pi/releases/tag/0.2)

### Minor todos:

* Functor-like postulates in `Proc.Ren.Lattice`:
  * `*-preserves-≃ₑ`
  * `*-preserves-∘`
* Better names in Galois connection for transition sequences
* Easy postulates in `Transition.Lattice`
* `target⋆ᴹ` for transition sequences
* Example
* Agda names with paper:
  * cofin
* Bump revision numbers for `agda-stdlib-ext`, `proof-relevant-pi` and `concurrent-slicing`
