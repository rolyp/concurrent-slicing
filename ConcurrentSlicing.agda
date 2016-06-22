-- Compile to validate the whole development. TODO: add a makefile for this.
module ConcurrentSlicing where

   open import ConcurrentSlicingCommon
   open import Action.Lattice
   open import Braiding.Proc.Lattice
   open import Braiding.Proc.Lattice.GaloisConnection
   open import Lattice
   open import Lattice.Product
   open import Name.Lattice
   open import Proc.Lattice
   open import Proc.Ren.Lattice
   open import Proc.Ren.Lattice.GaloisConnection
   open import Ren.Lattice
   open import Ren.Lattice.GaloisConnection
   open import Ren.Lattice.Properties
   open import Transition.Concur.Cofinal.Lattice
   open import Transition.Concur.Cofinal.Lattice.GaloisConnection
   open import Transition.Lattice
   open import Transition.Lattice.GaloisConnection
   open import Transition.Ren.Lattice
   open import Transition.Seq.Lattice
   open import Transition.Seq.Lattice.GaloisConnection
