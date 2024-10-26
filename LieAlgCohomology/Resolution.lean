import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.LinearAlgebra.TensorProduct.Basic
import LieAlgCohomology.Representation

-- to be added: `Module.Free.exteriorProduct`

suppress_compilation

open CategoryTheory
open LieModuleCat
open scoped TensorProduct

universe u v w

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

#check ChainComplex
#synth Category (LieModuleCat R L)

def resolution_object (n : ℕ) : LieModuleCat R L :=
  (ofModuleUniversalAlgebra R L).obj <| (ModuleCat.of (UniversalEnvelopingAlgebra R L) ((UniversalEnvelopingAlgebra R L) ⨂[R] ))
  sorry

def LieAlgCohomology.resolution : ChainComplex (LieModuleCat R L) ℕ :=
  ChainComplex.of _ ℕ
