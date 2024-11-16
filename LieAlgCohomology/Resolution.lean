import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import LieAlgCohomology.Representation

-- to be added: `Module.Free.exteriorProduct`

suppress_compilation

namespace LieModuleCat

open CategoryTheory
open LieModuleCat
open scoped TensorProduct
open scoped ExteriorAlgebra

universe u v w

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

#check ChainComplex
#synth Category (LieModuleCat R L)
#check Functor

scoped notation "𝔘" => UniversalEnvelopingAlgebra

def resolution_object (n : ℕ) : LieModuleCat R L :=
  (ofModuleUniversalAlgebra R L).obj ((ModuleCat.of (𝔘 R L) ((𝔘 R L) ⊗[R] (⋀[R]^n L))))

def d' (n : ℕ) : ((𝔘 R L) ⊗[R] (⋀[R]^(n + 1) L)) →ₗ[𝔘 R L] ((𝔘 R L) ⊗[R] (⋀[R]^n L)) := by sorry

def d (n : ℕ) : resolution_object R L (n + 1) ⟶ resolution_object R L n :=
  (ofModuleUniversalAlgebra R L).map (ModuleCat.ofHom (d' R L n))

def d_eq (n : ℕ) : d R L (n + 1) ≫ d R L n = 0 := by
  rw [d, d, ← (ofModuleUniversalAlgebra R L).map_comp]
  sorry

def LieAlgCohomology.resolution : ChainComplex (LieModuleCat R L) ℕ :=
  ChainComplex.of (resolution_object R L) (d R L) (d_eq R L)



end LieModuleCat
