import Mathlib
import FilteredRing.graded

noncomputable section

abbrev MvPolynomial.filtration (σ R : Type*) [CommSemiring R]
  := induced_fil' (MvPolynomial.homogeneousSubmodule σ R)

variable (R : Type*) [CommRing R]
variable (L : Type*) [LieRing L] [LieAlgebra R L] [Module.Free R L]
variable (B : Type*) (basis : Basis B R L) [LinearOrder B]

#check (MvPolynomial.gradedAlgebra (σ := B) (R := R))

attribute [local instance] MvPolynomial.gradedAlgebra

#synth GradedAlgebra (MvPolynomial.homogeneousSubmodule B R)

#synth FilteredAlgebra (MvPolynomial.filtration B R)

-- def π : FreeAlgebra R B →ₐ[R] MvPolynomial B R :=
--   FreeAlgebra.lift R (fun b ↦ MvPolynomial.X b)

-- abbrev iso : FreeAlgebra R B ≃ₐ[R] TensorAlgebra R L :=
--   (TensorAlgebra.equivFreeAlgebra basis).symm

-- def ω' : FreeAlgebra R B →ₐ[R] UniversalEnvelopingAlgebra R L :=
--   (UniversalEnvelopingAlgebra.mkAlgHom R L).comp (iso R L B basis).toAlgHom

open MvPolynomial

def AuxLieActionMap (m : ℕ) : L →ₗ[R] (filtration B R m →ₗ[R] MvPolynomial B R) := sorry
