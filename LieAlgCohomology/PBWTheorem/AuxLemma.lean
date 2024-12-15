import Mathlib

noncomputable section

variable (R : Type*) [CommRing R]
variable (L : Type*) [LieRing L] [LieAlgebra R L] [Module.Free R L]
variable (B : Type*) (basis : Basis B R L) [LinearOrder B]

def π : FreeAlgebra R B →ₐ[R] MvPolynomial B R :=
  FreeAlgebra.lift R (fun b ↦ MvPolynomial.X b)

abbrev iso : FreeAlgebra R B ≃ₐ[R] TensorAlgebra R L :=
  (TensorAlgebra.equivFreeAlgebra basis).symm

def ω' : FreeAlgebra R B →ₐ[R] UniversalEnvelopingAlgebra R L :=
  (UniversalEnvelopingAlgebra.mkAlgHom R L).comp (iso R L B basis).toAlgHom

/-
x : FreeAlgebra R B, x', ω' x = 0 → π x' = 0
ω' : FreeAlgebra R B →ₐ[R] UniversalEnvelopingAlgebra R L
π : FreeAlgebra R B →ₐ[R] MvPolynomial B R
-/

theorem lemma_C : 1 + 1 = 2 := rfl

/-
TODO :
1. GradedRing structure on FreeAlgebra. (put it in MissingLemmas folder).
2. Take maximum degree component in GradedRing(?)/FreeAlgebra(?).
3. Finish the statement of lemma_C as above.
4. Find a way to inductively define the Lie Action on (MvPolynomial B R).
 (corresponding to Lemma A and Lemma B)
-/
