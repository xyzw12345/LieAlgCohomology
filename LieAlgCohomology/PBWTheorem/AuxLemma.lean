import Mathlib
import LieAlgCohomology.PBWTheorem.SymmetricAlgebra

noncomputable section

variable (R : Type*) [CommRing R]
variable (B : Type*) [LinearOrder B] [LieRing (B →₀ R)] [LieAlgebra R (B →₀ R)]
#check FreeAlgebra R B
#check MvPolynomial B R
#synth Module R (B →₀ R)
#check TensorAlgebra.equivFreeAlgebra



def π : FreeAlgebra R B →ₐ[R] MvPolynomial B R :=
  FreeAlgebra.lift R (fun b ↦ MvPolynomial.X b)

def ω' : FreeAlgebra R B →ₐ[R] UniversalEnvelopingAlgebra R (B →₀ R) :=
  sorry

/-
x : FreeAlgebra R B, x', ω' x = 0 → π x' = 0
ω' : FreeAlgebra R B →ₐ[R] UniversalEnvelopingAlgebra R (B →₀ R)
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
