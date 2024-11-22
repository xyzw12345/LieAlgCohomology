import Mathlib

namespace SymmetricAlg

open MvPolynomial RingQuot

noncomputable section
variable (R : Type*) [CommRing R]
variable (L : Type*) [AddCommMonoid L] [Module R L]
local notation "ι" => TensorAlgebra.ι R

-- def I := TwoSidedIdeal.span {(ιₜ x * ιₜ y - ιₜ y * ιₜ x) | (x : L) (y : L)}

inductive SymRel : (TensorAlgebra R L) → (TensorAlgebra R L) → Prop :=
  | mul_comm (x y : L) : SymRel (ι x * ι y) (ι y * ι x)

def SymmetricAlgebra := RingQuot (SymRel R L)

local notation "𝔖" => SymmetricAlgebra

instance : Ring (𝔖 R L) := inferInstanceAs (Ring (RingQuot (SymRel R L)))

instance : Algebra R (𝔖 R L) := inferInstanceAs (Algebra R (RingQuot (SymRel R L)))

instance : CommRing (𝔖 R L) where
  mul_comm := sorry

variable {I : Type*}

lemma mv_polynomial_ext {S : Type*} [CommSemiring S] [Algebra R S] (f g : MvPolynomial I R →ₐ[R] S) (h : ∀ i : I, f (X i) = g (X i)) : f = g := by sorry

variable (I)

def symmetric_algebra_iso_mv_polynomial : MvPolynomial I R ≃ₐ[R] 𝔖 R (I →₀ R) :=
  AlgEquiv.ofAlgHom
    ⟨eval₂Hom (algebraMap R (𝔖 R (I →₀ R))) (fun i ↦ mkRingHom _ (ι (Finsupp.single i (1 : R)))), fun _ ↦ eval₂_C _ _ _⟩
    (liftAlgHom R ⟨TensorAlgebra.lift R (Finsupp.linearCombination R (fun (i : I) ↦ ((X i) : MvPolynomial I R))), fun {u v} h ↦ match h with | SymRel.mul_comm x y => by simp [mul_comm]⟩)
    (by
      apply ringQuot_ext'; ext i
      simp [SymmetricAlgebra]; rw [mkAlgHom, AlgHom.coe_mk])
    (by
      apply mv_polynomial_ext; intro i
      simp
      have h1 : ((mkRingHom (SymRel R (I →₀ R))) (ι fun₀ | i => 1)) = ((mkAlgHom R (SymRel R (I →₀ R))) (ι fun₀ | i => 1)) := by rw [mkAlgHom, AlgHom.coe_mk]
      have h2 : (TensorAlgebra.lift R) (Finsupp.linearCombination R (fun (i : I) ↦ ((X i) : MvPolynomial I R))) (ι fun₀ | i => 1) = X i := by simp
      rw [← h2, h1]
      apply liftAlgHom_mkAlgHom_apply)


-- Want to show that this equivalence actually preserves the graded structure on 𝔖
