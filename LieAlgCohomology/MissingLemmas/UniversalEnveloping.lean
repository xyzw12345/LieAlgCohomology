import Mathlib.Algebra.Lie.UniversalEnveloping

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

namespace UniversalEnvelopingAlgebra

theorem induction {C : UniversalEnvelopingAlgebra R L → Prop}
  (basis_R : ∀ r : R, C (algebraMap R (UniversalEnvelopingAlgebra R L) r))
  (basis_L : ∀ l : L, C (UniversalEnvelopingAlgebra.ι R l))
  (mul : ∀ a b, C a → C b → C (a * b)) (add : ∀ a b, C a → C b → C (a + b))
  (a : UniversalEnvelopingAlgebra R L) : C a := by
    have h1 : (UniversalEnvelopingAlgebra.mkAlgHom R L).toFun.Surjective := by
      apply RingQuot.mkAlgHom_surjective
    have h2 (a' : TensorAlgebra R L) : C ((UniversalEnvelopingAlgebra.mkAlgHom R L) a') := by
      apply TensorAlgebra.induction (C := fun x ↦ (C ((UniversalEnvelopingAlgebra.mkAlgHom R L) x)))
      · intro r; rw [AlgHom.commutes]; apply basis_R
      · intro l; apply basis_L
      · intro a b; rw [map_mul]; apply mul
      · intro a b; rw [map_add]; apply add
    obtain ⟨u, hu⟩ := h1 a
    exact hu ▸ h2 u

end UniversalEnvelopingAlgebra
