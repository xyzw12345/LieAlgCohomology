import Mathlib

namespace SymmetricAlgebra

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
  mul_comm a b := match a, b with
    | ⟨a⟩, ⟨b⟩ => by
      apply Quot.ind _ a; apply Quot.ind _ b; intro a b;
      rw [mul_quot, mul_quot]
      suffices h : ∀ (x : TensorAlgebra R L), (⟨Quot.mk (RingQuot.Rel (SymRel R L)) (x * a)⟩ : (RingQuot (SymRel R L))) = ⟨Quot.mk (RingQuot.Rel (SymRel R L)) (a * x)⟩ by
        exact (h b)
      let P : TensorAlgebra R L → TensorAlgebra R L → Prop := fun x y ↦ (⟨Quot.mk (RingQuot.Rel (SymRel R L)) (x * y)⟩ : (RingQuot (SymRel R L))) = ⟨Quot.mk (RingQuot.Rel (SymRel R L)) (y * x)⟩
      have P_smul (r : R) (x : TensorAlgebra R L) : P x (algebraMap R (TensorAlgebra R L) r) := by
        unfold P; rw [Algebra.commutes]
      have P_mul (x y z : TensorAlgebra R L) (h1 : P z x) (h2 : P z y) : P z (x * y) := by
        unfold P at h1 h2 ⊢
        rw [← mul_quot, ← mul_quot, ← mul_quot, ← mul_quot, ← mul_assoc, mul_quot, h1, ← mul_quot, mul_assoc, mul_quot, h2, ← mul_quot, mul_assoc]
      have P_add (x y z : TensorAlgebra R L) (h1 : P z x) (h2 : P z y) : P z (x + y) := by
        unfold P at h1 h2 ⊢
        rw [mul_add, add_mul, ← add_quot, ← add_quot, h1, h2]
      have P_symm {x y : TensorAlgebra R L} (h : P x y) : P y x := h.symm
      have P_base (x y : L) : P (ι x) (ι y) := by
        unfold P
        rw [Quot.sound (Rel.of (SymRel.mul_comm x y))]
      apply TensorAlgebra.induction (C := fun y ↦ ∀ (x : TensorAlgebra R L), P x y) _ _ _ _ a
      · intro r; exact P_smul r
      · intro x; apply TensorAlgebra.induction
        · intro r; exact P_symm (P_smul r (ι x))
        · intro y; exact P_base y x
        · intro a1 a2 h1 h2; exact P_symm (P_mul a1 a2 (ι x) (P_symm h1) (P_symm h2))
        · intro a1 a2 h1 h2; exact P_symm (P_add a1 a2 (ι x) (P_symm h1) (P_symm h2))
      · intro a1 a2 h1 h2 x; exact P_mul a1 a2 x (h1 x) (h2 x)
      · intro a1 a2 h1 h2 x; exact P_add a1 a2 x (h1 x) (h2 x)

variable (I : Type*)

def symmetric_algebra_iso_mv_polynomial : MvPolynomial I R ≃ₐ[R] 𝔖 R (I →₀ R) :=
  AlgEquiv.ofAlgHom
    ⟨eval₂Hom (algebraMap R (𝔖 R (I →₀ R))) (fun i ↦ mkRingHom _ (ι (Finsupp.single i (1 : R)))), fun _ ↦ eval₂_C _ _ _⟩
    (liftAlgHom R ⟨TensorAlgebra.lift R (Finsupp.linearCombination R (fun (i : I) ↦ ((X i) : MvPolynomial I R))), fun {u v} h ↦ match h with | SymRel.mul_comm x y => by simp [mul_comm]⟩)
    (by
      apply ringQuot_ext'; ext i
      simp [SymmetricAlgebra]; rw [mkAlgHom, AlgHom.coe_mk])
    (by
      apply algHom_ext; intro i
      simp
      have h1 : ((mkRingHom (SymRel R (I →₀ R))) (ι fun₀ | i => 1)) = ((mkAlgHom R (SymRel R (I →₀ R))) (ι fun₀ | i => 1)) := by rw [mkAlgHom, AlgHom.coe_mk]
      have h2 : (TensorAlgebra.lift R) (Finsupp.linearCombination R (fun (i : I) ↦ ((X i) : MvPolynomial I R))) (ι fun₀ | i => 1) = X i := by simp
      rw [← h2, h1]
      apply liftAlgHom_mkAlgHom_apply)

-- Want to show that this equivalence actually preserves the graded structure on 𝔖
