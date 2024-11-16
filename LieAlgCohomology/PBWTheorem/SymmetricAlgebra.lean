import Mathlib

namespace SymmetricAlgebra

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

variable (B : Type*)

def symmetric_algebra_iso_mv_polynomial : 𝔖 R (B →₀ R) ≃ₐ[R] MvPolynomial B R := sorry

#synth Module.Free R (B →₀ R)
