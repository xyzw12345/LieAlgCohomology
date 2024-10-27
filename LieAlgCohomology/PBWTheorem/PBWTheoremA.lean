import Mathlib

open BigOperators TensorProduct DirectSum TensorAlgebra UniversalEnvelopingAlgebra
-- import Mathlib.RingTheory.TensorProduct.Basic

-- set_option diagnostics true
noncomputable section
variable (R : Type*) [CommRing R]
variable (L : Type*) [AddCommMonoid L] [Module R L] [LieRing L] [LieAlgebra R L] [Module.Free R L]

local notation "ιₜ" => TensorAlgebra.ι R
local notation "𝔘" => UniversalEnvelopingAlgebra

local notation "π₁" => mkAlgHom

abbrev 𝔗 := TensorAlgebra R L

def I := TwoSidedIdeal.span {(ιₜ x * ιₜ y - ιₜ y * ιₜ x) | (x : L) (y : L)}

-- The 𝔖 defined here is the symmetric algebra.
def 𝔖 := RingQuot (I R L).ringCon.r

instance : Ring (𝔖 R L) := inferInstanceAs (Ring (RingQuot (I R L).ringCon.r))

instance : Algebra R (𝔖 R L) := inferInstanceAs (Algebra R (RingQuot (I R L).ringCon.r))

def J := TwoSidedIdeal.span {ιₜ x * ιₜ y - ιₜ y * ιₜ x - ιₜ ⁅x, y⁆ | (x : L) (y : L)}

#synth GradedRing ((LinearMap.range (ι R : L →ₗ[R] TensorAlgebra R L) ^ ·))

def filtration (m : ℕ) (T : Type*) [AddCommMonoid T] [Module R T] : Submodule R T := sorry

def T (m : ℕ) := filtration (R := R) m (TensorAlgebra R L)

def equiv_finite_directSum : T R L m ≃ₗ[R] (⨁ (i : Fin (m + 1)), ⨂[R]^i L) := sorry

-- theorem PBW : Nonempty (𝔖 R L →ₐ[k] 𝔊 R L) := sorry
