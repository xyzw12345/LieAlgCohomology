import Mathlib

open BigOperators TensorProduct DirectSum TensorAlgebra UniversalEnvelopingAlgebra

-- set_option diagnostics true
noncomputable section
variable (R : Type*) [CommRing R]
variable (L : Type*) [i13: LieRing L] [i14: LieAlgebra R L] [Module.Free R L]

local notation "ιₜ" => TensorAlgebra.ι R
local notation "𝔘" => UniversalEnvelopingAlgebra
local notation "π₁" => mkAlgHom
-- local notation "𝔗" => TensorAlgebra

abbrev 𝔗 := TensorAlgebra R L

#check MvPolynomial
#synth Algebra R (MvPolynomial L R)
#synth Module R (𝔗 R L)

def I := TwoSidedIdeal.span {(ιₜ x * ιₜ y - ιₜ y * ιₜ x) | (x : L) (y : L)}

-- The 𝔖 defined here is the symmetric algebra.
def 𝔖 := RingQuot (I R L).ringCon.r

instance : Ring (𝔖 R L) := inferInstanceAs (Ring (RingQuot (I R L).ringCon.r))

instance : Algebra R (𝔖 R L) := inferInstanceAs (Algebra R (RingQuot (I R L).ringCon.r))

def J := TwoSidedIdeal.span {ιₜ x * ιₜ y - ιₜ y * ιₜ x - ιₜ ⁅x, y⁆ | (x : L) (y : L)}

#synth GradedRing ((LinearMap.range (ι R : L →ₗ[R] TensorAlgebra R L) ^ ·))

abbrev graded_T (n : ℕ) := (LinearMap.range (ι R : L →ₗ[R] TensorAlgebra R L) ^ n)

abbrev filter_T (n : ℕ) := ⨆ (m : Fin (n + 1)), (graded_T R L m.1)

def filter_U (n : ℕ) : Submodule R (𝔘 R L) :=
  Submodule.map (π₁ R L) (filter_T R L n)

#synth GradedRing (graded_T R L)

def filter_U' (n : ℕ) : Submodule R (filter_U R L (n + 1)) := by sorry

set_option diagnostics true
abbrev graded_G (n : ℕ) := (filter_U R L (n + 1)) ⧸ (filter_U' R L n)

abbrev 𝔊 := ⨁ (n : ℕ), (graded_G R L n)

instance : Ring (𝔊 R L) := sorry

instance : Algebra R (𝔊 R L) := sorry

def ω' : (𝔗 R L) →ₐ[R] (𝔊 R L) := sorry
def ω : (𝔖 R L) →ₐ[R] (𝔊 R L) := sorry

theorem PBW_A : Function.Bijective (ω R L) := sorry
