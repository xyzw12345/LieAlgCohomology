import Mathlib
import LieAlgCohomology.PBWTheorem.SymmetricAlgebra

open BigOperators TensorProduct DirectSum TensorAlgebra UniversalEnvelopingAlgebra SymmetricAlgebra

/-
The work on this file might have to stop for a while, as we're now communicating
with the group that's working on graded/filtered objects since most constructions seems to
be more generally applicable. They'll probably write something of more general usage, and
we'll use those APIs after they've finished.

So the current work will be focusing on the other missing things like symmetric algebra and
some specific constructions in the proof.
-/

noncomputable section
variable (R : Type*) [CommRing R]
variable (L : Type*) [LieRing L] [LieAlgebra R L] [Module.Free R L]

local notation "ιₜ" => TensorAlgebra.ι R
local notation "𝔘" => UniversalEnvelopingAlgebra
local notation "π₁" => mkAlgHom
local notation "𝔖" => SymmetricAlgebra

abbrev 𝔗 := TensorAlgebra

#synth GradedRing ((LinearMap.range (ι R : L →ₗ[R] TensorAlgebra R L) ^ ·))

abbrev graded_T (n : ℕ) := (LinearMap.range (ι R : L →ₗ[R] TensorAlgebra R L) ^ n)

abbrev filter_T (n : ℕ) := ⨆ (m : Fin (n + 1)), (graded_T R L m.1)

def filter_U (n : ℕ) : Submodule R (𝔘 R L) :=
  Submodule.map (π₁ R L) (filter_T R L n)

#synth GradedRing (graded_T R L)

def filter_U' (n : ℕ) : Submodule R (filter_U R L (n + 1)) := by sorry

-- set_option diagnostics true
abbrev graded_G (n : ℕ) := (filter_U R L (n + 1)) ⧸ (filter_U' R L n)

abbrev 𝔊 := ⨁ (n : ℕ), (graded_G R L n)

instance : Ring (𝔊 R L) := sorry

instance : Algebra R (𝔊 R L) := sorry

def ω' : (𝔗 R L) →ₐ[R] (𝔊 R L) := sorry

lemma ω'_liftable (x y : L) : (ω' R L) (ιₜ x * ιₜ y) = (ω' R L) (ιₜ y * ιₜ x) := by
  sorry

lemma ω'_liftable' (x y : 𝔗 R L) : SymRel R L x y → (ω' R L) x = (ω' R L) y := fun h ↦ (
  match h with
  | SymRel.mul_comm u v => ω'_liftable R L u v
)

def ω : (𝔖 R L) →ₐ[R] (𝔊 R L) := by
  show (RingQuot (SymRel R L)) →ₐ[R] (𝔊 R L)
  refine RingQuot.liftAlgHom R (A := 𝔗 R L) (B := 𝔊 R L) ⟨ω' R L, ω'_liftable' R L⟩

theorem PBW_A : Function.Bijective (ω R L) := sorry
