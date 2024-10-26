import Mathlib

open BigOperators TensorProduct DirectSum TensorAlgebra
-- import Mathlib.RingTheory.TensorProduct.Basic

-- set_option diagnostics true
noncomputable section
variable (k : Type*) [Field k]
variable (V : Type*) [AddCommMonoid V] [Module k V] [LieRing V] [LieAlgebra k V]

local notation "ιₜ" => TensorAlgebra.ι k

#check ⨂[k]^2 V
#check V⊗[k]V

-- instance : Ring (TensorProduct k V V) := sorry

-- def TensorProduct.two_equiv : V⊗[k]V ≃ₗ[k] ⨂[k]^2 V := by
--   have h1 : TensorProduct k (⨂[k]^1 V) (⨂[k]^1 V) ≃ₗ[k] TensorPower k 2 V := by
--     apply TensorPower.mulEquiv
--   have h2 : V⊗[k]V ≃ₗ[k] ⨂[k]^1 V ⊗[k] ⨂[k]^1 V := by
--     refine (congr ?f ?g).symm
--     · refine PiTensorProduct.subsingletonEquiv ?f.i₀
--       exact Fin.last 0
--     · refine PiTensorProduct.subsingletonEquiv ?f.i₀
--       -- exact Fin.last 0
--   exact h2.trans h1

-- def TensorProduct.toTensorPower (v : V⊗[k]V) : ⨂[k]^2 V :=
--   (TensorProduct.two_equiv k V).toFun v

-- def 𝔗' := ⨁ n, ⨂[k]^n V

abbrev 𝔗 := TensorAlgebra k V

def I := TwoSidedIdeal.span {(ιₜ x * ιₜ y - ιₜ y * ιₜ x) | (x : V) (y : V)}

/-
  The 𝔖 defined here is the symmetric algebra.
-/
def 𝔖 := RingQuot (I k V).ringCon.r

#check 𝔖 k V

instance : Ring (𝔖 k V) := inferInstanceAs (Ring (RingQuot (I k V).ringCon.r))

instance : Algebra k (𝔖 k V) := inferInstanceAs (Algebra k (RingQuot (I k V).ringCon.r))

def J := TwoSidedIdeal.span {ιₜ x * ιₜ y - ιₜ y * ιₜ x - ιₜ ⁅x, y⁆ | (x : V) (y : V)}

#synth GradedRing ((LinearMap.range (ι k : V →ₗ[k] TensorAlgebra k V) ^ ·))

def filtration (m : ℕ) (T : Type*) [AddCommMonoid T] [Module k T] : Submodule k T := sorry

def T (m : ℕ) := filtration (k := k) m (TensorAlgebra k V)

def equiv_finite_directSum : T k V m ≃ₗ[k] (⨁ (i : Fin (m + 1)), ⨂[k]^i V) := sorry

-- def TensorSum (n : ℕ) := DirectSum (Fin (n+1)) fun (m : Fin (n+1)) => TensorPower k m V
def π := RingQuot.mkAlgHom k (J k V).ringCon.r

def U (m : ℕ) := LinearMap.range (LinearMap.domRestrict (π k V).toLinearMap (T k V m))

lemma universal_subset (m : ℕ) : (U k V m).carrier ⊆ (U k V (m + 1)).carrier := sorry

instance : HasQuotient ↥(U k V m) (Submodule k ↥(U k V m)) where
    quotient' := sorry

def G (m : ℕ) := ↥(U k V m) ⧸ Submodule.comap (U k V m).subtype (U k V (m-1))

instance : AddCommMonoid (G k V m) := sorry

instance : Module k (G k V m) := sorry

def 𝔊 := ⨁ n, G k V n

instance : Ring (𝔊 k V) := sorry

instance : Algebra k (𝔊 k V) := sorry

theorem PBW : Nonempty (𝔖 k V →ₐ[k] 𝔊 k V) := sorry
