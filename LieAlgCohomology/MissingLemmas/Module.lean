import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Algebra.Defs

def Module.ofAddMonoidEnd {R M : Type*} [Semiring R] [AddCommGroup M] (φ : R →+* AddMonoid.End M)
 : Module R M where
  smul := fun r ↦ (fun m ↦ (φ r) m)
  one_smul := fun b ↦ (by show (φ 1) b = b; rw [map_one]; rfl)
  mul_smul := fun x y b ↦ (by show (φ (x * y) b) = (φ x) ((φ y) b); rw [map_mul]; rfl)
  smul_zero := fun a ↦ (by show (φ a) 0 = 0; rw [map_zero])
  smul_add := fun a x y ↦ (by show (φ a) (x + y) = (φ a) x + (φ a) y; rw [map_add])
  add_smul := fun a b x ↦ (by show (φ (a + b)) x = (φ a) x + (φ b) x; rw [map_add]; rfl)
  zero_smul := fun x ↦ (by show (φ 0) x = 0; rw [map_zero]; rfl)

@[ext]
theorem AddMonoidEnd.ext {M : Type*} [AddCommGroup M] (f g : AddMonoid.End M) (h : ∀ (x : M), f x = g x)
  : f = g := AddMonoidHom.ext h
