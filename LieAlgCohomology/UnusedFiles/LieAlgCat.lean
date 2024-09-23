import Mathlib

universe u v

namespace LieAlg

variable (R : Type u) [CommRing R]
open CategoryTheory BigOperators

structure LieAlgCat where
  carrier : Type v
  [LieRing : LieRing carrier]
  [LieAlg : LieAlgebra R carrier]

instance : CoeSort (LieAlgCat.{u, v} R) (Type v):=
  ⟨LieAlgCat.carrier (R := R)⟩

instance (L : LieAlgCat R) : LieRing L := L.LieRing

instance (L : LieAlgCat R) : LieAlgebra R L := L.LieAlg

instance : Category (LieAlgCat.{u, v} R) where
  Hom L L' := L →ₗ⁅R⁆ L'
  id _ := LieHom.id
  comp f g := g.comp f
  id_comp _ := LieHom.id_comp _
  comp_id _ := LieHom.comp_id _
  assoc _ _ _ := rfl

instance : ConcreteCategory (LieAlgCat.{u, v} R) where
  forget := {
    obj := fun L ↦ L.carrier
    map := fun f ↦ f.toFun
  }
  forget_faithful := ⟨ fun h => LieHom.ext (fun x ↦ by dsimp at h; rw [h])⟩

instance {L L' : LieAlgCat.{u, v} R} : FunLike (L ⟶ L') L L' :=
  LieHom.instFunLike.{u, _, _} (R := R) (L₁ := L) (L₂ := L')

@[ext]
lemma ext {L L': LieAlgCat.{u, v} R} {f₁ f₂ : L ⟶ L'} (h : ∀ (x : L), f₁ x = f₂ x) : f₁ = f₂ :=
  DFunLike.ext _ _ h

instance hasForgetToModule : HasForget₂ (LieAlgCat.{u, v} R) (ModuleCat.{_, u} R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => f.toLinearMap
      }

def of (L : Type v) [LieRing L] [LieAlgebra R L] : LieAlgCat.{u, v} R :=
  ⟨L⟩

@[simp]
theorem forget₂_obj (L : LieAlgCat R) :
    (forget₂ (LieAlgCat R) (ModuleCat R)).obj L = ModuleCat.of R L :=
  rfl

theorem forget₂_obj_moduleCat_of (L : Type v) [LieRing L] [LieAlgebra R L] :
    (forget₂ (LieAlgCat R) (ModuleCat R)).obj (of R L) = ModuleCat.of R L :=
  rfl

@[simp]
theorem forget₂_map (L L' : LieAlgCat R) (f : L ⟶ L') :
    (forget₂ (LieAlgCat R) (ModuleCat R)).map f = LieHom.toLinearMap f :=
  rfl

def ofHom {R : Type u} [CommRing R] {L L' : Type v} [LieRing L] [LieRing L'] [LieAlgebra R L] [LieAlgebra R L'] (f : L →ₗ⁅R⁆ L') : of R L ⟶ of R L' :=
  f

@[simp 1100]
theorem ofHom_apply {R : Type u} [CommRing R] {L L' : Type v} [LieRing L] [LieRing L'] [LieAlgebra R L] [LieAlgebra R L'] (f : L →ₗ⁅R⁆ L') (x : L) : ofHom f x = f x :=
  rfl

instance : Inhabited (LieAlgCat R) :=
  ⟨of R PUnit⟩

instance ofUnique {L : Type v} [LieRing L] [LieAlgebra R L] [i : Unique L] : Unique (of R L) :=
  i

@[simp] theorem of_coe (L : LieAlgCat R) : of R L = L := rfl

theorem coe_of (L : Type v) [LieRing L] [LieAlgebra R L] : (of R L : Type v) = L :=
  rfl

variable {R}

@[simps]
def ofSelfIso (L : LieAlgCat R) : of R L ≅ L where
  hom := 𝟙 L
  inv := 𝟙 L

end LieAlg
