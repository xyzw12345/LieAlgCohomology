import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Lie.UniversalEnveloping
import LieAlgCohomology.MissingLemmas.Module
import LieAlgCohomology.MissingLemmas.UniversalEnveloping

#check LieDerivation
#check MonoidAlgebra
#check LieModuleHom

-- define the type synonym `M.asModule` for `M`
-- put the definition `LieModuleCat.toModuleUniversalAlgebra_objMap` on `M.asModule`

namespace LieModuleCat

open CategoryTheory

universe u v w
variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

structure LieModuleCat where
  carrier : Type w
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module R carrier]
  [isLieRingModule : LieRingModule L carrier]
  [isLieModule : LieModule R L carrier]

instance : CoeSort (LieModuleCat R L) (Type w) := ⟨LieModuleCat.carrier⟩

instance (M : LieModuleCat R L) : AddCommGroup M := M.isAddCommGroup

instance (M : LieModuleCat R L) : Module R M := M.isModule

instance (M : LieModuleCat R L) : LieRingModule L M := M.isLieRingModule

instance (M : LieModuleCat R L) : LieModule R L M := M.isLieModule

instance : Category (LieModuleCat R L) where
  Hom M N := LieModuleHom R L M N
  id M := LieModuleHom.id (R := R) (L := L)
  comp f g := LieModuleHom.comp g f

instance {M N : LieModuleCat R L} : FunLike (M ⟶ N) M N :=
  LieModuleHom.instFunLike (R := R) (L := L) (M := M) (N := N)

@[ext]
lemma ext {M N : LieModuleCat R L} (f g : M ⟶ N) (h : ∀ (x : M), f x = g x) :
  f = g := DFunLike.ext _ _ h

def toModuleUniversalAlgebra_objMap_smul (M : LieModuleCat R L) :
  UniversalEnvelopingAlgebra R L →ₐ[R] (Module.End R M) :=
    UniversalEnvelopingAlgebra.lift R (L := L) (A := Module.End R M) (LieModule.toEnd R L M)

def toModuleUniversalAlgebra_objMap (M : LieModuleCat R L) : Module (UniversalEnvelopingAlgebra R L) M :=
  @Module.ofAddMonoidEnd _ _ _ _ ((Module.toAddMonoidEnd (Module.End R M) M).comp
   (toModuleUniversalAlgebra_objMap_smul R L M))

attribute [instance] toModuleUniversalAlgebra_objMap

def toModuleUniversalAlgebra : LieModuleCat R L ⥤ ModuleCat (UniversalEnvelopingAlgebra R L) where
  obj M := ⟨M⟩
  map {M N} f := ⟨f.toLinearMap.toAddHom, fun m x ↦ (by
    show (f.toLinearMap.comp (toModuleUniversalAlgebra_objMap_smul R L M m)) x
      = ((toModuleUniversalAlgebra_objMap_smul R L N m).comp f.toLinearMap) x
    congr 1
    apply UniversalEnvelopingAlgebra.induction (a := m)
    · intro r; ext x; simp
    · intro l; ext x; unfold toModuleUniversalAlgebra_objMap_smul; simp
    · intro a b ha hb; simp;
      show f.toLinearMap ∘ₗ ((toModuleUniversalAlgebra_objMap_smul R L M a) ∘ₗ (toModuleUniversalAlgebra_objMap_smul R L M b)) = (((toModuleUniversalAlgebra_objMap_smul R L N a) ∘ₗ (toModuleUniversalAlgebra_objMap_smul R L N b)) ∘ₗ f.toLinearMap)
      rw [LinearMap.comp_assoc, ← hb, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc, ha]
    · intro a b ha hb; ext x; simp;
      apply_fun (fun f ↦ f x) at ha hb
      congr 1
  )⟩
  map_id M := by ext x; rfl
  map_comp f g := by ext x; rfl

attribute [-instance] toModuleUniversalAlgebra_objMap

def ofModuleUniversalAlgebra_objMap_isModule_smul (M : ModuleCat (UniversalEnvelopingAlgebra R L)) : R →+* AddMonoid.End M :=
  (Module.toAddMonoidEnd (UniversalEnvelopingAlgebra R L) M).comp (algebraMap R (UniversalEnvelopingAlgebra R L))

def ofModuleUniversalAlgebra_objMap_isModule (M : ModuleCat (UniversalEnvelopingAlgebra R L)) :
  Module R M :=
    Module.ofAddMonoidEnd (ofModuleUniversalAlgebra_objMap_isModule_smul R L M)

attribute [instance] ofModuleUniversalAlgebra_objMap_isModule

instance ofModuleUniversalAlgebra_objMap_isModule_isScalerTower (M : ModuleCat (UniversalEnvelopingAlgebra R L)) : IsScalarTower R (UniversalEnvelopingAlgebra R L) M where
  smul_assoc := fun x y z ↦ by
    show (x • y) • z = (ofModuleUniversalAlgebra_objMap_isModule_smul R L M x) (y • z)
    unfold ofModuleUniversalAlgebra_objMap_isModule_smul
    rw [RingHom.coe_comp, Function.comp_apply]
    show (x • y) • z = ((algebraMap R (UniversalEnvelopingAlgebra R L)) x) • (y • z)
    rw [smul_smul, Algebra.smul_def]

def ofModuleUniversalAlgebra_objMap_isLieRingModule (M : ModuleCat (UniversalEnvelopingAlgebra R L)) :
  LieRingModule L M := by sorry

attribute [instance] ofModuleUniversalAlgebra_objMap_isLieRingModule

def ofModuleUniversalAlgebra_objMap_isLieModule (M : ModuleCat (UniversalEnvelopingAlgebra R L)) :
  LieModule R L M := by sorry

attribute [instance] ofModuleUniversalAlgebra_objMap_isLieModule

def ofModuleUniversalAlgebra : ModuleCat (UniversalEnvelopingAlgebra R L) ⥤ LieModuleCat R L where
  obj M := ⟨M⟩
  map {M N} f := ⟨⟨f.toAddHom, sorry⟩, sorry⟩
  map_id M := by ext x; rfl
  map_comp f g := by ext x; rfl

attribute [-instance] ofModuleUniversalAlgebra_objMap_isLieModule
attribute [-instance] ofModuleUniversalAlgebra_objMap_isLieRingModule
attribute [-instance] ofModuleUniversalAlgebra_objMap_isModule

def equivalenceLieDerivationModuleUniversalAlgebra :
  LieModuleCat R L ≌ ModuleCat (UniversalEnvelopingAlgebra R L) where
    functor := toModuleUniversalAlgebra R L
    inverse := ofModuleUniversalAlgebra R L
    unitIso := sorry
    counitIso := sorry

end LieModuleCat
