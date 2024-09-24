import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Lie.UniversalEnveloping
import LieAlgCohomology.MissingLemmas.Module

#check LieDerivation
#check MonoidAlgebra
#check LieModuleHom

namespace LieDerivationCat

open CategoryTheory

universe u v w
variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

structure LieDerivationCat where
  carrier : Type w
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module R carrier]
  [isLieRingModule : LieRingModule L carrier]
  [isLieModule : LieModule R L carrier]
  [isLieDerivation : LieDerivation R L carrier]

instance : CoeSort (LieDerivationCat R L) (Type w) := ⟨LieDerivationCat.carrier⟩

instance (M : LieDerivationCat R L) : AddCommGroup M := M.isAddCommGroup

instance (M : LieDerivationCat R L) : Module R M := M.isModule

instance (M : LieDerivationCat R L) : LieRingModule L M := M.isLieRingModule

instance (M : LieDerivationCat R L) : LieModule R L M := M.isLieModule

instance (M : LieDerivationCat R L) : LieDerivation R L M := M.isLieDerivation

instance : Category (LieDerivationCat R L) where
  Hom M N := LieModuleHom R L M N
  id M := LieModuleHom.id (R := R) (L := L)
  comp f g := LieModuleHom.comp g f

instance {M N : LieDerivationCat R L} : FunLike (M ⟶ N) M N :=
  LieModuleHom.instFunLike (R := R) (L := L) (M := M) (N := N)

@[ext]
lemma ext {M N : LieDerivationCat R L} (f g : M ⟶ N) (h : ∀ (x : M), f x = g x) :
  f = g := DFunLike.ext _ _ h

def toModuleUniversalAlgebra_objMap (M : LieDerivationCat R L) : Module (UniversalEnvelopingAlgebra R L) M :=
  @Module.ofAddMonoidEnd _ _ _ _ ((Module.toAddMonoidEnd (Module.End R M) M).comp
   ((UniversalEnvelopingAlgebra.lift R (L := L) (A := Module.End R (M : Type v))
    (LieModule.toEnd R L M)).1))

attribute [instance] toModuleUniversalAlgebra_objMap

def toModuleUniversalAlgebra : LieDerivationCat R L ⥤ ModuleCat (UniversalEnvelopingAlgebra R L) where
  obj M := ⟨M⟩
  map {M N} f := {
    toFun := f
    map_add' := f.map_add
    map_smul' := fun m x ↦ (by
      dsimp
      show f ((toModuleUniversalAlgebra_objMap R L M).toAddMonoidEnd m x) =
        (toModuleUniversalAlgebra_objMap R L N).toAddMonoidEnd m (f x)
      sorry)
  }
  map_id M := by ext x; rfl
  map_comp f g := by ext x; rfl

attribute [-instance] toModuleUniversalAlgebra_objMap

def ofModuleUniversalAlgebra_objMap_isModule (M : ModuleCat (UniversalEnvelopingAlgebra R L)) :
  Module R M := by sorry

attribute [instance] ofModuleUniversalAlgebra_objMap_isModule

def ofModuleUniversalAlgebra_objMap_isLieRingModule (M : ModuleCat (UniversalEnvelopingAlgebra R L)) :
  LieRingModule L M := by sorry

attribute [instance] ofModuleUniversalAlgebra_objMap_isLieRingModule

def ofModuleUniversalAlgebra_objMap_isLieModule (M : ModuleCat (UniversalEnvelopingAlgebra R L)) :
  LieModule R L M := by sorry

attribute [instance] ofModuleUniversalAlgebra_objMap_isLieModule

def ofModuleUniversalAlgebra_objMap (M : ModuleCat (UniversalEnvelopingAlgebra R L)) :
  LieDerivation R L M := by sorry

def ofModuleUniversalAlgebra : ModuleCat (UniversalEnvelopingAlgebra R L) ⥤ LieDerivationCat R L where
  obj M := {
    carrier := M
    isLieDerivation := ofModuleUniversalAlgebra_objMap R L M
  }
  map {M N} f := {
    toFun := f
    map_add' := f.map_add
    map_smul' := sorry
    map_lie' := sorry
  }
  map_id M := by ext x; rfl
  map_comp f g := by ext x; rfl

attribute [-instance] ofModuleUniversalAlgebra_objMap_isLieModule
attribute [-instance] ofModuleUniversalAlgebra_objMap_isLieRingModule
attribute [-instance] ofModuleUniversalAlgebra_objMap_isModule

def equivalenceLieDerivationModuleUniversalAlgebra :
  LieDerivationCat R L ≌ ModuleCat (UniversalEnvelopingAlgebra R L) where
    functor := toModuleUniversalAlgebra R L
    inverse := ofModuleUniversalAlgebra R L
    unitIso := sorry
    counitIso := sorry

end LieDerivationCat
