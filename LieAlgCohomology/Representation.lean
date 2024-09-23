import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Lie.UniversalEnveloping

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

instance : Category (LieDerivationCat.{u, v, w} R L) where
  Hom M N := LieModuleHom R L M N
  id M := LieModuleHom.id (R := R) (L := L)
  comp f g := LieModuleHom.comp g f

def toModuleUniversalAlgebra_objMap (M : LieDerivationCat R L) : Module (UniversalEnvelopingAlgebra R L) M where
  smul := sorry
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

def toModuleUniversalAlgebra : LieDerivationCat R L ⥤ ModuleCat (UniversalEnvelopingAlgebra R L) where
  obj M := sorry
  map := sorry

def ofModuleUniversalAlgebra : ModuleCat (UniversalEnvelopingAlgebra R L) ⥤ LieDerivationCat R L where
  obj := sorry
  map := sorry

def equivalenceLieDerivationModuleUniversalAlgebra :
  LieDerivationCat R L ≌ ModuleCat (UniversalEnvelopingAlgebra R L) where
    functor := toModuleUniversalAlgebra R L
    inverse := ofModuleUniversalAlgebra R L
    unitIso := sorry
    counitIso := sorry

end LieDerivationCat
