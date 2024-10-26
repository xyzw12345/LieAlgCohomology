import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Lie.UniversalEnveloping
import LieAlgCohomology.MissingLemmas.Module
import LieAlgCohomology.MissingLemmas.UniversalEnveloping

#check MonoidAlgebra
#check LieModuleHom

-- define the type synonym `M.asModule` for `M`
-- put the definition `LieModuleCat.toModuleUniversalAlgebra_objMap` on `M.asModule`

suppress_compilation

namespace LieModuleCat

open CategoryTheory UniversalEnvelopingAlgebra

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
    lift R (L := L) (A := Module.End R M) (LieModule.toEnd R L M)

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
    · intro l; ext x; simp [toModuleUniversalAlgebra_objMap_smul]
    · intro a b ha hb; simp;
      show f.toLinearMap ∘ₗ ((toModuleUniversalAlgebra_objMap_smul R L M a) ∘ₗ (toModuleUniversalAlgebra_objMap_smul R L M b)) = (((toModuleUniversalAlgebra_objMap_smul R L N a) ∘ₗ (toModuleUniversalAlgebra_objMap_smul R L N b)) ∘ₗ f.toLinearMap)
      rw [LinearMap.comp_assoc, ← hb, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc, ha]
    · intro a b ha hb; ext x; simp;
      apply_fun (fun f ↦ f x) at ha hb
      congr 1
  )⟩
  map_id M := by ext x; rfl
  map_comp f g := by ext x; rfl

def ofModuleUniversalAlgebra_objMap_isModule_smul (M : ModuleCat (UniversalEnvelopingAlgebra R L)) : R →+* AddMonoid.End M :=
  (Module.toAddMonoidEnd (UniversalEnvelopingAlgebra R L) M).comp (algebraMap R (UniversalEnvelopingAlgebra R L))

instance ofModuleUniversalAlgebra_objMap_isModule (M : ModuleCat (UniversalEnvelopingAlgebra R L)) :
  Module R M :=
    Module.ofAddMonoidEnd (ofModuleUniversalAlgebra_objMap_isModule_smul R L M)

instance ofModuleUniversalAlgebra_objMap_isModule_isScalerTower (M : ModuleCat (UniversalEnvelopingAlgebra R L)) : IsScalarTower R (UniversalEnvelopingAlgebra R L) M where
  smul_assoc := fun x y z ↦ by
    show (x • y) • z = (ofModuleUniversalAlgebra_objMap_isModule_smul R L M x) (y • z)
    unfold ofModuleUniversalAlgebra_objMap_isModule_smul
    rw [RingHom.coe_comp, Function.comp_apply]
    show (x • y) • z = ((algebraMap R (UniversalEnvelopingAlgebra R L)) x) • (y • z)
    rw [smul_smul, Algebra.smul_def]

instance ofModuleUniversalAlgebra_objMap_isLieRingModule (M : ModuleCat (UniversalEnvelopingAlgebra R L)) :
  LieRingModule L M where
    bracket := fun x m ↦ (ι R x) • m
    add_lie := fun x y m ↦ by
      show (ι R (x + y)) • m = (ι R x) • m + (ι R y) • m
      rw [LieHom.map_add]
      exact add_smul _ _ m
    lie_add := fun x m n ↦ by
      show (ι R x) • (m + n) = (ι R x) • m + (ι R x) • n
      exact smul_add _ m n
    leibniz_lie := fun x y m ↦ by
      show (ι R x) • ((ι R y) • m) = (ι R ⁅x, y⁆) • m + (ι R y) • ((ι R x) • m)
      rw [smul_smul, smul_smul, ← add_smul, LieHom.map_lie]
      rw [LieRing.of_associative_ring_bracket, sub_add_cancel]

instance ofModuleUniversalAlgebra_objMap_isLieModule (M : ModuleCat (UniversalEnvelopingAlgebra R L)) :
  LieModule R L M where
    smul_lie := fun t x m ↦ by
      show (ι R (t • x)) • m = t • ((ι R x) • m)
      simp
    lie_smul := fun t x m ↦ by
      show (ι R x) • (t • m) = t • ((ι R x) • m)
      exact smul_comm (ι R x) t m

def ofModuleUniversalAlgebra : ModuleCat (UniversalEnvelopingAlgebra R L) ⥤ LieModuleCat R L where
  obj M := ⟨M⟩
  map {M N} f := ⟨⟨f.toAddHom, by simp⟩, fun {x m} ↦ by exact map_smul f ((ι R) x) m⟩
  map_id M := by ext x; rfl
  map_comp f g := by ext x; rfl

def equivalenceLieModuleUniversalAlgebra :
  LieModuleCat R L ≌ ModuleCat (UniversalEnvelopingAlgebra R L) where
    functor := toModuleUniversalAlgebra R L
    inverse := ofModuleUniversalAlgebra R L
    unitIso := sorry
    counitIso := sorry

/--
Note: the universe level is taken to be {u, v, max u v} instead of {u, v, w} is because that for some reasons I still don't understand, the universe level in `ModuleCat.moduleCat_enoughProjectives` has been specified.
-/
instance : EnoughProjectives (LieModuleCat.{u, v, max u v} R L) := by
  apply (Equivalence.enoughProjectives_iff (equivalenceLieModuleUniversalAlgebra R L)).2 ModuleCat.moduleCat_enoughProjectives

instance : Preadditive (LieModuleCat R L) := sorry

instance : Limits.HasFiniteProducts (LieModuleCat R L) := sorry

set_option diagnostics true

instance : Limits.HasZeroMorphisms (LieModuleCat R L) := by sorry

instance : Abelian (LieModuleCat R L) := abelianOfEquivalence (F := (equivalenceLieModuleUniversalAlgebra R L).1)


end LieModuleCat
