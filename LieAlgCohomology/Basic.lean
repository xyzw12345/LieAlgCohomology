import Mathlib

#check groupCohomology
#check Rep.trivial
#check ExteriorAlgebra
#check TensorAlgebra
#check AlternatingMap
#check ExteriorAlgebra.liftAlternatingEquiv
#check TensorProduct
#check LieDerivation
#check ModuleCat
#check Module.Free.tensor
#check Algebra.algebra_ext_iff
#check Module.toAddMonoidEnd
#check AlgHom
#check LinearMap
#check Module.Free.tensor

#check Algebra

#check GradedAlgebra

#check RingQuot

#check ChainComplex

#check CategoryTheory.Abelian

open CategoryTheory
variable {G : Type u} [Monoid G]
variable {k : Type u} [Ring k]
#synth Limits.HasZeroMorphisms (Rep k G)
#check Action.instHasZeroMorphisms

#synth Abelian (Rep k G)
#synth Preadditive (Rep k G)
#check Action.instAbelian
#check Action.instPreadditive

#synth Abelian (ModuleCat k)

variable {V : Type u} [Category V] [Abelian V]
#synth Limits.HasZeroMorphisms V
noncomputable section
universe u
variable {k L R : Type u} [LieRing L] [CommRing R] [LieAlgebra R L] [CommRing k]
namespace LieAlgCohomology

end LieAlgCohomology

variable {M : Type u} [AddCommGroup M] [Module R M]
