import Mathlib

#check groupCohomology
#check Rep.trivial
#check ExteriorAlgebra
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

noncomputable section
universe u
variable {k L R : Type u} [LieRing L] [CommRing R] [LieAlgebra R L] [CommRing k]
namespace LieAlgCohomology

end LieAlgCohomology

variable {M : Type u} [AddCommGroup M] [Module R M]
