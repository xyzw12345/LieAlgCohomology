import Mathlib
import LieAlgebraCohomology.MissingLemmas.HomogeneousTwoSidedIdeal

variable {ι : Type*} [DecidableEq ι] [AddMonoid ι]
variable {R : Type*} [CommSemiring R]

/-TODO: We are trying to give SymmetricAlgebra a gradedAlgebra Structure,
which perhaps generalizes to taking the quotient by a homogeneous ideal?
Since this action requires the AddSubmonoidClass to be able to pushforward,
we would only work on AddSubgroup and then extend this to Submodule.
0. Define the class of homogeneous two-sided ideals! [InProcess]
1. We will show that if we take the quotient by a "homogeneous" two-sided ideal, then
the pushforward of the GradedRing structure gives a GradedRing structure (which further
extends to GradedAlgebra) (we should address the case of CommRing separately)
2. We shall then proceed to tackle something closer to our final result, which
is taking the quotient by a homogeneous relation.
3. Finally, we use this to deduce the special case we want.
-/

section non_comm

variable {A B : Type*} [Ring A] [Ring B]
variable {𝒜 : ι → AddSubgroup A} [GradedRing 𝒜]

#check Ideal.IsHomogeneous


end non_comm
