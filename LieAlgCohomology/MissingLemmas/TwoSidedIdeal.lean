import Mathlib.Algebra.Quotient
import Mathlib.Algebra.RingQuot
import Mathlib.RingTheory.TwoSidedIdeal.Basic

variable {A : Type*} [Ring A]

instance : HasQuotient A (TwoSidedIdeal A) where
  quotient' I := RingQuot I.ringCon.r

variable (I : TwoSidedIdeal A)

section ring

-- To be added : instances like this
instance : Ring (A ⧸ I) := inferInstanceAs (Ring (RingQuot I.ringCon.r))

def TwoSidedIdeal.mkRingHom : A →+* A ⧸ I :=
  RingQuot.mkRingHom I.ringCon.r

end ring

section Algebra

variable (R : Type*) [CommSemiring R] [Algebra R A]

instance : Algebra R (A ⧸ I) := inferInstanceAs (Algebra R (RingQuot I.ringCon.r))

def TwoSidedIdeal.mkAlgHom : A →ₐ[R] A ⧸ I :=
  RingQuot.mkAlgHom R I.ringCon.r
