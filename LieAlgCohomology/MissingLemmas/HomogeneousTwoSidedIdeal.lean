import Mathlib
import LieAlgCohomology.MissingLemmas.TwoSidedIdeal

/-
· expected relations with: HomogeneousIdeal, TwoSidedIdeal, (Ideal?)
  (add simp lemmas, ...)
· In the case of Commring, prove the equivalence between this and HomogeneousIdeal
· expected instance: SetLike, HasQuotient
· GradedRing / GradedAlgebra on quotient ring
· a homogeneous relation extends to a HomogeneousTwoSidedIdeal

following:
  Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal
  Mathlib.RingTheory.TwoSidedIdeal.Operations
-/

variable {ι : Type*} [DecidableEq ι] [AddMonoid ι]
variable {A : Type*} [Ring A]
variable {σ : Type*} [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜]

def TwoSidedIdeal.IsHomogeneous (I : TwoSidedIdeal A) : Prop :=
  ∀ (i : ι) ⦃a b : A⦄, I.ringCon a b →
    I.ringCon (DirectSum.decompose 𝒜 a i : A) (DirectSum.decompose 𝒜 b i : A)

theorem TwoSidedIdeal.asIdeal_IsHomogeneous_of_IsHomogeneous
  (I : TwoSidedIdeal A) (h : I.IsHomogeneous 𝒜) :
    I.asIdeal.IsHomogeneous 𝒜 := sorry

class HomogeneousTwoSidedIdeal extends TwoSidedIdeal A where
  is_homogeneous' : TwoSidedIdeal.IsHomogeneous 𝒜 toTwoSidedIdeal

section BasicProperties

instance HomogeneousTwoSidedIdeal.setlike : SetLike (HomogeneousTwoSidedIdeal 𝒜) A where
  coe I := I.toTwoSidedIdeal
  coe_injective' := sorry

theorem HomogeneousTwoSidedIdeal.isHomogeneous
  (I : HomogeneousTwoSidedIdeal 𝒜) : I.toTwoSidedIdeal.IsHomogeneous 𝒜 := sorry

variable {𝒜}
def HomogeneousTwoSidedIdeal.toHomogeneousIdeal
  (I : HomogeneousTwoSidedIdeal 𝒜) : HomogeneousIdeal 𝒜 := sorry

theorem HomogeneousTwoSidedIdeal.isTwoSided (I : HomogeneousTwoSidedIdeal 𝒜) :
   ∀ {x y : A}, x ∈ I.toHomogeneousIdeal → x * y ∈ I.toHomogeneousIdeal := sorry

theorem HomogeneousTwoSidedIdeal.toHomogeneousIdeal_isTwoSided
  (I : HomogeneousTwoSidedIdeal 𝒜) : ∀ {x y : A}, x ∈ I.toHomogeneousIdeal
    → x * y ∈ I.toHomogeneousIdeal := I.isTwoSided

end BasicProperties



section HomogeneousIdeal

variable {𝒜} (I : HomogeneousIdeal 𝒜) (mul_mem_right : ∀ {x y : A}, x ∈ I → x * y ∈ I)

def HomogeneousIdeal.toTwoSided (I : HomogeneousIdeal 𝒜)
  (mul_mem_right : ∀ {x y : A}, x ∈ I → x * y ∈ I) : HomogeneousTwoSidedIdeal 𝒜 := sorry

variable {I} {mul_mem_right}

@[simp]
lemma HomogeneousIdeal.mem_toTwoSided {x : A} :
  x ∈ (I.toTwoSided mul_mem_right) ↔ x ∈ I := sorry

end HomogeneousIdeal



section Quotient

instance : HasQuotient A (HomogeneousTwoSidedIdeal 𝒜) where
  quotient' I := A ⧸ I.toTwoSidedIdeal

variable (I : HomogeneousTwoSidedIdeal 𝒜)

instance : Ring (A ⧸ I) := inferInstanceAs (Ring (A ⧸ I.toTwoSidedIdeal))

variable (R : Type*) [CommSemiring R] [Algebra R A]

instance : Algebra R (A ⧸ I) := inferInstanceAs (Algebra R (A ⧸ I.toTwoSidedIdeal))

end Quotient



section GradedRing

end GradedRing



section GradedAlgebra

end GradedAlgebra
