import Mathlib

-- We are following Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal

variable {ι : Type*} [DecidableEq ι] [AddMonoid ι]
variable {A : Type*} [Ring A]
variable {σ : Type*} [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜]

def TwoSidedIdeal.IsHomogeneous (I : TwoSidedIdeal A) : Prop :=
  ∀ (i : ι) ⦃a b : A⦄, I.ringCon a b →
    I.ringCon (DirectSum.decompose 𝒜 a i : A) (DirectSum.decompose 𝒜 b i : A)

theorem TwoSidedIdeal.asIdeal_IsHomogeneous_of_IsHomogeneous
  (I : TwoSidedIdeal A) (h : I.IsHomogeneous) :
    I.asIdeal.IsHomogeneous := sorry

class HomogeneousTwoSidedIdeal extends TwoSidedIdeal A :
  is_homogeneous' : TwoSidedIdeal.IsHomogeneous 𝒜 self.toTwoSidedIdeal

def HomogeneousTwoSidedIdeal.toTwoSidedIdeal
  (I : HomogeneousTwoSidedIdeal 𝒜) : TwoSidedIdeal A :=
    I.toTwoSidedIdeal

theorem HomogeneousTwoSidedIdeal.isHomogeneous :
  (I : HomogeneousTwoSidedIdeal 𝒜) : I.toTwoSidedIdeal.IsHomogeneous := sorry

def HomogeneousTwoSidedIdeal.toHomogeneousIdeal
  (I : HomogeneousTwoSidedIdeal 𝒜) : HomogeneousIdeal 𝒜 := sorry

-- We are following Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal
