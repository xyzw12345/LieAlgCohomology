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

#check RingQuot.mkRingHom
#check RingQuot.mkAlgHom

variable {ι : Type*} [DecidableEq ι] [AddMonoid ι]
variable {A : Type*} [Ring A]

class IsHomogeneousRelation {σ : Type*} [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (r : A → A → Prop) : Prop
  where
  is_homogeneous' : ∀ {x y : A}, r x y → ∀ i : ι, (((GradedRing.proj 𝒜 i) x = (GradedRing.proj 𝒜 i) y) ∨ (r ((GradedRing.proj 𝒜 i) x) ((GradedRing.proj 𝒜 i) y)))

namespace HomogeneousRelation

section RingCon

variable {σ : Type*} [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜] (rel : A → A → Prop) [inst : IsHomogeneousRelation 𝒜 rel]

instance : IsHomogeneousRelation 𝒜 (RingQuot.Rel rel) := ⟨by
  intro x y h; induction h
  case of x y h_rel =>
    intro i;
    rcases (inst.is_homogeneous' h_rel i) with (h1 | h2)
    · left; exact h1
    · right; exact RingQuot.Rel.of h2
  case add_left a b c h_rel h =>
    intro i;
    rcases (h i) with (h1 | h2)
    · left; rw [map_add, map_add, h1]
    · right; rw [map_add, map_add]; exact RingQuot.Rel.add_left h2
  case mul_left a b c h_rel h => sorry
  case mul_right a b c h_rel h => sorry
⟩

#help tactic

instance : IsHomogeneousRelation 𝒜 (Relation.EqvGen rel) := ⟨by
  intro x y h; induction h
  case rel x y h_rel =>
    intro i;
    rcases (inst.is_homogeneous' h_rel i) with (h1 | h2)
    · left; exact h1
    · right; exact Relation.EqvGen.rel ((GradedRing.proj 𝒜 i) x) ((GradedRing.proj 𝒜 i) y) h2
  case refl x => intro i; left; rfl
  case symm x y _ h =>
    intro i
    rcases (h i) with (h1 | h2)
    · left; exact h1.symm
    · right; exact h2.symm
  case trans x y z _ _ hxy hyz =>
    intro i
    rcases (hxy i) with (hxy1 | hxy2)
    · rw [hxy1]; exact hyz i
    · right; rcases (hyz i) with (hyz1 | hyz2)
      · rw [← hyz1]; exact hxy2
      · exact Relation.EqvGen.trans _ _ _ hxy2 hyz2
⟩

instance : IsHomogeneousRelation 𝒜 (RingConGen.Rel rel) :=
  (RingQuot.eqvGen_rel_eq rel).symm ▸ (inferInstance)

end RingCon

section GradedRing

variable (𝒜 : ι → AddSubmonoid A) [GradedRing 𝒜] (rel : A → A → Prop) [IsHomogeneousRelation 𝒜 rel]

instance : GradedRing ((AddSubmonoid.map (RingQuot.mkRingHom rel)).comp 𝒜) := sorry

end GradedRing

section GradedAlgebra

variable {R : Type*} [CommRing R] [Algebra R A]
variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (rel : A → A → Prop) [IsHomogeneousRelation 𝒜 rel]

instance : GradedAlgebra ((Submodule.map (RingQuot.mkAlgHom R rel)).comp 𝒜) := sorry

end GradedAlgebra

end HomogeneousRelation
