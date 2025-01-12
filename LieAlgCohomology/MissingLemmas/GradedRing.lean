import Mathlib

section A

variable {ι : Type u_1} [DecidableEq ι] [AddMonoid ι] {A : Type u_3} [Semiring A]
variable {σ : Type u_4} [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

lemma GradedRing.proj_zero_of_mem_grading {i : ι} {x : A} (h : x ∈ 𝒜 i) (j : ι) (h_ne : j ≠ i) : GradedRing.proj 𝒜 j x = 0 := sorry

end A

section B0

variable {ι : Type u_1} [DecidableEq ι] [AddMonoid ι] {A : Type u_3} [Semiring A]
variable {σ : Type u_4} [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

lemma GradedRing.proj_mul (x y : A) (i : ι) [DecidableEq A] (S T : Finset ι) (hs : ((DirectSum.decompose 𝒜) x).support ⊆ S) (ht : ((DirectSum.decompose 𝒜) y).support ⊆ T) :
  Finset.sum (S ×ˢ T) (fun st ↦ if (st.1 + st.2 = i) then (GradedRing.proj 𝒜 st.1 x) * (GradedRing.proj 𝒜 st.2 y) else 0) = GradedRing.proj 𝒜 i (x * y) := sorry

end B0

-- section B1

-- variable {ι : Type u_1} [DecidableEq ι] [AddGroup ι] {A : Type u_3} [Semiring A]
-- variable {σ : Type u_4} [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

-- lemma GradedRing.proj_mul' (x y : A) (i : ι) [DecidableEq A] : GradedRing.proj 𝒜 i (x * y) =
--   DFinsupp.sum ((DirectSum.decompose 𝒜) x) (fun j ↦ (fun u ↦ (GradedRing.proj 𝒜 (i - j) y) * u)) := sorry

-- end B1
