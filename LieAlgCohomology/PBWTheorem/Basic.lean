import Mathlib.Algebra.Lie.UniversalEnveloping

variable {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]

instance poincare_birkhoff_witt [Module.Free K L] : Module.Free K (UniversalEnvelopingAlgebra K L) := sorry
