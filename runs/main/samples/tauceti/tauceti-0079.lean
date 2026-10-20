public section

open AlgebraicGeometry CategoryTheory Matrix WithConv

open scoped TensorProduct

open scoped CategoryTheory.MonObj

namespace TauCeti.G2ShortRoot.PrimeField

open TauCeti.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance high] Algebra.toModule

universe v w

variable {A : Type v} [CommRing A] [Algebra (ZMod 3) A]

@[simp]
theorem specialIsogeny_weightTorusPoints (s : Fin 2 → Aˣ) :
    specialIsogeny A (weightTorusPoints A s) =
      weightTorusPoints A ![s 1, s 0 ^ 3] := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_specialIsogeny]
  exact g2SpecialIsogeny_coe_weightTorusPoints s

end TauCeti.G2ShortRoot.PrimeField
end
