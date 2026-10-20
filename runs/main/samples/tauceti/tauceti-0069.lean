public section

open CategoryTheory TensorProduct WithConv

open scoped commutatorElement

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule

universe v w

variable {L : Type v} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra.IsKilling ℚ L]
  [FiniteDimensional ℚ L] {H : LieSubalgebra ℚ L} [H.IsCartanSubalgebra]
  [LieModule.IsTriangularizable ℚ H L]

attribute [local instance high] Algebra.toModule

namespace IsChevalleySystem

variable {ω : L ≃ₗ⁅ℚ⁆ L} {x : Weight ℚ H L → L} (hx : IsChevalleySystem ω x)

include hx

@[simp]
theorem adjointRootSubgroup_mem_adjointElementaryGroup (α : Weight ℚ H L) (A : CommAlgCat.{w} ℤ)
    (t : Multiplicative A) :
    hx.adjointRootSubgroup α A t ∈ hx.adjointElementaryGroup A := by
  rw [adjointRootSubgroup_def, adjointElementaryGroup_def]
  exact UniversalEnvelopingAlgebra.kostantRootSubgroupParam_mem_kostantElementarySubgroup
    _ _ _ _ _ _ A α t

end IsChevalleySystem
end TauCeti
end
