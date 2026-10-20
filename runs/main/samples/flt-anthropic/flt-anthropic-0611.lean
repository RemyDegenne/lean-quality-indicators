namespace P2MW.S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point

set_option autoImplicit false

open Polynomial IsLocalRing

open scoped TensorProduct IsMulCommutative

namespace CDecompAux

variable {𝒪 : Type} [CommRing 𝒪] {H : Type} [AddCommGroup H] [Module 𝒪 H]
  {k : Type} [Field k] [Algebra 𝒪 k] (D : CohCarrier.HeckeData 𝒪 H k)
  (Sp : IharaLemma.IdempotentSplitting ↥D.opSubalgebra)
  (F : Type) [CommRing F] [Algebra 𝒪 F]

theorem sum_coe_e : ∑ j, ((Sp.e j : ↥D.opSubalgebra) : Module.End 𝒪 H) = 1 := by
  have := congrArg (Subtype.val : ↥D.opSubalgebra → Module.End 𝒪 H) Sp.coi.complete
  simpa using this

end CDecompAux
end P2MW.S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point
