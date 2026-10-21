namespace OAI

open Set Function Metric Filter Asymptotics Bornology

open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity.FiniteJordanConfiguration

variable {I : Type*} [Finite I]

lemma planeRegion_open (C : FiniteJordanConfiguration I) : IsOpen C.planeRegion :=
  C.region_open.preimage OnePoint.continuous_coe

end CircleDomainRigidity.FiniteJordanConfiguration
end
end OAI
