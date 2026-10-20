@[expose] public section

noncomputable section

open AddCommGroup Set Function AddSubgroup TopologicalSpace

open Topology

variable {𝕜 B : Type*}

section IdentifyIccEnds

namespace AddCircle

variable [AddCommGroup 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜] (p a : 𝕜)
  [hp : Fact (0 < p)]

local notation "𝕋" => AddCircle p

variable [Archimedean 𝕜]

variable {p a}

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]

theorem liftIco_zero_continuous [TopologicalSpace B] {f : 𝕜 → B} (hf : f 0 = f p)
    (hc : ContinuousOn f <| Icc 0 p) : Continuous (liftIco p 0 f) :=
  liftIco_continuous (by rwa [zero_add] : f 0 = f (0 + p)) (by rwa [zero_add])

end AddCircle
end IdentifyIccEnds
end
end
