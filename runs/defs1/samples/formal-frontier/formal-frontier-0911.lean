public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology.LevelCompact

universe uR uG uA

variable {R : Type uR} [CommRing R]

variable {G : Type uG} [Group G] [TopologicalSpace G]

variable [IsTopologicalGroup G] [CompactSpace G]

variable (A : Rep.{uA} R G) (L : LevelCompact A)

/-- Tate degree `-1` at `S`, topologized as the closed kernel of the
continuous norm from finite coinvariants. -/
noncomputable abbrev finiteTateNegOne (S : OpenNormalSubgroup G) :
    CompHausAddCommGrp.{uA} :=
  CompHausAddCommGrp.kernelGroup (normFromFiniteCoinvariants A L S)

end ContinuousGroupCohomology.LevelCompact
end
end
