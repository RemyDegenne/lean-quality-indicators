public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u

section GraphClass

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

local instance : ContinuousSMul G (trivialF2 G).V :=
  (isSmoothDiscrete_trivialF2 G).continuousSMul

/-- The two-point graph cochain as a continuous `2`-cocycle with coefficients in `trivialF2 G`.

The inverse of `trivialF2Equiv` is applied pointwise because the canonical coefficient object has
carrier `ULift (ZMod 2)`, while the explicit formula naturally takes values in `ZMod 2`. -/
noncomputable def evensGraphCocycle (U : OpenSubgroup G) (s : G)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hU : U.toSubgroup.index = 2)
    (hs : s ∉ U) (hα : Continuous α) : Z2 G (trivialF2 G).V :=
  ⟨fun p => (trivialF2Equiv G).symm (evensGraphCochain U.toSubgroup s α p),
    evensGraphCochain_mem_Z2 U s α hU hs hα⟩

end GraphClass
end TauCeti.ContCohomology
end
