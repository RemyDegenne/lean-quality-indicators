public noncomputable section

namespace CFSG.EvenSmallLie.GTwoFour

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.LieType.Chevalley.G2FieldFour CFSG.LocalAnalysis.ComponentInitial

open Subgroup

open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2]

local notation "X" => pinnedX Tag.G2 K

theorem mul_mul_mul_of_mem_center {G : Type*} [Group G] {u : G} (hu : u ∈ center G)
    (a b v : G) : a * u * (b * v) = a * b * (u * v) := by
  calc a * u * (b * v) = a * (u * b) * v := by group
    _ = a * (b * u) * v := by rw [← mem_center_iff.1 hu b]
    _ = a * b * (u * v) := by group

end CFSG.EvenSmallLie.GTwoFour
end
