public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex unitInterval

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]

variable {C}

variable (C)

variable {C}

lemma skeletonNeighborhoodHomotopy_map {n : ℕ} (t : I) (j : cell C n)
    {y : Fin n → ℝ} (hy : ‖y‖ ≤ 1)
    (x : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) (hx : (x : X) = map n j y) :
    ((skeletonNeighborhoodHomotopy C n (t, x) : X)) = map n j (radialPush 2⁻¹ t y) := by
  rw [coe_skeletonNeighborhoodHomotopy_apply, hx, cellDeformation_radialPushMap_map t j hy]

end TauCeti
end
end
