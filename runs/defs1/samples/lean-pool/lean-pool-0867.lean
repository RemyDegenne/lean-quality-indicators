public section

open MeasureTheory Set Filter

open scoped Topology

open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The element of `H^M(ℝ³)` whose slots are the `L²` classes of a Sobolev family through order
`M` (`prop:lps-smoothing`). -/
@[expose] def lpsSobolevOf (M : ℕ) (D : List (Fin 3) → Vec3 → ℝ)
    (hD : IsSobolevFamilyOn M univ (D []) D) : lpsSobolevSpace M :=
  ⟨_, lps_slots_mem_of_family hD⟩

end ESS
end
end
