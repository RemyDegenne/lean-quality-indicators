namespace OAI

section

namespace SourceBurnside.Stability.Frames

noncomputable section

open Classical Module

variable (V : Type*)

variable {V}

variable [LinearOrder V]

variable {F W : Type*} [DivisionRing F] [AddCommGroup W] [Module F W]

variable (ρ : V → W) (C : ConeSupply (F := F) ρ 10)

theorem cycles_bound_upToThree [FiniteDimensional F W]
    (hρ : Submodule.span F (Set.range ρ) = ⊤) (hrank : 10 < Module.finrank F W)
    (k : ℕ) (hk : k ≤ 3) {z : Ambient V}
    (hz : z ∈ chains (F := F) ρ Set.univ k) (hcycle : boundary V z = 0) :
    ∃ w ∈ chains (F := F) ρ Set.univ (k+1), boundary V w = z := by
  let D := coneSupply ρ hρ 10 hrank
  interval_cases k
  · exact degreeZero_lift ρ D hz
  · refine ⟨homotopy0 ρ D z, homotopy0_mem_univ ρ D hz, ?_⟩
    rw [boundary_homotopy0 ρ D hz, hcycle, mul_zero, sub_zero]
  · refine ⟨homotopy1 ρ D z, homotopy1_mem_univ ρ D hz, ?_⟩
    rw [boundary_homotopy1 ρ D hz, hcycle, map_zero, sub_zero]
  · exact twoCycle_bounds ρ hρ hrank hz hcycle

end
end SourceBurnside.Stability.Frames
end
end OAI
