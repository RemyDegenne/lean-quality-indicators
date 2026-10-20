@[expose] public section

namespace SteinhausThreeGap

theorem exists_back_return_multiplier (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    ∃ mn, mn < N ∧ Int.fract ((mn : ℝ) * a) = 1 - etaNeg a N := by
  have hmem : (1 : ℝ) - etaNeg a N ∈ orbit a N :=
    posOrbit_subset_orbit a N (max_posOrbit_mem a h2)
  obtain ⟨mn, hmn, hmnval⟩ := (mem_orbit_iff a N _).mp hmem
  exact ⟨mn, hmn, hmnval⟩

end SteinhausThreeGap
end
