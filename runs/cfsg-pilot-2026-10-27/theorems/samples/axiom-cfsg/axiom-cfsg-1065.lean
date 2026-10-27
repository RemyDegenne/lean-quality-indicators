public section

namespace CFSG.Quasithin.S151S9U

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem map_centerOf_le_centerOf_map {H Q : Type*} [Group H] [Group Q] (π : H →* Q)
    (B' : Subgroup H) : (centerOf B').map π ≤ centerOf (B'.map π) := by
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨Subgroup.mem_map_of_mem π hz.1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  obtain ⟨b, hb, rfl⟩ := hy
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hz.2 b hb]

end CFSG.Quasithin.S151S9U
end
