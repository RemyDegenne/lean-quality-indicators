public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem ya7_ofFn_mem (σ : Equiv.Perm (Fin 7)) :
    List.ofFn σ ∈ List.permutations' (List.finRange 7) := by
  rw [List.mem_permutations']
  have hnd1 : (List.ofFn σ).Nodup := by
    rw [List.nodup_ofFn]
    exact σ.injective
  refine List.perm_of_nodup_nodup_toFinset_eq hnd1 (List.nodup_finRange 7) ?_
  ext x
  simp only [List.mem_toFinset, List.mem_ofFn, List.mem_finRange, iff_true]
  exact ⟨σ⁻¹ x, by simp⟩

end CFSG.Quasithin
end
