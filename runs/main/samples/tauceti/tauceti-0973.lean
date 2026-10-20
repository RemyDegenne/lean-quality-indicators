public section

open scoped DirectSum

namespace TauCeti

theorem _root_.LinearMap.ker_eq_iSup_inf_of_map_le {R ι M N : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) {A : ι → Submodule R M}
    {A' : ι → Submodule R N} (hA : ⨆ i, A i = ⊤) (hA' : iSupIndep A')
    (hg : ∀ i, (A i).map g ≤ A' i) :
    LinearMap.ker g = ⨆ i, LinearMap.ker g ⊓ A i := by
  classical
  refine le_antisymm (fun x hx ↦ ?_) (iSup_le fun _ ↦ inf_le_left)
  obtain ⟨c, hc, rfl⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp A x).1 (hA ▸ Submodule.mem_top)
  have hsum : ∑ i ∈ c.support, g (c i) = 0 := by
    rw [← map_sum]
    simpa [Finsupp.sum] using hx
  have hzero := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero A').1 hA' c.support
    (fun i ↦ g (c i)) (fun i _ ↦ hg i ⟨c i, hc i, rfl⟩) hsum
  simp only [Finsupp.sum]
  exact Submodule.sum_mem _ fun i hi ↦
    Submodule.mem_iSup_of_mem i ⟨LinearMap.mem_ker.2 (hzero i hi), hc i⟩

end TauCeti
end
