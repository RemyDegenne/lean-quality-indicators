open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries

variable {G : Type u} {K : Type v}

variable [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]

variable [Field K]

omit [AddCommGroup G] [IsOrderedAddMonoid G] in
theorem exists_max_mem_support {x : K⟦G⟧} (hfin : x.support.Finite) (hx : x ≠ 0) :
    ∃ a ∈ x.support, ∀ g ∈ x.support, g ≤ a := by
  classical
  have hne : hfin.toFinset.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]
    exact HahnSeries.support_nonempty_iff.mpr hx
  obtain ⟨a, ha, hmax⟩ := hfin.toFinset.exists_max_image id hne
  exact ⟨a, (Set.Finite.mem_toFinset hfin).mp ha,
    fun g hg ↦ hmax g ((Set.Finite.mem_toFinset hfin).mpr hg)⟩

end HahnSeries
end
