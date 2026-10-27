public section

namespace CFSG.ComponentClassification.Sol76T13.R12.Pcls

open CFSG Subgroup

variable {G Q S : Type*} [Group G] [Group Q] [Group S] (πG : G →* S) (πQ : Q →* S)

variable {πG πQ}

theorem pullbackFst_surjective (hπQ : Function.Surjective πQ) :
    Function.Surjective (pullbackFst πG πQ) := by
  intro g
  obtain ⟨y, hy⟩ := hπQ (πG g)
  exact ⟨⟨(g, y), (mem_pullbackSub πG πQ).mpr hy.symm⟩, rfl⟩

end CFSG.ComponentClassification.Sol76T13.R12.Pcls
end
