public section

noncomputable section

open scoped unitInterval

namespace TauCeti.UniversalCover

variable {G : Type*} [Group G] [TopologicalSpace G]

variable [IsTopologicalGroup G]

theorem inv_ofBasedPath (α : BasedPath (1 : G)) :
    (ofBasedPath 1 α)⁻¹ = ofBasedPath 1 (.ofPath (α.toPath.inv.cast inv_one.symm rfl)) := by
  rw [ofBasedPath_def, inv_mk, ofBasedPath_ofPath]

end TauCeti.UniversalCover
end
end
