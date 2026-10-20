public noncomputable section

open CategoryTheory

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace LayerRefinement

variable {old new : NormalLayer G}

variable {a b c : NormalLayer G}

@[reassoc]
theorem tateInfl_comp_tateHIsoH_hom (T : LayerRefinement old new) (F : Formation G) (r : ℕ)
    [NeZero r] :
    T.tateInfl F r ≫ (new.tateHIsoH F r).hom = (old.tateHIsoH F r).hom ≫ T.cohomologyInfl F r := by
  rw [tateInfl_def, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end LayerRefinement
end TauCeti.ClassFieldTheory
end
