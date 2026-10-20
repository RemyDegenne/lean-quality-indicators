@[expose] public section

open Set Schoenflies

open scoped Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

namespace SplitData

variable {d : S.SplitData}

theorem skeletonSet_subset_realize {R : S.Realization} {earPos : γ → Plane}
    {earDraw : γ → ℝ → Plane} (hE : d.EarCrosscut R earPos earDraw) :
    R.skeletonSet ⊆ (d.realize R earPos earDraw hE).skeletonSet :=
  (skeletonSet_realize hE).symm ▸ Set.subset_union_left

end SplitData
end CellStructure
end Schoenflies
end
