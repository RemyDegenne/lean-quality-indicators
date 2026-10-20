@[expose] public section

open CategoryTheory Limits Set TopologicalSpace Topology

universe v u w

noncomputable section

namespace TopCat

/-- The inclusion to the coproduct as a bundled continuous map. -/
abbrev sigmaι {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) : α i ⟶ ↧(Σ i, α i) := by
  refine ofHom (ContinuousMap.mk ?_ ?_)
  · apply Sigma.mk i
  · continuity

end TopCat
end
end
