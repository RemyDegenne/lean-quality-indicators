@[expose] public section

noncomputable section

open Set Submodule

attribute [local instance] Classical.decEq

namespace LinearMap.CountableInvariantCoordinateFiltration

universe uS uJ

variable {S : Type uS} [Ring S] {κ : Type uJ}

variable {q : (κ →₀ S) →ₗ[S] (κ →₀ S)}

theorem incrementToRange_injective
    (F : LinearMap.CountableInvariantCoordinateFiltration q) (i : κ) :
    Function.Injective (F.incrementToRange i) := by
  intro x y hxy
  have hval : ((F.incrementToRange i x : LinearMap.range q) : κ →₀ S) =
      ((F.incrementToRange i y : LinearMap.range q) : κ →₀ S) :=
    congrArg (fun z : LinearMap.range q ↦ (z : κ →₀ S)) hxy
  exact Subtype.ext (Subtype.ext hval)

end LinearMap.CountableInvariantCoordinateFiltration
end
end
