@[expose] public section

noncomputable section

universe u v w w'

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace FundamentalGroupoid

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

@[simp]
theorem openCoverCocone_pt (U : ι → Opens X) :
    (openCoverCocone U).pt = Grpd.of (FundamentalGroupoid X) := rfl

end FundamentalGroupoid
end
end
