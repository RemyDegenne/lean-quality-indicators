public section

noncomputable section

open CategoryTheory Limits TopologicalSpace

open scoped FundamentalGroupoid

universe u v

namespace TauCeti.FundamentalGroupoid

open TauCeti.TopCat

variable {X : TopCat.{v}} {ι : Type u} (U : ι → Opens X)

@[simp]
lemma cechCocone_pt : (cechCocone U).pt =
    _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.obj X := by
  rfl

end TauCeti.FundamentalGroupoid
end
end
