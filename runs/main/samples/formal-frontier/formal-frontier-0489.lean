public section

open CategoryTheory TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

universe u

namespace Scheme.Opens

variable {X : Scheme.{u}} (U : X.Opens)

lemma appTop_surjective_of_isClopen [IsAffine X] (hU : IsClopen (U : Set X)) :
    Function.Surjective U.ι.appTop := by
  let _ : IsClosedImmersion U.ι := U.isClosedImmersion_ι_of_isClosed hU.1
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine U.ι).2

end Scheme.Opens
end AlgebraicGeometry
end
end
