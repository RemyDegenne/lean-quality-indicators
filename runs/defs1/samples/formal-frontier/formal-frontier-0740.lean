@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat Opposite

universe u

namespace Profinite

/-- Transport of the canonical finite-quotient limit along the included-diagram
isomorphism. -/
noncomputable def skeletalQuotientConeIsLimit (T : Profinite.{u}) :
    IsLimit (skeletalQuotientCone T) := by
  exact (IsLimit.postcomposeHomEquiv
    (Functor.isoWhiskerRight (skeletalQuotientDiagramIso T).symm FintypeCat.toProfinite)
    T.asLimitCone).symm T.asLimit

end Profinite
end
