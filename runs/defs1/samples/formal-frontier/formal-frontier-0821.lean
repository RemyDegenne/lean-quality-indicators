@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat Opposite

universe u

namespace Profinite

/-- The cone with point `T` obtained by transporting the ordinary finite-quotient cone
across the skeleton counit. -/
noncomputable def skeletalQuotientCone (T : Profinite.{u}) :
    Cone ((skeletalQuotientDiagram T ⋙ FintypeCat.Skeleton.incl) ⋙
      FintypeCat.toProfinite) :=
  (Cone.postcompose (Functor.isoWhiskerRight (skeletalQuotientDiagramIso T).symm
    FintypeCat.toProfinite).hom).obj T.asLimitCone

end Profinite
end
