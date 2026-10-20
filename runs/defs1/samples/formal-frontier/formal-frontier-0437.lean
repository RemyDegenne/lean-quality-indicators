@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat Opposite

universe u

namespace Profinite

/-- The finite-discrete limiting cone of a chosen presentation. -/
noncomputable def indDualPresentationCone
    (Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ) :
    Cone ((indDualPresentationDiagram Q ⋙ FintypeCat.Skeleton.incl) ⋙
      FintypeCat.toProfinite) :=
  Profinite.limitCone _

end Profinite
end
