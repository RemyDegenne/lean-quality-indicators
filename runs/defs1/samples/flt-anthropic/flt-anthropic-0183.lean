universe v' u' wE vE uE v₁ v₂ u₁ u₂ u w' w v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

noncomputable def fppfH0SectionsIsoApp (F : Sheaf (smallFppfTopology S) Ab.{u + 1}) :
    (fppfCohomologyFunctor S 0).obj F ≅ F.obj.obj (op (fppfTerminal S)) :=
  AddEquiv.toAddCommGrpIso
    (X := (fppfCohomologyFunctor S 0).obj F)
    (Y := F.obj.obj (op (fppfTerminal S)))
    (fppfCohomologyZeroAddEquiv S F)

end AlgebraicGeometry.Scheme
