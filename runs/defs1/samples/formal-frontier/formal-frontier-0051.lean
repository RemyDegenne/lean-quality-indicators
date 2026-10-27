@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits UnitriangularCoordinateRing

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The canonical group-object compositor for pullback over a scalar tower,
assembled from Mathlib's `Over.pullbackComp` and its group-object functor. -/
def unitriangularGroupSchemeBaseChangeTowerIso
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (ι : Type u) [Fintype ι] [LinearOrder ι] :
    (Over.pullback (unitriangularBaseMap R T)).mapGrp.obj (unitriangularGroupScheme R ι) ≅
      (Over.pullback (unitriangularBaseMap S T)).mapGrp.obj
        ((Over.pullback (unitriangularBaseMap R S)).mapGrp.obj (unitriangularGroupScheme R ι)) :=
  (eqToIso (congrArg (fun f => (Over.pullback f).mapGrp.obj (unitriangularGroupScheme R ι))
      (unitriangularBaseMap_comp R S T).symm)).trans
    (((Functor.mapGrpNatIso (Over.pullbackComp (unitriangularBaseMap S T)
      (unitriangularBaseMap R S))).app (unitriangularGroupScheme R ι)).trans
    (Functor.mapGrpCompIso.app (unitriangularGroupScheme R ι))
    )

end AlgebraicGeometry
end
end
