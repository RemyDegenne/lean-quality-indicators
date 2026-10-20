public section

namespace TauCeti.E6Minuscule

local notation "Λ" => TauCeti.coordinateLattice (Fin 27)

local notation "𝓑" => TauCeti.coordinateLatticeBasis (Fin 27)

universe v v'

noncomputable section

/-- The carrier's matrix points, presented by its defining integral Hopf ideal. -/
abbrev pointsPresentation (A : Type v) [CommRing A] :
    TauCeti.GeneralLinear.IntegralPointsPresentation 27 definingIdeal A where
  val := points A
  property := points_def A

end
end TauCeti.E6Minuscule
end
