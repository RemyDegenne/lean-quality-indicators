namespace TauCeti.ValuationSpectrum

open AlgebraicGeometry CategoryTheory _root_.TopologicalSpace TauCeti.Huber
  TauCeti.Huber.PairOfDefinition

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- `Spa(A,A⁺)` equipped with the underlying commutative-ring presentation-limit presheaf. -/
noncomputable def presentationLimitPresheafedSpace (P : PairOfDefinition A)
    (Aplus : Subring A) : PresheafedSpace CommRingCat.{v} where
  carrier := TopCat.of ↥(spa Aplus)
  presheaf := presentationLimitPresheafInCommRingCat P Aplus

end
end TauCeti.ValuationSpectrum
