@[expose] public section

namespace Connes

namespace PaperDualHaar

open MeasureTheory

open Construction

open Construction.PaperKernel

open BinaryPontryaginDual

noncomputable section

/-- The actual Zhou dual coordinates. Paper: §3. -/
def characterCoordinatesEquiv :
    PaperCharacterSpace ≃+ PaperFactorIsomorphism.DualCoordinates :=
  characterLinearEquiv.trans PaperDualCoordinates.dualEquiv.toAddEquiv

end
end PaperDualHaar
end Connes
end
