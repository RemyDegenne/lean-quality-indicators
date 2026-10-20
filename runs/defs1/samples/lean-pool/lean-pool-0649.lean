@[expose] public section

namespace Connes

namespace PaperDualTopology

open MeasureTheory

open Construction

open Construction.PaperKernel

open BinaryPontryaginDual

open PaperDualHaar

open PaperDualCoordinates

open PaperFactorIsomorphism

noncomputable section

/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D

end
end PaperDualTopology
end Connes
end
