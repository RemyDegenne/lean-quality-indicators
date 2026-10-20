@[expose] public section

namespace Connes

namespace PaperFourierAction

open MeasureTheory

open Construction

open Construction.PaperKernel

open PaperDualHaar

open PaperFourier

noncomputable section

/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D

end
end PaperFourierAction
end Connes
end
