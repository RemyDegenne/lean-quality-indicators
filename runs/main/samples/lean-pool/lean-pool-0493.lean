@[expose] public section

open Matrix Finset BigOperators Real MeasureTheory

noncomputable section

namespace VML

variable {X : Type*} [FlatTorus3 X]

lemma _root_.VML.VMLInput.hDiff_abc (p : VMLInput X) :
    FlatTorus3.IsSpatiallySmooth 2 p.aLoc ∧
    (∀ j, FlatTorus3.IsSpatiallySmooth 2 (fun y => p.bLoc y j)) ∧
    FlatTorus3.IsSpatiallySmooth 2 p.cLoc :=
  p.hDiff_maxwellian p.aLoc p.bLoc p.cLoc p.hMaxwellianForm

end VML
end
end
