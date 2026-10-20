@[expose] public section

namespace HsVirial

open Set

open Metric

open SimpleGraph

open MeasureTheory

open scoped BigOperators ENNReal

noncomputable section

lemma hardSphereTreeDifference_eq_coordinate_sub {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    (r : HardSphereConfiguration k 3) (i : Fin (k - 1)) :
    hardSphereTreeDifference hT r i =
      r i - hardSpherePosition r (hardSphereTreeParent hT i) := by
  simp [hardSphereTreeDifference]

end
end HsVirial
end
