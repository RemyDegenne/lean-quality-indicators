@[expose] public section

open Matrix Finset BigOperators Real MeasureTheory

noncomputable section

namespace VML

namespace FlatTorus3

variable {X : Type*} [FlatTorus3 X]

lemma _root_.VML.FlatTorus3.IsSpatiallySmooth.of_le {n m : ℕ∞} {f : X → ℝ}
    (h : IsSpatiallySmooth n f) (hle : m ≤ n) : IsSpatiallySmooth m f :=
  hDiff_of_le f hle h

end FlatTorus3
end VML
end
end
