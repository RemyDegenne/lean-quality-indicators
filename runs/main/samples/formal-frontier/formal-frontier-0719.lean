@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing

open scoped TensorProduct

universe u

namespace UpperTriangularCoordinateRing

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]

theorem relation_mem (i j : ι) : relation K ι i j ∈ ideal K ι :=
  Ideal.subset_span ⟨(i, j), rfl⟩

end UpperTriangularCoordinateRing
end
end
