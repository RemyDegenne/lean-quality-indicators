@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing

open scoped TensorProduct

universe u

namespace UpperTriangularCoordinateRing

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]

@[simp] theorem universal_apply (i j : ι) :
    (universal K ι).1 i j = quotient K ι (matrix K ι i j) := rfl

end UpperTriangularCoordinateRing
end
end
