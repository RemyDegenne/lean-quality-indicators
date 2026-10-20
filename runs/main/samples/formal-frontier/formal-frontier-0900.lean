@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing

open scoped TensorProduct

universe u

namespace UnitriangularCoordinateRing

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]

theorem quotient_diag (i : ι) : quotient K ι (matrix K ι i i) = 1 := by
  have hz : quotient K ι (relation K ι i i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (relation_mem K ι i i)
  simpa [relation, map_sub, map_one, sub_eq_zero] using hz

end UnitriangularCoordinateRing
end
end
