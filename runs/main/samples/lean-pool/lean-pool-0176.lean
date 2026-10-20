@[expose] public section

open Function MeasureTheory Set

open scoped ENNReal Topology ComplexConjugate

namespace QuadraticCarleson

noncomputable
section

namespace RealInterval

@[simp] theorem dilate_dilate_inv (a : ℝ) (ha : 0 < a) (I : RealInterval) :
    (I.dilate a ha).dilate a⁻¹ (inv_pos.mpr ha) = I := by
  cases I
  simp [dilate, ha.ne']

end RealInterval
end
end QuadraticCarleson
end
