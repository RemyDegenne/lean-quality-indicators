@[expose] public section

set_option linter.style.haveILetI false

open scoped Topology

noncomputable section

universe u v w

namespace ValuationRing

theorem localization_isValuationRing
    {V : Type u} {Vₛ : Type v} [CommRing V] [IsDomain V] [ValuationRing V]
    (S : Submonoid V) [CommRing Vₛ] [Algebra V Vₛ] [IsLocalization S Vₛ]
    (hS : S ≤ nonZeroDivisors V) :
    letI : IsDomain Vₛ := IsLocalization.isDomain_of_le_nonZeroDivisors Vₛ hS
    ValuationRing Vₛ := by
  letI : IsDomain Vₛ := IsLocalization.isDomain_of_le_nonZeroDivisors Vₛ hS
  apply ValuationRing.iff_dvd_total.mpr
  constructor
  intro x y
  obtain ⟨r, s, d, hx, hy⟩ := IsLocalization.surj₂ S Vₛ x y
  rcases ValuationRing.dvd_total r s with hrs | hsr
  · left
    obtain ⟨c, rfl⟩ := hrs
    refine ⟨algebraMap V Vₛ c, ?_⟩
    apply (IsLocalization.map_units Vₛ d).mul_right_cancel
    exact hy.trans (by
      rw [map_mul, mul_assoc, mul_comm (algebraMap V Vₛ c), ← mul_assoc, hx])
  · right
    obtain ⟨c, rfl⟩ := hsr
    refine ⟨algebraMap V Vₛ c, ?_⟩
    apply (IsLocalization.map_units Vₛ d).mul_right_cancel
    exact hx.trans (by
      rw [map_mul, mul_assoc, mul_comm (algebraMap V Vₛ c), ← mul_assoc, hy])

end ValuationRing
end
end
