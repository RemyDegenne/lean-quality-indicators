public section

open MeasureTheory Set

open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

section Cutoff

variable {U : Set Vec3} {χ : Vec3 → ℝ} {v ζ : Vec3 → Vec3}

theorem spatialDeriv_eq_zero_of_notMem_tsupport {g : Vec3 → ℝ} {x : Vec3}
    (hx : x ∉ tsupport g) (i : Fin 3) : spatialDeriv g i x = 0 :=
  image_eq_zero_of_notMem_tsupport (f := spatialDeriv g i)
    fun h => hx (tsupport_fderiv_apply_subset ℝ (basisVec i) h)

end Cutoff
end ESS
end
end
