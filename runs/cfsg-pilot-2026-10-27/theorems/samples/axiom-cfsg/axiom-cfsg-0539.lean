public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab

open KD7 Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace AD

theorem ι_conj_w₁ (H : AD S T₁) (a : MA) : H.ι a * H.ι MA.w₁ * (H.ι a)⁻¹ = H.ι MA.w₁ ∨
    H.ι a * H.ι MA.w₁ * (H.ι a)⁻¹ = H.ι MA.z * H.ι MA.w₁ := by
  rcases conj_w₁_all a with h | h
  · left; simpa only [map_mul, map_inv] using congrArg H.ι h
  · right; simpa only [map_mul, map_inv] using congrArg H.ι h

end AD
end KD8ab
end CFSG.ComponentClassification.HSFLit
end
