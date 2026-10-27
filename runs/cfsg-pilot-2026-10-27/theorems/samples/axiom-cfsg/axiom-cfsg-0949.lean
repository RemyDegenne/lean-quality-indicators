public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace DEHyp

variable {Ω : Set (Subgroup G)} (h : DEHyp Ω)

include h

theorem rhoD_range {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e) :
    (h.rhoD he).range = ⊤ := by
  rw [eq_top_iff, ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin 3) (K := ZMod 2), Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  obtain ⟨i, j, hij, c⟩ := t
  rcases TL4.zmod_two_cases c with rfl | rfl
  · rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk,
      Matrix.SpecialLinearGroup.transvection_coeff_zero]
    exact (h.rhoD he).range.one_mem
  · rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
    exact deb_transvection_mem_range h he hij

end DEHyp
end CFSG.ClassicalInvolution.Q3.Sec13
end
