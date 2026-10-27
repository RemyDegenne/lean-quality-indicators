public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinal

open Subgroup JankoTwelve

variable {G : Type} [Group G] [Finite G] {z : G} {fr : JankoFrame G z}

theorem exists_conj_mem_E (h : Hyp fr) (p12 : JankoProp12 fr) {x : G} (hx : x ∈ fr.I)
    (hxS : x ∉ fr.S) : ∃ e ∈ fr.E, e ≠ 1 ∧ e⁻¹ * x ∈ fr.S ∧ ∃ u ∈ fr.U, u * x * u⁻¹ = e := by
  rw [h.I_eq_E_sup_S] at hx
  obtain ⟨e, he, s, hs, rfl⟩ := exists_mul_of_mem_sup h.E_le_normalizer_S hx
  have he1 : e ≠ 1 := by rintro rfl; exact hxS (by simpa using hs)
  obtain ⟨u, hu, hue⟩ := exists_conj_eq_mul h p12 he he1 hs
  refine ⟨e, he, he1, by simpa using hs, u⁻¹, inv_mem hu, ?_⟩
  rw [← hue]
  group

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinal
end
