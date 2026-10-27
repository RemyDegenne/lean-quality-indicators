public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Recognition.PresentedWords CFSG.CosetTable

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

section DJ

theorem DJ_le_normalizer :
    DJ ≤ Subgroup.normalizer ((Subgroup.zpowers (hswJ 6) : Subgroup J) : Set J) := by
  rw [DJ, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  rcases dJ_conj_t j with h | h
  · exact congrArg Subgroup.zpowers h
  · show Subgroup.zpowers (dJ j * hswJ 6 * (dJ j)⁻¹) = _
    rw [h, Subgroup.zpowers_inv]

end DJ
end CFSG.Sporadic.Th.Recog
end
