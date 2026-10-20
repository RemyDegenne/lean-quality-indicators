public section

namespace TauCeti

variable {G X : Type*} [Group G] [MulAction G X]

lemma MulAction.orbitRelQuotient_smul_eq_smul_iff_mul_inv_mem [IsCancelSMul G X] (H : Subgroup G)
    (x : X) (g k : G) : (Quotient.mk'' (g • x) : MulAction.orbitRel.Quotient H X) =
        Quotient.mk'' (k • x) ↔
      g * k⁻¹ ∈ H := by
  constructor
  · intro h
    rw [Quotient.eq'', MulAction.orbitRel_apply] at h
    rcases h with ⟨l, hl⟩
    have hmul : ((l : G) * k) • x = g • x := by
      simpa [Subgroup.smul_def, smul_smul] using hl
    have hg : (l : G) * k = g := IsCancelSMul.right_cancel _ _ x hmul
    simp [← hg, mul_assoc]
  · intro hg
    rw [Quotient.eq'', MulAction.orbitRel_apply]
    exact ⟨⟨g * k⁻¹, hg⟩, by simp [Subgroup.smul_def, smul_smul]⟩

end TauCeti
end
