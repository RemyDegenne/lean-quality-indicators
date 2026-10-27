public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

theorem ofCodeE_codeE {D : ExtData MC} (x : Ext D) : ofCodeE (codeE x) = x := by
  obtain ⟨a, e⟩ := x
  obtain ⟨h1, h2, h3⟩ := ofCode_codeMC a
  have k0 : (256 * 0 + codeMC a) / 256 = 0 := by omega
  have k1 : (256 * 1 + codeMC a) / 256 = 1 := by omega
  cases e
  · refine Ext.ext ?_ ?_
    · show ofCode (256 * 0 + codeMC a) = a
      rw [mul_zero, zero_add, h1]
    · show ((256 * 0 + codeMC a) / 256 % 2 == 1) = false
      rw [k0]
      rfl
  · refine Ext.ext ?_ ?_
    · show ofCode (256 * 1 + codeMC a) = a
      rw [mul_one, h2]
    · show ((256 * 1 + codeMC a) / 256 % 2 == 1) = true
      rw [k1]
      rfl

end KD8c
end CFSG.ComponentClassification.HSFLit
end
