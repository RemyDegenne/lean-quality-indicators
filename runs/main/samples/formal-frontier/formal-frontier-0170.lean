set_option warningAsError true

@[expose] public section

namespace Bass

universe u v

variable {R : Type u} [Ring R]

theorem principalRightIdeals_isCompl_of_isIdempotentElem {e : R}
    (he : IsIdempotentElem e) :
    IsCompl (principalRightIdeal e) (principalRightIdeal (1 - e)) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro y hyE hyC
    obtain ⟨a, ha⟩ := hyE
    obtain ⟨b, hb⟩ := hyC
    have hey : e * y = y := by
      calc
        e * y = e * (e * a) := by rw [ha]
        _ = (e * e) * a := by rw [mul_assoc]
        _ = e * a := by rw [he.eq]
        _ = y := ha
    have hec : e * y = 0 := by
      calc
        e * y = e * ((1 - e) * b) := by rw [hb]
        _ = (e * (1 - e)) * b := by rw [mul_assoc]
        _ = 0 := by rw [he.mul_one_sub_self, zero_mul]
    exact hey.symm.trans hec
  · rw [codisjoint_iff]
    apply top_unique
    intro y _
    rw [Submodule.mem_sup]
    refine ⟨e * y, ⟨y, rfl⟩, (1 - e) * y, ⟨y, rfl⟩, ?_⟩
    noncomm_ring

end Bass
end
