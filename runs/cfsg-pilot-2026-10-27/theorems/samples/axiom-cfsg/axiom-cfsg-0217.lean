public section

namespace CFSG.Open

variable {G : Type*} [Group G] {p : ℕ} {E F : Subgroup G}

theorem IsElemAbelian.sup_of_commute (hE : IsElemAbelian p E) (hF : IsElemAbelian p F)
    (hc : ∀ a ∈ E, ∀ b ∈ F, a * b = b * a) : IsElemAbelian p (E ⊔ F) := by
  have hEF : E ⊔ F = Subgroup.closure ((E : Set G) ∪ F) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [hEF]
  refine IsElemAbelian.closure_of_commute ?_ ?_
  · rintro a (ha | ha) b (hb | hb)
    · exact hE.comm ha hb
    · exact hc a ha b hb
    · exact (hc b hb a ha).symm
    · exact hF.comm ha hb
  · rintro a (ha | ha)
    · exact hE.2 a ha
    · exact hF.2 a ha

end CFSG.Open
end
