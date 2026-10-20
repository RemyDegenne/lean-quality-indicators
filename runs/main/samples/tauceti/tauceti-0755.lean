public section

namespace TauCeti

variable (Γ : Type*) [Group Γ] [LinearOrder Γ]

namespace ConvexSubgroup

variable {Γ}

@[simp]
theorem toSubgroup_lt {H K : ConvexSubgroup Γ} : H.toSubgroup < K.toSubgroup ↔ H < K := by
  simp [lt_iff_le_not_ge, toSubgroup_le]

end ConvexSubgroup
end TauCeti
end
