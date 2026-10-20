public section

namespace TauCeti

variable (Γ : Type*) [Group Γ] [LinearOrder Γ]

namespace ConvexSubgroup

variable {Γ}

section TotalOrder

variable {Γ : Type*} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]

@[simp]
theorem mem_maxAvoid_iff {γ : Γ} {hγ : γ ≠ 1} {x : Γ} :
    x ∈ maxAvoid hγ ↔ MulArchimedeanClass.mk γ < MulArchimedeanClass.mk x :=
  MulArchimedeanClass.mem_ballSubgroup_iff
    (fun h ↦ hγ (MulArchimedeanClass.mk_eq_top_iff.mp h))

end TotalOrder
end ConvexSubgroup
end TauCeti
end
