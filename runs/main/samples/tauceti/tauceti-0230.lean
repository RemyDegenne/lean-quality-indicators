public section

namespace TauCeti

variable (Γ : Type*) [Group Γ] [LinearOrder Γ]

namespace ConvexSubgroup

variable {Γ}

theorem mem_of_one_le_le {H : ConvexSubgroup Γ} {x h : Γ}
    (hh : h ∈ H) (h1 : 1 ≤ x) (hx : x ≤ h) : x ∈ H :=
  H.convex (one_mem H) hh h1 hx

end ConvexSubgroup
end TauCeti
end
