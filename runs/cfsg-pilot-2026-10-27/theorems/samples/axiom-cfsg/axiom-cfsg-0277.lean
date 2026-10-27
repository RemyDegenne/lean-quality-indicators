public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

section Sit

variable {V H T A L K : Subgroup G} {i : ℕ}

theorem Sit813.relIndex_v1Grp (h : Sit813 V H T i A L K)
    (h4 : Nat.card (v1Grp V H T A K) = 4) : (v1Grp V H T A K).relIndex V = 2 := by
  have e := Subgroup.relIndex_mul_card (H := v1Grp V H T A K) (K := V)
  rw [inf_of_le_left Sit813.v1Grp_le_V, h4, h.card_V_eq_eight] at e
  omega

end Sit
end CFSG.LocalAnalysis.WeakClosure81
end
