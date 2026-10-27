public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace AE8End

variable {Ω : Set (Subgroup G)} {u : G}

namespace Chart

variable (c : Chart Ω u)

section Ae8b2Aux

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr Equiv

theorem ae8b2_ofPerm_mem (σ : Equiv.Perm (Fin 6)) (hσ : Equiv.Perm.sign σ = 1) :
    ofPerm σ ∈ aeSub 6 := by
  rw [mem_aeSub]
  exact ⟨by simp [ofPerm, wsum], hσ⟩

end Ae8b2Aux
end Chart
end AE8End
end CFSG.ClassicalInvolution.Q3.Sec13
end
