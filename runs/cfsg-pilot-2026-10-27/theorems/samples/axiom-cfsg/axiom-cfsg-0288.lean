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

theorem ae8b2_cz_spec : ∀ i : Fin 6, i ≠ 0 →
    (Finset.univ \ {0, ae8b2_cz i}).card = 4 ∧ (Finset.univ \ {i, ae8b2_cz i}).card = 4 ∧
      ae8b2_ind (Finset.univ \ {0, ae8b2_cz i}) + ae8b2_ind (Finset.univ \ {i, ae8b2_cz i}) =
        ae8b2_ind {0, i} := by
  unfold ae8b2_cz
  decide

end Ae8b2Aux
end Chart
end AE8End
end CFSG.ClassicalInvolution.Q3.Sec13
end
