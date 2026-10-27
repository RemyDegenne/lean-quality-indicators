public section

namespace CFSG.Quasithin.F112R.AJ2L

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.ComponentClassification.J2Cover CFSG.KC.SLDc

theorem permU_mul_permA_mem : permU * permA ∈ R :=
  R.mul_mem permU_mem_R (P_le_R (Subgroup.subset_closure (Set.mem_insert _ _)))

end CFSG.Quasithin.F112R.AJ2L
end
