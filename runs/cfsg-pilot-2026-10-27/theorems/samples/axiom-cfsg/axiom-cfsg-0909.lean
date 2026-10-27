public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7G23

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed

variable {G : Type} [Group G]

theorem le_centralizer {K : Subgroup G} {z : G} (hz : IsUniqueInvolution K z) :
    K ≤ Subgroup.centralizer {z} :=
  fun _ hk => normalizer_le_centralizer hz (Subgroup.le_normalizer hk)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7G23
end
