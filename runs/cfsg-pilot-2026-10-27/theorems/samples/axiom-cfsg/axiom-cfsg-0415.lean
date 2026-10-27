public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

variable {G H : Type*} [Group G] [Group H]

theorem coe_centralizerMulEquiv (e : G ≃* H) (x : G) (g : Subgroup.centralizer ({x} : Set G)) :
    ((centralizerMulEquiv e x g : Subgroup.centralizer ({e x} : Set H)) : H) = e g :=
  rfl

end CFSG.Sporadic.FischerOddCore
end
