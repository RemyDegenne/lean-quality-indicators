public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin Sigma47

namespace RuDataM

variable {G : Type} [Group G] [Finite G] {M : RuDataM G}

namespace Conf47

variable (C : Conf47 M)

attribute [local instance] fact_prime_five

namespace Fives

variable {C} (D : C.Fives)

theorem rhoT_inv {w : G} (hw : w * C.t = C.t * w) : D.rhoT w⁻¹ = (D.rhoT w)⁻¹ := by
  unfold rhoT
  rw [show D.ct * w⁻¹ * D.ct⁻¹ = (D.ct * w * D.ct⁻¹)⁻¹ by group,
    M.phiG_inv (D.ctconj_mem_H hw)]

end Fives
end Conf47
end RuDataM
end CFSG.Quasithin.RuType
end
