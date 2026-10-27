public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed

open scoped commutatorElement

section Cfg

variable {G : Type*} [Group G]

namespace TwoCfg

variable {t v : G} {J : Subgroup G} (h : TwoCfg t v J)

include h

theorem tv_ne_one (htop : centralizer ({t} : Set G) ≠ ⊤) : t * v ≠ 1 := by
  intro h1
  apply h.v_ne_t htop
  have h2 : v = t⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [h2]
  exact inv_eq_of_mul_eq_one_right h.t_sq

end TwoCfg
end Cfg
end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
end
