public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup

namespace Janko

open JankoPTwoThree JankoInvolution

variable {G : Type*} [Group G] {z : G} (hH : IsTwoANine (centralizer ({z} : Set G)))
  (e : centralizer ({z} : Set G) ⧸ center (centralizer ({z} : Set G)) ≃* alternatingGroup (Fin 9))

include hH

theorem D_inf_centralizer (hz : orderOf z = 2) :
    closure {t e, ℓ e ^ 2} ⊓ centralizer (zpowers (s₂ e) : Set G) = closure {t e, z} := by
  rw [closure_t_ℓ_sq_eq_map, zpowers_eq_closure, centralizer_closure,
    show s₂ e = ((liftOdd e sbar₂ : centralizer ({z} : Set G)) : G) from rfl,
    map_subtype_inf_centralizer, closure_t_y_inf_centralizer hH e, MonoidHom.map_closure,
    Set.image_pair, coe_subtype, coe_zbar_eq hz hH]
  rfl

end Janko
end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
end
