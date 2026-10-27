public section

namespace CFSG.ASVolI

open CFSG.Open

local instance burnsideF4gF4_neZero_rank : NeZero CFSG.Blueprint.Chevalley.Tag.F4.rank :=
  ⟨by decide⟩

local instance burnsideF4gF4Two_neZero_rank : NeZero CFSG.Blueprint.Chevalley.Tag.F4.rank :=
  ⟨by decide⟩

noncomputable section G2TwoInvWrap

section G2Model

open CFSG.ASVolI.ChF

open CFSG.Quasithin (u33GenP u33GenPG u33Data u33Extra u33z u33Z U33G u33PresHom u33PresHom_genPG
  u33Tel_hom u33Tel u33Phi' g2HomC g2RhoC g2IndexTwoData G2Group two_eq_zero_of_card_two
  eq_zero_or_eq_one_of_card_two u33PresHom_injective u33Tel_zero card_u33Pres u33_orders
  g2HomC_injective)

open CFSG.Quasithin.F6.G22Perm (sEl psi psi_f psi_rho psi_injective exists_rep rhoPow)

open CFSG.Quasithin.F6.G22Shape (lat mem_S_iff sEl_mem_S card_S reprN_mul reprN_gen reprN_genInv
  reprN_rho reprN_one eqN)

variable
  {K : Type} [Field K]

theorem burnsideF4gG2TwoInv_ctr_S (h2 : (2 : K) = 0) (hk2 : ∀ c : K, c = 0 ∨ c = 1)
    {w : G2Group K} (hw : w ∈ ctr (lat h2 hk2).S) : w = 1 ∨ w = sEl h2 26 := by
  obtain ⟨-, hc⟩ := burnsideF4gG2TwoInv_mem_ctr.1 hw
  exact burnsideF4gG2TwoInv_cent_S h2 hk2 (fun t ht => (hc t ht).symm)

end G2Model
end G2TwoInvWrap
end CFSG.ASVolI
end
