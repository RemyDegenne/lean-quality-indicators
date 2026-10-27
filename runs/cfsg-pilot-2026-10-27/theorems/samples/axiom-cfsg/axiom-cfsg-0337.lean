public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin S4

variable {G : Type*} [Group G]

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

theorem card_K_eq [Finite G] (hGz : Subgroup.centralizer ({E.z} : Set G) = T) :
    Nat.card E.K = 128 * E.zK.ncard := by
  have h := ncard_conjClass_mul_card E.K E.z
  rw [hGz, inf_eq_right.mpr E.T_le_K, E.card_T] at h
  rw [← h, mul_comm]
  rfl

end Emb
end CFSG.Quasithin.A10
end
