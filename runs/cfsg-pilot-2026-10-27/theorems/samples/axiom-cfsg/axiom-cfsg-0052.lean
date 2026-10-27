public section

namespace CFSG.StandardType.FrameRoute.FS81

open Certificates.WE6Offender

open scoped Matrix Pointwise

theorem Psub_card (hc : check () = true) : Nat.card Psub = 81 := by
  have hmap : Nat.card (Psub.map (Subgroup.subtype (wE6 1))) = Nat.card Psub :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective (wE6 1))
  rw [Psub, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr P_le_wE6, P_card hc] at hmap
  exact hmap.symm

end CFSG.StandardType.FrameRoute.FS81
end
