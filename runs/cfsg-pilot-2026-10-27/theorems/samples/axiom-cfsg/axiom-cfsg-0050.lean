public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup

theorem card_S0 : Nat.card ↥S0 = 8 :=
  (nat_card_subgroup_of_mem_list (fun _ => mem_S0_iff) S0List_nodup).trans rfl

end CFSG.Sporadic.Recognition.LyonsSims
end
