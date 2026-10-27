public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin CFSG.Quasithin.G6 Subgroup Equiv

theorem comm_mem_evenOn_eight_123 : ∀ m : PermMod 8,
    permAct 8 (a8c123 : Perm (Fin 8)) m * m⁻¹ ∈ evenOn 1 2 3 := by
  decide +kernel

end CFSG.Quasithin.H13.VolI
end
