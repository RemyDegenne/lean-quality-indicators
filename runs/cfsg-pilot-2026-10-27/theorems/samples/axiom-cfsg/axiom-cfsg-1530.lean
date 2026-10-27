public section

namespace CFSG.ASVolI

open CFSG.Open

theorem burnsideC6h_c64a_swap_ne_one : Equiv.swap (0 : Fin 7) 1 ≠ 1 := by
  intro h
  have h1 := congrArg (fun f : Equiv.Perm (Fin 7) => f 0) h
  simp only [Equiv.swap_apply_left, Equiv.Perm.coe_one, id_eq] at h1
  exact absurd h1 (by decide)

end CFSG.ASVolI
end
