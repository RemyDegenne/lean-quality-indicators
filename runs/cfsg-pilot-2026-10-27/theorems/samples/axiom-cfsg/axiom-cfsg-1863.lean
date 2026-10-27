public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin

namespace A7Mod

theorem eq_sum_smul_f (x : V7) : x = ∑ i, (x : Fin 7 → ZMod 2) i • f i := by
  apply Subtype.ext
  funext j
  have hx : ∑ i, (x : Fin 7 → ZMod 2) i = 0 := x.2
  have key : ∀ i, (x : Fin 7 → ZMod 2) i * (if j = i then 0 else 1) =
      (x : Fin 7 → ZMod 2) i + (if j = i then (x : Fin 7 → ZMod 2) i else 0) := by
    intro i
    generalize (x : Fin 7 → ZMod 2) i = a
    split_ifs
    · revert a
      decide
    · rw [mul_one, add_zero]
  have h2 : (↑(∑ i, (x : Fin 7 → ZMod 2) i • f i) : Fin 7 → ZMod 2) j =
      ∑ i, (x : Fin 7 → ZMod 2) i * (if j = i then 0 else 1) := by
    rw [Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, Pi.smul_apply, f_apply, smul_eq_mul]
  rw [h2, Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, Finset.sum_ite_eq,
    ite_eq_left (Finset.mem_univ j), hx, zero_add]

end A7Mod
end CFSG.Quasithin.H13
end
