public section

namespace CFSG.Quasithin.H13.Par32

open CFSG.Quasithin.H13.A6Coc

theorem mem_r1_iff (x : Equiv.Perm (Fin 6)) : x ∈ r1 ↔ x ∈ elemsR1 := by
  constructor
  · refine closure_subset invol_R1 (by simp [elemsR1]) (fun y hy s hs => ?_) x
    exact mem_of_code_mem (by rw [codes_R1]; exact rmul_R1 y hy s hs)
  · intro hx
    have ha : a1 ∈ r1 := Subgroup.subset_closure (by simp [gensR1])
    have hb : b1 ∈ r1 := Subgroup.subset_closure (by simp [gensR1])
    have hc : c45 ∈ r1 := Subgroup.subset_closure (by simp [gensR1])
    simp only [elemsR1, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [r1.one_mem, ha, hb, hc, r1.mul_mem ha hb, r1.mul_mem ha hc, r1.mul_mem hb hc,
      r1.mul_mem (r1.mul_mem ha hb) hc]

end CFSG.Quasithin.H13.Par32
end
