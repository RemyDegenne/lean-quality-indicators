public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Ly0

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Recognition.McLMultiplier Equiv
  Subgroup

section Sets

variable {D : Cp3Data}

theorem fixSet_mem_fam (h : tabCheck = true) (hv : cp3Valid D = true) :
    {x | y0G x = x} ∈ fam D := by
  refine ⟨0, by norm_num, ?_⟩
  rw [sets_eq h hv 0 (by norm_num)]
  obtain ⟨-, -, hw0, -⟩ := cp3Valid_spec hv
  rw [hw0, wG_nil]
  simp

end Sets
end CFSG.Sporadic.Recognition.LyonsSims.Ly0
end
