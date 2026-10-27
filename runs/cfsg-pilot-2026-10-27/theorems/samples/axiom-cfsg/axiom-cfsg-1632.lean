public section

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.LU24 CFSG.Quasithin.H.LU CFSG.Monster.Code
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Open CFSG.Quasithin.H.Coc

theorem V10_lt_top : V10 < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro h
  have h8 : toW 11 8 ∈ V10 := by rw [h]; exact Subgroup.mem_top _
  have hpar := (toW_mem_V10_iff (by norm_num)).1 h8
  rw [par_eight] at hpar
  exact Bool.false_ne_true hpar.symm

end CFSG.ASVolI.H16
end
