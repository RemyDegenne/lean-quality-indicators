public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem ruEElt_zero :
    ruEElt 0 = ruZ := by
  have h := rep_ruEElt (i := 0) (by norm_num)
  rw [ruE_check.2.2.2.1] at h
  exact h.unique rep_ruZ

end CFSG.Sporadic.RuSchreier
end
