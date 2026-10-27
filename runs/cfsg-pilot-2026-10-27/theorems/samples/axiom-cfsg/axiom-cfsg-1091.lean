public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster.B.Co2 (v0 wAct_mul)

theorem cpsi_cvOf
    (k : Jhat) : cpsi ⟨cvOf (jhatS k), jhatS_mem_cPi0 k⟩ = piPt k := by
  apply piPt_eq_of
  have h := (jhatS_mem_cPi0 k).choose_spec.2
  rw [mul_one] at h
  exact h.symm

end CFSG.Monster.B.TwoA.Amalgam
end
