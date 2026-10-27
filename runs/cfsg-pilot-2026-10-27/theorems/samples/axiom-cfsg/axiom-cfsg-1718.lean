public section

namespace CFSG.Quasithin.F112R.St84.AutJ2Model

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.SmallOddCore.Native

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

open CFSG.ComponentClassification.J2Cover CFSG.Fischer

open CFSG.Quasithin.F112R.St84.Heis

theorem autJ2VtxC5_gm (h : autJ2VtxC5 () = true) : conjGenOK gmRT γM = true := by
  have h' := h
  simp only [autJ2VtxC5, Bool.and_eq_true] at h'
  exact h'.2

end CFSG.Quasithin.F112R.St84.AutJ2Model
end
