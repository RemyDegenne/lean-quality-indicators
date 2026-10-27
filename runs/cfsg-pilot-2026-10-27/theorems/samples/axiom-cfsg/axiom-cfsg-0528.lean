public section

noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ASInputs.C10KH

open CFSG.Quasithin CFSG.Quasithin.JonesParshall

variable {D : FFModel}

section SecForm

variable {b : D.Amb → D.Amb → ZMod 2} (hb : SecPairing D b)

variable [Module (ZMod 2) (Additive D.Sec)]

theorem secForm_mk (x y : ↥D.sec) :
    secForm hb (Additive.ofMul (QuotientGroup.mk x)) (Additive.ofMul (QuotientGroup.mk y)) =
      b x y :=
  secVal_mk hb x y

end SecForm
end CFSG.Quasithin.ASInputs.C10KH
end
end
