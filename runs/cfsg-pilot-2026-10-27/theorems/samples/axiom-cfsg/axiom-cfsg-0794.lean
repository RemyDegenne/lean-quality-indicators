public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable

open CFSG.ComponentClassification.GrSLit.L34Facts

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

section Setting

theorem zz_comm (h : IsQSetting q l) (i j : ZMod 4) (g : E) : g * zz l i j = zz l i j * g :=
  h.psi_comm _ g

end Setting
end CFSG.ComponentClassification.GrSLit.L34Facts.Real
end
