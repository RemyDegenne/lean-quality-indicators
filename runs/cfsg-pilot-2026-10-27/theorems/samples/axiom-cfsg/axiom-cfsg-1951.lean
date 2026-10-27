public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ggE0At_E7_holds
    : GGE0At .E7 :=
  ggE0At_E7 (excNoSuzukiReeAdj_holds (Or.inr (Or.inl rfl)))

end CFSG.StandardType
end
