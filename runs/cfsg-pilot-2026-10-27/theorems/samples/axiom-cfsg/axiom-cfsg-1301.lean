public section

namespace CFSG.ASVolI

open CFSG.Open

local instance burnsideF4gF4_neZero_rank : NeZero CFSG.Blueprint.Chevalley.Tag.F4.rank :=
  ⟨by decide⟩

local instance burnsideF4gF4Two_neZero_rank : NeZero CFSG.Blueprint.Chevalley.Tag.F4.rank :=
  ⟨by decide⟩

section F427KindTits

open CFSG.ASVolI.ChF

theorem burnsideF4g_F427_kind_Tits : burnsideF4f_F427_kind .Tits := by
  intro f E _ Gp M₁ M₂ hyp hGp
  obtain rfl : f = 1 := hyp.model.2.1
  exact burnsideF4gF4TwoInv_F427_Tits E Gp M₁ M₂ hyp hGp

end F427KindTits
end CFSG.ASVolI
end
