public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin

variable {V : Type} [CommGroup V]

section Exists

theorem fixV_bot : fixV (⊥ : Subgroup (MulAut V)) = ⊤ :=
  eq_top_iff.mpr fun v _ x hx => by rw [Subgroup.mem_bot.mp hx]; rfl

end Exists
end CFSG.CGT.PushingUpLit.CGT6
end
