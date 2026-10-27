public section

namespace CFSG.Quasithin.ModH.He2

open CFSG.QuasithinUnique.Ch1.SporLat.He (heIncl)

open CFSG.Open CFSG.Quasithin.ModH CFSG.Quasithin.ModH.He1

variable {J : Type} [Group J] [Finite J] (hl : HeLat J)

omit [Finite J] in
theorem S_le_map {X : Subgroup J} {α : MulAut J} (hX : hl.S ≤ X)
    (hα : hl.S.map α.toMonoidHom = hl.S) : hl.S ≤ X.map α.toMonoidHom := by
  calc hl.S = hl.S.map α.toMonoidHom := hα.symm
    _ ≤ X.map α.toMonoidHom := Subgroup.map_mono hX

end CFSG.Quasithin.ModH.He2
end
