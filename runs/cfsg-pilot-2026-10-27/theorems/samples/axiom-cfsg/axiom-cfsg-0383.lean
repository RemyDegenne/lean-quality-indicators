public section

namespace CFSG.Quasithin.H13.S125KG.J4

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Sporadic.J4

open CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc CFSG.Quasithin.F134.J4E9 CFSG.Quasithin.J4Fam

open CFSG.QuasithinUnique.Ch1.SporLat

open CFSG.Quasithin.A312M24 (G24)

theorem Eg_le_lift
    (Y : Subgroup G24) : Eg uJ 11 ≤ lift Y := by
  intro x hx
  have hxH : x ∈ Hj := Eg_le_Hj hx
  refine ⟨⟨x, hxH⟩, ?_, rfl⟩
  have hk : (⟨x, hxH⟩ : ↥Hj) ∈ fHj.ker := by rw [ker_fHj]; exact hx
  show fHj ⟨x, hxH⟩ ∈ Y
  rw [MonoidHom.mem_ker.mp hk]
  exact Y.one_mem

end CFSG.Quasithin.H13.S125KG.J4
end
