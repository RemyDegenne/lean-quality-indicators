public section

namespace CFSG.Quasithin.H13.L14413

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.A6

open CFSG.Quasithin.H13.L32A

open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace XCtx_F4

open CFSG.Quasithin.H13.L14413.XCtx_F4

variable {T L V V₂ X : Subgroup G} {g : G} {C : XCtx_F4 G T L V V₂ X g} (K : C.Coords_F4)

theorem Coords_F4.z_comm_F4 {u : G} (hu : u ∈ fsuU T V) : u * K.z = K.z * u := by
  have hz : K.z ∈ centerOf (fsuU T V) := C.zU ▸ K.hz
  exact Subgroup.mem_centralizer_iff.mp hz.2 u hu

end XCtx_F4
end CFSG.Quasithin.H13.L14413
end
