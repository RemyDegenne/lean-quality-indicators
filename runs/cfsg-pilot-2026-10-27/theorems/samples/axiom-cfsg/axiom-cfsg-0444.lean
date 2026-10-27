public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem toG_comap {V : Subgroup G} (hV : IsElemAbelian 2 V) {H : Subgroup G} (hH : H ≤ V) :
    toG hV (H.comap (valHom hV)) = H := by
  rw [toG, Subgroup.map_comap_eq_self]
  rw [valHom_range hV]
  exact hH

end CFSG.Quasithin.C124
end
