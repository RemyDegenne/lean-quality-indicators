public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

section Congr

variable {V V' : Type*} [CommGroup V] [CommGroup V']

theorem kq_map_congr [Finite V] [Finite V'] (e : V ≃* V') (X : Subgroup (MulAut V)) (k : ℕ) :
    kq (X.map (congrHom e)) k = kq X k := by
  refine le_antisymm (kq_map_congr_le e X k) ?_
  have h := kq_map_congr_le e.symm (X.map (congrHom e)) k
  rwa [Subgroup.map_map, congrHom_symm_comp, Subgroup.map_id] at h

end Congr
end CFSG.Quasithin.H13
end
