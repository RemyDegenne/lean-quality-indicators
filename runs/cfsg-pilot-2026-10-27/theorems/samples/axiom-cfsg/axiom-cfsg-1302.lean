public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

open scoped commutatorElement

variable {G : Type} [Group G]

theorem map_conj_one (B : Subgroup G) : B.map (MulAut.conj (1 : G)).toMonoidHom = B := by
  ext x
  simp [Subgroup.mem_map]

end CFSG.QuasithinUnique.A5.G3
end
