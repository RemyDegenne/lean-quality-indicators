public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin

open CFSG.Quasithin.H13.Ch3Sec3

open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat)

open scoped MatrixGroups commutatorElement

section KerAct

variable {G : Type} [Group G]

variable {K : Subgroup G}

theorem conj_mem_kerAct_of_mem_normalizer {X : Subgroup G} {h x : G}
    (hh : h ∈ Subgroup.normalizer (X : Set G)) (hx : x ∈ kerAct X) :
    h * x * h⁻¹ ∈ kerAct X := by
  have h1 := kerAct_conj_mem_map h hx
  have e : X.map (MulAut.conj h).toMonoidHom = X := A38.map_conj_eq_iff.mpr hh
  rwa [e] at h1

end KerAct
end CFSG.Quasithin.H13.NFa2
end
