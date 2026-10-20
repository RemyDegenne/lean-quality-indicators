public section

open CategoryTheory

open scoped MonoidAlgebra

namespace TauCeti

universe u

section CommRing

variable (k : Type u) [CommRing k] {G : Type u} [Group G] [Finite G] (S : Subgroup G)

theorem indK0_indK0 {T : Subgroup G} (h : S ≤ T)
    (x : ExactK0 (finiteModulesExactStructure k[S.subgroupOf T])) :
    indK0 k T (indK0 k (S.subgroupOf T) x) =
      indK0 k S (resK0 k (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom x) :=
  DFunLike.congr_fun (indK0_comp_indK0 k S h) x

end CommRing
end TauCeti
end
