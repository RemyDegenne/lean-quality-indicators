public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.Stage1.Thm3.Sec4

open scoped Pointwise

section Conj

variable {G : Type} [Group G]

theorem centralizer_conj_eq
    (c x : G) :
    centralizer ({c * x * c⁻¹} : Set G) = cmap c (centralizer ({x} : Set G)) :=
  (GorensteinWalter.map_centralizer_singleton_conj c x).symm

end Conj
end CFSG.GH74.GLS
end
