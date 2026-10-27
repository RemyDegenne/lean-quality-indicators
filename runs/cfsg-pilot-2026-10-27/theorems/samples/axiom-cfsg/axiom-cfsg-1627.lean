public section

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU
  CFSG.LieType.Universal.Unitary

open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local

open CFSG.GH74.GLS.IVK

theorem luLocalLeaf'_gh_of_cores
    (hLin : LUA3Lin_gh) (hUni : LUA3Uni_gh) (hFive : LUA3Five'_gh) : LULocalLeaf'_gh :=
  luLocalLeaf'_gh_of_leaves luGenLeaf (luA3Leaf'_gh_of_cores hLin hUni hFive)

end CFSG.GH74.GLS.LU.Local
end
