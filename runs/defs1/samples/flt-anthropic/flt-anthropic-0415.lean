namespace P2MW.S_CerednikDrinfeld_BruhatTits_exists_iso_tree_mulEquiv_projGenLinGroup_baseChange

set_option autoImplicit false

open scoped MatrixGroups

namespace CerednikDrinfeld

namespace BruhatTits

namespace TransportPGL

p2m_open

open LT.LatticeTree Matrix

variable {R' K' R K : Type} [CommRing R'] [Field K'] [Algebra R' K'] [CommRing R] [Field K] [Algebra R K]

def pglMap (ι : IntegralHom R' K' R K) : PGL(2, K') →* PGL(2, K) :=
  ProjGenLinGroup.lift ((ProjGenLinGroup.mk (n := Fin 2) (R := K)).comp ι.mapGL) (mk_comp_mapGL_comp_scalar ι)

end TransportPGL
end BruhatTits
end CerednikDrinfeld
end P2MW.S_CerednikDrinfeld_BruhatTits_exists_iso_tree_mulEquiv_projGenLinGroup_baseChange
