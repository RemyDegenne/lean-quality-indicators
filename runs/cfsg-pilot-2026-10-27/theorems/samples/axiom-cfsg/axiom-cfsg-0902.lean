public section

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

namespace FFH0Hyp

variable {G : Type} [Group G] [Finite G] {M T V : Subgroup G} {hU : IsElemAbelian 2 V}
  {I : Finset (Subgroup (MulAut (IntMod V hU)))} {L : Subgroup (MulAut (IntMod V hU))}
  (h : FFH0Hyp M T V hU I L)

include h

theorem autI_baum_le (hMN : M ≤ Subgroup.normalizer (V : Set G)) :
    autI hU (baum T) ≤ autI hU (thompsonJ M) :=
  autI_baum_le_autI_thompsonJ hMN h.sylow h.V_le h.fam h.thompsonJ_eq
    (thompsonJ_le_thompsonJ_of_isSylowTwoOf h.sylow) h.perm

end FFH0Hyp
end CFSG.AGLEmbeddingD2.Tits.MsidePrelim
end
