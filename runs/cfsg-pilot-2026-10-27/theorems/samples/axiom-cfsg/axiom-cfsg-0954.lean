public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem glbPrimeCore_map_automorphism (p : ℕ) (H : Subgroup G) (φ : MulAut G) :
    (GLBPrimeCore p H).map φ.toMonoidHom = GLBPrimeCore p (H.map φ.toMonoidHom) := by
  refine le_antisymm (glbPrimeCore_map_automorphism_le p H φ) ?_
  apply (Subgroup.map_le_map_iff_of_injective (f := φ.symm.toMonoidHom) φ.symm.injective).mp
  rw [map_automorphism_symm_map]
  have hinv := glbPrimeCore_map_automorphism_le p (H.map φ.toMonoidHom) φ.symm
  rwa [map_automorphism_symm_map] at hinv

end CFSG.LocalAnalysis.RankThreeTheoremC
end
