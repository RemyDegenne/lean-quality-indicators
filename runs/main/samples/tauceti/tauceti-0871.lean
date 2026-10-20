public noncomputable section

open CategoryTheory Representation

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace NormalLayer

variable (L : NormalLayer G) (F : Formation G) (g h : G)

theorem groundLevelEquiv_conjugateCohomologyIso_zero_apply (x : L.H F 0) :
    (L.conjugate g).groundLevelEquiv F
        ((groupCohomology.H0Iso ((L.conjugate g).rep F)).hom.hom
          ((L.conjugateCohomologyIso F g 0).hom x)) =
      L.conjugateGroundLevelEquiv F g
        (L.groundLevelEquiv F ((groupCohomology.H0Iso (L.rep F)).hom.hom x)) := by
  refine Subtype.ext ?_
  rw [groundLevelEquiv_apply_coe, conjugateGroundLevelEquiv_apply_coe, groundLevelEquiv_apply_coe,
    conjugateCohomologyIso, groupCohomology.mapIso_hom]
  refine (congrArg Subtype.val (groupCohomology.map_H0Iso_hom_f_apply _ _ x)).trans ?_
  exact L.conjugateCoefficientEquiv_apply_coe F g _

end NormalLayer
end TauCeti.ClassFieldTheory
end
