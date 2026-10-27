public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Ly0

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Recognition.McLMultiplier
  CFSG.LieType.Multipliers Equiv Subgroup

section Injective

theorem coverMap_ker_eq_center :
    (coverMap McLMultiplier.isPresentation_mclGen_of_certificate
      McLMultiplier.lift_mclCommW_of_certificate).ker =
      Subgroup.center MclCover :=
  ker_eq_center_of_central_ker _
    (coverMap_surjective _ _) (coverMap_ker_le_center _ _)
    (center_eq_bot_of_equiv_mcl CFSG.Sporadic.McL.mclEquivJ.symm)

end Injective
end CFSG.Sporadic.Recognition.LyonsSims.Ly0
end
