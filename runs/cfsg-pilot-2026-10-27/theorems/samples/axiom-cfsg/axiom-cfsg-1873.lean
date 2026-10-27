public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec13.ResProof

open CFSG CFSG.RankThree.LocalRank

variable {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]

section Theta

variable (hq : IsQuasisimple (X ⧸ aschbacherSolvableCore 3 X))
  (hZ : Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) =
    N.map (QuotientGroup.mk' (aschbacherSolvableCore 3 X)))

omit [Finite X] in
include hZ in
theorem centerQuotHom_mk (x : X) :
    centerQuotHom N hZ (x : X ⧸ N) =
      ((x : X ⧸ aschbacherSolvableCore 3 X) :
        (X ⧸ aschbacherSolvableCore 3 X) ⧸ Subgroup.center (X ⧸ aschbacherSolvableCore 3 X)) :=
  rfl

end Theta
end CFSG.RankThree.PartTwo.Sec13.ResProof
end
