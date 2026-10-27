public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggPZNbrResDatumOn_of_sympLin
    (hRig : GGLabelRigidInput) (hcyc : GGLabelCenterPCyclicInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGPZNbrResDatumOn (fun p lab => S p lab ∧ ¬ GGResAN2Label p lab)) :
    GGPZNbrResDatumOn S :=
  ggPZNbrResDatumOn_of_weylType ggWeylTypeFamilyOn_sympLin hRig hcyc h

end CFSG.StandardType
end
