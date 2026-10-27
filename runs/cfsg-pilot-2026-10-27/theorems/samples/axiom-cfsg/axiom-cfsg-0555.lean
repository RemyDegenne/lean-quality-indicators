public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

theorem isCompositionFactor_of_le_layer {Q : Type} [Group Q] {N : Subgroup Q}
    (hN : N ≤ CFSG.layer Q) (hn : (N.subgroupOf (CFSG.layer Q)).Normal) {L : Type} [Group L]
    (h : E1.IsCompositionFactor ↥N L) : E1.IsCompositionFactor Q L := by
  have : (CFSG.layer Q).Characteristic := CFSG.LocalCores.layer_characteristic
  have h1 : E1.IsCompositionFactor ↥(N.subgroupOf (CFSG.layer Q)) L :=
    (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
      (Subgroup.subgroupOfEquivOfLe hN).symm).1 h
  exact kbr_isCompositionFactor_of_normal_subgroup _
    (kbr_isCompositionFactor_of_normal_subgroup _ h1)

end CFSG.LocalAnalysis.WeakClosure81
end
