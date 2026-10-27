public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.RelativeRoots

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Overlap

theorem isLift_nativeRefl
    (i : Fin 4) : IsLift (simple .F4 i) (nativeReflT i) :=
  ⟨nativeReflT_mem i, relProj_nativeRefl_smul i⟩

end CFSG.LieType.Chevalley.C2E6Std.RelativeRoots
end
