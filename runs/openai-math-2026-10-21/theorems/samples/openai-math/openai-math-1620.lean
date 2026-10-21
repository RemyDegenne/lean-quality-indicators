namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularExecutionBounds

open Turing MachineComposition PCP PCP.PreprocessingRegularTables PCP.PreprocessingCloudIndex

open PCP.PreprocessingMachineBounds MachineRegularInternalRow

theorem coreTimeBound_mono (q L R x v i k o m O L' R' x' v' i' k' o' m' O' : Nat)
    (hL : L ≤ L') (hR : R ≤ R') (hx : x ≤ x') (hv : v ≤ v') (hi : i ≤ i')
    (hk : k ≤ k') (ho : o ≤ o') (hm : m ≤ m') (hO : O ≤ O') :
    coreTimeBound q L R x v i k o m O ≤ coreTimeBound q L' R' x' v' i' k' o' m' O' := by
  unfold coreTimeBound
  gcongr

end BinPackingGames.Foundations.Complexity.MachineRegularExecutionBounds
end OAI
