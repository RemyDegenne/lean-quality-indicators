namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section

namespace Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation

open Construction HistoryBulkReferencePeriodicMeanSource

open HistorySignedResidueFactorization

theorem norm_staticPairMask_le {l : ℕ} (h k : History l) (outside : List ℕ) :
    ‖staticPairMask h k outside‖ ≤ 1 := by
  classical
  unfold staticPairMask guardIndicator
  split_ifs <;> norm_num

end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation
end
end OAI
