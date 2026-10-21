namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

open Irrep Representation

namespace GridSplit

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

lemma columnRelative_sigma (g : ColumnSamples bits H) :
    columnRelative bits H g = (columnFreeEquiv bits H 0).symm.permCongr
      (Equiv.Perm.sigmaCongrRight (fun x =>
        remainingPerm (columnFamily bits H x) (g x).val (g x).property)) := by
  exact sigma_relative (columnFreeEquiv bits H 0) (columnFreeEquiv bits H (Fin.last n))
    (fun x => remainingBijection (columnFamily bits H x) (g x).val (g x).property)
    (fun x => freeIdentification (columnFamily bits H x))

end GridSplit
end BinaryCoordinateSweeps
end
end
end OAI
