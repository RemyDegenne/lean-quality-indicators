namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.CodedRecursiveMapInputs

universe u

variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}

variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}

variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)

variable {T : ZFSet.{u}} (task : SetActionCode G I m one T)

variable (sourceInvariant : ∀ g i j a b, ZFSet.pair (ZFSet.pair g i) j ∈ T →
  ZFSet.pair i a ∈ Sources → ZFSet.pair j b ∈ Sources → a = b)

include task sourceInvariant in
theorem nextIndexAction_setAction : SetActionCode G h.nextIndices m one (h.nextIndexAction T) :=
  indexedTaskActionGraph_setAction task
    (recursiveAttachmentIndices_subset I J D (⋃₀ ⋃₀ Fs) Sources Fs)
    (fun _ _ _ _ _ _ _ _ index entry => h.nextIndices_closed task sourceInvariant entry index)

end PartitionPilot.Forcing.CodedRecursiveMapInputs
end OAI
