public section

namespace CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8FourRecordData810_rank_card :
    (c8FourRecordBinaryImages c8FourRecordData810).card = 2 ^ 3 ∧
      c8FourRecordData810.generators.length = 3 := by
  decide +kernel

end CFSG.LargeEvenClassification.Helpers
end
