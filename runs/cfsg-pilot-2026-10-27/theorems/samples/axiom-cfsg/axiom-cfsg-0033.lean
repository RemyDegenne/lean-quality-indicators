public section

namespace CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8FourRecordData249_rank_card :
    (c8FourRecordBinaryImages c8FourRecordData249).card = 2 ^ 2 ∧
      c8FourRecordData249.generators.length = 2 := by
  decide +kernel

end CFSG.LargeEvenClassification.Helpers
end
