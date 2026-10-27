public section

namespace CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8FourRecordData175_valid : c8FourRecordValid c8FourRecordData175 :=
  c8K_valid _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end CFSG.LargeEvenClassification.Helpers
end
