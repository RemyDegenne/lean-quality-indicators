namespace OAI

namespace DepthThreeLowerBound

theorem reduceByUpdates_step (p c : List Bool) (s : ℕ) :
    reduceByUpdates p (s + 1) c = reduceByUpdates p s (cancelByUpdates p c s) := rfl

end DepthThreeLowerBound
end OAI
