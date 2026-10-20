@[expose] public section

namespace PebblingLean

namespace Hypercube

namespace Paper

open Pebbling

theorem lower_bound (n : ℕ) :
    ((4 : ℚ) / 3) ^ n ≤ (optimalPebblingNumber n : ℚ) :=
  lower_bound_of_isOptimalNumber
    (isOptimalNumber_optimalPebblingNumber n)

end Paper
end Hypercube
end PebblingLean
end
