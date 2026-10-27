public section

namespace TauCeti

open Matrix

/-- **The integral character table produced by the rational Dixon computation for the cyclic
group of order two.** -/
def cyclicGroupTwoCharacterTable :
    Matrix CyclicGroupTwoClassIndex CyclicGroupTwoClassIndex ℤ :=
  cyclicGroupTwoCentralCharacterTable

end TauCeti
end
