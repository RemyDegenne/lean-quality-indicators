@[expose] public section

namespace PebblingLean

namespace Hypercube

/-- The all-zero vertex of a hypercube. -/
def zeroVertex (n : ℕ) : HypercubeVertex n :=
  fun _ => false

end Hypercube
end PebblingLean
end
