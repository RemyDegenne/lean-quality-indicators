public section

open Set Topology OnePoint

namespace TauCeti

namespace ThricePuncturedSphere

/-- The open set `B = {z | 0 < re z}` of the standard two-set cover of the thrice-punctured sphere:
the half-plane `0 < re z` with the puncture `1` removed. -/
def rightOpen : Set ThricePuncturedSphere :=
  {z | 0 < (z : ℂ).re}

end ThricePuncturedSphere
end TauCeti
end
