public section

namespace TauCeti

namespace BasedOrientedGaussCode

variable {n : ℕ}

/-- A visit, read as its crossing label together with whether it is the over visit. -/
def visitData (D : BasedOrientedGaussCode n) (i : Fin (2 * n)) : Fin n × Bool :=
  (D.visit i, D.over i)

end BasedOrientedGaussCode
end TauCeti
end
