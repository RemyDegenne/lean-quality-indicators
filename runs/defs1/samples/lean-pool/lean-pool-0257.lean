@[expose] public section

namespace RungeKuttaOrderConditions.Butcher

variable {K : Type*} [CommRing K]

/-- The two-leaf cherry tree of order 3. -/
def t31 : RTree := .node [leaf, leaf]

end RungeKuttaOrderConditions.Butcher
end
