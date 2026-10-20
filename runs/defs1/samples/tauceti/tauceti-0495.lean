public section

namespace TauCeti

namespace Bigraded

open AddMonoidAlgebra

/-- The Poincaré series of the stabilization factor `W`: one generator in bidegree `(0, 0)` and
one in bidegree `(-1, -1)`. -/
noncomputable def W : Series := 1 + single (-1, -1) 1

end Bigraded
end TauCeti
end
