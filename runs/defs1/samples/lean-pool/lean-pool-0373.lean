@[expose] public section

open scoped Topology

noncomputable section

namespace Milla

open Polynomial

/-- The coefficient `h₂` (standing for `¼g₂(L)`). -/
noncomputable def h2 : Coeff := MvPolynomial.X 0

end Milla
end
end
