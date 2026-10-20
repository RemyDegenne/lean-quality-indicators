public section

open Polynomial TauCeti.Polynomial

namespace TauCeti

namespace Cyclotomic

variable {e : ℕ}

/-- The distinguished complex `e`-th root of unity `exp (2πi/e)`.  It is primitive for `e ≠ 0`
(`TauCeti.Cyclotomic.isPrimitiveRoot_complexRoot`); at `e = 0` it is `exp 0 = 1`. -/
noncomputable def complexRoot (e : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / e)

end Cyclotomic
end TauCeti
end
