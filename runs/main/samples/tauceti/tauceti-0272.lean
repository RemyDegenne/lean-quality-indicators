public section

open Polynomial TauCeti.Polynomial

namespace TauCeti

namespace Cyclotomic

variable {e : ℕ}

@[simp↓]
theorem coeff_nsmul (n : ℕ) (x : Cyclotomic e) (j : ℕ) :
    (n • x).coeff j = n • x.coeff j := by
  simpa only [coeffAddHom_apply] using (coeffAddHom e j).map_nsmul n x

end Cyclotomic
end TauCeti
end
