public section

open Polynomial TauCeti.Polynomial

namespace TauCeti

namespace Cyclotomic

variable {e : ℕ}

@[simp↓]
theorem coeff_zsmul (z : ℤ) (x : Cyclotomic e) (j : ℕ) :
    (z • x).coeff j = z • x.coeff j := by
  simpa only [coeffAddHom_apply] using (coeffAddHom e j).map_zsmul z x

end Cyclotomic
end TauCeti
end
