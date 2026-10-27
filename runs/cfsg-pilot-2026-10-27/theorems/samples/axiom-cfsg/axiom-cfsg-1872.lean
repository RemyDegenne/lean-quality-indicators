public section

namespace CFSG.Quasithin.H13.S126M22

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat
  PermLat CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

theorem m12 : ∀ x : Fin 22, g1⁻¹ (e2 (g1 x)) = (e1 * e3) x := by decide +kernel

end CFSG.Quasithin.H13.S126M22
end
