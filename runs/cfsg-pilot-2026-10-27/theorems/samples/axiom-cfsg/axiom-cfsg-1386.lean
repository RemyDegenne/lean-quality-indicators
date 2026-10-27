public section

namespace CFSG.Timmesfeld.Transvection.Pres

open Matrix CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.LieType.RootSystem TauCeti.GLSymplecticFin

open scoped commutatorElement

variable {n : ℕ}

theorem rt_dot_rt (a b : Fin n ⊕ Fin n) :
    rt a b ⬝ᵥ rt a b = 2 + 2 * (wt a ⬝ᵥ wt b) := by
  simp only [rt, add_dotProduct, dotProduct_add, Sp.dot_wt_self, dotProduct_comm (wt b) (wt a)]
  ring

end CFSG.Timmesfeld.Transvection.Pres
end
