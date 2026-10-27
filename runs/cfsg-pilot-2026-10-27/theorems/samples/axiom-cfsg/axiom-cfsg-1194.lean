public section

namespace CFSG.Quasithin.J4M2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Quasithin.J4Loc CFSG.Quasithin.F134.J4E9 CFSG.Quasithin.J4Rad

open CFSG.Sporadic.J4.QT2 (w₀ Zl z0_mem_Zl)

open Om

section Orbit

theorem rho_spec (hF : J4Facts) (g : ↥M2) (i j : Fin 77) :
    rho hF g i = j ↔ (g : J) • pt i = pt j := by
  have h1 : rho hF g i = (ePt hF).symm (g • ePt hF i) := by
    simpa using rho_apply hF g (ePt hF i)
  rw [h1, Equiv.symm_apply_eq]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

end Orbit
end CFSG.Quasithin.J4M2
end
