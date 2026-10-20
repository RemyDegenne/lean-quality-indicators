namespace P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified

p2m_reactivate

p2m_reactivate

section DeskModule01

set_option autoImplicit false

noncomputable section

open Matrix

namespace FLT

namespace PrincipalSeriesGL2Padic

p2m_open

open LocalNewvector

variable (p : ℕ) [Fact p.Prime]

section Cells

def weyl : GL (Fin 2) ℚ_[p] := LocalGL2.weylInt ℤ_[p] ℚ_[p]

end Cells
end PrincipalSeriesGL2Padic
end FLT
end
end DeskModule01
end P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified
