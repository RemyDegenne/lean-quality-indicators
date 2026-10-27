public noncomputable section

open Module

namespace TauCeti

namespace UqSl2

namespace LadderModule

/-- The ladder basis `v₀, …, v_m` of `L_m^ε`. -/
def basis (q : ℂ) (m : ℕ) (ε : ℤˣ) : Basis (Fin (m + 1)) ℂ (LadderModule q m ε) :=
  Pi.basisFun ℂ (Fin (m + 1))

end LadderModule
end UqSl2
end TauCeti
end
