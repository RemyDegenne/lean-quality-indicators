namespace P2MW.S_IncidenceSystem_Data_isUnit_det_jacobian_iff

set_option autoImplicit false

set_option maxHeartbeats 1600000

open MvPolynomial

namespace IncidenceSystem

p2m_open

section dT

variable {R : Type*} [CommRing R]

noncomputable def dT (d : R →+ R) (p : Polynomial R) : Polynomial R :=
  ⟨.ofCoeff (p.toFinsupp.coeff.mapRange d d.map_zero)⟩

end dT
end IncidenceSystem
end P2MW.S_IncidenceSystem_Data_isUnit_det_jacobian_iff
