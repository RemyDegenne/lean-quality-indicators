namespace P2MW.S_ModularCurve_transcendental_lambdaModC

set_option autoImplicit false

p2m_open

namespace ModularCurve

namespace TrLambda

p2m_open

def IsOneUnit {R : Type*} [CommRing R] (x : LaurentSeries R) : Prop := x.coeff 0 = 1 ∧ ∀ n < 0, x.coeff n = 0

end TrLambda
end ModularCurve
end P2MW.S_ModularCurve_transcendental_lambdaModC
