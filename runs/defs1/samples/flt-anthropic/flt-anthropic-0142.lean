namespace P2MW.S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 6400000

section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

p2m_reactivate

section

section

section

noncomputable section

p2m_open

namespace WeierstrassCurve

namespace Affine

p2m_open

universe u

variable {F : Type u} [Field F] [DecidableEq F] {W : Affine F}

variable [IsAlgClosed F] [W.IsElliptic] [InfinitePlace W]

def geomDivisorSum : AlgebraicCurve.Divisor F W.FunctionField →+ W.Point :=
  Finsupp.liftAddHom fun v => zmultiplesHom W.Point (geomPointEquivPlace.symm v)

end Affine
end WeierstrassCurve
end
end
end
end
end
end
end P2MW.S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem
