public section

namespace TauCeti.BinaryGolay

/-- **The Construction A lattice of the extended binary Golay code**: the integer vectors of
`ℚ^(Fin 24)` reducing to a Golay codeword modulo two, with the dot product halved. -/
noncomputable def constructionALattice : IntegralLattice (Fin 24 → ℚ) :=
  ConstructionA.integralLattice 2 code.toAddSubgroup
    (TwoPowCode.isTypeII_one_iff.mpr isTypeII_code).le_euclideanDual

end TauCeti.BinaryGolay
end
