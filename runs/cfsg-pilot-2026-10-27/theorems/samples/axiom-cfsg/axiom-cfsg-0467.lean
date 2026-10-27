public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphRadical

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphInvolution

section Coords

variable {E : Type} [Field E]

theorem radCoord_invariant_of_sq
    (h2 : (2 : E) = 0) {a : ModGL TwistTag.E6.tag E}
    (ha : a ∈ parabolicRadical TwistTag.E6.tag E setA)
    (hsq : (a * diagramMap TwistTag.E6 E) ^ 2 = 1) :
    ∀ β ∈ degOneList, radCoord a (permLattice TwistTag.E6.perm.symm β) = radCoord a β := by
  rw [sq_mul_diagramMap'] at hsq
  obtain ⟨hP, hPc⟩ := radCoord_diagramMap_conj h2 ha
  intro β hβ
  have h := radCoord_mul h2 ha hP β hβ
  rw [hsq, radCoord_one β hβ, hPc β hβ] at h
  linear_combination -h - radCoord a β * h2

end Coords
end CFSG.LieType.Chevalley.E6GraphRadical
end
