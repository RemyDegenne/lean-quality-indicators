public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Psi

variable {L : Type} [Field L]

theorem relExp_eq_two_pow_mul_scale (a : ℕ) (j : Fin ReeTag.F4.tag.rank) :
    ((ReeTag.F4.relationExponent a j : ℕ) : ℤ) =
      2 ^ a * (ReeTag.F4.scale (ReeTag.F4.perm j) : ℤ) := by
  rw [relExp_vec, scale_vec, perm_vec]
  exact relExp_eq_aux a j

end Psi
end CFSG.RankThree.PartOne.KLR
end
