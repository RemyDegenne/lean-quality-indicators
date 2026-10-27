public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
  CFSG.ClassicalInvolution.Balance.StrongBalance.Linear CFSG.LieType.Universal.Unitary

section DGroups

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] {p : ℕ}
  [Fact p.Prime]

theorem pairBlock_mem (J : Finset (Fin 6)) (hJ : J.card = 2) (X : Su K ℓ f 2) :
    pairBlock J hJ X ∈ coordBlockSU K ℓ f J :=
  ⟨_, rfl⟩

end DGroups
end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc
end
