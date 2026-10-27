public noncomputable section

namespace CFSG.StandardType.QTwo

section Fixed

open CFSG.StandardType

open CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

open scoped Pointwise Matrix

variable {G : Type} [Group G] [Finite G]

variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {m n : ℕ}

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]

variable (S : QTwoChartSetting B Bs x L D J 𝒦 m n)

theorem qTwoFour_frameSet_one {ε : Fin m ↪ Fin (n + 1)} (I : Finset (Fin m)) :
    qTwoFrameSet ε 1 I = I.map ε := by
  ext x
  simp only [qTwoFrameSet, Finset.mem_map, Equiv.toEmbedding_apply,
    Equiv.Perm.coe_one, id_eq]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨ε z, ⟨z, hz, rfl⟩, rfl⟩

end Fixed
end CFSG.StandardType.QTwo
end
