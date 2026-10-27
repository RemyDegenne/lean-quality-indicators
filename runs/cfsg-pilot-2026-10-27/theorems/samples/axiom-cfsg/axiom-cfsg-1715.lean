public section

namespace CFSG.RankThree.PartOne.SEITZ7

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3 CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.RankThree.PartOne.CTP

open scoped commutatorElement

variable {K : Type} [Field K] {σ : K →+* K}

theorem range_phiAB [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) :
    (phiAB σ hσ).range = Lsub σ hσ := by
  apply le_antisymm
  · rintro _ ⟨⟨M, N⟩, rfl⟩
    rw [phiAB_apply]
    exact mul_mem (Asub_le_Lsub σ hσ ⟨_, rfl⟩) (Bsub_le_Lsub σ hσ ⟨_, rfl⟩)
  · refine sup_le ?_ ?_
    · rintro _ ⟨M, rfl⟩
      exact ⟨(M, 1), by rw [phiAB_apply, map_one, mul_one]⟩
    · rintro _ ⟨N, rfl⟩
      exact ⟨(1, N), by rw [phiAB_apply, map_one, one_mul]⟩

end CFSG.RankThree.PartOne.SEITZ7
end
