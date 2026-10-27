public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

theorem Frame2.weaklyClosed_A' (F : Frame2 G z) : WeaklyClosedIn F.A' F.T := by
  refine ⟨F.A'_le_T, fun g hg => ?_⟩
  have hel := Gen.isElemAbelian_conjSubgroup g F.A'_elem
  have hcard : Nat.card (cjS g F.A') = 64 := by rw [Gen.card_conjSubgroup, F.card_A']
  rcases F.A_max _ hg hel hcard with h | h
  · exfalso
    apply s39_6_1 F
    refine ⟨g⁻¹, ?_⟩
    have := congrArg (cjS g⁻¹) h
    rw [Gen.cj_inv_cj] at this
    exact this.symm
  · exact h

end CFSG.Quasithin.A94
end
