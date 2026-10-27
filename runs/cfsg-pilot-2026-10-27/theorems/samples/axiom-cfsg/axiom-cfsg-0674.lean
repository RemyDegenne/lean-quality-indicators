public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

variable {k : ℕ}

section Solvable

theorem exists_pair_of_not_isSolvable {𝒜 : Set (Finset (Fin k))} {a : AEQ k}
    (hns : ¬ Group.IsSolvable ↥(Ea (aeMembers k 𝒜) a)) :
    ∃ α ∈ 𝒜, ∃ α' ∈ 𝒜, α ≠ α' ∧ CenSet a α ∧ CenSet a α' := by
  by_contra hcon
  refine hns (isSolvable_Ea_of_uniq fun α hα α' hα' h1 h2 => ?_)
  by_contra hne
  exact hcon ⟨α, hα, α', hα', hne, h1, h2⟩

end Solvable
end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7
end
