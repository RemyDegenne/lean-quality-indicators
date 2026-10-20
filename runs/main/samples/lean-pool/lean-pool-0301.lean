@[expose] public section

namespace ScottishBook155

universe u

namespace CoherentBiSystem

variable {ι : Type u} [LinearOrder ι]

variable (G : ι → Type u)

variable [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]

theorem totalProject_of_ge (B : CoherentBiSystem G)
    {a i : ι} (hai : a ≤ i) (x : G i) :
    totalProject G B a i x = B.project a i hai x := by
  by_cases hia : i ≤ a
  · have hai' : a = i := le_antisymm hai hia
    subst i
    rw [totalProject_of_le G B le_rfl, B.embed_refl]
    have hp : B.project a a hai x = x := by
      simpa only [B.embed_refl] using B.project_retracts a a hai x
    exact hp.symm
  · rw [totalProject]
    split_ifs
    congr

end CoherentBiSystem
end ScottishBook155
end
