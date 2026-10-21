namespace OAI

namespace ContingencyTables.SmallGraphProfiles

open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal

open SmallContextCoordinates CompletionCounts FirstSuccess FairBits

open scoped BigOperators Classical

noncomputable section

attribute [local irreducible] stateCode unitNext capViews codeNeighborProposal

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

variable (e : Fin q ≃ Cells (paperSmall r c))

local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

lemma unitAdvance_encoded (htotal : (∑ i,r i)=∑ j,c j) (h : ℕ)
    (initial x : PaperStates r c) (bits : Fin s → Bool) :
    unitAdvance (List.ofFn bits,encodedConfiguration r c e h initial x)=
      encodedConfiguration r c e h initial (unitCodeBitStep r c e x bits) := by
  apply Prod.ext
  · rfl
  ·
    have hn := unitNext_encoded r c e htotal h initial x bits
    simpa only [unitAdvance,encodedConfiguration] using hn

end
end ContingencyTables.SmallGraphProfiles
end OAI
