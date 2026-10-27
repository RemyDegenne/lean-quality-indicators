@[expose] public section

namespace HypergraphLowerBound

open private WitnessStrong WitnessStrong.toWitnessData apply_frameData ws_singleton
  exists_cover_subset_card_le_of_noLargePartition
  from LeanPool.FrontierMathOpenHypergraphs.Uniform

/-- The explicit cardinality expression for the Lubell frame. -/
noncomputable def lubellCardSum (t : ℕ) : ℕ :=
  (Finset.Icc 2 t).sum (fun j => Nat.choose t j * lubellMultiplicity t j)

end HypergraphLowerBound
end
