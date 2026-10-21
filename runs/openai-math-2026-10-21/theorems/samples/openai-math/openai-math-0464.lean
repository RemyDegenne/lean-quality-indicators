namespace OAI

noncomputable section

open scoped Classical Matrix

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks

open scoped Classical Matrix

variable {R : Type*} [CommRing R] {a b c : ℕ}

variable {d : LocalRanks (.splitting a b c false)} (G : d.CoherentBases (R:=R))

local instance : Fintype ((Kind.splitting a b c false).table.Child .branch) := fintypeChild (.splitting a b c false) .branch

local instance : Fintype (d.Columns .before) := d.fintypeColumns .before

local instance : Fintype (d.Columns .after) := d.fintypeColumns .after

local instance : Fintype (d.Columns .branch) := d.fintypeColumns .branch

lemma CoherentBases.split_middle :
    (G.basis .branch none).reindex d.splitBranchParent d.splitBranchParent=
      G.basis .before (some (.inr (.inl ()))) := G.corner ⟨.before,some (.inr (.inl ()))⟩

end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
end
end OAI
