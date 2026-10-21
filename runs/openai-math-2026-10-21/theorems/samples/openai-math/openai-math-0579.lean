namespace OAI

namespace TuringRigidity.OrdinalArithmetic

open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible

open BoundedDefinability SetModelFunctions

universe u

theorem ordinal_omega_opow_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) : (Ordinal.omega0 ^ a).toZFSet ∈ M := by
  obtain ⟨f,hf,hg⟩ := internal_omegaGraph M hM hT a.toZFSet ha (ZFSet.isOrdinal_toZFSet a)
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact hM _ (omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity) _ ((mem_omega _).mpr ⟨1,rfl⟩)
  have hv := omegaStageImage _ f a.toZFSet hg.1 (ZFSet.mem_insert_iff.mpr (Or.inl rfl)) hg.mem_iff
  rw [Ordinal.rank_toZFSet] at hv
  exact hv ▸ stageImage_mem M hM hT h1 ha hf

end TuringRigidity.OrdinalArithmetic
end OAI
