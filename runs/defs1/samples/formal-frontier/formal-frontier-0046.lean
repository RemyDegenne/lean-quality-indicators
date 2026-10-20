@[expose] public section

universe a w p r v

open CategoryTheory Limits Opposite

open scoped Simplicial TensorProduct

namespace SSet

/-- Normalized chains in one degree as finitely supported coefficient families.
The ring universe is independent of the simplex and module universes. -/
noncomputable def normalizedChainComplexXIsoFinsupp {R : Type r} [Ring R]
    (S : SSet.{w}) (M : ModuleCat.{max w v} R) (n : ℕ) :
    (S.normalizedChainComplex M).X n ≅ ModuleCat.of R (S.nonDegenerate n →₀ M) := by
  classical
  exact
    (S.isColimitCofanNormalizedChainComplex M n).coconePointUniqueUpToIso
        (colimit.isColimit (Discrete.functor (fun _ : S.nonDegenerate n ↦ M))) ≪≫
      ModuleCat.coprodIsoDirectSum (fun _ : S.nonDegenerate n ↦ M) ≪≫
      (finsuppLEquivDirectSum R M (S.nonDegenerate n)).symm.toModuleIso

end SSet
end
