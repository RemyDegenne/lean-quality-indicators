public section

universe a b w p

open CategoryTheory Limits Opposite

open scoped Simplicial TensorProduct

namespace SSet

/-- The morphism from degree-zero homology of terminal normalized tensor chains
obtained by descending the fixed degree-zero coefficient coordinates through
Mathlib's opcycles. -/
noncomputable def tensorNormalizedHomologyZeroToCoefficient
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T) :
    (tensorNormalizedChainComplex.{a, w, p} A T).homology 0 ⟶
      ModuleCat.of ℤ (ULift.{max w p} A) := by
  exact (tensorNormalizedChainComplex.{a, w, p} A T).homologyι 0 ≫
    (tensorNormalizedChainComplex.{a, w, p} A T).descOpcycles (i := 0)
      (tensorNormalizedZeroIsoCoefficient.{a, w, p} A T hT).hom 1 (by simp) (by
        rw [tensorNormalizedTerminal_d_one_zero.{a, w, p} A T hT, zero_comp])

end SSet
end
