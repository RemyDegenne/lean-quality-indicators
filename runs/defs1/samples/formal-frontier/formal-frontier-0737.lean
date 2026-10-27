@[expose] public section

open CategoryTheory Limits AlgebraicTopology

open scoped Simplicial

noncomputable section

namespace TopCat

universe u

open ContinuousMap

/-- Reduced integral degree-zero homology is the coproduct of the integer
coefficient object over path components other than that of `x`. The comparison
is the uniqueness isomorphism between two kernels of the same augmentation.

For the reduced-homology background see J. Peter May, *A Concise Course in Algebraic Topology*,
Chapter 14, §§1 and 3. This construction uses Mathlib's ordinary singular
homology (Joël Riou) and the project's augmentation-kernel model, not a
comparison with May's based-relative theory. -/
noncomputable def reducedSingularHomologyZeroComponentsIso (X : TopCat.{u}) (x : X) :
    reducedSingularHomology X 0 ≅
      ∐ (fun _ : {c : ZerothHomotopy X // c ≠ .mk x} ↦
        singularHomologyIntegerCoefficients) :=
  (reducedSingularHomologyZeroToOrdinaryIsKernel X).conePointUniqueUpToIso
    (singularHomologyZeroComponentInclusionIsKernel X
      singularHomologyIntegerCoefficients x)

end TopCat
end
end
