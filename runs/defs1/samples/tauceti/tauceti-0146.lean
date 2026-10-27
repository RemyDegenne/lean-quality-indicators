public section

open Matrix

open scoped MatrixGroups

namespace TauCeti

namespace TraceFormulaMatrixModule

variable {n : ℤ}

/-- For `n ≠ 0`, `ℳₙ^∞` is a transversal of the `SL(2, ℤ)`-orbits of `ℳₙ` (Popa--Zagier,
Section 2): sending a representative to its orbit is a bijection onto `Γ \ ℳₙ`. -/
noncomputable def upperTriangularRepsEquiv (hn : n ≠ 0) :
    upperTriangularReps n ≃ MulAction.orbitRel.Quotient SL(2, ℤ) (TraceFormulaMatrixModule n) :=
  MulAction.transversalEquivOrbitRelQuotient (exists_smul_mem_upperTriangularReps hn)
    fun _ hx _ ↦ smul_eq_self_of_mem_upperTriangularReps hx

end TraceFormulaMatrixModule
end TauCeti
end
