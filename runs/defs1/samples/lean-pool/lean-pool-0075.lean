section

namespace PermanentFormulaLowerBound

universe u v w

open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin

/-- The generic `n`-by-`n` permanent polynomial over the complex numbers. -/
@[expose] public noncomputable def permanentPolynomial (n : ℕ) :
    MvPolynomial (Fin n × Fin n) ℂ :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).permanent

end PermanentFormulaLowerBound
end
