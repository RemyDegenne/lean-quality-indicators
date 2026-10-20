@[expose] public section

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-- **Append** a pivot row to a list of pivot rows: previous rows are left untouched,
unlike the back-substitution performed by `insertPivot`. -/
def insertPivotA (D : List (PivRow n)) (w : Vec n) (p : Fin n) : List (PivRow n) :=
  D ++ [(w, p)]

end QECCertificates
end
