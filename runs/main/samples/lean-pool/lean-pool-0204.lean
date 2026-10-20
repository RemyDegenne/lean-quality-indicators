@[expose] public section

open Module

variable {K : Type*} [Field K]

variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]

local notation "v" => ValuationRing.valuation R K

open Matrix

variable {k l : ℕ+}

noncomputable section

lemma rowEliminator_colEliminator (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffsSup v) :
    rowEliminator (((colEliminator g h).val : Matrix _ _ K) * g)
      (colEliminator_mul_coeffs_sup g h) =
      rowEliminator g h := by
  classical
  simp [rowEliminator, rowEliminationList, rowEliminationTransvection, multFactor,
    colEliminator_mul_lastRow]

end
end
