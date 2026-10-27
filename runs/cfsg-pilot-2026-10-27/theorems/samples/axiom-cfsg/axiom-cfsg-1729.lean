public noncomputable section

namespace CFSG.ONSchreier

open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.ONSchreier.Native Matrix

open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native

theorem nuA_uu {j : ℕ} (hj : j < nL) :
    ap lineOrbit.alpha j < nL ∧ normalize (mA *ᵥ uu j) = uu (ap lineOrbit.alpha j) := by
  obtain ⟨hc, -, -, -, hlt, he, -, -⟩ := lparts.2.2.2 j hj
  refine ⟨hlt, ?_⟩
  have hw : (mulVecT colsA lineOrbit.keys[j]!).toV.wf = true := by
    unfold mulVecT colsA
    exact wf_combW (by rw [toVM_transpose_map_ofV]; exact RowsWF.transpose 154 rowsA)
      (wf_of_canon154 hc)
  rw [uu_of_lt hj, uu_of_lt hlt, he, vecOf_nuW hw, ← toMat_rowsA]
  unfold colsA
  rw [vecOf_mulVecT rowsA (wf_of_canon154 hc)]

end CFSG.ONSchreier
end
