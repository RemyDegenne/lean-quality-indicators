public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Open Subgroup Matrix

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL proj conjAut fieldAut dualAut
  conjAut_proj coe_slConjugation fieldAut_proj dualAut_proj
  odd_linear_graph_field_involution_conjugacy)

open CFSG.LocalAnalysis.ComponentInitial.OddHigherLinear (transpose_eq_or_eq_neg_of_sq
  field_involution_conjugacy)

variable {K : Type} [Field K] [Finite K] {n p e : ℕ}

theorem inverts_good_conjAut (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p] (hK : Nat.card K = p ^ e)
    (h3 : 3 < p ^ e) (hn : 3 ≤ n) (A : GL (Fin n) K) (h2 : conjAut n K A ^ 2 = 1)
    (h1 : conjAut n K A ≠ 1) :
    ∃ x : projectiveSL n K, orderOf x = p ∧ conjAut n K A x = x⁻¹ ∧
      (IsSpecialGood p x ∨ IsOrbitGood p x) := by
  obtain ⟨N, hN2, hN0, -, hinv⟩ := exists_inv_unipSL_conjAut hn A h2 h1
  obtain ⟨hxord, hxgood⟩ := good_unipSL hp hp2 hK h3 hn hN0 hN2
  exact ⟨proj n K (unipSL N hN2), hxord, hinv, Or.inl hxgood⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
end
