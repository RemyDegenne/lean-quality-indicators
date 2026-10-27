public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {K : Type} [Field K]
  {V : Type} [AddCommGroup V] [Module K V]

theorem exists_frame_T0 (hσ : IsUnitaryInvolution σ) : ∃ b : Fin 3 → Fin 6 → F, Frame σ e3uT0Vec b := by
  have hv : exteriorPower.ιMulti F 3 (e3uT0Vec (F := F)) ≠ 0 := by
    rw [← pt0_eq_ιMulti_T0]
    exact pt0_ne_zero
  have hiso : ∀ i j : Fin 3,
      ∑ k : Fin 6, σ (e3uT0Vec (F := F) i k) * e3uT0Vec (F := F) j k = 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [e3uT0Vec, Fin.sum_univ_six, CharTwo.add_self_eq_zero]
  obtain ⟨b, hab, hbb⟩ := exists_hyperbolic_partners hσ hv hiso
  exact ⟨b, fun i j => hiso i j, fun i j => hbb i j, fun i j => hab i j⟩

end CFSG.RankThree.GF2n.Smith81.S81V
end
