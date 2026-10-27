public section

namespace CFSG.Quasithin.A94.L52

open Matrix CFSG.CGT.M24S

open scoped Pointwise

theorem Dsub_inf (i j : Fin 5) (hi : inB i) (hj : inB j) (hij : i ≠ j) :
    Dsub i hi ⊓ Dsub j hj = Subgroup.zpowers zt := by
  apply le_antisymm
  · intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨p, hp⟩ := (mem_Dsub i hi x).1 h1
    obtain ⟨q, hq⟩ := (mem_Dsub j hj x).1 h2
    have hDD : Dmat i p = Dmat j q := add_left_cancel (hp.symm.trans hq)
    have hp1 : p.1 = 0 := by
      rw [← Dmat_i4 i hi p, hDD, Dmat_col4 j hj q i]
      simp [Ne.symm hij, Ne.symm (inB_ne0 i hi)]
    have hp2 : p.2.1 = 0 := by
      rw [← Dmat_0i i hi p, hDD, Dmat_row0 j hj q i]
      simp [Ne.symm hij, Ne.symm (inB_ne4 i hi)]
    have hcx : cm x = 1 + Matrix.single 0 4 p.2.2 := by
      rw [hp, Dmat_only04 i p hp1 hp2]
    rcases eq_one_or_zt x _ hcx with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers zt
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.2 ⟨zt_mem_Dsub i hi, zt_mem_Dsub j hj⟩

end CFSG.Quasithin.A94.L52
end
