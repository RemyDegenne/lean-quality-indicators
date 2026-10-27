public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem mem_smallChain_original {g : Equiv.Perm (Fin 1782)} :
    g ∈ smallChain.original.toList ↔ g = suzB0 ∨ g = suzB1 := by
  rw [schreier_vector_mem_toList_iff_get]
  constructor
  · rintro ⟨i, rfl⟩
    rw [smallChain_original_eq]
    have hi : (i : ℕ) < 2 := i.2
    interval_cases h : (i : ℕ)
    · left
      rw [show Fin.cast smallChain_originalCount i = 0 from Fin.ext h, Matrix.cons_val_zero]
    · right
      rw [show Fin.cast smallChain_originalCount i = 1 from Fin.ext h, Matrix.cons_val_one,
        Matrix.cons_val_zero]
  · rintro (rfl | rfl)
    · exact ⟨⟨0, by rw [smallChain_originalCount]; norm_num⟩, by
        rw [smallChain_original_eq]; exact Matrix.cons_val_zero _ _⟩
    · exact ⟨⟨1, by rw [smallChain_originalCount]; norm_num⟩, by
        rw [smallChain_original_eq]
        exact (Matrix.cons_val_one _ _).trans (Matrix.cons_val_zero _ _)⟩

end CFSG.Sporadic.SuzOddCore
end
