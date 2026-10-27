public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {m : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 m K}

theorem levHom_conj_mem_radQ {w : hypSU h 2 0} (hw : w ∈ radQ h)
    (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    levHom h A * w * (levHom h A)⁻¹ ∈ radQ h :=
  (Subgroup.mem_normalizer_iff.mp (parP_le_normalizer_radQ h (levHom_le_parP h ⟨A, rfl⟩)) w).mp hw

end CFSG.Quasithin.H13.U4Par
end
