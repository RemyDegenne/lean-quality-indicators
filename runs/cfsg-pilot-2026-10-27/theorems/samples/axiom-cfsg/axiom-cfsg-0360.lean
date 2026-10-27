public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Generic

variable {T : Type*} [CommGroup T]

theorem s16f_exists_quotHom (U : Subgroup T) :
    ∃ ρ : ↥(stabSub U) →* MulAut (T ⧸ U),
      ∀ (g : ↥(stabSub U)) (x : T),
        ρ g (QuotientGroup.mk x) = QuotientGroup.mk ((g : MulAut T) x) := by
  refine ⟨MonoidHom.mk' (fun g => QuotientGroup.congr U U (g : MulAut T)
      (s16f_map_eq_of_mem_stabSub g.2)) ?_, ?_⟩
  · intro g h
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [MulAut.mul_apply]
      simp only [QuotientGroup.congr_mk]
      rfl
  · intro g x
    exact QuotientGroup.congr_mk U U (g : MulAut T) (s16f_map_eq_of_mem_stabSub g.2) x

end Generic
end CFSG.LocalAnalysis.UniquenessCase.PartTwo
end
