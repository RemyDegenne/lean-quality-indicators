public section

namespace CFSG.Quasithin.H13.F431.L3.P3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.QuasithinUnique.Fin257
  CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.LocalAnalysis.ComponentInitial.LinearCover CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L

variable {F : Type} [Field F] [CharP F 2]

theorem projQ3_le_normalizer_V2 [Finite F] :
    (Q3 F 1).map (proj 3 F) ≤
      Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  rintro _ ⟨M, hM, rfl⟩
  refine CFSG.QuasithinUnique.Fin257.L3.mem_normalizer_of_conj _
    (fun v hv => projQ3_conj_V2 hM hv) (fun v hv => ?_)
  have := projQ3_conj_V2 ((Q3 F 1).inv_mem hM) hv
  simpa [map_inv] using this

end CFSG.Quasithin.H13.F431.L3.P3
end
