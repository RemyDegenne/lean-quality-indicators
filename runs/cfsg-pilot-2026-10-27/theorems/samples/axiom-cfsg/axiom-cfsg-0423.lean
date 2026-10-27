public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG

theorem s16c167_mem_stabSub_of_forward {W : Type} [CommGroup W] {U : Subgroup W} {g : MulAut W}
    (h : ∀ u ∈ U, g u ∈ U) (h' : ∀ u ∈ U, g⁻¹ u ∈ U) : g ∈ stabSub U := by
  intro u
  refine ⟨fun hu => ?_, h u⟩
  have := h' _ hu
  rwa [MulAut.inv_apply_self] at this

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
end
