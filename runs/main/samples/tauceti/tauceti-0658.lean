public section

namespace TauCeti.Huber

open UniformSpace

section Iterate

variable {k m : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] {T : Fin k → Set A} (hT : IsWeightFamily T)
  {W : Fin m → Set (Completion (weightedRestrictedSubring T hT))} (hW : IsWeightFamily W)
  {U : Fin (k + m) → Set A} (hU : IsWeightFamily U)
  (hTU : ∀ i, U (Fin.castAdd m i) = T i)
  (hUW : ∀ j, algebraMap A (Completion (weightedRestrictedSubring T hT)) '' U (Fin.natAdd k j) =
    W j)

@[simp]
theorem iterateSplitHom_comp_iterateFirstBlockHom :
    (iterateSplitHom hT hW hU hTU hUW).comp (iterateFirstBlockHom hT hU hTU)
      = algebraMap (Completion (weightedRestrictedSubring T hT))
        (Completion (weightedRestrictedSubring W hW)) := by
  refine completion_weightedRestrictedSubring_ringHom_ext_of_continuous hT
    ((continuous_iterateSplitHom hT hW hU hTU hUW).comp
      (continuous_iterateFirstBlockHom hT hU hTU))
    (continuous_algebraMap_completion_weightedRestrictedSubring _ _ hW) (fun a ↦ ?_) fun i ↦ ?_
  · simp only [RingHom.coe_comp, Function.comp_apply, iterateFirstBlockHom_coe_weightedC,
      algebraMap_completion_weightedRestrictedSubring_apply _ _ hU,
      algebraMap_completion_weightedRestrictedSubring_apply _ _ hW,
      iterateSplitHom_coe_weightedC, iterateStructureHom_apply]
  · simp only [RingHom.coe_comp, Function.comp_apply, iterateFirstBlockHom_coe_weightedX,
      iterateSplitHom_coe_weightedX, iterateVar_castAdd,
      algebraMap_completion_weightedRestrictedSubring_apply _ _ hW]

end Iterate
end TauCeti.Huber
end
