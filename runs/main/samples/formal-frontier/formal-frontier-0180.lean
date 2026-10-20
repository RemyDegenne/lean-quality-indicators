@[expose] public section

universe u v w

namespace ProfiniteGrp

theorem primewisePadicKernelIdeal_comp_changeUniverse
    {Y : Type w} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{v} →ₜ* Y) :
    primewisePadicKernelIdeal
      (f.comp (primewisePadicChangeUniverse.{u,v} :
        primewisePadic.{u} →ₜ* primewisePadic.{v})) =
      (primewisePadicKernelIdeal f).comap primewisePadicRingChangeUniverse.{u,v} := by
  ext x
  simp only [mem_primewisePadicKernelIdeal, Ideal.mem_comap,
    ContinuousMonoidHom.coe_comp, Function.comp_apply]
  exact Iff.of_eq (congrArg (fun y : primewisePadic.{v} ↦ f y = 1)
    (primewisePadicChangeUniverse_ringMultiplicativeEquiv.{u,v} x))

end ProfiniteGrp
end
