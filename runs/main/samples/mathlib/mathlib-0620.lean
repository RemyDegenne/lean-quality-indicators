@[expose] public section

noncomputable section

open scoped NNReal Topology Uniformity

open Finset Metric Function Filter

universe u v v' wE wE₁ wE' wG wG'

section continuous_eval

variable {𝕜 ι : Type*} {E : ι → Type*} {F : Type*}
    [NormedField 𝕜] [Finite ι] [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    [TopologicalSpace F] [AddCommGroup F] [IsTopologicalAddGroup F] [Module 𝕜 F]

namespace ContinuousLinearMap

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [Module 𝕜 G] [ContinuousConstSMul 𝕜 F]

lemma continuousOn_uncurry_of_multilinear (f : G →L[𝕜] ContinuousMultilinearMap 𝕜 E F) {s} :
    ContinuousOn (fun (p : G × (Π i, E i)) ↦ f p.1 p.2) s :=
  f.continuous_uncurry_of_multilinear.continuousOn

end ContinuousLinearMap
end continuous_eval
end
end
