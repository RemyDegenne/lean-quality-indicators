namespace OAI

section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal BigOperators

namespace HardSphere.Groups

open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital

attribute [local instance] Classical.propDecidable

lemma anchorPoint_project {K : ℕ} (L : Length) (v : Fin 3 → Fin K) :
    projectPoint L (anchorPoint v)=gridCenter L v := rfl

end HardSphere.Groups
end
end
end OAI
