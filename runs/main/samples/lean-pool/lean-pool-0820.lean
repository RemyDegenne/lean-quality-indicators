section

@[expose] public section

noncomputable section

namespace EulerPacketCofactor

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerPacketPiola
  EulerOperatorGevreyCalculus EulerGevrey

open scoped ContDiff

local instance instPacketCofactorGevrey1 : NormedAddCommGroup EndSpace := inferInstance

local instance instPacketCofactorGevrey2 : NormedSpace ℝ EndSpace := inferInstance

local instance instPacketCofactorGevrey3 : NormedAddCommGroup (EndSpace →L[ℝ] EndSpace) :=
    inferInstance

local instance instPacketCofactorGevrey4 : NormedSpace ℝ (EndSpace →L[ℝ] EndSpace) := inferInstance

local instance instPacketCofactorGevrey5 : NormedAddCommGroup (EndSpace →L[ℝ] EndSpace →L[ℝ]
    EndSpace) :=
    inferInstance

local instance instPacketCofactorGevrey6 : NormedSpace ℝ (EndSpace →L[ℝ] EndSpace →L[ℝ] EndSpace)
    := inferInstance

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem recovered_curvature_eq (F F₂ H : P → EndSpace)
    (hdet : ∀ x, (operatorMatrix (F x)).det = 1)
    (h₂ : ∀ x v, F₂ x v = -(H x (F x v))) :
    H = fun x => -((F₂ x).comp (adjugate (F x))) := by
  funext x
  apply ContinuousLinearMap.ext
  intro v
  have hv : F x (adjugate (F x) v) = v :=
    congrArg (fun L : EndSpace => L v) (comp_adjugate (F x) (hdet x))
  change H x v = -(F₂ x (adjugate (F x) v))
  rw [h₂,hv,neg_neg]

end EulerPacketCofactor
end
end
end
