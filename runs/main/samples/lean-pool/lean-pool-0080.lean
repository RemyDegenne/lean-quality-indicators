section

@[expose] public section

noncomputable section

namespace EulerGevreyCutoff

open Set Filter Complex MeasureTheory

open scoped Topology ContDiff

theorem complexFlat_differentiableAt {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ complexFlat z :=
  Complex.differentiableAt_exp.comp z (differentiableAt_id.inv hz).neg

end EulerGevreyCutoff
end
end
end
