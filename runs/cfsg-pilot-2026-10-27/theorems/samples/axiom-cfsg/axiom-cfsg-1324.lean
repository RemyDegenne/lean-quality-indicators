public noncomputable section

namespace CFSG.RankThree.E6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag}

theorem weylMatrix_eq_toMatrix' (w : WeylGroup τ) :
    weylMatrix w =
      LinearMap.toMatrix' (CFSG.LieType.RootSystem.weylAction (isFiniteType_cartan τ) w) := by
  ext i j
  rw [weylMatrix_apply, LinearMap.toMatrix'_apply, smul_def]

end CFSG.RankThree.E6
end
