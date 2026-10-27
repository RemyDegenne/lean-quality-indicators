public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification

variable {n : ℕ} {K : Type} [Field K]

theorem l212in_det_map (σ : K ≃+* K) (B : GL (Fin n) K) :
    GeneralLinearGroup.det (GeneralLinearGroup.map (σ : K →+* K) B) =
      Units.map (σ : K →+* K) (GeneralLinearGroup.det B) := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, Units.coe_map, GeneralLinearGroup.val_det_apply]
  exact (RingHom.map_det (σ : K →+* K) (B : Matrix (Fin n) (Fin n) K)).symm

end CFSG.LocalAnalysis.RankFourTheoremC
end
