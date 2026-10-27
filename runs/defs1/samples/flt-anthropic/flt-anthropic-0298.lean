namespace P2MW.S_ModularCurve_periodMap_heckeULin

set_option Elab.async false

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace ModularCurve

namespace Period

namespace SolHeckeU

p2m_open

open HeckeEis

open UpperHalfPlane Filter Topology Complex

namespace HeckeAnalytic

open Matrix CongruenceSubgroup

def repGL (ℓ : ℕ) [NeZero ℓ] (i : Option (Fin ℓ)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((repMat ℓ i).map (algebraMap ℤ ℝ)) (by
    have h : ((repMat ℓ i).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) (repMat ℓ i).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, det_repMat]
    simp [NeZero.ne ℓ])

end HeckeAnalytic
end SolHeckeU
end Period
end ModularCurve
end
end P2MW.S_ModularCurve_periodMap_heckeULin
