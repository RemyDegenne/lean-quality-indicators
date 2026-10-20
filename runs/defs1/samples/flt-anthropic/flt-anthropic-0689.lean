namespace P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two

namespace Fact1

set_option autoImplicit false

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup

open scoped MatrixGroups ModularForm

noncomputable section

namespace HeckeAnalytic

def repGL (ℓ : ℕ) [NeZero ℓ] (i : Option (Fin ℓ)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((repMat ℓ i).map (algebraMap ℤ ℝ)) (by
    have h : ((repMat ℓ i).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) (repMat ℓ i).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, det_repMat]
    simp [NeZero.ne ℓ])

end HeckeAnalytic
end
end Fact1
end P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two
