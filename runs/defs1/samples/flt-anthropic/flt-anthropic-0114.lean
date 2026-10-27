namespace P2MW.S_HeckeEis_eichlerShimuraMap_heckeTLin

set_option autoImplicit false

open scoped Manifold MatrixGroups

noncomputable section

namespace HeckeEis

namespace HeckeESSol

p2m_open

open UpperHalfPlane Filter Topology Complex

open scoped MatrixGroups ModularForm

namespace HeckeAnalytic

open Matrix CongruenceSubgroup

def repMat (ℓ : ℕ) : Option (Fin ℓ) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(ℓ : ℤ), 0; 0, 1]
  | some j => !![1, (j : ℤ); 0, (ℓ : ℤ)]

end HeckeAnalytic
end HeckeESSol
end HeckeEis
end
end P2MW.S_HeckeEis_eichlerShimuraMap_heckeTLin
