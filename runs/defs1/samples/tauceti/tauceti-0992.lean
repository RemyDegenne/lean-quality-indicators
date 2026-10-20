public section

noncomputable section

open Manifold

open scoped ContDiff

namespace TauCeti.Sol

/-- Translations and dihedral automorphisms act on Sol by Riemannian isometries. -/
def semidirectProductToIsom :
    Sol ⋊[dihedralMulAut] DihedralGroup 4 →* Isom 𝓘(ℝ, ℝ × ℝ × ℝ) Sol :=
  SemidirectProduct.lift toIsom dihedralToIsom fun g => MonoidHom.ext fun p =>
    (dihedralToIsom_conj_toIsom g p).symm

end TauCeti.Sol
end
end
