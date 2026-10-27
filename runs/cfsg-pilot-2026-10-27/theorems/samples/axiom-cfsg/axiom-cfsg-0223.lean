public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

theorem br1_h131 (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) :
    Assumption131 (M.img H) (packFamilyU D V H i M) (packSpaceU D V₀ V H i M)
      (x.mB - i - 1) :=
  x.assumption131U M

end Ctx188
end CFSG.LocalAnalysis.WeakClosure81
end
