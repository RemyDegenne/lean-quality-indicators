public section

open CategoryTheory CategoryTheory.Limits

namespace FiniteGroupTateCohomology

universe u

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

namespace Cyclic

variable (A : Rep.{u} R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)

lemma tateCohomologyIsoOdd_negOne :
    tateCohomologyIsoOdd A g hg (-1) (by simp) =
      tateCohomologyNegOneIsoKernelNorm A ≪≫
        (oddModelIsoKernelNorm (R := R) (G := G) A g hg).symm := by
  rfl

end Cyclic
end FiniteGroupTateCohomology
end
