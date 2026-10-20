@[expose] public section

open CategoryTheory Convexity

open scoped BigOperators Simplicial

noncomputable section

namespace Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false in
theorem lsingle_comp_affineBoundaryHom {m n : ℕ} (a : AffineSimplex m (n + 1)) :
    ModuleCat.ofHom (Finsupp.lsingle a (R := ℤ) (M := ModuleCat.of ℤ ℤ)) ≫
        affineBoundaryHom m n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        ModuleCat.ofHom (Finsupp.lsingle (a.face i)
          (R := ℤ) (M := ModuleCat.of ℤ ℤ)) := by
  rw [← affineChainIso_ι]
  simp only [affineBoundaryHom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [SSet.ιChainComplex_d_assoc]
  rw [Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Preadditive.zsmul_comp, affineChainIso_ι]
  rfl

end Convexity.StdSimplex
end
end
