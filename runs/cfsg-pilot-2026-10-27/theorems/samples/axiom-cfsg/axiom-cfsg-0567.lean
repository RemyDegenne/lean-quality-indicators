public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

open CFSG.LieType.SeitzGeneration HyperBlocks CFSG.Open

open CFSG.RankThree.PartOne.KCOrthogonal (glue glue_apply glue_mul glue_one restrictEquiv
  exists_coe_add_of_isCompl)

open scoped DirectSum CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]

variable {p : ℕ}

theorem finrank_ker_projBlock_add_finrank_blockSpace [FiniteDimensional F V] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A) (D : Hyperplane A p) :
    Module.finrank F ↥(LinearMap.ker (projBlock A hp hpF hA D)) +
      Module.finrank F ↥(blockSpace A D.1) = Module.finrank F V :=
  Submodule.finrank_add_eq_of_isCompl (isCompl_blockSpace_ker A hp hpF hA D).symm

end CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
end
