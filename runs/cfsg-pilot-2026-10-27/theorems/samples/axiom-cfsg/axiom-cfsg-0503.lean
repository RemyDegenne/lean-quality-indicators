public section

namespace CFSG.Quasithin

namespace H

namespace Sp4

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix PairG CFSG.LocalAnalysis.ComponentInitial

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (sym2 sym2_transpose unitri inv_unitri
  isUnitriangular_unitri eq_unitri_of_isUnitriangular eq_sym2)

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (blockMat unipotent mem_unipotent
  exists_mem_unipotent)

open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp)

open CFSG.RankThree.SubgroupLists (spForm spE spForm_spE_left spForm_mulVec)

open scoped Matrix Pointwise

local notation "ι₀" => (Sum.inl 0 : Fin 2 ⊕ Fin 2)

local notation "ι₂" => (Sum.inr 0 : Fin 2 ⊕ Fin 2)

section Lin

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

theorem pairMatHom_injective : Function.Injective (pairMatHom ι F) := by
  rintro ⟨A, A'⟩ ⟨C, C'⟩ h
  obtain ⟨h1, h2⟩ := pairAut_injective h
  exact Prod.ext (matHom_injective h1) (matHom_injective h2)

end Lin
end Sp4
end H
end CFSG.Quasithin
end
