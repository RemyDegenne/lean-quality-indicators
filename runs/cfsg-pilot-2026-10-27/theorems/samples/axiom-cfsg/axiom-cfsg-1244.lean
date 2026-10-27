public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank

open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section CfgW

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem Cfg2W.hinv_X2 (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : HInv H (XB t X₁) :=
  c.hinv_X1.conj c.b66.t_normH

end CfgW
end CFSG.GH74.GLS.LU.Local.Five
end
