public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open Matrix CFSG.Quasithin.A38c15 CFSG.Quasithin.E2P.Asc80 CFSG.Quasithin.E1

open scoped MatrixGroups commutatorElement

variable {p : ℕ} [Fact p.Prime]

theorem leviBlock_le_normalizer_rowU : leviBlock p ≤ Subgroup.normalizer (rowU p : Set _) :=
  leviBlock_le_linePar.trans linePar_le_normalizer_rowU

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
end
