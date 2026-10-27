public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.SL2Model
  CFSG.Quasithin.SL3Model

open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type*} [Group G]

section Translate

variable {U S : Subgroup G} {g h : G}

theorem S₂_tripleU : TripleGrp.S₂ (tripleU U g h) = U ⊓ rconj U g ⊓ rconj U h := by
  show tripleU U g h 0 ⊓ tripleU U g h 1 ⊓ tripleU U g h 2 = _
  rw [tripleU_zero, tripleU_one, tripleU_two]

end Translate
end CFSG.Quasithin
end
