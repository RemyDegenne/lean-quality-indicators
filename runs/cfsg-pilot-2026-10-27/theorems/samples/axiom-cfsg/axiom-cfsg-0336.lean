public section

namespace CFSG.RankThree.PartOne.LinAlg

open CFSG

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G]

section MatrixForm

variable {n : ℕ}

variable {E : Subgroup G} (f : Multiplicative (Fin n → ZMod p) ≃* E)

theorem coordGL_mem_torusWeylGL_iff (φ : MulAut E) :
    coordGL f φ ∈ torusWeylGL f ↔ φ ∈ torusWeyl E :=
  Subgroup.mem_map_iff_mem (coordGL_injective f)

end MatrixForm
end CFSG.RankThree.PartOne.LinAlg
end
