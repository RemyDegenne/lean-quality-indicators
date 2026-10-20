@[expose] public section

universe u

namespace MulActionHom

variable {G : Type u} [Group G] {H K L : Subgroup G}

/-- The equivariant map from left cosets of `H` to left cosets of `K` induced
by an inclusion `H ≤ K`. Its underlying function is `Subgroup.quotientMapOfLE`. -/
def quotientMapOfLE (h : H ≤ K) : (G ⧸ H) →[G] G ⧸ K where
  toFun := Subgroup.quotientMapOfLE h
  map_smul' g q := by
    refine Quotient.inductionOn' q ?_
    intro a
    simp only [MulAction.Quotient.smul_mk, Subgroup.quotientMapOfLE_apply_mk, id_eq]

end MulActionHom
end
