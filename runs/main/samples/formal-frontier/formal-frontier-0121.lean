@[expose] public section

universe u v

namespace Subgroup

variable {G : Type u} [Group G]

@[simp] theorem indexTwoEquivNontrivialHom_symm_apply_val
    (χ : G →* Multiplicative (ZMod 2)) (hχ : χ ≠ 1) :
    ((indexTwoEquivNontrivialHom (G := G)).symm ⟨χ, hχ⟩).val = χ.ker := rfl

end Subgroup
end
