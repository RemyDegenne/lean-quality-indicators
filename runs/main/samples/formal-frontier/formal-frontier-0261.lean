@[expose] public section

noncomputable section

universe u

namespace Subgroup.RightTransversal

variable {G : Type u} [Group G]

section Representatives

variable {H : Subgroup G} (T : H.RightTransversal)

@[simp]
lemma nextEquiv_symm_apply (g : G) (t : ↥(T : Set G)) :
    (nextEquiv T g).symm t = next T t g⁻¹ := rfl

end Representatives
end Subgroup.RightTransversal
end
end
