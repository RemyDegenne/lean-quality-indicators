@[expose] public section

namespace CategoryTheory

open Set Groupoid

universe u v

variable {C : Type u} [Groupoid C]

namespace Subgroupoid

variable (S : Subgroupoid C)

section Hom

variable {D : Type*} [Groupoid D] (φ : C ⥤ D)

/-- The "forward" image of a subgroupoid under a functor injective on objects -/
def map (hφ : Function.Injective φ.obj) (S : Subgroupoid C) : Subgroupoid D where
  arrows c d := {x | Map.Arrows φ hφ S c d x}
  inv := by
    rintro _ _ _ ⟨⟩
    rw [inv_eq_inv, ← Functor.map_inv, ← inv_eq_inv]
    constructor; apply S.inv; assumption
  mul := by
    rintro _ _ _ _ ⟨f, hf⟩ q hq
    obtain ⟨c₃, c₄, g, he, rfl, hg, gq⟩ := (Map.arrows_iff φ hφ S q).mp hq
    cases hφ he; rw [gq, ← eq_conj_eqToHom, ← φ.map_comp]
    constructor; exact S.mul hf hg

end Hom
end Subgroupoid
end CategoryTheory
end
