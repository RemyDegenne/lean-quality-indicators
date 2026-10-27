@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

open scoped MonObj

universe v u

variable {D : Type u}

/-- The free module on an isomorphism. -/
noncomputable def freeModMapIso
    [Category.{v} D] [MonoidalCategory D] (B : D) [MonObj B]
    {V W : D} (e : V ≅ W) :
    freeMod B V ≅ freeMod B W where
  hom := freeModMap B e.hom
  inv := freeModMap B e.inv
  hom_inv_id := by
    apply Mod.Hom.ext
    change (B ◁ e.hom) ≫ (B ◁ e.inv) = 𝟙 (B ⊗ V)
    rw [← MonoidalCategory.whiskerLeft_comp, e.hom_inv_id,
      MonoidalCategory.whiskerLeft_id]
  inv_hom_id := by
    apply Mod.Hom.ext
    change (B ◁ e.inv) ≫ (B ◁ e.hom) = 𝟙 (B ⊗ W)
    rw [← MonoidalCategory.whiskerLeft_comp, e.inv_hom_id,
      MonoidalCategory.whiskerLeft_id]

end RS
end
