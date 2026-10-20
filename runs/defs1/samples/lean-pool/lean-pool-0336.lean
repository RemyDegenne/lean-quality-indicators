@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

section SuperConveniences

variable {S : SuperCommAlgebra.{v, v}}

variable {P P' Q Q' T : S.Mod.{v, v, v, v}}

/-- The tensor product of two isomorphisms of super modules. -/
noncomputable def SuperCommAlgebra.Mod.tensorIso (a : P ≅ P')
    (b : Q ≅ Q') : P.tensor Q ≅ P'.tensor Q' where
  hom := SuperCommAlgebra.Mod.tensorHom a.hom b.hom
  inv := SuperCommAlgebra.Mod.tensorHom a.inv b.inv
  hom_inv_id := by
    rw [← SuperCommAlgebra.Mod.tensorHom_comp, a.hom_inv_id,
      b.hom_inv_id, SuperCommAlgebra.Mod.tensorHom_id]
  inv_hom_id := by
    rw [← SuperCommAlgebra.Mod.tensorHom_comp, a.inv_hom_id,
      b.inv_hom_id, SuperCommAlgebra.Mod.tensorHom_id]

end SuperConveniences
end RS
end
