public section

universe w' v u

namespace TauCeti

open CategoryTheory Category Limits Preadditive

variable (C : Type u) [Category.{v} C]

namespace DifferentialModule

variable {C}

section DifferentialObject

variable [HasZeroMorphisms C] {S : Type*} [AddMonoidWithOne S] [HasShift C S]
  (e : shiftFunctor C (1 : S) ≅ 𝟭 C)

/-- The differential object of a differential module `M`, for a natural isomorphism
`e : shiftFunctor C 1 ≅ 𝟭 C`: the differential is `M.d ≫ e.inv.app M.X : M.X ⟶ M.X⟦1⟧`, and its
shifted square vanishes because `M.d ≫ M.d = 0`. -/
@[expose, implicit_reducible, simps]
def toDifferentialObject : DifferentialModule C ⥤ DifferentialObject S C where
  obj M :=
    { obj := M.X
      d := M.d ≫ e.inv.app M.X
      d_squared := by
        rw [Functor.map_comp, assoc, ← e.inv.naturality_assoc]
        simp }
  map φ :=
    { f := φ.f
      comm := by
        rw [assoc, ← e.inv.naturality]
        simp }

end DifferentialObject
end DifferentialModule
end TauCeti
end
