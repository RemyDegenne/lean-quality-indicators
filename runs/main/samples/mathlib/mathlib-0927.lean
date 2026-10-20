public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)

attribute [instance] QuasiSeparated.quasiCompact_diagonal

theorem quasiSeparatedSpace_of_quasiSeparated (f : X ⟶ Y)
    [hY : QuasiSeparatedSpace Y] [QuasiSeparated f] : QuasiSeparatedSpace X := by
  rw [quasiSeparatedSpace_iff_quasiSeparated] at hY ⊢
  rw [← terminalIsTerminal.hom_ext (f ≫ terminal.from Y) (terminal.from X)]
  infer_instance

end AlgebraicGeometry
end
end
