@[expose] public section

universe v₁ v₂ v₃ v₁' u₁ u₂ u₃ u₁'

namespace CategoryTheory

open Category CategoryTheory.Functor MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory.{v₃} E]
  {C' : Type u₁'} [Category.{v₁'} C']

namespace Equivalence

variable (e : C ≌ D)

/-- If a monoidal functor `F` is an equivalence of categories then its inverse is also monoidal. -/
@[instance_reducible]
noncomputable def inverseMonoidal [e.functor.Monoidal] : e.inverse.Monoidal := by
  letI := e.toAdjunction.rightAdjointLaxMonoidal
  have : IsIso (LaxMonoidal.ε e.inverse) := by
    simp only [this, Adjunction.rightAdjointLaxMonoidal_ε, Adjunction.homEquiv_unit]
    infer_instance
  have : ∀ (X Y : D), IsIso (LaxMonoidal.μ e.inverse X Y) := fun X Y ↦ by
    simp only [Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit]
    infer_instance
  apply Monoidal.ofLaxMonoidal

end Equivalence
end CategoryTheory
end
