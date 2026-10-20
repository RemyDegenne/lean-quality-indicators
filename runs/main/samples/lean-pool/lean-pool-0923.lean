@[expose] public section

open Set Function

open CategoryTheory CategoryTheory.SingleObj Quiver

open unitInterval

noncomputable section

universe u

namespace FiniteGraphFreeGroup

section

variable {V : Type u} [Quiver.{u} V] [Quiver.Arborescence V]

@[simp]
theorem treeContractionCoordinate_zero_right (t : I) :
    treeContractionCoordinate t 0 = ⟨(1 + (t : ℝ)) / 2, by
      constructor <;> nlinarith [t.2.1, t.2.2]⟩ := by
  apply Subtype.ext
  simp [treeContractionCoordinate]

end
end FiniteGraphFreeGroup
end
end
