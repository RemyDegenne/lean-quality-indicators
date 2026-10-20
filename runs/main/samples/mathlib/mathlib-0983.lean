@[expose] public section

open CategoryTheory TopologicalSpace Opposite Topology

universe u w w'

namespace TopologicalSpace.Opens

variable {X Y Z : TopCat.{u}} {U V W : Opens X}

@[simp]
theorem toTopCat_map (X : TopCat.{u}) {U V : Opens X} {f : U ⟶ V} {x} {h} :
    ((toTopCat X).map f) ⟨x, h⟩ = ⟨x, f.le h⟩ :=
  rfl

end TopologicalSpace.Opens
end
