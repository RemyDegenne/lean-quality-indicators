public section

noncomputable section

namespace TauCeti

open Set Topology unitInterval

universe u v w

variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]

namespace MappingCylinder

variable {f : C(X, Y)}

/-- The inclusion of the source of `f` into its mapping cylinder as the bottom face of the
cylinder. -/
def incl (f : C(X, Y)) : C(X, MappingCylinder f) := (mkCyl f).comp ⟨fun x => (0, x), by fun_prop⟩

end MappingCylinder
end TauCeti
end
end
