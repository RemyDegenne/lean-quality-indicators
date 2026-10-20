@[expose] public section

open CategoryTheory Order Set TopologicalSpace

namespace Locale

section pt_definition

variable (L : Type*) [CompleteLattice L]

/-- The type of points of a complete lattice `L`, where a *point* of a complete lattice is,
by definition, a frame homomorphism from `L` to `Prop`. -/
abbrev PT := FrameHom L Prop

end pt_definition
end Locale
end
