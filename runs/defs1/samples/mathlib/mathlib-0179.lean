@[expose] public section

universe u v

open Set

variable {X : Type u} {Y : Type v}

section Defs

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

/-- A map `f : X → Y` is said to be an *open map*,
if the image of any open `U : Set X` is open in `Y`. -/
@[wikidata Q56653513]
def IsOpenMap (f : X → Y) : Prop := ∀ U : Set X, IsOpen U → IsOpen (f '' U)

end Defs
end
