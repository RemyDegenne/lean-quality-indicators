@[expose] public section

open CategoryTheory TopologicalSpace Opposite Topology

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

namespace IsOpenMap

open TopologicalSpace

variable {f}

/-- An open map `f : X ⟶ Y` induces an adjunction between `OpenNhds x` and `OpenNhds (f x)`. -/
def adjunctionNhds (h : IsOpenMap f) (x : X) : IsOpenMap.functorNhds h x ⊣ OpenNhds.map f x where
  unit := { app := fun _ => homOfLE fun x hxU => ⟨x, hxU, rfl⟩ }
  counit := { app := fun _ => homOfLE fun _ ⟨_, hfxV, hxy⟩ => hxy ▸ hfxV }

end IsOpenMap
end
