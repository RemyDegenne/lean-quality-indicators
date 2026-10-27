@[expose] public section

namespace LO

namespace Modal

namespace Kripke

variable {F : Frame} {x y z : F.World}

open Relation

section «lp_section_1»

infix:45 " ≺^* " => Frame.RelReflTransGen

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.TransitiveReflexiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^* ·)

end «lp_section_1»
end Kripke
end Modal
end LO
end
