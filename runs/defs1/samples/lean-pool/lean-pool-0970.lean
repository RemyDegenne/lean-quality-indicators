@[expose] public section

namespace LO

namespace Modal

section «lp_section_1»

open Kripke

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.FrameClass.logic (C : FrameClass) : Logic := { φ | C ⊧ φ }

end «lp_section_1»
end Modal
end LO
end
