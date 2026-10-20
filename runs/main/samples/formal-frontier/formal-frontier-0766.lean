@[expose] public section

open CategoryTheory Set

universe u v

namespace ProfiniteAddGrp

namespace IsTopologicalGenerator

variable {G : ProfiniteAddGrp.{u}} {H : ProfiniteAddGrp.{v}} {g : G}

theorem equiv_iff (e : G ≃ₜ+ H) :
    IsTopologicalGenerator H (e g) ↔ IsTopologicalGenerator G g := by
  constructor
  · intro h
    simpa using h.map_equiv e.symm
  · exact fun h ↦ h.map_equiv e

end IsTopologicalGenerator
end ProfiniteAddGrp
end
