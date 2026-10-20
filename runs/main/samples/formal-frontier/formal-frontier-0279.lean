@[expose] public section

open CategoryTheory

universe u

namespace ProfiniteGrp

@[simp]
theorem closedCosetProj_apply (G : ProfiniteGrp.{u}) (H : ClosedSubgroup G) (g : G) :
    G.closedCosetProj H g = QuotientGroup.mk g := rfl

end ProfiniteGrp
end
