@[expose] public section

universe u v

open CategoryTheory Filter

namespace ProfiniteGrp

namespace MaximalProPQuotient

variable (p : ℕ) [Fact p.Prime] (G : ProfiniteGrp.{u})

variable {G}

variable {P : ProfiniteGrp.{u}} [IsProP p P]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
theorem lift_eta (f : G →ₜ* P) :
    eta p G ≫ lift p f = ProfiniteGrp.ofHom f := by
  let e := isoLimittoFiniteQuotientFunctor P
  rw [← e.cancel_iso_hom_right]
  rw [Category.assoc]
  change eta p G ≫ ((_ ≫ e.inv) ≫ e.hom) = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end MaximalProPQuotient
end ProfiniteGrp
end
