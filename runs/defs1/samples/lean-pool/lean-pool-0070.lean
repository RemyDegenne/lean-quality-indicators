@[expose] public section

open Function

noncomputable section

namespace MarshallHall

universe u

variable {G : Type u} [Group G]

/-- Right multiplication acting on right cosets of a subgroup. -/
def rightMul (H : Subgroup G) (a : G) : RightCosetQuotient H → RightCosetQuotient H :=
  Quotient.lift (fun x : G => Quotient.mk'' (x * a)) (by
    intro x y hxy
    apply Quotient.sound'
    have hxy' : (QuotientGroup.rightRel H) x y := hxy
    rw [QuotientGroup.rightRel_apply] at hxy' ⊢
    simpa [mul_assoc] using hxy')

end MarshallHall
end
end
