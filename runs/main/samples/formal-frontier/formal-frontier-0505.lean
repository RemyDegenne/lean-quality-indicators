@[expose] public section

universe u v

open CategoryTheory Filter

namespace ProfiniteGrp

namespace MaximalProPQuotient

variable (p : ℕ) [Fact p.Prime] (G : ProfiniteGrp.{u})

namespace Quotient

omit [Fact p.Prime] in
theorem quotient_inf_isPGroup (U V : Quotient p G) :
    IsPGroup p (G ⧸
      (U.toOpenNormalSubgroup ⊓ V.toOpenNormalSubgroup).toSubgroup) := by
  let f : G →* (G ⧸ U.toOpenNormalSubgroup.toSubgroup) ×
      (G ⧸ V.toOpenNormalSubgroup.toSubgroup) :=
    (QuotientGroup.mk' U.toOpenNormalSubgroup.toSubgroup).prod
      (QuotientGroup.mk' V.toOpenNormalSubgroup.toSubgroup)
  have hprod : IsPGroup p ((G ⧸ U.toOpenNormalSubgroup.toSubgroup) ×
      (G ⧸ V.toOpenNormalSubgroup.toSubgroup)) :=
    U.isPGroup'.prod V.isPGroup'
  have hrange : IsPGroup p f.range := hprod.to_subgroup f.range
  have hker : f.ker =
      (U.toOpenNormalSubgroup ⊓ V.toOpenNormalSubgroup).toSubgroup := by
    dsimp only [f]
    rw [MonoidHom.ker_prod, QuotientGroup.ker_mk',
      QuotientGroup.ker_mk']
    rfl
  have hquot : IsPGroup p (G ⧸ f.ker) :=
    hrange.of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  exact hquot.of_equiv (QuotientGroup.quotientMulEquivOfEq hker)

end Quotient
end MaximalProPQuotient
end ProfiniteGrp
end
