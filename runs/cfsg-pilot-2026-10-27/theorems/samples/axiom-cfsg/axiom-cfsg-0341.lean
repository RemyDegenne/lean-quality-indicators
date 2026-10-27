public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG

open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

open CFSG.Assembly.RankThreeEven (projSL projSU)

open CFSG.RankThree.PartTwo.Sec4.Item49Tools

open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (outer_card_dvd_two_of_equiv_outside_six)

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (higher_linear_outer_order_divides_field_gcd_bound)

namespace Item49Small

theorem finite_outer (X : Type*) [Group X] [Finite X] : Finite (Outer X) := by
  have : Finite (MulAut X) := MulEquiv.finite_left
  infer_instance

end Item49Small
end CFSG.RankThree.PartTwo.Sec4
end
