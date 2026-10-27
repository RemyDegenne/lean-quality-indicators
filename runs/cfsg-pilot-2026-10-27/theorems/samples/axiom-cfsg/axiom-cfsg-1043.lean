public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

open CFSG.RankThree.PartTwo.Sec4.Item434Kit

open CFSG.Assembly.RankThreeEven (projSL)

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (higher_linear_outer_order_divides_field_gcd_bound)

open Matrix

theorem zeta_sq_mul_sq : zeta ^ 2 * zeta ^ 2 = zeta := by
  linear_combination zeta * zeta_spec.1

end CFSG.RankThree.PartTwo.Sec4.RonanK432
end
