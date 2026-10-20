@[expose] public section

namespace Utilities

namespace TwoPole

universe u v

theorem winnable_four_pile_sub_two
    (G : CFGraph.{u}) (a uMark : G.V)
    (hG : graphConnected G) (hGenus : CFGraph.genus G = 2) :
    winnable G
      ((4 : ℤ) • oneChip a - (2 : ℤ) • oneChip uMark) := by
  apply winnable_of_degree_eq_genus G hG
  rw [CFDiv.degree.map_sub, deg_zsmul_one_chip, deg_zsmul_one_chip, hGenus]
  norm_num

end TwoPole
end Utilities
end
