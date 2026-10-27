public section

namespace CFSG.StandardType.GGResIShape.A5b4c0w12

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hchk : checkTreeI ((exc.map (· ^ 20)).prod) (ggStdTableSymI (CartanMatrix.A 5) 4 0 (-1) (-2)) 4
    [] tree = true := by decide +kernel

end CFSG.StandardType.GGResIShape.A5b4c0w12
end
