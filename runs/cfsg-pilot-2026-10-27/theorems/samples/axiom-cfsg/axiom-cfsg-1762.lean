public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer

theorem w₂_gen : yamGen 16 = yamGen 2 * (yamGen 16 * yamGen 2 * yamGen 16) * yamGen 2 :=
  sujExt (by decide +kernel)

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
end
