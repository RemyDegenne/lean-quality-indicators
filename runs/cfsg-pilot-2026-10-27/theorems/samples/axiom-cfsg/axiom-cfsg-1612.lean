public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Matrix CFSG.Fischer CFSG.Assembly.LowTwoRank

open CFSG.Fischer.Classification (CubeRel)

open CFSG.ClassicalInvolution.Models.SymplecticPairs

open CFSG.LieType.Steinberg.Sp (blockMat)

open CFSG.LieType.Universal.Unitary (SU antidiag conjTr mem_SU)

open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)

open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)

namespace EightU

theorem cGi'_mul_cG' : cGi' * cG' = 1 := by decide +kernel

end EightU
end CFSG.SeitzReduction.SymplecticPilot
end
