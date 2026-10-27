public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable (p f : ℕ) [Fact p.Prime]

theorem axisFrameSide : AxisFrameSide p f :=
  AxisFrameSide.of_core p f (axisFrameSideCore p f)

end CFSG.ClassicalInvolution.NDB
end
