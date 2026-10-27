public section

namespace CFSG.Quasithin.A94.L52

open Matrix CFSG.CGT.M24S

open scoped Pointwise

theorem phiQ_mem (p : QPar) : phiQ p ∈ Qh :=
  mul_mem (U1_le_Qh (unipOfS1_mem _ _)) (U2_le_Qh (unipOfS2_mem _ _))

end CFSG.Quasithin.A94.L52
end
