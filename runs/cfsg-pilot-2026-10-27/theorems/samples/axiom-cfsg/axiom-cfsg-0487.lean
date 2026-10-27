public section

namespace CFSG.Holt.H78

namespace CaseAD

open MulAction CFSG.Holt CFSG.Open

open scoped Pointwise

namespace DCase

variable {G : Type} [Group G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  {α : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)} {hS : Sec4Setting G Ω}
  {hP : Prop46Setup G Ω α v P} (H : DCase hS hP)

variable [Finite G] [FaithfulSMul G Ω]

omit [Finite G] [FaithfulSMul G Ω] in
theorem Vdir_le_stab (j : H.A₁.D.ι) : H.Vdir j ≤ stabilizer G (holtDelta G Ω α H.β₁) :=
  fun _ hg => stabilizer_pair_le α H.β₁ (H.V_le_pair (Subgroup.mem_inf.mp hg).1)

end DCase
end CaseAD
end CFSG.Holt.H78
end
