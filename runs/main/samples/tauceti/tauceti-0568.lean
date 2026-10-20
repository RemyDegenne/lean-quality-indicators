public section

namespace TauCeti.ConstructionA

variable (m : ℕ) [NeZero m] (ι : Type*) [Fintype ι]

@[simp]
theorem isLagrangian_codeInZeroLatticeDiscriminantGroup_iff (C : AdditiveCode (ZMod m) ι) :
    (zeroLattice m ι).discriminantBilinearModule.IsLagrangian
        (codeInZeroLatticeDiscriminantGroup m ι C) ↔
      ((FiniteBilinearModule.zmodStandard m).coordinatePower ι).IsLagrangian C := by
  rw [codeInZeroLatticeDiscriminantGroup_eq_codeInZeroLatticeDiscriminantBilinearModule,
    ← (discriminantIsometry m ι).isLagrangian_map_iff,
    map_codeInZeroLatticeDiscriminantBilinearModule]

end TauCeti.ConstructionA
end
