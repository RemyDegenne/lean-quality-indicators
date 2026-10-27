public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External

open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryModel

open CFSG.ShultStronglyClosedTI.TwoCoreGrowth

section Root

variable {K : Type} [Field K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

theorem sq_eq_one_of_mem_rootZ [CharP K 2] {u : ProjectiveSpecialUnitaryMatrixGroup J}
    (hu : u ∈ rootZ J hJ) : u ^ 2 = 1 := by
  obtain ⟨z, hz, rfl⟩ := hu
  exact (unitary_projective_root_square_one_iff J hJ z).mpr (congrArg Multiplicative.toAdd hz)

end Root
end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
end
