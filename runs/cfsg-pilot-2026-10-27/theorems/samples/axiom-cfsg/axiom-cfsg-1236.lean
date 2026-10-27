public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

open CFSG.RankThree.E6 CFSG.LieType.AlgebraicGroups

namespace E6EvenFixedRootDatum

variable {Ω : Type} [Field Ω] [CharP Ω 2] [IsAlgClosed Ω] (D : E6EvenFixedRootDatum Ω)

theorem thetaOrbit_eq (α : Fin Tag.E6.rank → ℤ) : thetaOrbit D.theta α = {α, D.δ α} := by
  rw [thetaOrbit_eq_iterate]
  ext β
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, rfl⟩
    exact D.iterate_δ m α
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

end E6EvenFixedRootDatum
end CFSG.RankThree.Lattice
end
