public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE

variable {K M : Type} [Group K] [Group M] {x z : K}

theorem commute_psi_of_commute {τ : Tag} {K : Type} [Field K] {L : Type} [Field L]
    {x z : adjointGroup τ K}
    {ψ : ↥(Subgroup.centralizer ({x} : Set (adjointGroup τ K))) →* ModGL τ L}
    {y : ↥(Subgroup.centralizer ({x} : Set (adjointGroup τ K)))}
    (hzC : z ∈ Subgroup.centralizer ({x} : Set (adjointGroup τ K)))
    (hyz : (y : adjointGroup τ K) * z = z * (y : adjointGroup τ K)) :
    Commute (ψ y) (ψ ⟨z, hzC⟩) := by
  show ψ y * ψ ⟨z, hzC⟩ = ψ ⟨z, hzC⟩ * ψ y
  calc ψ y * ψ ⟨z, hzC⟩ = ψ (y * ⟨z, hzC⟩) := (map_mul ψ y ⟨z, hzC⟩).symm
    _ = ψ ⟨(y : adjointGroup τ K) * z, mul_mem y.2 hzC⟩ := rfl
    _ = ψ ⟨z * (y : adjointGroup τ K), mul_mem hzC y.2⟩ := by
        congr 1
        exact Subtype.ext hyz
    _ = ψ (⟨z, hzC⟩ * y) := rfl
    _ = ψ ⟨z, hzC⟩ * ψ y := map_mul ψ ⟨z, hzC⟩ y

end CFSG.LocalAnalysis.GLTheoremA.Y10F
end
