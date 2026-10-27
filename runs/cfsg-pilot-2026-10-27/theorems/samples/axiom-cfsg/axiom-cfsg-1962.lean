public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open Module CFSG.RankThree.Classical2 CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalAut
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
  CFSG.GroupTheory.WeirSylow CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open scoped Pointwise

section Conj

variable {K : Type} [Field K] [Finite K]

theorem exists_conj_mem_matrixProjectiveImage_four [CharP K 2]
    {g : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hg : Nat.Coprime 3 (orderOf g)) :
    ∃ β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
      β⁻¹ * g * β ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
  classical
  set P := projectivePointFamily (coordinateQuadPlus 4 K) with hP
  set O := MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) P
    with hO
  have hmemE : ∀ δ, δ ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) ↔ δ • P = P :=
    CFSG.SeitzReduction.OmegaPilot.mem_image_iff_smul_pointFamily le_rfl
  have hgO : ∀ Y ∈ O, g • Y ∈ O := fun Y hY => by
    obtain ⟨β, rfl⟩ := hY
    exact ⟨g * β, mul_smul _ _ _⟩
  have hO13 : O.ncard = 1 ∨ O.ncard = 3 :=
    CFSG.SeitzReduction.OmegaPilot.orbit_pointFamily_ncard_four (K := K)
  obtain ⟨Y, hYO, hgY⟩ : ∃ Y ∈ O, g • Y = Y := by
    rcases hO13 with h1 | h3
    · obtain ⟨Z, hZ⟩ := Set.ncard_eq_one.1 h1
      have hPO : P ∈ O := MulAction.mem_orbit_self P
      have hgP := hgO P hPO
      rw [hZ, Set.mem_singleton_iff] at hPO hgP
      exact ⟨P, MulAction.mem_orbit_self P, hgP.trans hPO.symm⟩
    · obtain ⟨a, b, c, hab, hac, hbc, habc⟩ := Set.ncard_eq_three.1 h3
      have hmem : ∀ Y ∈ O, Y = a ∨ Y = b ∨ Y = c := fun Y hY => by
        rw [habc] at hY
        simpa using hY
      have haO : a ∈ O := by rw [habc]; simp
      have hbO : b ∈ O := by rw [habc]; simp
      have hcO : c ∈ O := by rw [habc]; simp
      rcases exists_fixed_of_three hg hab hac hbc (hmem _ (hgO a haO)) (hmem _ (hgO b hbO))
          (hmem _ (hgO c hcO)) with h | h | h
      · exact ⟨a, haO, h⟩
      · exact ⟨b, hbO, h⟩
      · exact ⟨c, hcO, h⟩
  obtain ⟨β, rfl⟩ := hYO
  exact ⟨β, (hmemE _).2 (by rw [mul_smul, mul_smul, hgY, inv_smul_smul])⟩

end Conj
end CFSG.HardMathSupport.Dickson.Bal207
end
