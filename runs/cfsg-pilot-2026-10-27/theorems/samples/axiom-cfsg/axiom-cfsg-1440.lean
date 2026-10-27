public section

namespace CFSG.StandardType

namespace NsFrameComp

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB NoOffOm CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.OddIso Multiplicative

section Orbit

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

local notation "Xe" x:max => ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
  Module.End K (Fin n → K))

variable {x : ↥(unitarySU 2 f K n)} {a : K[X]}

open Classical in
theorem exists_orbW_decomp (H : UnitaryPrimaryData h.bar (stdHermForm h n) (toUnitHom x))
    (ha : a ∈ primaryFactors (Xe x)) (v : Fin n → K) :
    ∃ w ∈ orbW h x a, v - w ∈ (orbW h x a).orthogonalBilin (stdHermForm h n) ∧
      ∀ U : Submodule K (Fin n → K), (∀ u ∈ U, lin x u ∈ U) → v ∈ U → w ∈ U := by
  have hsq := H.squarefree
  set P : K[X] → Prop := fun b => b = a ∨ b = dualPoly h.bar a with hP
  set w := ∑ b ∈ (primaryFactors (Xe x)).filter P, primaryProjection (Xe x) b v with hw
  have hsum := eq_sum_primaryProjection hsq v
  have hsplit : v - w = ∑ b ∈ (primaryFactors (Xe x)).filter (fun b => ¬ P b),
      primaryProjection (Xe x) b v := by
    rw [sub_eq_iff_eq_add', hw, Finset.sum_filter_add_sum_filter_not]
    exact hsum
  refine ⟨w, ?_, ?_, fun U hU hvU => ?_⟩
  · refine Submodule.sum_mem _ fun b hb => ?_
    obtain ⟨hbF, hbP⟩ := Finset.mem_filter.mp hb
    have hmem := primaryProjection_mem hsq hbF v
    rcases hbP with rfl | rfl
    · exact Submodule.mem_sup_left hmem
    · exact Submodule.mem_sup_right hmem
  · rw [hsplit]
    refine Submodule.sum_mem _ fun b hb => ?_
    obtain ⟨hbF, hbP⟩ := Finset.mem_filter.mp hb
    have hmem := primaryProjection_mem hsq hbF v
    refine Submodule.mem_orthogonalBilin.mpr fun m hm => ?_
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Submodule.mem_sup.mp hm
    have had := dualPoly_mem_primaryFactors H ha
    have h1 : stdHermForm h n m₁ (primaryProjection (Xe x) b v) = 0 :=
      orthogonal_of_ne_dualPoly H ha hbF (fun e => hbP (Or.inr e)) hm₁ hmem
    have h2 : stdHermForm h n m₂ (primaryProjection (Xe x) b v) = 0 :=
      orthogonal_of_ne_dualPoly H had hbF
        (fun e => hbP (Or.inl (e.trans (dualPoly_dualPoly_of_mem H ha)))) hm₂ hmem
    change stdHermForm h n (m₁ + m₂) (primaryProjection (Xe x) b v) = 0
    rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
  · refine Submodule.sum_mem _ fun b _ => ?_
    exact aeval_mem_of_inv (X := Xe x) hU _ hvU

end Orbit
end NsFrameComp
end CFSG.StandardType
end
