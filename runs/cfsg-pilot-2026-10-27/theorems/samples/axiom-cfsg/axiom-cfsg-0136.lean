public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace TwelveTwentyFive

theorem le_normalizer_proofS (D : Data G) {V L : Subgroup G} (hV : InCalW D.M D.T V)
    (hL : F12.IsComponentModO2 D.M L) (hLV : ⁅L, V⁆ ≠ ⊥)
    (hJL : ⁅F12.jOf D.T, L⁆ ≤ pCoreOf 2 L) :
    L ⊔ D.T ≤ normalizer (proofS D : Set G) := by
  have hLE := le_normalizer_proofE D hL hJL
  have hLCE : L ≤ normalizer ((centralizer (proofE D : Set G) : Subgroup G) : Set G) :=
    A1a.le_normalizer_centralizer hLE
  have key : ∀ x ∈ L, ∀ s ∈ proofS D, x * s * x⁻¹ ∈ proofS D := by
    intro x hx s hs
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h1 := commutator_mem_of_mem_proofS D hV hL hLV hJL x hx s hs
      have h2 : x * s * x⁻¹ = ⁅x, s⁆ * s := by simp only [commutatorElement_def]; group
      rw [h2]
      exact D.T.mul_mem (uc22p22e_pCoreOf_le_T D h1) hs.1
    · exact (Subgroup.mem_normalizer_iff.1 (hLCE hx) s).1 hs.2
  refine sup_le (fun x hx => ?_) ?_
  · rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨key x hx s, fun hs => ?_⟩
    have := key x⁻¹ (L.inv_mem hx) _ hs
    simpa [mul_assoc] using this
  · exact A1a.le_normalizer_inf Subgroup.le_normalizer
      (A1a.le_normalizer_centralizer (T_le_normalizer_proofE D))

end TwelveTwentyFive
end CFSG.LocalAnalysis.UniquenessCase.PartTwo
end
