public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem isSylowTwoOf_of_normalizer_le {X C P : Subgroup G} (hPC : IsSylowTwoOf P C) (hCX : C ≤ X)
    (hN : ∀ x ∈ X, x ∈ Subgroup.normalizer (P : Set G) → x ∈ C) : IsSylowTwoOf P X := by
  rw [A4.isSylowTwoOf_iff_maximal] at hPC ⊢
  obtain ⟨hPC1, hP2, hmaxC⟩ := hPC
  refine ⟨hPC1.trans hCX, hP2, fun Q hQX hQ hPQ => ?_⟩
  by_contra hQP
  have hlt : P < Q := lt_of_le_of_ne hPQ (fun h => hQP (h ▸ le_rfl))
  have hnil : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hnc : NormalizerCondition ↥Q := Group.normalizerCondition_of_isNilpotent
  have hPtop : P.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => ?_
    apply hQP
    intro q hq
    have : (⟨q, hq⟩ : ↥Q) ∈ P.subgroupOf Q := by rw [h]; exact Subgroup.mem_top _
    exact this
  obtain ⟨q, hq, hqP⟩ := IsConcreteLE.exists_of_lt (hnc _ hPtop)
  have hqN : (q : G) ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    by_cases hhQ : h ∈ Q
    · have := (Subgroup.mem_normalizer_iff.mp hq) ⟨h, hhQ⟩
      exact this
    · constructor
      · intro hh
        exact absurd (hPQ.trans le_rfl |> fun _ => (hlt.le hh)) hhQ
      · intro hh
        apply absurd _ hhQ
        have h1 : (q : G) * h * (q : G)⁻¹ ∈ Q := hlt.le hh
        have := Q.mul_mem (Q.mul_mem (Q.inv_mem q.2) h1) q.2
        simpa [mul_assoc] using this
  have hqC : (q : G) ∈ C := hN q (hQX q.2) hqN
  have hP'Q : P ⊔ Subgroup.zpowers (q : G) ≤ Q := sup_le hlt.le (Subgroup.zpowers_le.mpr q.2)
  have hP'2 : IsPGroup 2 ↥(P ⊔ Subgroup.zpowers (q : G)) := hQ.to_le hP'Q
  have hP'C : P ⊔ Subgroup.zpowers (q : G) ≤ C :=
    sup_le hPC1 (Subgroup.zpowers_le.mpr hqC)
  have hle := hmaxC _ hP'C hP'2 le_sup_left
  exact hqP (hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))

end Sylow
end S143
end CFSG.Quasithin
end
