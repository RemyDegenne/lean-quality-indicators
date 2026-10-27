public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint
  CFSG.Sporadic.Recognition.LyonsSims

section Align

theorem exists_conj_mem_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hP : Nat.card P = p ^ (Nat.card G).factorization p) {v : G}
    (hv : IsPGroup p (zpowers v)) : ∃ c : G, c⁻¹ * v * c ∈ P := by
  let S : Sylow p G := Sylow.ofCard P hP
  obtain ⟨Q, hQ⟩ := hv.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G S Q
  refine ⟨c, ?_⟩
  have hvQ : v ∈ (Q : Subgroup G) := hQ (mem_zpowers v)
  rw [← hc, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at hvQ
  have : (MulAut.conj c)⁻¹ • v = c⁻¹ * v * c := by
    simp [MulAut.smul_def]
  rw [this] at hvQ
  exact hvQ

end Align
end CFSG.Sporadic.Recognition.McLAS
end
