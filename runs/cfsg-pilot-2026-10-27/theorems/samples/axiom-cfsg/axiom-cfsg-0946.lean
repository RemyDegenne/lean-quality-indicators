public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem Hyp.exists_sylow_kernel (hd : d.Hyp) :
    ∃ S : Sylow 2 (centralizer (d.L : Set G)), ⟨d.t, hd.t_mem⟩ ∈ S ∧
      IsCyclic (S : Subgroup (centralizer (d.L : Set G))) ∧
      (∀ x ∈ S, orderOf x = 2 → x = ⟨d.t, hd.t_mem⟩) ∧
      centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) =
        (S : Subgroup (centralizer (d.L : Set G))).map (centralizer (d.L : Set G)).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tC : centralizer (d.L : Set G) := ⟨d.t, hd.t_mem⟩ with htCdef
  have htC2 : orderOf tC = 2 := by rw [htCdef, orderOf_mk, hd.t_two]
  have hp : IsPGroup 2 (zpowers tC) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htC2, pow_one])
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have htS : tC ∈ (S : Subgroup (centralizer (d.L : Set G))) := hS (mem_zpowers tC)
  have hcyc := hd.std.isCyclic_sylow S
  obtain ⟨-, huniq, -, -, -, -, hCH, -, -⟩ :=
    CFSG.ComponentClassification.StandardRecognition.standard_cyclic_local_centralizer_kernel
      hd.std.standard S hcyc htS htC2 (hd.std.core d.t hd.t_two)
  exact ⟨S, htS, hcyc, huniq, hCH⟩

end Data
end CFSG.LocalAnalysis.EvenBN.Tits
end
