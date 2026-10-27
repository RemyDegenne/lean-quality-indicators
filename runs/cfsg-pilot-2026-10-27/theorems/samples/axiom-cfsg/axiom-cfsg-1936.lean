public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.ClassicalInvolution.Q3.TC.Graph

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10 (aeBlocks8')

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

namespace CSetting

variable {K J : Subgroup G} (hS : CSetting 3 IH Ω K J)

include hS

theorem maxOrbSet_eq_eight' (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) 8)
    {Ks : Subgroup G} (hKs : Ks ∈ orbOf (TC.nbrAdj Ω) J K) (hKsK : Ks ≠ K)
    (hKsπ : Ks ∉ orbOf (TC.nbrAdj Ω) K J)
    (hz : ∀ z zs : G, IsUniqueInvolution K z → IsUniqueInvolution Ks zs → zs = z)
    (hKsX : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ k ∈ Ks, x * k = k * x) :
    ∀ M ∈ maxOrbSet Ω (orbOf (TC.nbrAdj Ω) K J), M = K ∨ M = Ks := by
  classical
  have hC := hS.toCHyp
  have hJΩ : J ∈ Ω := hC.orb_subset_omega (mem_orbOf_self K J)
  obtain ⟨g, hg⟩ := hC.trans K hS.adj.1 J hJΩ
  obtain ⟨Ks₀, y, hD, α, h, b, y₀, hy₀, hy₀y, -, -, hlab₀, hlab₁⟩ :=
    hC.exists_data128_of (by norm_num) I hg
  have hy := hC.y_comm_of_rigid (by norm_num) I (ae3Rigid (by norm_num) (by norm_num)) hD
  have h1 := hS.maxOrbSet_eq_eight I hD hy hy₀ hy₀y hlab₀ hlab₁
  have hKsB : Ks ∈ maxOrbSet Ω (orbOf (TC.nbrAdj Ω) K J) := by
    refine hC.mem_maxOrbSet_of_adj (hC.swap.orb_subset_omega hKs) fun L hL =>
      hC.nbrAdj_of_comm (hC.swap.orb_subset_omega hKs) (hC.orb_subset_omega hL)
        (fun e => hKsπ (e ▸ hL)) fun a ha b hb => ?_
    exact (hKsX b (le_pSpan hL hb) a ha).symm
  intro M hM
  rcases h1 M hM with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    rcases h1 Ks hKsB with h' | h'
    · exact absurd h' hKsK
    · rw [h, h']

end CSetting
end CFSG.ClassicalInvolution.Q3.TC.Thin
end
