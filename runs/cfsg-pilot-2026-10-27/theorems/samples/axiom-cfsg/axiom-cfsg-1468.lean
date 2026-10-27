public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial

open CFSG.Quasithin (perfectCore)

open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section Cover

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]

variable {e : L ≃* LinearFlag.projectiveSL n K} {t : G}

theorem swapNeighbourCover_rootTorus (hn : 5 ≤ n)
    (hparam : ∀ (a b : Fin n) (hab : a ≠ b),
      Nonempty (SwapNeighbourParam e t (modelToG e (rootTorus (K := K) hab))
        (({a, b} : Finset (Fin n))ᶜ)))
    {s : ℕ} (hs : s + 2 ≤ n) : SwapNeighbourCover e t s := by
  intro S hS
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_index_notMem (S := S) (by omega)
  refine ⟨modelToG e (rootTorus (K := K) hab), ({a, b} : Finset (Fin n))ᶜ, fun x hx => ?_,
    ⟨a, by simp⟩, ?_, modelToG_rootTorus_le e hab ha hb, hparam a b hab⟩
  · simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => ha (h ▸ hx), fun h => hb (h ▸ hx)⟩
  · rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
    omega

end Cover
end CFSG.SeitzReduction.LinearPilot
end
