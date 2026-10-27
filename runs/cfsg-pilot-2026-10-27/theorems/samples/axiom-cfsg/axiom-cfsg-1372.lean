public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique C10P4F

open scoped Matrix IsMulCommutative

variable {G : Type} [Group G]

theorem exists_multiCoord_of_copies {J W : Subgroup G} [IsMulCommutative ↥W]
    (hJW : J ≤ Subgroup.normalizer (W : Set G)) {k : ℕ} (hk : 1 ≤ k)
    (h : DirectSumOfCopies (autOn J W) ⊤ ⊥
      (FFModel.nat (Assembly.LowTwoRank.StatedSL 5 (ZMod 2))) k) :
    ∃ C : MultiCoord J W k, C.dual = fun _ => false := by
  obtain ⟨U, π, -, hind, hsup, hreal⟩ := h
  have hπ : Function.Bijective π :=
    ⟨realizesVia_injective_of_faithful (FFModel.nat_faithful _) (hreal ⟨0, hk⟩),
      (hreal ⟨0, hk⟩).1⟩
  refine exists_multiCoord hJW π hπ U ?_ ?_ (fun _ => false) (fun i _ => hreal i)
    (fun _ hi => absurd hi (by simp))
  · rw [iSupIndep_def]
    intro i
    rw [disjoint_iff]
    have := hind i
    rwa [bot_sup_eq] at this
  · rw [← hsup, bot_sup_eq]

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
end
