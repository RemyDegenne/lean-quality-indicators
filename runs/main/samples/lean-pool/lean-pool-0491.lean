@[expose] public section

noncomputable section

namespace BKAR

namespace BKARContDiff

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {ρ : (Edge V → ℝ) → ℝ}

theorem allBranchesAnalytic_of_contDiff
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ),
      pref.toFinset = F.edges →
      prefixTs.length = pref.length →
      0 ≤ top →
      (∀ t ∈ Set.uIcc 0 top, ∀ e : F.EdgeParam,
        t ≤ F.paramsOfOrder pref prefixTs e) →
      Forest.allBranchesAnalytic choices n F pref prefixTs top ρ
  | 0, F, pref, prefixTs, top, _hpref, _hprefixTs, _htop, _hbound => by
      exact Forest.allBranchesAnalytic_zero choices F pref prefixTs top ρ
  | n + 1, F, pref, prefixTs, top, hpref, hprefixTs, htop, hbound => by
      rw [Forest.allBranchesAnalytic]
      have hsmooth :=
        hρ.allBranchesAnalytic_smooth_obligations choices F pref prefixTs
          top hpref hprefixTs
      refine ⟨hbound, hsmooth.1, hsmooth.2.1, hsmooth.2.2, ?_, ?_⟩
      · intro e
        exact
          hρ.allBranchesAnalytic_child_recursive_sum_intervalIntegrable
            choices F e pref prefixTs top hprefixTs
      · intro e t ht
        let child := (choices F e).forest
        have hprefChild : (pref ++ [e.val]).toFinset = child.edges := by
          rw [List.toFinset_append, (choices F e).extension.edges_eq, hpref]
          simp
        have hprefixTsChild :
            (prefixTs ++ [t]).length = (pref ++ [e.val]).length := by
          simp [hprefixTs]
        have htIcc : t ∈ Set.Icc 0 top := by
          simpa [Set.uIcc_of_le htop] using ht
        have hboundChild :
            ∀ s ∈ Set.uIcc 0 t,
              ∀ e' : child.EdgeParam,
                s ≤ child.paramsOfOrder (pref ++ [e.val])
                  (prefixTs ++ [t]) e' :=
          allBranchesAnalytic_parameterBound_child choices F pref prefixTs
            top hpref hprefixTs htop hbound e ht
        exact
          allBranchesAnalytic_of_contDiff hρ choices n child
            (pref ++ [e.val]) (prefixTs ++ [t]) t
            hprefChild hprefixTsChild htIcc.1 hboundChild

end BKARContDiff
end BKAR
end
end
