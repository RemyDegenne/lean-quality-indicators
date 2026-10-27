public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace Hyp183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem T_ne_bot (h : Hyp183 D V₀ V H i) : D.T ≠ ⊥ := fun hT =>
  h.setting.pair.ne_bot (le_bot_iff.mp (hT ▸ h.V_le_T))

end Hyp183
end CFSG.LocalAnalysis.WeakClosure81
end
