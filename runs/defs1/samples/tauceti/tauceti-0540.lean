public section

namespace TauCeti.Hodge

universe u v u' v'

namespace HodgeStructureOn

variable {W : Type u} [AddCommGroup W] [Module ℂ W]

variable {ω : Conjugation W} {n : ℤ}

variable {hs : HodgeStructureOn W ω n} {U : Submodule ℂ W}

namespace IsSubstructure

/-- The pure Hodge structure induced on the quotient by a sub-Hodge structure: its filtration is
the image of the ambient filtration. Opposedness descends because the sub-Hodge structure is
itself split by the two complementary ambient steps. -/
noncomputable def quotient (h : hs.IsSubstructure U) :
    HodgeStructureOn (W ⧸ U) (ω.quotient h.conj_mem) n where
  F p := (hs.F p).map U.mkQ
  F_antitone _ _ hpq := Submodule.map_mono (hs.F_antitone hpq)
  F_top := by
    obtain ⟨p, hp⟩ := hs.F_top
    exact ⟨p, by rw [hp, Submodule.map_top, Submodule.range_mkQ]⟩
  opposed p := by
    rw [h.map_quotient_conj_map_mkQ, ← hs.conjF_def]
    constructor
    · rw [disjoint_iff, Submodule.map_inf_eq_map_inf_comap, Submodule.comap_map_mkQ,
        ← le_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ,
        sup_comm]
      exact h.F_inf_conjF_sup_le p
    · rw [codisjoint_iff, ← Submodule.map_sup, (hs.isCompl_F_conjF p).sup_eq_top,
        Submodule.map_top, Submodule.range_mkQ]

end IsSubstructure
end HodgeStructureOn
end TauCeti.Hodge
end
