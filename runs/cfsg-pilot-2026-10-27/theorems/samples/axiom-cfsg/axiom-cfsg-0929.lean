public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

open CFSG.Quasithin (perfectCore)

open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

open CFSG.SeitzReduction.LinearPilot (rootTorusParam)

section Transport

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  (h : UnitaryFieldData 2 f K) {n : ℕ} (e : L ≃* unitaryPSU h n)

theorem exists_neighbourCore_eq_map_conj {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ w ∈ L, neighbourCore e hcd = (neighbourCore e hab).map (MulAut.conj w).toMonoidHom := by
  obtain ⟨ρ, hρa, hρb⟩ := LinearPilot.exists_perm_apply_eq_apply_eq hab hcd
  obtain ⟨w, hw, -, hN⟩ := exists_pieceCore_map_conj h e ρ
  refine ⟨w, hw, ?_⟩
  have h1 := hN a b hab
  have e1 : neighbourCore e (ρ.injective.ne hab) = neighbourCore e hcd := by
    rw [neighbourCore_def, neighbourCore_def]
    congr 2
    subst hρa hρb
    rfl
  rw [← e1, h1]

end Transport
end CFSG.SeitzReduction.UnitaryPilot
end
