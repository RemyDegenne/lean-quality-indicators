public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBd8

namespace Psl2

section Borel

variable {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {U K : Subgroup X}

theorem eq_normalizer_of_isPSL {n : ℕ} (h : IsPSL 2 2 n X) (d : OvgData X A U K) :
    K = Subgroup.normalizer (U : Set X) := by
  have hKle : K ≤ Subgroup.normalizer (U : Set X) := by
    rcases SBc6.overgroup_of_psl h d.U_syl d.U_le with h1 | h1
    · exact absurd h1 d.K_ne
    · exact h1
  have hNne : Subgroup.normalizer (U : Set X) ≠ ⊤ := fun h1 =>
    SBc6.not_normal_sylow_of_psl h d.U_syl (le_of_eq h1.symm)
  have hNinv : ∀ α ∈ A, (Subgroup.normalizer (U : Set X)).map α.toMonoidHom =
      Subgroup.normalizer (U : Set X) := by
    intro α hα
    rw [Subgroup.map_equiv_normalizer_eq U α, d.A_U α hα]
  exact le_antisymm hKle (d.K_max _ hKle hNne hNinv)

end Borel
end Psl2
end SBd8
end CFSG.Quasithin
end
