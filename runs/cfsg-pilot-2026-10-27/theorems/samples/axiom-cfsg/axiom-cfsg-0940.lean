public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Quasithin

open scoped Pointwise

theorem exists_mulEquiv_pointStab_eq_map_sylow {W : Type} [CommGroup W] [Finite W]
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] {Γ : Subgroup (GL ι K)}
    {H : Subgroup (MulAut W)} (hreal : (FFModel.nat Γ).Realizes H ⊤ ⊥) {e₀ : ι → K}
    (hline : KTabC.SylowFixedLine Γ e₀) (U : Sylow 2 ↥Γ)
    (hU : (U : Subgroup ↥Γ) ≤ KTabD.lineStab Γ e₀) (S : Sylow 2 ↥H) :
    ∃ φ : ↥Γ ≃* ↥H, (U : Subgroup ↥Γ).map φ.toMonoidHom = S ∧
      KTabD.pointStab H S = (KTabD.lineStab Γ e₀).map φ.toMonoidHom := by
  obtain ⟨φ₀, hφ₀⟩ := KTabD.exists_mulEquiv_pointStab_eq_map hreal hline S
  have hS : (S : Subgroup ↥H) ≤ (KTabD.lineStab Γ e₀).map φ₀.toMonoidHom := by
    rw [← hφ₀]
    exact sylow_le_pointStab H S
  obtain ⟨φ, hφU, hφQ⟩ :=
    exists_mulEquiv_map_sylow_eq (Q := KTabD.lineStab Γ e₀) φ₀ U hU S hS
  exact ⟨φ, hφU, by rw [hφQ]; exact hφ₀⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
end
