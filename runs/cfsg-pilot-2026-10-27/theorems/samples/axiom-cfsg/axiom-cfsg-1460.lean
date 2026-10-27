public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS

section FromModel

variable {G Gs : Type} [Group G] [Group Gs] {z : G} {S : Sylow 2 G} {z' : Gs} {S' : Sylow 2 Gs}

theorem setup_of_model [Finite G] [Finite Gs] {q : ℕ} {ε : ℤ} (I : CompatIso G z S z' S')
    (hz : (center ↥(S : Subgroup G)).map (S : Subgroup G).subtype = zpowers z)
    (hz' : (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z')
    (hA : IsCyclic ↥(pPrimeCore 2 ↥(Cz z)) ∧
      Nat.card ↥(pPrimeCore 2 ↥(Cz z)) ∣ Nat.card ↥(pPrimeCore 2 ↥(Cz z')))
    {E₁ E₂ : Subgroup Gs} {t' u' : Gs} (d : LUModelData Gs q ε z' S' E₁ E₂ t' u') :
    ∃ (K₁ K₂ : Subgroup G) (t u : G), LUComps G q z K₁ K₂ ∧ LUSyl G z S K₁ K₂ t u ∧
      LUEps G q ε z K₁ u := by
  set ψ := I.ψ with hψ
  have hA0e : ↥(pPrimeCore 2 ↥(Cz z)) ≃* ↥(A0 z) :=
    (pPrimeCore 2 ↥(Cz z)).equivMapOfInjective (Cz z).subtype (Cz z).subtype_injective
  have hcyc : IsCyclic ↥(A0 z) := by
    have := hA.1
    exact isCyclic_of_surjective hA0e.toMonoidHom hA0e.surjective
  have hcomps := LUComps.transport I hz hz' hcyc d.comps d.syl.z_inv
  obtain ⟨t, u, ht, hu, hψt, hψu, hsyl⟩ := LUSyl.transport I hz hz' d.comps d.syl
  have hE₁ : E₁ ≤ layerTimesSylow z' (S' : Subgroup Gs) :=
    (le_layer_of_isCompIn d.comps.comp₁).trans le_sup_left
  have hHle : E₁ ⊓ centralizer ({u'} : Set Gs) ≤ layerTimesSylow z' (S' : Subgroup Gs) :=
    inf_le_left.trans hE₁
  have hH := pull_inf_centralizer ψ E₁ hu hψu
  refine ⟨pull ψ E₁, pull ψ E₂, t, u, hcomps, hsyl, ?_⟩
  refine ⟨d.eps, d.mod8, hcyc, ?_, ?_, ?_⟩
  · have h1 : Nat.card ↥(A0 z) = Nat.card ↥(pPrimeCore 2 ↥(Cz z)) :=
      (Nat.card_congr hA0e.toEquiv).symm
    rw [h1]
    exact (Int.natCast_dvd_natCast.mpr hA.2).trans d.A0_dvd
  · rw [← hH]
    have := d.H_cyc
    exact isCyclic_of_surjective (pullEquiv ψ hHle).symm.toMonoidHom (pullEquiv ψ hHle).symm.surjective
  · rw [← hH, card_pull ψ hHle]
    exact d.H_card

end FromModel
end CFSG.GH74.GLS.LU.Local
end
