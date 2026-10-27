public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem

theorem tits_chamber_universal_completion
    {I C : Type*} (X : ChamberSystem I C) (hX : X.Connected) (hS : X.SimplyTwoConnected)
    {G : Type*} [Group G] (ρ : G →* X.typeAut) (c₀ : C)
    (htrans : ∀ c : C, ∃ g : G, ((ρ g : X.typeAut) : Equiv.Perm C) c₀ = c)
    (P : Set I → Subgroup G)
    (hP : ∀ J : Set I, J.encard ≤ 2 → ∀ g : G,
      g ∈ P J ↔ ((ρ g : X.typeAut) : Equiv.Perm C) c₀ ∈ X.residue J c₀)
    {Y : Type*} [Group Y] (φ : ∀ J : Set I, J.encard ≤ 2 → P J →* Y)
    (hφ : ∀ (J K : Set I) (hJ : J.encard ≤ 2) (hK : K.encard ≤ 2), K ⊆ J → ∀ (g : G)
      (hgK : g ∈ P K) (hgJ : g ∈ P J), φ K hK ⟨g, hgK⟩ = φ J hJ ⟨g, hgJ⟩) :
    ∃! ψ : G →* Y, ∀ (J : Set I) (hJ : J.encard ≤ 2) (g : P J), ψ g = φ J hJ g := by
  let _ : MulAction G C := MulAction.compHom C (X.typeAut.subtype.comp ρ)
  exact tits_chamber_universal_completion_of_family X (fun J => J.encard ≤ 2)
    (by simp) (fun i => encard_singleton_le_two i) hX
    ((TitsChamber.simplyTwoConnected_iff X).1 hS)
    (fun g i x y h => ((ρ g).2 i x y).2 h) c₀ htrans P hP φ hφ

end CFSG.ClassicalInvolution.Phan
end
