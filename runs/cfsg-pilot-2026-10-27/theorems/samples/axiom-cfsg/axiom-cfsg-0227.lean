public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional

namespace InnerDiagTwE6

section Isogeny

open CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {k : Type} [Field k] [Finite k]

variable (θ : k →+* k)

variable (θ : k →+* k)

variable (hθ : ∀ c, θ (θ c) = c)

include hθ in
theorem exists_diag_of_rankOne {G : Type*} [Group G] (ψ : fixedGroup k θ →* G)
    (hR : ∀ (d : G) (j : Fin (Tag.rank .F4)) (h : fixedGroup k θ),
      h ∈ ggTorus (twistedDatum k θ) →
      (∀ z ∈ (twistedDatum k θ).rootGroup (Pi.single j 1), d⁻¹ * ψ z * d = ψ z) →
      (∀ z ∈ (twistedDatum k θ).rootGroup (-Pi.single j 1),
        d⁻¹ * ψ z * d = ψ (h * z * h⁻¹)) →
      ∀ z ∈ (twistedDatum k θ).rootGroup (-Pi.single j 1), d⁻¹ * ψ z * d = ψ z)
    {c : G} (hc : GGPsiInnerDiag (twistedDatum k θ) ψ c) :
    ∃ g ∈ ψ.range, ∃ b : Fin (Tag.rank .E6) → kˣ,
      (∀ i, b (rhoPerm i) = Units.map θ.toMonoidHom (b i)) ∧
      ∀ (j : Fin (Tag.rank .F4)) (γ : Fin (Tag.rank .F4) → ℤ),
        (γ = Pi.single j 1 ∨ γ = -Pi.single j 1) →
        ∀ z ∈ (twistedDatum k θ).rootGroup γ, ∃ z' : fixedGroup k θ,
          (c * g)⁻¹ * ψ z * (c * g) = ψ z' ∧
            ((e6Isogeny k (z' : e6Data_valid.minGroup k) : ↥(adjointGroup .E6 k)) :
              ModGL .E6 k) =
              rootDiagUnit .E6 b *
                ((e6Isogeny k (z : e6Data_valid.minGroup k) : ↥(adjointGroup .E6 k)) :
                  ModGL .E6 k) * (rootDiagUnit .E6 b)⁻¹ := by
  obtain ⟨g, hg, hγ⟩ := hc
  have hT := iSup_hHat_le_ggTorus θ hθ
  have hpos : ∀ j : Fin (Tag.rank .F4), ∃ t ∈ ⨆ i, hHat k θ i,
      ∃ bt : Fin (Tag.rank .E6) → kˣ, (∀ i, bt (rhoPerm i) = Units.map θ.toMonoidHom (bt i)) ∧
        ((e6Isogeny k (t : e6Data_valid.minGroup k) : ↥(adjointGroup .E6 k)) : ModGL .E6 k) =
          rootDiagUnit .E6 bt ∧
        ∀ z ∈ (twistedDatum k θ).rootGroup (Pi.single j 1),
          (c * g)⁻¹ * ψ z * (c * g) = ψ (t * z * t⁻¹) := by
    intro j
    obtain ⟨h, hh, hz⟩ := hγ _ (single_mem_roots j)
    obtain ⟨t, ht, htz⟩ := exists_twistedTorus_conj θ hθ j hh
    obtain ⟨bt, hbt, hπ⟩ := exists_compat_of_mem_iSup_hHat θ hθ ht
    exact ⟨t, ht, bt, hbt, hπ, fun z hzz => by rw [hz z hzz, htz z hzz]⟩
  choose t ht bt hbt hπ hact using hpos
  have hneg : ∀ j : Fin (Tag.rank .F4), ∀ z ∈ (twistedDatum k θ).rootGroup (-Pi.single j 1),
      (c * g)⁻¹ * ψ z * (c * g) = ψ (t j * z * (t j)⁻¹) := by
    intro j
    obtain ⟨h, hh, hz⟩ := hγ _ (neg_single_mem_roots j)
    have hcen : ∀ z ∈ (twistedDatum k θ).rootGroup (Pi.single j 1),
        ((c * g) * ψ (t j))⁻¹ * ψ z * ((c * g) * ψ (t j)) = ψ z := by
      intro z hzz
      calc ((c * g) * ψ (t j))⁻¹ * ψ z * ((c * g) * ψ (t j)) =
            (ψ (t j))⁻¹ * ((c * g)⁻¹ * ψ z * (c * g)) * ψ (t j) := by group
        _ = (ψ (t j))⁻¹ * ψ (t j * z * (t j)⁻¹) * ψ (t j) := by rw [hact j z hzz]
        _ = ψ z := by rw [map_mul, map_mul, map_inv]; group
    have hact' : ∀ z ∈ (twistedDatum k θ).rootGroup (-Pi.single j 1),
        ((c * g) * ψ (t j))⁻¹ * ψ z * ((c * g) * ψ (t j)) =
          ψ (((t j)⁻¹ * h) * z * ((t j)⁻¹ * h)⁻¹) := by
      intro z hzz
      calc ((c * g) * ψ (t j))⁻¹ * ψ z * ((c * g) * ψ (t j)) =
            (ψ (t j))⁻¹ * ((c * g)⁻¹ * ψ z * (c * g)) * ψ (t j) := by group
        _ = (ψ (t j))⁻¹ * ψ (h * z * h⁻¹) * ψ (t j) := by rw [hz z hzz]
        _ = ψ (((t j)⁻¹ * h) * z * ((t j)⁻¹ * h)⁻¹) := by
          rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_mul, map_inv, map_inv, map_mul,
            map_inv]
          group
    have key := hR ((c * g) * ψ (t j)) j ((t j)⁻¹ * h) (mul_mem (inv_mem (hT (ht j))) hh) hcen
      hact'
    intro z hzz
    calc (c * g)⁻¹ * ψ z * (c * g) = ψ (t j) *
          (((c * g) * ψ (t j))⁻¹ * ψ z * ((c * g) * ψ (t j))) * (ψ (t j))⁻¹ := by group
      _ = ψ (t j) * ψ z * (ψ (t j))⁻¹ := by rw [key z hzz]
      _ = ψ (t j * z * (t j)⁻¹) := by rw [map_mul, map_mul, map_inv]
  refine ⟨g, hg, fun a => bt (orbitMap a) a, fun i => ?_, fun j γ hγ' z hz =>
    ⟨t j * z * (t j)⁻¹, ?_, ?_⟩⟩
  · simp only
    rw [orbitMap_rhoPerm]
    exact hbt _ i
  · rcases hγ' with rfl | rfl
    · exact hact j z hz
    · exact hneg j z hz
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hπ j]
    exact rootDiagUnit_conj_eq_of_agree θ j hγ' (b := fun a => bt (orbitMap a) a)
      (fun a ha => by simp only [ha]) hz

end Isogeny
end InnerDiagTwE6
end CFSG.StandardType
end
