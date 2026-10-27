public section

namespace CFSG.HardMathSupport.C14Exc

open CFSG CFSG.Assembly CFSG.StandardType

theorem geo_central_of_absGeo {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {Γ : Type*}
    [Group Γ] {G : Subgroup Γ} {F₀ : Γ →* Γ} {Θ : G →* MulAut R} (hΘ : Function.Injective Θ)
    (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ) {Ebar : Subgroup (MulAut R)} (hEI : ∀ e ∈ Ebar, e ∈ I)
    (hAbs : AbsGeo p G F₀ (bridgeSub Θ Ebar)) :
    ∀ u : MulAut R, GGL45NtCIp p I Ebar u → ∀ w ∈ I, (∀ e ∈ Ebar, w * e = e * w) →
      w * u = u * w := by
  intro u hu w hwI hwcomm
  obtain ⟨g, rfl⟩ := (hI u).1 hu.1
  obtain ⟨h, rfl⟩ := (hI w).1 hwI
  have hgp : (g : Γ) ∈ pCent p G (bridgeSub Θ Ebar) := (cip_iff_pCent hΘ hI hEI g).1 hu
  have hwcent : ∀ e ∈ bridgeSub Θ Ebar, (h : Γ) * e = e * (h : Γ) := by
    intro e he
    obtain ⟨k, hkE, rfl⟩ := (eA5_mem_bridgeSub_iff Θ Ebar e).1 he
    have hc : Θ h * Θ k = Θ k * Θ h := hwcomm _ hkE
    have hhk : h * k = k * h := hΘ (by rw [map_mul, map_mul, hc])
    simpa using congrArg Subtype.val hhk
  have hc : (h : Γ) * (g : Γ) = (g : Γ) * (h : Γ) :=
    hAbs.2.1 (g : Γ) hgp (h : Γ) h.2 hwcent
  have hgh : h * g = g * h := Subtype.ext (by simpa using hc)
  rw [← map_mul, ← map_mul, hgh]

end CFSG.HardMathSupport.C14Exc
end
