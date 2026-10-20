public section

open CategoryTheory Multiplicative

namespace TauCeti.Toric.FanHom

universe u

variable {N N' V V' : Type u} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  (f : FanHom Φ Ψ) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)

theorem eq_analyticMap_iff (hΦ0 : Nonempty Φ.cones)
    {g : Φ.analyticRealization hΦ ⟶ Ψ.analyticRealization hΨ} :
    g = f.analyticMap hΦ hΨ ↔ ∀ t, g (Φ.analyticTorusι hΦ hΦ0 t) =
      Ψ.analyticTorusι hΨ ⟨⟨f.leastCone hΦ0.some.2, f.leastCone_mem hΦ0.some.2⟩⟩
        (complexTorusMap f.latticeMap t) := by
  constructor
  · rintro rfl t
    exact f.analyticMap_analyticTorusι hΦ hΨ hΦ0 t
  · intro h
    apply Φ.analyticRealization_hom_ext_torus hΦ hΦ0
    intro t
    rw [h, f.analyticMap_analyticTorusι hΦ hΨ hΦ0]

end TauCeti.Toric.FanHom
end
