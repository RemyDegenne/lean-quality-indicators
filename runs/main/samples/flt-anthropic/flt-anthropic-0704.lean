namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_isOpen_forall_apply_mul_iotaGL_mul_eq

set_option autoImplicit false

open IsDedekindDomain NumberField

p2m_reactivate

p2m_reactivate

namespace LanglandsTunnell

namespace CubicInduction

namespace SmoothVector

p2m_open

p2m_open

variable (v : HeightOneSpectrum (𝓞 ℚ))

variable {v}

theorem exists_nhds_forall_apply_mul_eq {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) :
    ∃ V : Set (LocalGL3 v), IsOpen V ∧ (1 : LocalGL3 v) ∈ V ∧ ∀ g : LocalGL3 v, ∀ r ∈ V, f (g * r) = f g := by
  obtain ⟨V, hV, h1V, hCV⟩ := exists_open_forall_mem_compact_apply_mul_eq
    (isLocallyConstant_of_mem_principalSeries3 hf) (isCompact_wordInvSet v)
  refine ⟨V, hV, h1V, fun g r hr => ?_⟩
  obtain ⟨p, c, hp, hgc⟩ := exists_apply_mul_eq_mul_apply_wordInv_mul hf g
  have h := hCV _ (wordInv_mem_wordInvSet hp) r hr
  rw [hgc r, h, ← mul_one (word p)⁻¹, ← hgc 1, mul_one]

end SmoothVector
end CubicInduction
end LanglandsTunnell
end P2MW.S_LanglandsTunnell_CubicInduction_exists_isOpen_forall_apply_mul_iotaGL_mul_eq
