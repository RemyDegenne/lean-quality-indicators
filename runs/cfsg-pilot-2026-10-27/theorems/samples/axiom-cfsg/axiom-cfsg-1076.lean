public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {K : Type} [Field K]

variable [Finite K]

theorem exists_lift_two_pow (h2 : (2 : K) = 0) (hn : 0 < n) {y : projectiveSL n K} {a : ℕ}
    (hy : y ^ (2 ^ a) = 1) :
    ∃ g : SpecialLinearGroup (Fin n) K, proj n K g = y ∧ g ^ (2 ^ a) = 1 := by
  classical
  obtain ⟨g₀, rfl⟩ := proj_surjective n K y
  have hw : g₀ ^ (2 ^ a) ∈ scalars n K := by
    rw [← proj_eq_one_iff, map_pow]
    exact hy
  have hwinv : (g₀ ^ (2 ^ a))⁻¹ ∈ scalars n K := (scalars n K).inv_mem hw
  have hcentral : ∀ z ∈ scalars n K, ∀ g : SpecialLinearGroup (Fin n) K, Commute z g :=
    fun z hz g => scalars_commute hz g
  let f : ↥(scalars n K) → ↥(scalars n K) := fun z => z ^ (2 ^ a)
  have hfinj : Function.Injective f := by
    intro z₁ z₂ h
    have h' : (z₁ : SpecialLinearGroup (Fin n) K) ^ (2 ^ a) =
        (z₂ : SpecialLinearGroup (Fin n) K) ^ (2 ^ a) := congrArg Subtype.val h
    have hc : Commute (z₁ : SpecialLinearGroup (Fin n) K) (z₂ : SpecialLinearGroup (Fin n) K)⁻¹ :=
      hcentral _ z₁.2 _
    have h1 : ((z₁ : SpecialLinearGroup (Fin n) K) * (z₂ : SpecialLinearGroup (Fin n) K)⁻¹) ^ (2 ^ a) =
        1 := by
      rw [hc.mul_pow, inv_pow, h', mul_inv_cancel]
    have h3 := scalars_eq_one_of_two_pow h2 hn
      ((scalars n K).mul_mem z₁.2 ((scalars n K).inv_mem z₂.2)) a h1
    exact Subtype.ext (mul_inv_eq_one.1 h3)
  have hfsurj : Function.Surjective f := Finite.injective_iff_surjective.1 hfinj
  obtain ⟨z, hz⟩ := hfsurj ⟨(g₀ ^ (2 ^ a))⁻¹, hwinv⟩
  have hz' : (z : SpecialLinearGroup (Fin n) K) ^ (2 ^ a) = (g₀ ^ (2 ^ a))⁻¹ := congrArg Subtype.val hz
  refine ⟨(z : SpecialLinearGroup (Fin n) K) * g₀, ?_, ?_⟩
  · rw [map_mul, proj_eq_one_iff.2 z.2, one_mul]
  · rw [(hcentral _ z.2 g₀).mul_pow, hz', inv_mul_cancel]

end CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin
end
