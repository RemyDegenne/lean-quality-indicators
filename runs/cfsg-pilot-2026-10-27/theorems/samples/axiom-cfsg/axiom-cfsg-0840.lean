public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis.SteinbergBX CFSG.LocalAnalysis.SteinbergBX.GMSAffine

namespace EvenPairPlane

variable {Ω : Type*} {N : Subgroup (Equiv.Perm Ω)} {τ : Equiv.Perm Ω} {α β : Ω} {s : ℕ}

theorem parallelClass_eq_or_disjoint [Finite Ω] (hG : InvolutionGeometry N τ α β s)
    {ℓ₀ ℓ m : Set Ω} (hℓ₀ : ℓ₀ ∈ permTranslates N (Function.fixedPoints ⇑τ))
    (hℓ : ℓ ∈ parallelClass (permTranslates N (Function.fixedPoints ⇑τ)) ℓ₀)
    (hm : m ∈ parallelClass (permTranslates N (Function.fixedPoints ⇑τ)) ℓ₀) :
    ℓ = m ∨ Disjoint ℓ m := by
  obtain ⟨hℓL, rfl | hℓd⟩ := hℓ
  · obtain ⟨-, rfl | hmd⟩ := hm
    · exact Or.inl rfl
    · exact Or.inr hmd.symm
  · obtain ⟨hmL, rfl | hmd⟩ := hm
    · exact Or.inr hℓd
    · exact eq_or_disjoint_of_disjoint hG hℓL hmL hℓ₀ hℓd hmd

end EvenPairPlane
end CFSG.SeitzReduction.RankOne
end
