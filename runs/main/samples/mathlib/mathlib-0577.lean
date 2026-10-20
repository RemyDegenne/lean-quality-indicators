@[expose] public section

open Complex hiding I

open Matrix hiding mul_smul

open Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup Topology

noncomputable section

open scoped ComplexConjugate MatrixGroups

namespace ModularGroup

variable {g : SL(2, ℤ)} (z : ℍ)

section FundamentalDomain

attribute [local simp] UpperHalfPlane.coe_specialLinearGroup_apply

variable {z}

@[inherit_doc ModularGroup.fd]
scoped[Modular] notation "𝒟" => ModularGroup.fd

@[inherit_doc ModularGroup.fdo]
scoped[Modular] notation "𝒟ᵒ" => ModularGroup.fdo

open scoped Modular

section Topology

lemma coe_fdo : (↑) '' 𝒟ᵒ = {z : ℂ | 0 < z.im ∧ 1 < ‖z‖ ∧ |z.re| < 1/2} := by
  ext x
  refine ⟨?_, fun ⟨hxim, hxnorm, hxre⟩ ↦ ⟨⟨x, hxim⟩, ⟨one_lt_normSq_iff.mpr hxnorm, hxre⟩, rfl⟩⟩
  rintro ⟨τ, hτ, rfl⟩
  exact ⟨τ.im_pos, one_lt_normSq_iff.mp hτ.1, hτ.2⟩

end Topology
end FundamentalDomain
end ModularGroup
end
end
