namespace P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi

attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

set_option synthInstance.maxSize 1024

p2m_open

open scoped SchwartzMap NNReal ENNReal FourierTransform nonZeroDivisors

noncomputable section

namespace NumberField

namespace AdelicFourier

namespace Poisson2Box

p2m_open

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

section Lattice

variable (F)

variable {F}

scoped instance (d : 𝓞 F) (hd : d ≠ 0) : DiscreteTopology (latL d hd) := by
  unfold latL; infer_instance

scoped instance (d : 𝓞 F) (hd : d ≠ 0) : IsZLattice ℝ (latL d hd) := by
  unfold latL; infer_instance

def boxEquiv {d : 𝓞 F} (hd : d ≠ 0) (k : Fin 2 → F) :
    {ξ : Fin 2 → F // ∀ i, ∃ a : 𝓞 F, ξ i = k i + (d : F) * a} ≃ latL d hd :=
  Equiv.ofBijective (fun ξ => ⟨iotaV F (ξ.1 - k), iotaV_sub_mem_latL hd ξ.2⟩) (by
    constructor
    · intro ξ η h
      have h' : iotaV F (ξ.1 - k) = iotaV F (η.1 - k) := congrArg Subtype.val h
      exact Subtype.ext (sub_left_injective (iotaV_injective F h'))
    · intro x
      obtain ⟨x, hx⟩ := x
      rw [mem_latL_iff] at hx
      choose a ha using hx
      refine ⟨⟨fun i => k i + (d : F) * a i, fun i => ⟨a i, rfl⟩⟩, Subtype.ext ?_⟩
      funext i
      simp only [iotaV, Pi.sub_apply, add_sub_cancel_left]
      exact (ha i).symm)

end Lattice
end Poisson2Box
end AdelicFourier
end NumberField
end
end P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_schwartzMap_mul_indicator_pi
