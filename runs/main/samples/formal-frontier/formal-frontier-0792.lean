@[expose] public section

noncomputable section

universe u

namespace SplitQuadric

open ToricIdeals.SplitQuadric

variable (A : Type u) [CommRing A]

theorem phi_injective : Function.Injective (phi A) := by
  change Function.Injective
    (Ideal.Quotient.lift (relationIdeal A) (theta A).toRingHom
      (fun p hp => relationIdeal_le_ker_aeval A (parameterValues A)
        (parameterValues_relation A) hp))
  exact RingHom.lift_injective_of_ker_le_ideal
    (f := (theta A).toRingHom) (relationIdeal A)
    (fun p hp => relationIdeal_le_ker_aeval A (parameterValues A)
      (parameterValues_relation A) hp)
    (le_of_eq (kernel_theta A))

end SplitQuadric
end
end
