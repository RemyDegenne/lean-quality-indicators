@[expose] public section

universe uR uP

open Finsupp Set

namespace Module.Projective

variable {R : Type uR} [Ring R]

variable {P : Type uP} [AddCommGroup P] [Module Rᵐᵒᵖ P]

theorem free_of_countablyGenerated
    [Module.Projective Rᵐᵒᵖ P]
    (I : TwoSidedIdeal R) (hI : I ≠ ⊤) (hunit : ∀ r ∉ I, IsUnit r)
    (hP : Module.CountablyGenerated Rᵐᵒᵖ P) :
    Module.Free Rᵐᵒᵖ P := by
  obtain ⟨k, ⟨b⟩⟩ :=
    exists_sigma_fin_rightBasis_of_countablyGenerated I hI hunit hP
  exact Module.Free.of_basis b

end Module.Projective
end
